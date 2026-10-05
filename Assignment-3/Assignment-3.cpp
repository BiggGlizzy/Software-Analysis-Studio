//===- Assignment-3.cpp -- Taint analysis ------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2022>  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//
/*
 * Graph reachability, Andersen's pointer analysis and taint analysis
 *
 * Created on: Feb 18, 2024
 */

#include "Assignment-3.h"
#include "WPA/Andersen.h"
#include "Graphs/ConsGEdge.h"  // for NormalGepCGEdge, used in solveWorklist's Gep handling
#include <sys/stat.h>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#include <functional>   // for the recursive dfs lambda in reachability()
 
using namespace SVF;
using namespace llvm;
using namespace std;

/// TODO: Implement your code to parse the two lines to identify sources and sinks from `SrcSnk.txt` for your
/// reachability analysis The format in SrcSnk.txt is in the form of
/// line 1 for sources  "{ api1 api2 api3 }"
/// line 2 for sinks    "{ api1 api2 api3 }"


// Parses "source -> { ... }" / "sink -> { ... }" lines into checker_source_api / checker_sink_api.
void ICFGTraversal::readSrcSnkFromFile(const string& filename) { 
	std::ifstream in(filename);
	if (!in.is_open()) {
		std::cerr << "Failed to open source/sink config file: " << filename << std::endl;
		return;
	}
 
	std::string line;
	while (std::getline(in, line)) {
		size_t arrowPos = line.find("->");
		if (arrowPos == std::string::npos)
			continue;
 
		// Decide source vs. sink from the label text, not line order.
		std::string label = line.substr(0, arrowPos);
		std::set<std::string>* target = nullptr;
		if (label.find("source") != std::string::npos)
			target = &checker_source_api;
		else if (label.find("sink") != std::string::npos)
			target = &checker_sink_api;
		else
			continue;
 
		// Grab everything between the braces.
		size_t lbrace = line.find('{', arrowPos);
		size_t rbrace = line.find('}', arrowPos);
		if (lbrace == std::string::npos || rbrace == std::string::npos || rbrace < lbrace)
			continue;
 
		std::string content = line.substr(lbrace + 1, rbrace - lbrace - 1);
 
		// Split on whitespace into individual function names.
		std::istringstream iss(content);
		std::string token;
		while (iss >> token) {
			target->insert(token);
		}
	}
 
	in.close();
}

/// TODO: Convert each collected ICFG path into a string and insert it into
/// `std::set<std::string> paths`. The path should use the format
/// "START->1->2->4->5->END", where each pair of adjacent node IDs is connected
/// by an ICFG edge, similar to Assignment 2.


// Turns a node-ID path into "START->1->2->...->END" and stores it.
/*
void ICFGTraversal::collectICFGPath(std::vector<unsigned>& path) {
	std::stringstream ss;
	ss << "START";
	for (unsigned nodeId : path) {
		ss << "->" << nodeId;
	}
	ss << "->END";
	paths.insert(ss.str());
}
*/

/// TODO: Implement context-sensitive ICFG traversal from `src` to `snk` by
/// matching call and return edges while maintaining a `callstack`. Each path,
/// including loops and qualified by its callstack, should only be traversed
/// once using `visited`. Call `collectICFGPath` for every reachable path.


// Context-sensitive DFS from src to snk on the ICFG, using callstack to make sure
// Call/Return edges are matched (no "return to a caller we never came from").
void ICFGTraversal::reachability(const ICFGNode* src, const ICFGNode* snk) {
	// Reset shared state -- this can be called many times, once per candidate pair.
	callstack.clear();
	path.clear();
	visited.clear();
 
	// Local recursive lambda so we don't need a new member function in the header.
	std::function<void(const ICFGNode*)> dfs = [&](const ICFGNode* cur) {
		// Skip if we've already explored this node under this exact call context.
		ICFGNodeCallStackPair curItem = std::make_pair(cur, callstack);
		if (visited.find(curItem) != visited.end())
			return;
		visited.insert(curItem);
 
		path.push_back(cur->getId());
 
		// Keep exploring past the sink too, in case a longer path loops back through it.
		/*
		if (cur == snk) {
			collectICFGPath(path);
		}
		*/
		//replaced with:
		if (cur == snk) {
			std::stringstream ss;
			ss << "START";
			for (unsigned nodeId : path) {
				ss << "->" << nodeId;
			}
			ss << "->END";
			paths.insert(ss.str());
		}
 
		for (const ICFGEdge* edge : cur->getOutEdges()) {
			const ICFGNode* dst = edge->getDstNode();
 
			if (edge->isIntraCFGEdge()) {
				dfs(dst); // plain statement-to-statement flow
			}
			else if (edge->isCallCFGEdge()) {
				// Entering a callee: remember which call site we came from.
				callstack.push_back(edge->getSrcNode());
				dfs(dst);
				callstack.pop_back(); // undo so sibling edges see the old callstack
			}
			else if (edge->isRetCFGEdge()) {
				if (!callstack.empty()) {
					// Only follow a return that matches the call site we entered from.
					if (const RetICFGNode* retNode = SVFUtil::dyn_cast<RetICFGNode>(dst)) {
						if (callstack.back() == retNode->getCallICFGNode()) {
							callstack.pop_back();
							dfs(dst);
							callstack.push_back(retNode->getCallICFGNode());
						}
						// else: mismatched call/return, prune this branch
					}
				}
				else {
					dfs(dst); // no caller context recorded, nothing to mismatch against
				}
			}
		}
 
		path.pop_back(); // backtrack so `path` reflects only the current branch
	};
 
	dfs(src);
}

// TODO: Implement your Andersen's Algorithm here
/// The solving rules are as follows:
/// p <--Addr-- o        =>  pts(p) = pts(p) ∪ {o}
/// q <--COPY-- p        =>  pts(q) = pts(q) ∪ pts(p)
/// q <--LOAD-- p        =>  for each o ∈ pts(p) : q <--COPY-- o
/// q <--STORE-- p       =>  for each o ∈ pts(q) : o <--COPY-- p
/// q <--GEP, fld-- p    =>  for each o ∈ pts(p) : pts(q) = pts(q) ∪ {o.fld}
/// pts(q) denotes the points-to set of q


// Andersen's pointer analysis worklist loop (Address rule is already handled before this runs).
void AndersenPTA::solveWorklist() {
	while (!isWorklistEmpty()) {
		NodeID nodeId = popFromWorklist();
		ConstraintNode* node = consCG->getConstraintNode(nodeId);
 
		const PointsTo& pts = getPts(nodeId);
		for (const NodeID o : pts) {
			// Store rule: *nodeId = q, and nodeId points to o => q flows into o.
			for (ConstraintEdge* edge : node->getStoreInEdges()) {
				NodeID q = edge->getSrcID();
				if (addCopyEdge(q, o)) {
					pushIntoWorklist(q);
				}
			}
 
			// Load rule: r = *nodeId, and nodeId points to o => o flows into r.
			for (ConstraintEdge* edge : node->getLoadOutEdges()) {
				NodeID r = edge->getDstID();
				if (addCopyEdge(o, r)) {
					pushIntoWorklist(o);
				}
			}
		}
 
		// Direct out-edges mix plain Copy edges and Gep (field) edges, and they need
		// different treatment: Copy unions the whole set, but Gep must map each
		// object o to its field-specific object o.fld via getGepObjVar() -- just
		// unioning the raw set here (as before) silently points at the wrong
		// (base) object and breaks aliasing through struct/array fields.
		for (ConstraintEdge* edge : node->getDirectOutEdges()) {
			NodeID x = edge->getDstID();

			if (const NormalGepCGEdge* gepEdge = SVFUtil::dyn_cast<NormalGepCGEdge>(edge)) {
				// Gep rule: for each o in pts(nodeId), pts(x) = pts(x) U {o.fld}
				for (const NodeID o : getPts(nodeId)) {
					NodeID fieldObj = getGepObjVar(o, gepEdge->getConstantFieldIdx());
					if (unionPts(x, fieldObj)) {
						pushIntoWorklist(x);
					}
				}
			}
			else {
				// Copy rule: pts(x) = pts(x) U pts(nodeId)
				if (unionPts(x, getPts(nodeId))) {
					pushIntoWorklist(x); // only re-queue if x's set actually grew
				}
			}
		}
	}
}

/// TODO: Checking aliases of the two variables at source and sink. For example:
/// src instruction:  actualRet = source();
/// snk instruction:  sink(actualParm,...);
/// return true if actualRet is aliased with any parameter at the snk node (e.g., via ander->alias(..,..))


// True if the source call's return value may alias any argument passed to the sink call.
bool ICFGTraversal::aliasCheck(const CallICFGNode* src, const CallICFGNode* snk) {
	const RetICFGNode* srcRetNode = src->getRetICFGNode();
	if (srcRetNode == nullptr || srcRetNode->getActualRet() == nullptr)
		return false; // source call's return value is unused/void
 
	NodeID srcRetId = srcRetNode->getActualRet()->getId();
 
	// Check every sink argument, since sink(a, b, c) could be tainted via any of them.
	for (const auto* param : snk->getActualParms()) {
		NodeID snkParamId = param->getId();
		AliasResult res = ander->alias(srcRetId, snkParamId);
		if (res != AliasResult::NoAlias) // MayAlias/MustAlias both count as tainted
			return true;
	}
 
	return false;
}

// Start taint checking.
// There is a tainted flow from p@source to q@sink
// if (1) alias(p,q)==true and (2) source reaches sink on ICFG.
void ICFGTraversal::taintChecking() {
	const fs::path& config = CUR_DIR() / "Tests/SrcSnk.txt";
	// configure sources and sinks for taint analysis
	readSrcSnkFromFile(config.string()); // path -> string conversion needed here
 
	// Set file permissions to read-only for user, group and others
	if (chmod(config.string().c_str(), S_IRUSR | S_IRGRP | S_IROTH) == -1) {
		std::cerr << "Error setting file permissions for " << config << ": " << std::strerror(errno) << std::endl;
		abort();
	}
	ander = new AndersenPTA(pag);
	ander->analyze();
	for (const CallICFGNode* src : identifySources()) {
		for (const CallICFGNode* snk : identifySinks()) {
			if (aliasCheck(src, snk)) // cheap filter before the expensive path search
				reachability(src, snk);
		}
	}
}

/*!
 * Andersen analysis
 */
void AndersenPTA::analyze() {
	initialize();
	initWorklist();
	do {
		reanalyze = false;
		solveWorklist();
		if (updateCallGraph(getIndirectCallsites())) // new indirect calls may need re-solving
			reanalyze = true;
	} while (reanalyze);
	finalize();
}