//===- SVF-Teaching Assignment 2-------------------------------------//
//
//     SVF: Static Value-Flow Analysis Framework for Source Code
//
// Copyright (C) <2013->
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===-----------------------------------------------------------------------===//
/*
 // SVF-Teaching Assignment 2 : Source Sink ICFG DFS Traversal
 //
 // 
 */

#include <set>
#include "Assignment-2.h"
#include <iostream>
using namespace SVF;
using namespace std;

/// Print each path once this method is called, and
/// add each path as a string into std::set<std::string> paths
/// Print the path in the format "START->1->2->4->5->END", where -> indicate an ICFGEdge connects two ICFGNode IDs
void ICFGTraversal::collectICFGPath(std::vector<unsigned> &path){
    std::string result = "START";
    for (unsigned id : path) {
        result += "->";
        result += std::to_string(id);
    }
    result += "->END";

    paths.insert(result);
}


/// Implement context-sensitive ICFG traversal here to traverse each program path (once for any loop) from src to dst
void ICFGTraversal::reachability(const ICFGNode *src, const ICFGNode *dst)
{
    std::pair<const ICFGNode*, CallStack> pair = std::make_pair(src, callstack);
    if (visited.count(pair))
        return;

    visited.insert(pair);
    path.push_back(src->getId());

    if (src == dst) {
        collectICFGPath(path);
    } else {
        for (const ICFGEdge *edge : src->getOutEdges()) {
            const ICFGNode *edgeDst = edge->getDstNode();

            if (edge->isIntraCFGEdge()) {
                reachability(edgeDst, dst);
            }
            else if (edge->isCallCFGEdge()) {
                callstack.push_back(edge->getSrcNode());
                reachability(edgeDst, dst);
                callstack.pop_back();
            }
            else if (edge->isRetCFGEdge()) {
                const RetICFGNode *retNode = SVFUtil::cast<RetICFGNode>(edgeDst);
                const ICFGNode *callSite = retNode->getCallSite();

                if (!callstack.empty() && callstack.back() == callSite) {
                    callstack.pop_back();
                    reachability(edgeDst, dst);
                    callstack.push_back(callSite);
                }
                else if (callstack.empty()) {
                    reachability(edgeDst, dst);
                }
            }
        }
    }

    visited.erase(pair);
    path.pop_back();
}