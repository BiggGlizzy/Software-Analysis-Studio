
//===- SVF-Teaching Assignment 1-------------------------------------//
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
 // SVF-Teaching Assignment 1 : Graph Traversal
 //
 // 
 */


#include "Assignment-1.h"
using namespace std;

/// TODO: print each path once this method is called, and
/// add each path as a string into std::set<std::string> paths
/// Print the path in the format "START: 1->2->4->5->END", where -> indicate an edge connecting two node IDs
void GraphTraversal::printPath(std::vector<const Node *> &path)
{
    std::string result = "START: ";
    for (size_t i = 0; i < path.size(); i++) {
        result += std::to_string(path[i]->getNodeID());
        result += "->";
    }
    result += "END";

    paths.insert(result);
    std::cout << result << std::endl;
}

/// Depth first search to traverse each program path (once for any loop) from src to dst
void GraphTraversal::DFS(set<const Node *> &visited, vector<const Node *> &path, const Node *src, const Node *dst)
{
    visited.insert(src);
    path.push_back(src);

    if (src == dst) {
        printPath(path);
    } else {
        for (const Edge *e : src->getOutEdges()) {
            const Node *next = e->getDst();
            if (visited.find(next) == visited.end()) {
                DFS(visited, path, next, dst);
            }
        }
    }

    visited.erase(src);
    path.pop_back();
}
