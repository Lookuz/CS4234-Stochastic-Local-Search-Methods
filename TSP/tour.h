#include <iostream>
#include <vector>
#include <unordered_map>
#include <cassert>
#include <algorithm>

// represents a tour aka a sequence of vertices
class Tour {
public:
    Tour() : N{0} { }

    void addNode(int n) {
        nodes.push_back(n);
        position[n] = N;
        ++N;
    }
    int pred(int n) {
        return nodes[ (position[n] + N - 1) % N ];
    }
    int succ(int n) {
        return nodes[ (position[n] + 1) % N ];
    }
    int size() {
        return N;
    }
    int getPosition(int n) {
        return position[n];
    }
    void print() {
        std::cout << "Tour: ";
        for (const auto& n : nodes) {
            std::cout << n << ", ";
        }
        std::cout << " (Total " << N << " nodes)\n";
    }
    // desc is a list of tuples, <startPos, endPos, dir> where dir = 1 or -1
    // todo: can be optimized further i think, right now it is O(N)
    void reOrderByPosition(std::vector<std::tuple<int, int, int>> desc) {
        std::vector<int> newTour;
        for (const auto &tup : desc) {
            auto [startPos, endPos, dir] = tup; // start from u, go in direction dir, until hit v
            // std::cout << startPos << ", " << endPos << "\n";
            assert(dir == 1 || dir == -1);
            int pos = startPos;
            while (pos != endPos) {
                newTour.push_back(nodes[pos]);
                pos = (pos + N + dir) % N;
            }
            newTour.push_back(nodes[pos]); // endPos included
        }
        assert(newTour.size() == N);
        // newTour is now correct, replace nodes with newTour
        nodes.clear();
        nodes.reserve(N);
        copy(newTour.begin(), newTour.end(), back_inserter(nodes)); // copy newTour back to tour
        position.clear();
        for (int i = 0; i < N; ++i) {
            position[nodes[i]] = i;
        }
    }

    // 3 nodes are given
    // returns the order in which they appear in the tour, starting from n1
    // assumes nodes are distinct
    std::vector<int> getSortedOrderThree(int n1, int n3, int n5) {
        std::vector<int> ans; ans.resize(3);
        ans[0] = n1;
        if (position[n3] < position[n5]) {
            if (position[n3] < position[n1] && position[n1] <= position[n5]) { // n3 ... n1 ... n5
                ans[1] = n5;
                ans[2] = n3;
            } else { // ... n3 ... n5 ... n1
                ans[1] = n3;
                ans[2] = n5;
            }
        } else { // n5 ... n3 ...
            if (position[n5] < position[n1] && position[n1] <= position[n3]) { // n5 ... n1 ... n3
                ans[1] = n3;
                ans[2] = n5;
            } else { // ... n5 ... n3 ... n1
                ans[1] = n5;
                ans[2] = n3;
            }
        }
    }

    std::vector<int> getSortedOrder(std::vector<int> &toSort) {
        std::vector<std::pair<int, int>> lst;
        int first = toSort[0]; // we return the nodes in order, starting from first element
        for(const auto& n : toSort) {
            lst.emplace_back(position[n], n);
        }
        std::sort(lst.begin(), lst.end());

        int i = 0;
        while(lst[i].second != first) { // find the first element
            ++i;
        }
        std::vector<int> ans;
        for (int j = 0; j < toSort.size(); ++j) {
            ans.push_back(lst[(j + i) % toSort.size()].second);
        }
        return ans;
    }


    int N; // number of nodes
    std::vector<int> nodes;
    std::unordered_map<int, int> position; // position[nodeId] = index of nodeId in the tour
};