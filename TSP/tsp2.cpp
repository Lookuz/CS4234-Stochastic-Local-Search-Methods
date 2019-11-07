#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <limits>
#include <random>
#include <stack>
#include <queue>
#include <cassert>

#include "matrix.h"
#include "UnionFind.h"

#define DEBUG 0 // set to 1 to activate debug outputs 

#ifdef DEBUG
    #define LOG(x) std::cerr << x << std::endl
#else
    #define LOG(x)
#endif

using namespace std;

typedef pair<int, int> ii;
typedef vector<int> vi;
typedef vector<ii> vii;

// Random number generator.
random_device rd;
default_random_engine rng(rd());

// Size of nearest neighbors matrix.
const static size_t MAX_K = 20;
const static int NUM_DOUBLE_BRIDGE_BEFORE_LOCAL_SHUFFLE = 7;
const static int THREE_OPT_BUFFER_TIME = 50;
const static int EXECUTION_DURATION = 1950; // time for the whole algo
const static int GEO_SHUFFLE_WIDTH = 10;

// ---------------- Helper functions -------------------------------------------------

void printVec(vector<int> v) {
    for (const auto& n : v) {
        std::cout << n << ", ";
    }
    cout << "\n";
}

void printVecVec(vector<vector<int>> &adjList) {
    for (int i = 0; i < adjList.size(); ++i) {
        cout << i << ": [";
        for (const auto& x : adjList[i]) {
            cout << x << ", ";
        }
        cout << "]\n";
    }
}

void printTourAndPos(vector<int> &tour, vector<int> &position) {
    cout << "tour    : ";
    printVec(tour);
    cout << "position: ";
    printVec(position);
}

vector<int> getPositionVec(vector<int> &tour) {
    vector<int> position; position.resize(tour.size());
    for (int i = 0; i < tour.size(); ++i) {
        position[tour[i]] = i;
    }
    return position;
}

long getMaxWeight(vector<int> &tour, Matrix<long> &d) {
    int N = tour.size();
    long m = 0;
    for (int i = 0; i < N; ++i) {
        m = max(m, d[tour[i]][tour[(i + 1) % N]]);
    }
    return m;
}

// check if a position vector matches a tour vector
void checkConsistent(vector<int> &tour, vector<int> &position) {
    assert(tour.size() == position.size());
    for (int i = 0; i < position.size(); ++i) {
        assert(position[tour[i]] == i);
    }
}

// Return the current time.
static inline chrono::time_point<chrono::high_resolution_clock> now() {
    return chrono::high_resolution_clock::now();
}

// Output stream operator for durations.
template<typename T, typename E>
inline ostream& operator<<(ostream& out, const chrono::duration<T, E>& d) {
    out << chrono::duration_cast<chrono::milliseconds>(d).count() << " ms";
    return out;
}

// 3-argument maximum function.
template<typename T>
static inline T maximum(const T& a, const T& b, const T& c) {
    return max(a, max(b, c));
}

// 4-argument maximum function.
template<typename T>
static inline T maximum(const T& a, const T& b, const T& c, const T& d) {
    return max(a, max(b, max(c, d)));
}

/**
 * Returns the shortest distance d[i][j], i != j in the given distance matrix.
 */
long minDistance(const Matrix<long>& d) {
    size_t N = d.rows();
    long min = numeric_limits<long>::max();
    for (size_t i = 0; i < N; ++i) {
        for (size_t j = 0; j < N; ++j) {
            if (i != j)
                min = std::min(min, d[i][j]);
        }
    }
    return min;
}

/**
 * Returns the total length of a tour.
 */
inline long long length(const vector<int>& tour, const Matrix<long>& d) {
    size_t N = tour.size();
    long long length = 0;
    for (size_t i = 0, j = 1; i < N; ++i, ++j) {
        length += d[tour[i]][tour[j % N]];
    }
    return length;
}

/**
 * Reverse a segment of a tour.
 *
 * This functions reverses the segment [start, end] of the given
 * tour and updates the position vector accordingly.
 *
 * @param tour The input tour.
 * @param start Start index of segment to reverse.
 * @param end End index of segment to reverse.
 * @param position Position of each city in the input tour. Will be updated.
 */
inline void reverse(vector<int> &tour, int start, int end, vector<int>& position) {
    int N = tour.size();
    int numSwaps = (start <= end ? end - start + 1: end + N - start + 1) / 2;
    int i = start;
    int j = end;
    for (int n = 0; n < numSwaps; ++n) {
        swap(tour[i], tour[j]);
        position[tour[i]] = i;
        position[tour[j]] = j;
        i = (i + 1) % N;
        j = ((j + N) - 1) % N;
    }
}

// takes the 2 ADJACENT segments ... A .. B - C .. D ...
// and swaps to ... C .. D - A .. B ...
// takes in indices, not nodeId's
// assumes that A .. B precedes C .. D!
inline void swapAdjacentSegments(vector<int> &tour, vector<int>& position, int A, int B, int C, int D) {
    int N = tour.size();
    vector<int> temp;
    int cur = C;
    while (cur != D) {
        temp.push_back(tour[cur]);
        cur = (cur + 1) % N;
    }
    temp.push_back(tour[cur]); // temp contains segment [C .. D]

    cur = A;
    while (cur != B) {
        temp.push_back(tour[cur]);
        cur = (cur + 1) % N;
    }
    temp.push_back(tour[cur]); // temp contains segment [C .. D, A .. B]

    for (int i = 0; i < temp.size(); ++i) { // copy over to tour
        tour[(A + i) % N] = temp[i];
        position[temp[i]] = (A + i) % N;
    }
}

/**
 * Order three edges by tour position.
 *
 * This function takes as input three disjoint edges GH, IJ and KL, and their
 * positions in the tour (G_i, H_i, ..., L_i), and sets AB, CD and EF, and
 * associated tour indices A_i, B_i, ..., F_i, to be the input edges in tour
 * order.
 *
 * E.g if GH, IJ and KL have the order ..->GH->..->IJ->..->KL->.., then
 * AB = GH, CD = IJ, EF = KL, else AB = IJ, CD = GH, EF = KL.
 *
 * This is a helper function used in the inner loop of threeOpt(...).
 */
inline void ordered(
        int& A, size_t& A_i, int& B, size_t& B_i,
        int& C, size_t& C_i, int& D, size_t& D_i,
        int& E, size_t& E_i, int& F, size_t& F_i,

        int G, size_t G_i, int H, size_t H_i,
        int I, size_t I_i, int J, size_t J_i,
        int K, size_t K_i, int L, size_t L_i) {
    E = K; E_i = K_i;
    F = L; F_i = L_i;
    if ((I_i < G_i && G_i < K_i) ||
        (K_i < I_i && I_i < G_i) ||
        (G_i < K_i && K_i < I_i)) {
        A = I; A_i = I_i;
        B = J; B_i = J_i;
        C = G; C_i = G_i;
        D = H; D_i = H_i;
    } else {
        A = G; A_i = G_i;
        B = H; B_i = H_i;
        C = I; C_i = I_i;
        D = J; D_i = J_i;
    }
}

/* compute alpha values for the graph given
 * it will use prims to create the V-tree (where the special node is V-1)
 * Implementation is correct, but without subgradient optimization, no significant improvement to score
 */
Matrix<long> createAlphaMatrix(Matrix<long> &adjMatrix) { // adjMatrix is square
    vector<int> parent; // store predecessor of nodes in mst
    vector<int> taken; // nodes in the partial mst
    priority_queue<tuple<int, int, int>> pq;  // priority_queue is a max heap, we use -ve sign to reverse order
    vector<vector<int>> mst; // adjList of mst, it is a DAG
    vector<int> topoList; // store topo order of mst

    int V = adjMatrix.rows() - 1; // we pretend last node doesn't exist
    parent.assign(V, -1); // parent unknown
    taken.assign(V, 0); // all unvisited
    mst.assign(V, vector<int>());
    
    // process node 0
    int firstNode = 0;
    taken[firstNode] = 1;
    topoList.push_back(firstNode);
    for (int nbr = 1; nbr < V; ++nbr) { // neighbors of 0
        pq.push({-1*adjMatrix[firstNode][nbr], -nbr, firstNode}); // -weight, -nodeId, parent
    }
    
    int mst_cost = 0, num_taken = 0; // no edge has been taken
    while (!pq.empty()) {
        auto [w, u, p] = pq.top(); pq.pop();
        w = -w; u = -u; // negate to reverse order
        if (taken[u]) continue; // already taken, skipped
        mst_cost += w; // add w of this edge
        parent[u] = p; // rmb parent
        taken[u] = 1; // mark taken
        mst[p].push_back(u); // insert into mst
        topoList.push_back(u); // rmb the topo order
        
        // process nbrs
        for (int nbr = 1; nbr < V; ++nbr) {
            if (nbr != u && !taken[nbr]) { // new node to add
                pq.push({-1*adjMatrix[u][nbr], -nbr, u});
            }
        }                                         
        ++num_taken;
        if (num_taken == V - 1) break; // have enough edges
    }
    
    // now with mst and topoList, we can compute the alpha matrix
    Matrix<long> alphaMatrix(adjMatrix.rows(), adjMatrix.cols());
    Matrix<long> betaMatrix(adjMatrix.rows(), adjMatrix.cols());

    // compute alpha(V-1, j) where V is the distinguished node S
    int specialNode = V;
    long s1, s2; // shortest edges S -> j

    if (adjMatrix[specialNode][0] <= adjMatrix[specialNode][1]) { // initialize s1, s2
        s1 = adjMatrix[specialNode][0]; s2 = adjMatrix[specialNode][1];
    } else {
        s1 = adjMatrix[specialNode][1]; s2 = adjMatrix[specialNode][0];
    }

    for(int j = 2; j < V; ++j) {
        if (adjMatrix[specialNode][j] < s1) { // new smallest edge
            s2 = s1;
            s1 = adjMatrix[specialNode][j];
        } else if (adjMatrix[specialNode][j] < s2) { // new 2nd smallest edge
            s2 = adjMatrix[specialNode][j]; 
        }
    }

    for(int j = 0; j < V; ++j) { // a(S, j) is either 0 (as good as s1), or you replace s2
        alphaMatrix[specialNode][j] = alphaMatrix[j][specialNode] = max(0l, adjMatrix[specialNode][j] - s2);
    }
    alphaMatrix[specialNode][specialNode] = -1; // undefined

    // compute alpha(i, j) for all i except root
    // root is 0
    int root = 0;
    for (int i = 0; i < V; ++i) { // for each node i except S and root
        int u = topoList[i];
        betaMatrix[u][u] = -1;
        alphaMatrix[u][u] = -1;
        for (int j = i+1; j < V; ++j) {
            int v = topoList[j];
            betaMatrix[u][v] = betaMatrix[v][u] = max(betaMatrix[u][parent[v]], adjMatrix[v][parent[v]]);
            alphaMatrix[u][v] = alphaMatrix[v][u] = adjMatrix[u][v] - betaMatrix[u][v]; 
        } 
    }
    return alphaMatrix;
}

/**
 * Create a distance matrix from an input stream and return it.
 */
Matrix<long> createDistanceMatrix(istream& in) {
    // Read vertex coordinates.
    size_t N;
    in >> N;
    vector<double> x(N);
    vector<double> y(N);
    for (size_t i = 0; i < N; ++i) {
        in >> x[i] >> y[i];
    }

    // Calculate distance matrix.
    Matrix<long> d(N, N);
    for (size_t i = 0; i < N; ++i) {
        for (size_t j = i + 1; j < N; ++j) {
            d[i][j] = d[j][i] = round(sqrt(pow(x[i]-x[j], 2) + pow(y[i]-y[j], 2)));
        }
    }

    return d;
}

/**
 * Calculate K-nearest neighbors matrix from a distance matrix.
 *
 * @param d Distance matrix.
 * @return d.rows() x K matrix where element i,j is the j:th nearest
 *         neighbor of city i.
 */
Matrix<int> createNeighborsMatrix(const Matrix<long>& d, size_t K) {
    size_t N = d.rows();
    size_t M = d.cols() - 1; // node is not neighbor of itself
    K = min(M, K);
    Matrix<int> neighbor(N, K);
    vector<int> row(M); // For sorting.

    for (size_t i = 0; i < N; ++i) {
        // Fill row with 0, 1, ..., i - 1, i + 1, ..., M - 1.
        int k = 0;
        for (size_t j = 0; j < M; ++j, ++k) {
            row[j] = (i == j) ? ++k : k;
        }
        // Sort K first elements in row by distance to i.
        partial_sort(row.begin(), row.begin() + K, row.end(),
            [&](int j, int k) {
                return d[i][j] < d[i][k];
            }
        );
        // Copy first K elements (now sorted) to neighbor matrix.
        copy(row.begin(), row.begin() + K, neighbor[i]);
    }
    return neighbor;
}

/**
 * Calculates a greedy TSP tour.
 *
 * This is the naive algorithm given in the Kattis problem description.
 *
 * @param d Distance matrix.
 * @return Greedy TSP tour.
 */
inline vector<int> greedy(const Matrix<long>& d) {
    size_t N = d.rows();
    vector<int> tour(N);
    vector<bool> used(N, false);
    tour[0] = 0;
    used[0] = true;
    for (size_t i = 1; i < N; ++i) {
        // Find k, the closest city to the (i - 1):th city in tour.
        int32_t k = -1;
        for (int j = 0; j < N; ++j) {
            if (!used[j] && (k == -1 || d[tour[i-1]][j] < d[tour[i-1]][k])) {
                k = j;
            }
        }
        tour[i] = k;
        used[k] = true;
    }
    return tour;
}

// do the 2-approx MST construction
inline vector<int> twoApprox(const Matrix<long>& d) {
    int N = d.rows();
    if (N == 1) {
        return {0};
    }

    vector<tuple<int, int, int>> EL; EL.reserve(N * (N - 1) / 2);
    for (int i = 0; i < N; ++i) {
        for (int j = i + 1; j < N; ++j) {
            EL.emplace_back(-1 * d[i][j], i, j); // (weight, u, v)
        }
    }

    sort(EL.begin(), EL.end());
  
    vector<vector<int>> adjList; adjList.resize(N);
    int mst_cost = 0, num_taken = 0;               // no edge has been taken
    UnionFind UF(N);                               // all N are disjoint sets
    // note: the runtime cost of UFDS is very light
    for (int i = 0; i < EL.size(); ++i) {
        auto [w, u, v] = EL[i];
        if (UF.isSameSet(u, v)) continue;            // already in the same CC
        mst_cost += w;                               // add w of this edge
        UF.unionSet(u, v);                           // link them
        ++num_taken;                                 // 1 more edge is taken
        adjList[u].push_back(v);
        adjList[v].push_back(u);
        if (num_taken == N - 1) break;                 // optimization
    }
    
    // DFS traversal on MST
    vector<int> tour; tour.reserve(2 * N);
    vector<bool> visited; visited.assign(N, false);
    visited[0] = true;
    vector<int> stack; stack.push_back(0);
    int cur;
    while (!stack.empty()) {
        cur = stack.back(); stack.pop_back();
        visited[cur] = true;
        tour.push_back(cur); // add to tour
        for (const auto& nbr : adjList[cur]) {
            if (visited[nbr]) continue;
            stack.push_back(nbr);
            visited[nbr] = true;
        }
    }

    #if DEBUG
    cout << "adjList:\n";
    printVecVec(adjList);
    cout << "tour\n";
    printVec(tour);
    #endif

    return tour;
}

// algorithm for initial tour
// greedily chooses the shortest edges first to construct a tour
// O(N^2 log N)
// there is a faster version, but I dont think it will help much
vector<int> multiFragSlow(const Matrix<long>& d) {
    int N = d.rows();
    if (N == 1) {
        return {0};
    }

    int numEdgesTaken = 0; // num edges taken, stop when equal N-1
    vector<int> degrees; degrees.assign(N, 0); // degree[i] = degree of node i
    vector<int> tail; tail.resize(N);  // stores the other end of a fragment. e.g. if the fragment is u - .... - v, then tail[u] = v and tail[v] = u
    for (int i = 0; i < tail.size(); ++i) {
        tail[i] = i; // initially, you are your own tail
    }
    
    vector<vector<int>> adjList; adjList.resize(N); // we will construct this graph
    priority_queue<tuple<int, int, int>> pq; // (-weight, u, v) Note that pq is max heap so must negate weight
    for (int i = 0; i < N; ++i) {
        for (int j = i + 1; j < N; ++j) {
            pq.emplace(-1 * d[i][j], i, j);
        }
    }

    while (!pq.empty()) {
        auto [w, u, v] = pq.top(); pq.pop();
        w = -w; // negate back the weight
        // cout << w << ", " << u << ", " << v << "\n";
        
        if (degrees[u] >= 2 || degrees[v] >= 2) { // already part of a path
            continue; // can't use this edge
        }
        if (tail[u] == v) { // will form a cycle
            continue;
        }
        
        // connect u and v, and update their tails
        // tail[u] ---- u --- v ----- tail[v]
        adjList[u].push_back(v);
        adjList[v].push_back(u);

        int tv = tail[v]; // temp variables are needed
        int tu = tail[u];
        tail[tu] = tv;
        tail[tv] = tu;
        degrees[u]++;
        degrees[v]++;
        numEdgesTaken++;

        if (numEdgesTaken == N - 1) break;
    }
    // find one end of the tour
    int start = 0;
    for (int i = 0; i < adjList.size(); ++i) {
        if (adjList[i].size() == 1) {
            start = i;
            break;
        }
    }
    // build the tour
    vector<bool> taken; taken.assign(N, false);
    taken[start] = true;
    vector<int> tour; tour.push_back(start);
    int cur = adjList[start][0];
    while (tour.size() < N - 1) {
        taken[cur] = true;
        tour.push_back(cur);
        assert(adjList[cur].size() == 2);
        // we find the next node in the tour
        if (taken[adjList[cur][0]]) { // not this one
            cur = adjList[cur][1];
        } else {
            cur = adjList[cur][0];
        }
    }
    tour.push_back(cur);

    return tour;
}

// returns predecessor of t1 in the tour
inline int pred(vector<int> &tour, vector<int> &position, int &t1) {
    return tour[(position[t1] - 1 + tour.size()) % tour.size()];
}
// returns successor of t1 in the tour
inline int succ(vector<int> &tour, vector<int> &position, int &t1) {
    return tour[(position[t1] + 1) % tour.size()];
}

// returns whether t1 and t2 are adjacent in the tour
inline bool isAdjacent(vector<int> &tour, vector<int> &position, int t1, int t2) {
    return (pred(tour, position, t1) == t2 || succ(tour, position, t1) == t2);
}

// re-order the tour...
// desc is a list of tuples, <startPos, endPos, dir> where dir = 1 or -1
// does NOT update the position vector
void reOrder(vector<int>& tour, vector<int> &position, vector<tuple<int, int, int>> desc) {
    int N = tour.size();
    vector<int> newTour;
    for (const auto &tup : desc) {
        auto [startPos, endPos, dir] = tup; // start from u, go in direction dir, until hit v
        assert(dir == 1 || dir == -1);
        int pos = startPos;
        while (startPos != endPos) {
            newTour.push_back(tour[pos]);
            pos = (pos + tour.size() + dir) % tour.size();
        }
        newTour.push_back(tour[pos]); // endPos included
    }
    assert(newTour.size() == N);
    tour.clear();
    tour.reserve(N);
    copy(newTour.begin(), newTour.end(), back_inserter(tour)); // copy newTour back to tour
}

/**
 * Optimizes the given tour using 2-opt.
 * @param tour The tour to optimize.
 * @param d Distance matrix.
 * @param neighbor Nearest neighbors matrix.
 * @param position Position of each city in the input tour. Will be updated.
 * @param max Longest inter-city distance in input tour. Will be updated.
 * @param min Shortest possible inter-city distance.
 */
inline void twoOpt(vector<int>& tour, const Matrix<long>& d,
        const Matrix<int>& neighbor, vector<int> &position,
        long& max, long min) {
    size_t N = d.rows(); // Number of cities.

    // Candidate edges uv, wz and their positions in tour.
    int u, v, w, z;
    size_t u_i, v_i, w_i, z_i;

    bool locallyOptimal = false;
    while (!locallyOptimal) {
        locallyOptimal = true;

        // For each edge uv.
        for (u_i = 0, v_i = 1; u_i < N; ++u_i, ++v_i) {
            u = tour[u_i];
            v = tour[v_i % N];

            // For each edge wz (w k:th closest neighbor of u).
            for (size_t k = 0; k < neighbor.cols(); ++k) {
                w_i = position[neighbor[u][k]];
                z_i = w_i + 1;
                w = tour[w_i];
                z = tour[z_i % N];

                if (v == w || u == z) {
                    continue; // Skip adjacent edges.
                }

                // d[u][w] + min is a lower bound on new length.
                // d[u][v] + max is an upper bound on old length.
                if (d[u][w] + min > d[u][v] + max) {
                    break; // Go to next edge uv.
                }

                if (d[u][w] + d[v][z] < d[u][v] + d[w][z]) {
                    //   --u w--        --u-w->
                    //      X     ===>
                    //   <-z v->        <-z-v--
                    reverse(tour, v_i % N, w_i, position); // implicitly deletes and adds edges
                    max = maximum(max, d[u][w], d[v][z]);
                    locallyOptimal = false;
                    break;
                }
            }
        }
    }
}

inline void twoHOpt(vector<int>& tour, const Matrix<long>& d,
        const Matrix<int>& neighbor, vector<int> &position,
        long& max, long min) {
    size_t N = d.rows(); // Number of cities.

    // Candidate edges uv, wz and their positions in tour.
    int A, pA, sA, B, pB, sB; // pA = pred(A), sA = succ(A)
    int A_i, pA_i, sA_i, B_i, pB_i, sB_i;
    
    bool locallyOptimal = false;
    while (!locallyOptimal) {
        locallyOptimal = true;

        // For each node A
        for (A_i = 0; A_i < N; ++A_i) {
            pA_i = (A_i + N - 1) % N;
            sA_i = (A_i + 1) % N;
            A = tour[A_i];
            pA = tour[pA_i]; 
            sA = tour[sA_i];

            // For each node B that is 'near' A
            for (size_t k = 0; k < neighbor.cols(); ++k) {
                B_i = position[neighbor[A][k]];
                pB_i = (B_i + N - 1) % N;
                sB_i = (B_i + 1) % N;
                B = tour[B_i];
                pB = tour[pB_i];
                sB = tour[sB_i];

                if (B == sA || B == pA) {
                    continue; // Skip
                }

                // pA -> A -> sA and B -> sB
                // becomes
                // pA -> sA and B -> A -> sB
                if (sB != pB &&
                    (d[pA][sA] + d[B][A] + d[A][sB] - d[pA][A] - d[A][sA] - d[B][sB] < 0)) { // can improve
                    // make the move
                    // sB_i to pA_i is fixed, no change
                    // shift sA onwards, back 1 step, until we shift B.
                    int cur = (pA_i + 1) % N;
                    int next;
                    while (cur != B_i) { // pos is at A_i now
                        //cout << cur << "\n";
                        next = (cur + 1) % N;
                        tour[cur] = tour[next];
                        position[tour[cur]] = cur;
                        cur = next;
                    }
                    tour[cur] = A;
                    position[A] = cur;
                    // update
                    max = maximum(max, d[pA][sA], d[B][A]);
                    max = maximum(max, max, d[A][sB]);
                    locallyOptimal = false;
                    break;
                }
            }
        }
    }
}

// 3-opt, but to speed it up, we assume that the edges used in the 3-opt swap are close to each other
inline void threeOptFast(vector<int>& tour, const Matrix<long>& d,
        const Matrix<int>& neighbor, vector<int> &position,
        long& max, long min) {
    int N = tour.size();
    int WIDTH = 40; // search width N/4 is pretty good already

    int A, B, C, D, E, F;
    int A_i, B_i, C_i, D_i, E_i, F_i;

    bool locallyOptimal = false;
    while (!locallyOptimal) {
        locallyOptimal = true;

        // For each edge CD.
        for (size_t i = 0; i < N; ++i) {
            C_i = i;
            D_i = (C_i + 1) % N;
            C = tour[C_i];
            D = tour[D_i];

            // For each edge AB, AB before CD in the tour
            for (size_t j = 0; j < WIDTH; ++j) {
                B_i = (C_i + N - j) % N; // we allow B_i = C_i
                A_i = (B_i + N - 1) % N;
                if (A_i == D_i) break; // wraparound too far // can remove this if you use WIDTH N/2 and below
                A = tour[A_i];
                B = tour[B_i];
                
                for (int k = 0; k < WIDTH; ++k) {
                    E_i = (D_i + k) % N;
                    F_i = (E_i + 1) % N;
                    E = tour[E_i];
                    F = tour[F_i];
                    if (E_i == A_i) {
                        break; // overlap, A-B ... C-D ... (E=A)-B
                    }
                    // vector<int> o{A_i, B_i, C_i, D_i, E_i, F_i};
                    // cout << "chosen vertices:\n";
                    // printVec(o);

                    // consider the 4 cases
                    // Try exchanging AB, CD and EF for another edge triple.
                    long d_AB_CD_EF = d[A][B] + d[C][D] + d[E][F];
                    if (d[A][D] + d[E][C] + d[B][F] < d_AB_CD_EF) {
                        // original: F..A - B..C - D..E
                        // new tour: F..A - D..E - C..B
                        reverse(tour, B_i, C_i, position); // B..C is short, so reverse this segment
                        swapAdjacentSegments(tour, position, B_i, C_i, D_i, E_i);
                        max = maximum(max, d[A][D], d[E][C], d[B][F]);
                        locallyOptimal = false;
                        goto next_CD; // Go to next edge CD
                    } else if (d[D][B] + d[C][F] + d[A][E] < d_AB_CD_EF) {
                        // original: F..A - B..C - D..E
                        // new tour: F..A - E..D - B..C
                        reverse(tour, D_i, E_i, position);
                        swapAdjacentSegments(tour, position, B_i, C_i, D_i, E_i);
                        max = maximum(max, d[D][B], d[C][F], d[A][E]);
                        locallyOptimal = false;
                        goto next_CD; // Go to next edge CD.
                    } else if (d[A][C] + d[B][E] + d[D][F] < d_AB_CD_EF) {
                        // original: F..A - B..C - D..E
                        // new tour: F..A - C..B - E..D
                        reverse(tour, B_i, C_i, position);
                        reverse(tour, D_i, E_i, position);
                        max = maximum(max, d[A][C], d[B][E], d[D][F]);
                        locallyOptimal = false;
                        goto next_CD; // Go to next edge CD.
                    } else if (d[E][B] + d[C][F] + d[A][D] < d_AB_CD_EF) {
                        // original: F..A - B..C - D..E
                        // new tour: F..A - D..E - B..C
                        swapAdjacentSegments(tour, position, B_i, C_i, D_i, E_i);
                        max = maximum(max, d[E][B], d[C][F], d[A][D]);
                        locallyOptimal = false;
                        goto next_CD; // Go to next edge CD.
                    }
                }
            }
            next_CD: continue;
        }
    }
}

/**
 * Optimizes the given tour using 3-opt.
 *
 * This function uses the fast approach described on page 12-15 of "Large-Step
 * Markov Chains for the Traveling Salesman Problem" (Martin/Otto/Felten, 1991)
 *
 * The algorithm will only consider "real" 3-exchanges involving all three
 * edges. So for best results, the tour should be preprocessed with the 2-opt
 * algorithm first.
 *
 * @param tour The tour to optimize.
 * @param d Distance matrix.
 * @param neighbor Nearest neighbors matrix.
 * @param position Position of each city in the input tour. Will be updated.
 * @param max Longest inter-city distance in input tour. Will be updated.
 * @param min Shortest possible inter-city distance.
 * @param deadline Deadline at which function will try to return early.
 */
inline void threeOpt(vector<int>& tour, const Matrix<long>& d,
        const Matrix<int>& neighbor, vector<int>& position,
        long& max, long min,
        const chrono::time_point<chrono::high_resolution_clock>& deadline) {
    const size_t N = d.rows(); // Number of cities.

    // Candidate edges PQ, RS, TU and their positions in tour.
    int P, Q, R, S, T, U;
    size_t P_i, Q_i, R_i, S_i, T_i, U_i;

    // AB, CD, EF is PQ, RS, TU, but in tour order.
    int A, B, C, D, E, F;
    size_t A_i, B_i, C_i, D_i, E_i, F_i;

    bool locallyOptimal = false;
    while (!locallyOptimal) {
        locallyOptimal = true;

        // For each edge PQ.
        for (size_t i = 0; i < N; ++i) {
            P_i = i;
            Q_i = (P_i + 1) % N;
            P = tour[P_i];
            Q = tour[Q_i];

            if (chrono::high_resolution_clock::now() > deadline)
                return; // Deadline has passed, return early.

            // For each edge RS (S j:th nearest neighbor of P).
            for (size_t j = 0; j < neighbor.cols(); ++j) {
                S_i = position[neighbor[P][j]];
                R_i = (S_i + N - 1) % N;
                R = tour[R_i];
                S = tour[S_i];

                if (P == R || R == Q) // RS same as, or follows, PQ.
                    continue; // Go to next edge RS.

                if (d[P][S] + 2 * min > d[P][Q] + 2 * max) // breaking PQ is definitely bad move
                    break; // Go to next edge PQ.

                if (d[P][S] + 2 * min > d[P][Q] + d[R][S] + max) // using RS is definitely bad move
                    continue; // Go to next edge RS.

                // For each edge TU (U k:th nearest neighbor of P).
                for (size_t k = 0; k < neighbor.cols(); ++k) {
                    U_i = position[neighbor[P][k]];
                    T_i = (U_i + N - 1) % N;
                    T = tour[T_i];
                    U = tour[U_i];

                    if (U == S || // TU same as RS.
                        T == S || // TU follows RS.
                        U == R || // TU preceeds RS.
                        T == P || // TU same as PQ.
                        T == Q)   // TU follows PQ.
                        continue; // Go to next edge TU.

                    if (d[P][S] + d[Q][U] + min > d[P][Q] + d[R][S] + max)
                        break; // Go to next edge RS.

                    // Let AB, CD, EF be the edges PQ, RS, TU in tour order.
                    ordered(A, A_i, B, B_i, C, C_i, D, D_i, E, E_i, F, F_i,
                            P, P_i, Q, Q_i, R, R_i, S, S_i, T, T_i, U, U_i);

                    // Try exchanging AB, CD and EF for another edge triple.
                    // See 3opt_cases.png for an illustration.
                    bool changed = false;
                    long d_AB_CD_EF = d[A][B] + d[C][D] + d[E][F];
                    if (d[D][A] + d[F][B] + d[C][E] < d_AB_CD_EF) {
                        // Change AB, CD, EF to DA, FB, CE.
                        reverse(tour, F_i, A_i, position);
                        reverse(tour, D_i, E_i, position);
                        max = maximum(max, d[D][A], d[F][B], d[C][E]);
                        changed = true;
                    } else if (d[B][D] + d[E][A] + d[F][C] < d_AB_CD_EF) {
                        // Change AB, CD, EF to BD, EA, FC.
                        reverse(tour, F_i, A_i, position);
                        reverse(tour, B_i, C_i, position);
                        max = maximum(max, d[B][D], d[E][A], d[F][C]);
                        changed = true;
                    } else if (d[A][C] + d[B][E] + d[D][F] < d_AB_CD_EF) {
                        // Change AB, CD, EF to AC, BE, DF.
                        reverse(tour, B_i, C_i, position);
                        reverse(tour, D_i, E_i, position);
                        max = maximum(max, d[A][C], d[B][E], d[D][F]);
                        changed = true;
                    } else if (d[B][E] + d[D][A] + d[F][C] < d_AB_CD_EF) {
                        // Change AB, CD, EF to BE, DA, FC.
                        reverse(tour, A_i, F_i, position);
                        reverse(tour, B_i, C_i, position);
                        reverse(tour, D_i, E_i, position);
                        max = maximum(max, d[B][E], d[D][A], d[F][C]);
                        changed = true;
                    }

                    if (changed) {
                        locallyOptimal = false;
                        goto next_PQ; // Go to next edge PQ.
                    }
                }
            }
            next_PQ: continue;
        }
    }
}

/**
 * Perform a random 4-opt ("double bridge") move on a tour.
 *
 * E.g.
 *
 *    A--B             A  B
 *   /    \           /|  |\
 *  H      C         H------C
 *  |      |   -->     |  |
 *  G      D         G------D
 *   \    /           \|  |/
 *    F--E             F  E
 *
 * Where edges AB, CD, EF and GH are chosen randomly.
 *
 * @param tour Input tour (must have at least 8 cities).
 * @return The new tour.
 */
inline vector<int> doubleBridge(const vector<int>& tour) {
    const size_t N = tour.size();
    vector<int> newTour;
    newTour.reserve(N);
    uniform_int_distribution<size_t> randomOffset(1, N / 4);
    size_t A = randomOffset(rng);
    size_t B = A + randomOffset(rng);
    size_t C = B + randomOffset(rng);
    copy(tour.begin(), tour.begin() + A, back_inserter(newTour));
    copy(tour.begin() + C, tour.end(), back_inserter(newTour));
    copy(tour.begin() + B, tour.begin() + C, back_inserter(newTour));
    copy(tour.begin() + A, tour.begin() + B, back_inserter(newTour));
    return newTour;
}

// shuffles subtours
inline vector<int> localShuffle(const vector<int>& tour) {
    const int N = tour.size();
    size_t subTourSize = N / 8;
    vector<int> newTour;
    newTour.reserve(N);
    copy(tour.begin(), tour.end(), back_inserter(newTour));

    // shuffle newTour
    uniform_int_distribution<size_t> randomOffset(1, N / 2);
    size_t A = randomOffset(rng);
    shuffle(newTour.begin() + A, newTour.begin() + A + subTourSize, rng);
    return newTour;
}

inline void geoKShuffle(vector<int>& tour, vector<int> &position) {
    if (tour.size() <= GEO_SHUFFLE_WIDTH) {
        shuffle(tour.begin(), tour.end(), rng);
        for (int i = 0; i < tour.size(); ++i) {
            position[tour[i]] = i;
        }
        return;
    }

    int blockSize = 2 * GEO_SHUFFLE_WIDTH; // can tune this
    int numBlocks = tour.size() / blockSize;
    int left, right;
    for (int i = 0; i < numBlocks; ++i) {
        left = i * blockSize;
        right = i * blockSize + GEO_SHUFFLE_WIDTH;
        // cout << left << ", " << right << "\n";
        shuffle(tour.begin() + left, tour.begin() + right, rng);
    }
    for (int i = 0; i < tour.size(); ++i) {
        position[tour[i]] = i;
    }
    return;
}


/**
 * Approximates optimal TSP tour through graph read from the given input stream.
 *
 * The tour is approximated using iterated local search (ILS), with a greedy initial
 * tour and 2-opt + 3-opt as local search methods, and a random 4-exchange ("double
 * bridge") as perturbation.
 *
 * The function will try to return before the given deadline, but expect some
 * variations.
 *
 * @param in Input stream.
 * @param deadline Deadline before which function should try to return.
 * @return An approximation of the optimal TSP tour.
 */
template<typename T>
vector<int> approximate(Matrix<long> &d, const chrono::time_point<T>& deadline) {
    chrono::milliseconds buffer(THREE_OPT_BUFFER_TIME);
    auto threeOptDeadline = deadline - buffer; // three OPT must terminate slightly earlier due to slowness

    const long min = minDistance(d); // Shortest distance.
    const size_t N = d.rows();       // Number of cities.

    if (N == 1) { // test case 7 is a single city
        return vector<int>({0});
    }

    // Calculate distance / K-nearest neighbors matrix.
    // Matrix<long> alphaMatrix = createAlphaMatrix(d);
    const Matrix<int> neighbor = createNeighborsMatrix(d, MAX_K);

    // Generate initial tour. greedy/multiFrag/twoApprox
    // vector<int> tour = greedy(d);
    vector<int> tour = multiFragSlow(d);

    // Create max / position for initial 2-opt + 3-opt.
    vector<int> position(N);
    long max = 0;
    for (int i = 0; i < N; ++i) {
        // max = std::max(max, d[i][(i + 1) % N]); // Original. I think not correct
        max = std::max(max, d[tour[i]][tour[(i + 1) % N]]); // i think this is the correct one
        position[tour[i]] = i;                  // tour[i] is i:th city in tour.
    }

    // Optimize tour with 2-opt + 3-opt.
    // twoOpt(tour, d, neighbor, position, max, min);
    // twoHOpt(tour, d, neighbor, position, max, min);
    threeOptFast(tour, d, neighbor, position, max, min);
    // threeOpt(tour, d, neighbor, position, max, min, threeOptDeadline);

    /*
     * Main loop.
     *
     * We repeatedly
     *   1) "Kick" the tour with a random 4-exchange.
     *   2) Optimize the tour with 2-opt + 3-opt.
     * until only max(50, 2 * average iteration time) milliseconds remains
     * before deadline, and then pick the shortest tour we found.
     */

    // Some main loop statistics.
    size_t i = 0;                        // Number of iterations of main loop.
    chrono::milliseconds totalTime(0);   // Total time spent in main loop.
    chrono::milliseconds averageTime(0); // Average main loop iteration time.

    vector<int> shortestTour = tour;          // Best tour found.
    long long shortestTourLength = length(tour, d); // Length of best tour found.
    int numDB = 0; // number of double bridge moves
    int numShuffles = 0; // number of shuffle moves
    int numFailSinceLastShuffle = 0; // number of double bridges that failed to improve the tour

    for (i = 0; (now() + std::max(buffer, 2 * averageTime)) < deadline; ++i) {
        auto start = now();

        if (N < 8) {
            shuffle(tour.begin(), tour.end(), rng); // Tiny tour, so just shuffle it instead.
        } else {
            if (numFailSinceLastShuffle > NUM_DOUBLE_BRIDGE_BEFORE_LOCAL_SHUFFLE) {
                tour = localShuffle(tour); // do local reshuffle
                numShuffles++;
                // cout << "Shuffling at DB = " << numDB << "\n";
                numFailSinceLastShuffle = 0;
            } else {
                // do double bridge move.
                tour = doubleBridge(tour);
                numDB++;
            }
        }

        // Update max / position needed by fast 2/3-opt.
        max = 0;
        for (int j = 0; j < N; ++j) {
            max = std::max(max, d[tour[j]][tour[(j + 1) % N]]);
            position[tour[j]] = j;
        }

        // Optimize tour with 2-opt + 3-opt.
        twoOpt(tour, d, neighbor, position, max, min);
        twoHOpt(tour, d, neighbor, position, max, min);
        threeOptFast(tour, d, neighbor, position, max, min);
        // threeOpt(tour, d, neighbor, position, max, min, threeOptDeadline);

        // compare with best tour
        long long tourLength = length(tour, d);
        if (tourLength < shortestTourLength) {
            // Shorter tour found.
            shortestTour = tour;
            shortestTourLength = tourLength;
            // cout << "Improvement Found at numDB = " << numDB << "\n";
            numFailSinceLastShuffle = 0; // reset
        } else { // unsuccessful double bridge
            numFailSinceLastShuffle++;
        }

        // Collect statistics.
        totalTime += chrono::duration_cast<chrono::milliseconds>(now() - start);
        averageTime = totalTime / (i + 1);
    }

    // cout << "Main Loop Statistics\n";
    // cout << "iterations: " << i << "\n";
    // cout << "totalTime: " << totalTime << "\n";
    // cout << "averageTime: " << averageTime << "\n";
    
    // stats
    long long stLength = length(shortestTour, d);
    long long optLength; cin >> optLength;
    cout << "numCities: " << shortestTour.size() << "\n";
    cout << "length: " << stLength << "\n";
    cout << "Percent above OPT: " << (static_cast<double>(stLength) / optLength * 100) << "\n";
    cout << "numDB: " << numDB << "\n";
    cout << "numShuffles: " << numShuffles << "\n";

    return shortestTour;
}

int main(int argc, char *argv[]) {
    // create dist matrix
    Matrix<long> d = createDistanceMatrix(cin);

    // Matrix<long> alpha = createAlphaMatrix(d);
    // cout << "alpha\n";
    // cout << alpha;

    // Approximate/print a TSP tour in EXECUTION_DURATION milliseconds.
    // vector<int> st = approximate(d, now() + chrono::milliseconds(EXECUTION_DURATION));

    // print tour
    // for (auto city : st) {
    //     cout << city << endl;
    // }
    // cout << "tour len: " << st.size() << "\n";

    const Matrix<int> neighbor = createNeighborsMatrix(d, MAX_K);
    vector<int> t1 = twoApprox(d);
    vector<int> t2 = t1;
    vector<int> p1 = getPositionVec(t1);
    vector<int> p2 = getPositionVec(t2);
    long mx1 = getMaxWeight(t1, d);
    long mx2 = getMaxWeight(t2, d);
    long mi1 = minDistance(d);
    long mi2 = minDistance(d);

    auto dl = now() + chrono::milliseconds(EXECUTION_DURATION);
    
    // cout << "initial len t1: " << length(t1, d) << "\n";
    // threeOpt(t1, d, neighbor, p1, mx1, mi1, dl);
    // cout << "final len t1: " << length(t1, d) << "\n";

    // cout << "initial len t2: " << length(t2, d) << "\n";
    // threeOptFast(t2, d, neighbor, p2, mx2, mi2);
    // cout << "len t2 (iter: 1): " << length(t2, d) << "\n";
    // threeOptFast(t2, d, neighbor, p2, mx2, mi2);
    // cout << "len t2 (iter: 2): " << length(t2, d) << "\n";
    // threeOptFast(t2, d, neighbor, p2, mx2, mi2);
    // cout << "len t2 (iter: 3): " << length(t2, d) << "\n";

    // checkConsistent(t2, p2);

    // testing
    vector<int> t;
    for (int i = 0; i < d.rows(); ++i) {
        t.push_back(i);
    }
    vector<int> position; position.resize(t.size());
    for (int i = 0; i < t.size(); ++i) {
        position[t[i]] = i;
    }

    printTourAndPos(t, position);
    geoKShuffle(t, position);
    checkConsistent(t, position);
    printTourAndPos(t, position);

    return 0;
}