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

using namespace std;

random_device rd; // Random number generator.
default_random_engine rng(rd());
chrono::time_point<chrono::high_resolution_clock> ts1, ts2;

// Size of nearest neighbors matrix.
const static size_t MAX_K = 20;
const static int NUM_DOUBLE_BRIDGE_BEFORE_LOCAL_SHUFFLE = 10;
const static int THREE_OPT_BUFFER_TIME = 30;
const static int EXECUTION_DURATION = 1950; // time for the whole algo
const static int GEO_SHUFFLE_WIDTH = 10;
const static int MIN_IMPROVEMENTS_TO_REPEAT = 5; // number of improvements that a 2/3-opt loop must find to repeat that loop again
const static int MAX_DEPROVEMENTS = 3;
const static int SHUFFLE_PROBABILITY = 24; // chance to shuffle vs double bridge, value from 0 to 100

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

static inline void startWatch() {
    ts1 = now();
}
static inline void stopWatch() {
    ts2 = now();
    cout << "time elapsed: " << ts1 - ts2 << "\n";
}

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

inline vector<int> getPositionVec(vector<int> &tour) {
    vector<int> position; position.resize(tour.size());
    for (int i = 0; i < tour.size(); ++i) {
        position[tour[i]] = i;
    }
    return position;
}

inline long getMaxWeight(vector<int> &tour, Matrix<long> &d) {
    int N = tour.size();
    long m = 0;
    for (int i = 0; i < N; ++i) {
        m = max(m, d[tour[i]][tour[(i + 1) % N]]);
    }
    return m;
}

// check if a position vector matches a tour vector.
void checkConsistent(vector<int> &tour, vector<int> &position) {
    assert(tour.size() == position.size());
    for (int i = 0; i < position.size(); ++i) {
        assert(position[tour[i]] == i);
    }
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


// Returns the shortest distance d[i][j], i != j in the given distance matrix.
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

// Returns the total length of a tour.
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
    int numSwaps = (start <= end ? (end - start + 1) : (end + N - start + 1)) / 2;
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
// todo: i feel like this can be optimized but idk how
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

// Create a distance matrix from an input stream and return it.
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

// constructs a greedy tour
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

// constructs the 2-approx MST-based tour
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
    cout << "2-Approx:\nadjList:\n";
    printVecVec(adjList);
    cout << "tour\n";
    printVec(tour);
    #endif

    return tour;
}

// constructs algorithm for initial tour by greedily choosing shortest edges first
// O(N^2 log N)
vector<int> multiFrag(const Matrix<long>& d) {
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
inline bool isAdjacent(vector<int> &tour, vector<int> &position, int &t1, int &t2) {
    return (pred(tour, position, t1) == t2 || succ(tour, position, t1) == t2);
}

// twoOptLoop, but we shortcut the search using partial gain method
inline void twoOptLoopV2(vector<int>& tour, const Matrix<long>& d,
        const Matrix<int>& neighbor, vector<int> &position) {
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
                w = tour[w_i];
                
                if (d[u][w] >= d[u][v]) break; // WLOG only consider edges that (u, w) < (u, v)
                                               // since neighbor list is sorted ascending, no point checking further 

                z_i = w_i + 1;
                z = tour[z_i % N];

                if (v == w || u == z) {
                    continue; // Skip adjacent edges.
                }

                if (d[u][w] + d[v][z] < d[u][v] + d[w][z]) {
                    //   --u w--        --u-w->
                    //      X     ===>
                    //   <-z v->        <-z-v--
                    reverse(tour, v_i % N, w_i, position); // implicitly deletes and adds edges
                    locallyOptimal = false;
                    break;
                }
            }
        }
    }
}

inline void twoHOptLoop(vector<int>& tour, const Matrix<long>& d,
        const Matrix<int>& neighbor, vector<int> &position) {
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
                    locallyOptimal = false;
                    break;
                }
            }
        }
    }
}

// 3-opt properly done
inline void threeOptLoopV3(vector<int>& tour, const Matrix<long>& d,
        const Matrix<int>& neighbor, vector<int> &position) {
    int N = tour.size();

    int A, B, P, Q, C, D;
    int A_i, B_i, P_i, Q_i, C_i, D_i;
    long delta1, delta2;

    bool locallyOptimal = false;
    while (!locallyOptimal) {
        locallyOptimal = true;

        // For each edge AB.
        long d_AB_CD_EF;
        for (A_i = 0; A_i < N; ++A_i) {
            A = tour[A_i];
            B_i = (A_i + 1) % N;
            B = tour[B_i];

            for(int i = 0; i < neighbor.cols(); ++i) {
                P = neighbor[B][i]; // P is a nearest neighbor of B

                delta1 = d[B][P] - d[A][B];
                if (delta1 >= 0) break; // we want partial gain positive
                
                if (P == A) continue; // we want A B P distinct
                
                P_i = position[P];

                // we have 2 choices, Q is either the pred or the succ of P
                // try Q is successor first
                Q_i = (P_i + 1) % N;
                Q = tour[Q_i];
                if (Q_i != A_i) { // all A B P Q are distinct
                    for (int j = 0; j < neighbor.cols(); ++j) { // try to find C
                        C = neighbor[Q][j];
                        C_i = position[C];

                        // check if C is valid 5th point
                        if (C == P || C == A || C == B) continue; // C not distinct, try another C
                        // C is between B and P
                        if ((C_i < P_i && P_i < B_i) ||
                            (P_i < B_i && B_i < C_i) ||
                            (B_i < C_i && C_i < P_i)) { // C is between B and P
                            delta2 = delta1 + d[Q][C] - d[P][Q];
                            if (delta2 >= 0) break; // no point searching further down neighbor list

                            // we have a good set of A,B,P,Q,C
                            D_i = (C_i + 1) % N;
                            D = tour[D_i];

                            // vector<int> o{A_i, B_i, P_i, Q_i, C_i, D_i};
                            // cout << "case 1: "; printVec(o);

                            if (delta2 + d[A][D] - d[C][D] < 0) { // improving 3-opt move
                                swapAdjacentSegments(tour, position, Q_i, A_i, B_i, C_i);
                                locallyOptimal = false;
                                goto next_AB;
                            }
                        }
                    }
                }
                
                // now, we try Q is pred
                Q_i = (P_i + N - 1) % N;
                Q = tour[Q_i];
                if (Q_i != A_i) { // all A B P Q are distinct
                    for (int j = 0; j < neighbor.cols(); ++j) { // try to find C
                        C = neighbor[Q][j];
                        C_i = position[C];

                        // check if C is valid 5th point
                        if (C == P || C == A || C == B) continue; // C not distinct, try another C
                        // C is between B and P
                        if ((C_i < P_i && P_i < B_i) ||
                            (P_i < B_i && B_i < C_i) ||
                            (B_i < C_i && C_i < P_i)) { // C is between B and P
                            delta2 = delta1 + d[Q][C] - d[P][Q];
                            if (delta2 >= 0) break; // no point searching further down neighbor list

                            // we have a good set of A,B,P,Q,C
                            D_i = (C_i + 1) % N;
                            D = tour[D_i];

                            // vector<int> o{A, B, P, Q, C, D};
                            // cout << "case 1: "; printVec(o);

                            if (delta2 + d[A][D] - d[C][D] < 0) { // improving 3-opt move
                                reverse(tour, D_i, Q_i, position);
                                reverse(tour, P_i, A_i, position);
                                locallyOptimal = false;
                                goto next_AB;
                            }
                        }
                    }
                }
            }
            next_AB: continue;
        }
    }    
}

// merges 2 and 3 opt
inline void kOpt(vector<int>& tour, const Matrix<long>& d,
        const Matrix<int>& neighbor, vector<int> &position) {
    int N = tour.size();

    int A, B, P, Q, C, D;
    int A_i, B_i, P_i, Q_i, C_i, D_i;
    long delta1, delta2;

    bool locallyOptimal = false;
    while (!locallyOptimal) {
        locallyOptimal = true;

        // For each edge AB.
        long d_AB_CD_EF;
        for (A_i = 0; A_i < N; ++A_i) {
            A = tour[A_i];
            B_i = (A_i + 1) % N;
            B = tour[B_i];

            for(int i = 0; i < neighbor.cols(); ++i) {
                P = neighbor[B][i]; // P is a nearest neighbor of B

                delta1 = d[B][P] - d[A][B];
                if (delta1 >= 0) break; // we want partial gain positive
                
                if (P == A) continue; // we want A B P distinct
                
                P_i = position[P];

                // we have 2 choices, Q is either the pred or the succ of P
                // we try Q is pred first
                Q_i = (P_i + N - 1) % N;
                Q = tour[Q_i];
                if (Q_i != A_i) { // all A B P Q are distinct
                    // try see if 2-opt change here is improving
                    if (delta1 - d[P][Q] + d[Q][A] < 0) {
                        reverse(tour, B_i, Q_i, position);
                        locallyOptimal = false;
                        goto next_AB;
                    }

                    for (int j = 0; j < neighbor.cols(); ++j) { // try to find C
                        C = neighbor[Q][j];
                        C_i = position[C];

                        // check if C is valid 5th point
                        if (C == P || C == A || C == B) continue; // C not distinct, try another C
                        // C is between B and P
                        if ((C_i < P_i && P_i < B_i) ||
                            (P_i < B_i && B_i < C_i) ||
                            (B_i < C_i && C_i < P_i)) { // C is between B and P
                            delta2 = delta1 + d[Q][C] - d[P][Q];
                            if (delta2 >= 0) break; // no point searching further down neighbor list

                            // we have a good set of A,B,P,Q,C
                            D_i = (C_i + 1) % N;
                            D = tour[D_i];

                            // vector<int> o{A, B, P, Q, C, D};
                            // cout << "case 1: "; printVec(o);

                            if (delta2 + d[A][D] - d[C][D] < 0) { // improving 3-opt move
                                reverse(tour, D_i, Q_i, position);
                                reverse(tour, P_i, A_i, position);
                                locallyOptimal = false;
                                goto next_AB;
                            }
                        }
                    }
                }

                // try Q is successor
                Q_i = (P_i + 1) % N;
                Q = tour[Q_i];
                if (Q_i != A_i) { // all A B P Q are distinct
                    for (int j = 0; j < neighbor.cols(); ++j) { // try to find C
                        C = neighbor[Q][j];
                        C_i = position[C];

                        // check if C is valid 5th point
                        if (C == P || C == A || C == B) continue; // C not distinct, try another C
                        // C is between B and P
                        if ((C_i < P_i && P_i < B_i) ||
                            (P_i < B_i && B_i < C_i) ||
                            (B_i < C_i && C_i < P_i)) { // C is between B and P
                            delta2 = delta1 + d[Q][C] - d[P][Q];
                            if (delta2 >= 0) break; // no point searching further down neighbor list

                            // we have a good set of A,B,P,Q,C
                            D_i = (C_i + 1) % N;
                            D = tour[D_i];

                            // vector<int> o{A_i, B_i, P_i, Q_i, C_i, D_i};
                            // cout << "case 1: "; printVec(o);

                            if (delta2 + d[A][D] - d[C][D] < 0) { // improving 3-opt move
                                swapAdjacentSegments(tour, position, Q_i, A_i, B_i, C_i);
                                locallyOptimal = false;
                                
                                goto next_AB;
                            }
                        }
                    }
                }
                
            }
            next_AB: continue;
        }
    }    
}



// Perform a double bridge move on a tour.
// Input tour must have at least 8 cities
// returns the new tour.
inline vector<int> doubleBridgeV1(const vector<int>& tour) { // vector<int> &position) {
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

// Perform a double bridge move on a tour
// update tour and position in place
// Input tour must have at least 8 cities
// benchmark shows this version is slower that V1, but not significantly so
inline void doubleBridgeV2(vector<int>& tour, vector<int> &position) {
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
    copy(newTour.begin(), newTour.end(), tour.begin());
    assert(tour.size() == N);
    for (int i = 0; i < tour.size(); ++i) {
        position[tour[i]] = i;
    }
    return;
}

// This splits the tour into several blocks, and shuffles each block
// modifies tour and position in place
inline void geoKShuffleV1(vector<int>& tour, vector<int> &position) {
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

// This splits the tour into several blocks, and shuffles each block
// modifies tour in place
inline void geoKShuffleV1(vector<int>& tour) {
    if (tour.size() <= GEO_SHUFFLE_WIDTH) {
        shuffle(tour.begin(), tour.end(), rng);
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
    return;
}

// This randomly selects a subtour and shuffles it
// modifies tour and position in place
inline void geoKShuffleV2(vector<int>& tour, vector<int> &position) {
    if (tour.size() <= GEO_SHUFFLE_WIDTH) {
        shuffle(tour.begin(), tour.end(), rng);
        for (int i = 0; i < tour.size(); ++i) {
            position[tour[i]] = i;
        }
        return;
    }
    uniform_int_distribution<size_t> randomOffset(0, tour.size() - GEO_SHUFFLE_WIDTH); // [a, b] Inclusive
    int left = randomOffset(rng);
    // cout << "left: " << left << "\n";
    shuffle(tour.begin() + left, tour.begin() + left + GEO_SHUFFLE_WIDTH, rng); // [a, b) exclusive
    for (int i = left; i < left + GEO_SHUFFLE_WIDTH; ++i) {
        position[tour[i]] = i;
    }
    return;
}

// This randomly selects a subtour and shuffles it
// modifies tour in place
inline void geoKShuffleV2(vector<int>& tour) {
    if (tour.size() <= GEO_SHUFFLE_WIDTH) {
        shuffle(tour.begin(), tour.end(), rng);
    }
    uniform_int_distribution<size_t> randomOffset(0, tour.size() - GEO_SHUFFLE_WIDTH); // [a, b] Inclusive
    int left = randomOffset(rng);
    // cout << "left: " << left << "\n";
    shuffle(tour.begin() + left, tour.begin() + left + GEO_SHUFFLE_WIDTH, rng); // [a, b) exclusive
    return;
}

// the actual local search algo
template<typename T>
vector<int> approximate(Matrix<long> &d, const chrono::time_point<T>& deadline) {
    chrono::milliseconds buffer(THREE_OPT_BUFFER_TIME);
    auto threeOptDeadline = deadline - buffer; // three OPT must terminate slightly earlier due to slowness

    const size_t N = d.rows();       // Number of cities.

    if (N == 1) { // test case 7 is a single city
        return vector<int>({0});
    }

    const Matrix<int> neighbor = createNeighborsMatrix(d, MAX_K); // nearest neighbor matrix

    // Generate initial tour. greedy/multiFrag/twoApprox
    // vector<int> tour = greedy(d);
    vector<int> tour = multiFrag(d);
    // vector<int> tour = twoApprox(d);

    // initialize position vector
    vector<int> position(N);
    for (int i = 0; i < N; ++i) {
        position[tour[i]] = i;
    }

    // Local optimization
    twoOptLoopV2(tour, d, neighbor, position);
    threeOptLoopV3(tour, d, neighbor, position);

    // Some main loop statistics.
    size_t i = 0;                        // Number of iterations of main loop.
    chrono::milliseconds totalTime(0);   // Total time spent in main loop.
    chrono::milliseconds averageTime(0); // Average main loop iteration time.

    vector<int> shortestTour = tour;          // Best tour found.
    long long shortestTourLength = length(tour, d); // Length of best tour found.
    int numDB = 0; // number of double bridge moves
    int numShuffles = 0; // number of shuffle moves
    int numFailSinceLastShuffle = 0; // number of double bridges that failed to improve the tour
    int numDeprovement = 0;
    uniform_int_distribution<size_t> randomOffset(1, 100);

    for (i = 0; (now() + std::max(buffer, 2 * averageTime)) < deadline; ++i) {
        auto start = now();

        if (N < 8) {
            shuffle(tour.begin(), tour.end(), rng); // Tiny tour, so just shuffle it instead.
        } else {
            // do double bridge move OR a shuffle depending on chance
            size_t A = randomOffset(rng);
            if (A <= SHUFFLE_PROBABILITY) {
                geoKShuffleV2(tour);
                //cout << "Shuffle!\n";
            } else {
                tour = doubleBridgeV1(tour);
                //cout << "D-bridge!\n";
                numDB++;
            }
        }

        // Update position
        for (int j = 0; j < N; ++j) {
            position[tour[j]] = j;
        }

        // Optimize tour with 2-opt + 3-opt.
        // startWatch();
        // twoOptLoopV2(tour, d, neighbor, position);
        // threeOptLoopV3(tour, d, neighbor, position);
        kOpt(tour, d, neighbor, position);
        // stopWatch();
        // startWatch();
        // stopWatch();
        // cout << "\n";
        
        // compare with best tour
        long long tourLength = length(tour, d);
        if (tourLength < shortestTourLength) {
            // Shorter tour found.
            shortestTour = tour; // store shorter tour
            shortestTourLength = tourLength;
            numDeprovement = 0; // allow another bunch of deprovements
            //cout << "found better tour\n";
        } else if (tourLength == shortestTourLength) { // equal length
            // we dont increase numDeprovement, see it as horizontal move
            //cout << "found equal tour\n";
        } else { // we deproved
            ++numDeprovement;
            if (numDeprovement > MAX_DEPROVEMENTS) { // we have allowed too many deproving double bridges
                //cout << "reverting to best tour\n";
                tour = shortestTour; // restore the best tour
                numDeprovement = 0;
            } else {
                // continue with this worse tour and hope for improvement
                //cout << "deproved, continuing\n";
                ++numDeprovement;
            }
        }

        // Collect statistics.
        totalTime += chrono::duration_cast<chrono::milliseconds>(now() - start);
        averageTime = totalTime / (i + 1);
    }

    // select stats to print
    // cout << "Main Loop Statistics\n";
    // cout << "iterations: " << i << "\n";
    // // cout << "totalTime: " << totalTime << "\n";
    // // cout << "averageTime: " << averageTime << "\n";
    // long long stLength = length(shortestTour, d);
    // long long optLength; cin >> optLength;
    // cout << "numCities: " << shortestTour.size() << "\n";
    // cout << "length: " << stLength << "\n";
    // cout << "Percent above OPT: " << (static_cast<double>(stLength) / optLength * 100) << "\n";
    // cout << "numDB: " << numDB << "\n";
    // cout << "numShuffles: " << numShuffles << "\n";

    return shortestTour;
}

// Use this function for benchmarking stuff
void benchMark(Matrix<long> &d) {
    
    const Matrix<int> neighbor = createNeighborsMatrix(d, MAX_K);
    
    vector<int> t1 = twoApprox(d);
    vector<int> t2 = t1;
    vector<int> t3 = t1;
    vector<int> p1 = getPositionVec(t1);
    vector<int> p2 = getPositionVec(t2);
    vector<int> p3 = getPositionVec(t3);

    auto dl = now() + chrono::milliseconds(EXECUTION_DURATION);
    
    cout << "initial len t1: " << length(t1, d) << "\n";
    startWatch();
    cout << "len t1: " << length(t1, d) << "\n";
    stopWatch();

    cout << "initial len t2: " << length(t2, d) << "\n";
    startWatch();
    threeOptLoopV3(t2, d, neighbor, p2);
    cout << "len t2: " << length(t2, d) << "\n";
    stopWatch();
    
}

int main(int argc, char *argv[]) {

    Matrix<long> d = createDistanceMatrix(cin);
    // cout << d << "\n";
    // Approximate/print a TSP tour in EXECUTION_DURATION milliseconds.
    vector<int> st = approximate(d, now() + chrono::milliseconds(EXECUTION_DURATION));
    // benchMark(d);
    // for test.py
    int showDescription = 2; // 0 is for kattis. 1 is for human. 2 for test.py
    
    uint64_t stLength = length(st, d);
    uint64_t optLength; cin >> optLength;
    if (showDescription == 0) { // print tour
        for (auto city : st) {
            cout << city << endl;
        }
        //cout << "tour len: " << st.size() << "\n";
    } else if (showDescription == 1) {
        cout << "length: " << stLength << "\n";
        cout << "Percent above OPT: " << (static_cast<double>(stLength) / optLength * 100) << "\n\n";
    } else {
        cout << stLength << " " << optLength;
    }

    // testing for correctness ================================================
    // vector<int> t;
    // for (int i = 0; i < d.rows(); ++i) {
    //     t.push_back(i);
    // }
    // vector<int> position = getPositionVec(t);

    // // printTourAndPos(t, position);
    // startWatch();
    // vector<int> newt;
    // for (int i = 0; i < 1000; ++i) {
    //     newt = doubleBridgeV1(t);
    //     for (int j = 0; j < t.size(); ++j) {
    //         position[t[j]] = j;
    //     }
    //     //checkConsistent(t, position);
    // }
    // stopWatch();
    // // cout << "\n";
    // startWatch();
    // for (int i = 0; i < 1000; ++i) {
    //     doubleBridgeV2(t, position);
    //     checkConsistent(t, position);
    // }
    // stopWatch();

    return 0;
}