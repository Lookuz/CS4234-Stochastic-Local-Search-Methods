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

#ifdef DEBUG
    #define LOG(x) std::cerr << x << std::endl
#else
    #define LOG(x)
#endif

using namespace std;

// Random number generator.
random_device rd;
default_random_engine rng(rd());

// Size of nearest neighbors matrix.
const static size_t MAX_K = 20;

// ---------------- Helper functions -------------------------------------------------

void printVec(vector<int> v) {
    for (const auto& n : v) {
        std::cout << n << ", ";
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
 *
 * @param d Distance matrix.
 * @return Minimum distance in d.
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
 *
 * @param tour The input tour.
 * @param d Distance matrix.
 * @return The total length of the tour.
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
inline void reverse(vector<int> &tour, size_t start, size_t end, vector<int>& position) {
    size_t N = tour.size();
    size_t numSwaps = (( (start <= end ? end - start : (end + N) - start) + 1)/2);
    int i = start;
    int j = end;
    for (size_t n = 0; n < numSwaps; ++n) {
        swap(tour[i], tour[j]);
        position[tour[i]] = i;
        position[tour[j]] = j;
        i = (i + 1) % N;
        j = ((j + N) - 1) % N;
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

// -----------------------------------------------------------------------------------

typedef pair<int, int> ii;
typedef vector<int> vi;
typedef vector<ii> vii;


// compute alpha values for the graph given
// it will use prims to create the V-tree (where the special node is V-1)
Matrix<long> createAlphaMatrix(Matrix<long> &adjMatrix) { // adjMatrix is square
    vi parent; // store predecessor of nodes in mst
    vi taken; // nodes in the partial mst
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
 *
 * @param in Input stream.
 * @return The read distance matrix.
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
Matrix<int> createNeighborsMatrix(const Matrix<long>& alphaMatrix, size_t K) {
    size_t N = alphaMatrix.rows();
    size_t M = alphaMatrix.cols() - 1; // node is not neighbor of itself
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
                return alphaMatrix[i][j] < alphaMatrix[i][k];
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

// returns predecessor of t1 in the tour
inline int pred(vector<int> &tour, vector<int> &position, int &t1) {
    int N = tour.size();
    return tour[(position[t1] - 1 + N) % N];
}
// returns successor of t1 in the tour
inline int succ(vector<int> &tour, vector<int> &position, int &t1) {
    int N = tour.size();
    return tour[(position[t1] + 1) % N];
}

// returns whether t1 and t2 are adjacent in the tour
inline bool isAdjacent(vector<int> &tour, vector<int> &position, int t1, int t2) {
    return (pred(tour, position, t1) == t2 || succ(tour, position, t1) == t2);
}

// re-order the tour...
// desc is a list of tuples, <startPos, endPos, dir> where dir = 1 or -1
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
    // Deadline for 3-opt inside main loop is 50 ms before hard deadline.
    chrono::milliseconds fifty_ms(50);
    auto threeOptDeadline = deadline - fifty_ms;

    // Calculate distance / K-nearest neighbors matrix.
    // Matrix<long> alphaMatrix = createAlphaMatrix(d);
    const Matrix<int> neighbor = createNeighborsMatrix(d, MAX_K);
    const long min = minDistance(d); // Shortest distance.
    const size_t N = d.rows();           // Number of cities.

    // Generate initial greedy tour.
    vector<int> tour = greedy(d);

    // Create max / position for initial 2-opt + 3-opt.
    vector<int> position(N);
    long max = 0;
    for (int i = 0; i < N; ++i) {
        max = std::max(max, d[i][(i + 1) % N]); // Maximum distance in tour.
        position[tour[i]] = i;                  // tour[i] is i:th city in tour.
    }

    // Optimize tour with 2-opt + 3-opt.
    twoOpt(tour, d, neighbor, position, max, min);
    threeOpt(tour, d, neighbor, position, max, min, threeOptDeadline);

    /*
     * Main loop.
     *
     * We repeatedly
     *
     *   1) "Kick" the tour with a random 4-exchange.
     *   2) Optimize the tour with 2-opt + 3-opt.
     *
     * until only max(50, 2 * average iteration time) milliseconds remains
     * before deadline, and then pick the shortest tour we found.
     */

    // Some main loop statistics.
    size_t i = 0;                        // Number of iterations of main loop.
    chrono::milliseconds totalTime(0);   // Total time spent in main loop.
    chrono::milliseconds averageTime(0); // Average main loop iteration time.

    vector<int> shortestTour = tour;          // Best tour found.
    long long shortestTourLength = length(tour, d); // Length of best tour found.

    for (i = 0; (now() + std::max(fifty_ms, 2 * averageTime)) < deadline; ++i) {
        auto start = now();

        if (N >= 8) {
            // Perform random 4-opt "double bridge" move.
            tour = doubleBridge(tour);
        } else {
            // Tiny tour, so just shuffle it instead.
            shuffle(tour.begin(), tour.end(), rng);
        }

        // Update max / position needed by fast 2/3-opt.
        max = 0;
        for (int j = 0; j < N; ++j) {
            max = std::max(max, d[tour[j]][tour[(j + 1) % N]]);
            position[tour[j]] = j;
        }

        // Optimize tour with 2-opt + 3-opt.
        twoOpt(tour, d, neighbor, position, max, min);
        threeOpt(tour, d, neighbor, position, max, min, threeOptDeadline);

        long long tourLength = length(tour, d);
        if (tourLength < shortestTourLength) {
            // Shorter tour found.
            shortestTour = tour;
            shortestTourLength = tourLength;
        }

        // Collect statistics.
        totalTime += chrono::duration_cast<chrono::milliseconds>(now() - start);
        averageTime = totalTime / (i + 1);
    }

    // cout << "Main Loop Statistics\n";
    // cout << "iterations: " << i << "\n";
    // cout << "totalTime: " << totalTime << "\n";
    // cout << "averageTime: " << averageTime << "\n";

    return shortestTour;
}

int main(int argc, char *argv[]) {
    // create dist matrix
    Matrix<long> d = createDistanceMatrix(cin);

    // Approximate/print a TSP tour in ~1950 milliseconds.
    vector<int> st = approximate(d, now() + chrono::milliseconds(1950));

    // print tour
    // for (auto city : st) {
    //     cout << city << endl;
    // }
    // cout << "tour len: " << st.size() << "\n";

    // stats
    long long stLength = length(st, d);
    long long optLength; cin >> optLength;
    cout << "length: " << stLength << "\n";
    cout << "Percent above OPT: " << (static_cast<double>(stLength) / optLength * 100) << "\n\n";

    return 0;
}