#include <iostream>
#include <fstream>
#include <chrono>
#include <iomanip>
#include <string>
#include <algorithm>
#include <random>
#include <cmath>
#include <cstring>
using namespace std;

typedef long long llong;
typedef unsigned int uint;

#define pop(stack) stack[--stack ## fillPointer]
#define push(item, stack) stack[stack ## fillPointer++] = item

struct Edge {
    int v1;
    int v2;
};

// Start time counter
chrono::steady_clock::time_point start;

// Base parameters
int N, E;

// Learning Parameters
uint seed;
int noImproveMax; // Max number of iterations before no improvement in vertex chosen to be removed. Initial 5
double cutoffTime; // Max run time. Note that this only takes into account construction of VC and SLS
int mode;
int tryStep;
llong maxSteps, step;

// Graph Construction variables
Edge *edge;
int *edgeWeight;
int *vertexCost;
int **vertexEdges;
int **adjList;
int *vertexDegree;

// Search Heuristic scoring criteria
int *dscore;
int *validScore;
llong *timeStamp;

// Best Parameters
int bestCoverSize;
int *bestVertexCover;
double bestCompTime;
llong bestStep, bestWeight;

// Edge Stack Parameters
int uncoveredStackfillPointer;
int *uncoveredStack;
int *uncoveredStackIndex;

// Computation variables
int avgWeight, deltaTotalWeight, threshold, coverSize, removeCandidateSize;
int *vertexCover;
int *removeCandidates;
int *removeCandiatesIndex;
double pScale;
llong currWeight;

// Returns execution time in seconds
double getElapsedTime() {
    chrono::steady_clock::time_point finish = chrono::steady_clock::now();
    chrono::duration<double> duration = finish - start;
    return duration.count();
}

// Builds Instance of the original graph
int constructGraph() {
    int v, e, v1, v2;

    cin >> N >> E;

    edge = new Edge[E];
    edgeWeight = new int[E];
    uncoveredStack = new int[E];
    uncoveredStackIndex = new int[E];
    dscore = new int[N + 1];
    validScore = new int[N +1]; 
    timeStamp = new llong[N + 1];
    vertexEdges = new int *[N + 1];
    adjList = new int *[N + 1];
    vertexDegree = new int[N + 1];
    vertexCost = new int[N + 1];
    vertexCover = new int[N + 1];
    removeCandidates = new int[N + 1];
    removeCandiatesIndex = new int[N + 1];
    bestVertexCover = new int[N + 1];

    fill_n(vertexDegree, N + 1, 0); // Degree of vertex; for increasing search neighbourhood
    fill_n(vertexCover, N + 1, 0); // Marks whether vertex in cover
    fill_n(dscore, N + 1, 0); 
    fill_n(timeStamp, N + 1, 0);
    fill_n(edgeWeight, E, 1);
    fill_n(validScore, N + 1, 1000000); // scoring criteria for heuristic

    // Vertex cost
    for (v = 1; v < N + 1; v++) {
        cin >> vertexCost[v];
    }

    // Edges
    // NOTE: Post-processing done to addVertex 1 to weights
    // Following DIMACS format
    for (e = 0; e < E; e++) {
        cin >> v1 >> v2;
        vertexDegree[v1 + 1]++;
        vertexDegree[v2 + 1]++;

        edge[e].v1 = v1 + 1;
        edge[e].v2 = v2 + 1;
    }

    adjList[0] = 0;
    vertexEdges[0] = 0;
    for (v = 1; v < N + 1; v++) {
        adjList[v] = new int[vertexDegree[v]];
        vertexEdges[v] = new int[vertexDegree[v]];
    }

    int *tempVertexDegree = new int[N + 1];
    fill_n(tempVertexDegree, N + 1, 0);

    for (e = 0; e < E; e++) {
        v1 = edge[e].v1;
        v2 = edge[e].v2;

        vertexEdges[v1][tempVertexDegree[v1]] = e;
        vertexEdges[v2][tempVertexDegree[v2]] = e;

        adjList[v1][tempVertexDegree[v1]] = v2;
        adjList[v2][tempVertexDegree[v2]] = v1;

        tempVertexDegree[v1]++;
        tempVertexDegree[v2]++;
    }

    delete[] tempVertexDegree;

    return 0;
}

void ResetRemoveCand() {
    int v, degree, i;
    int j = 0;

    for (v = 1; v < N + 1; v++) {
        if (vertexCover[v] == 1) {
            removeCandidates[j] = v;
            removeCandiatesIndex[v] = j;
            j++;

            // Update score criteria: Sum of cost of neighbours - current vertex cost
            // Higher is better -> greater decrease in cost
            validScore[v] = -vertexCost[v];
            degree = vertexDegree[v];
            for (i = 0; i < degree; i++) {
            	if (vertexCover[adjList[v][i]]==0) {
            		validScore[v] += vertexCost[adjList[v][i]];
				}
			}            
        } else {
            removeCandiatesIndex[v] = 0;
        }
    }

    removeCandidateSize = j;
}

// Set edge to uncovered
inline void uncoverEdge(int e) {
    uncoveredStackIndex[e] = uncoveredStackfillPointer;
    push(e, uncoveredStack);
}

// Cover next uncovered edge
inline void coverEdge(int e) {
    int index, lastUncoveredEdge;
    lastUncoveredEdge = pop(uncoveredStack);
    index = uncoveredStackIndex[e];
    uncoveredStack[index] = lastUncoveredEdge;
    uncoveredStackIndex[lastUncoveredEdge] = index;
}

// Removes a vertex from cover
void removeVertex(int v) {
    int i, e, n;
    int edgeCount = vertexDegree[v];

    vertexCover[v] = 0;
    coverSize--;
    dscore[v] = -dscore[v]; // Flip from gain to loss
    validScore[v] = 1000000;

    int last_remove_cand_v = removeCandidates[--removeCandidateSize];
    int index = removeCandiatesIndex[v];
    removeCandidates[index] = last_remove_cand_v;
    removeCandiatesIndex[last_remove_cand_v] = index;
    removeCandiatesIndex[v] = 0;

    currWeight -= vertexCost[v];

    for (i = 0; i < edgeCount; i++) {
        e = vertexEdges[v][i];
        n = adjList[v][i];

        if (vertexCover[n] == 0) {
            dscore[n] += edgeWeight[e];
            uncoverEdge(e);
        } else {
            dscore[n] -= edgeWeight[e];
            validScore[n] += vertexCost[v];
        }
    }
}

// Adds vertex into vertex cover
void addVertex(int v) {
    int i, e, n;
    int edgeCount = vertexDegree[v];
   
    vertexCover[v] = 1; 
    coverSize++;
    dscore[v] = -dscore[v];
    currWeight += vertexCost[v];
    validScore[v] = -vertexCost[v];
    
    removeCandidates[removeCandidateSize] = v;
    removeCandiatesIndex[v] = removeCandidateSize++;

    // Update scores
    for (i = 0; i < edgeCount; i++) {
        e = vertexEdges[v][i];
        n = adjList[v][i];

        if (vertexCover[n] == 0) { // Edge previously not covered
            dscore[n] -= edgeWeight[e];
            coverEdge(e);
            validScore[v] += vertexCost[n];
        } else {
            dscore[n] += edgeWeight[e];
            validScore[n] -= vertexCost[v];

            if(validScore[n] == -vertexCost[n]) {
            	removeVertex(n);
			}
        }
    }
}

// Updates current best
void updateBestSolution() {
    int v;

    if (currWeight < bestWeight) {
        for (v = 1; v < N + 1; v++) {
            bestVertexCover[v] = vertexCover[v];
        }
        bestWeight = currWeight;
        bestCoverSize = coverSize;
        bestCompTime = getElapsedTime();
        bestStep = step;
    }
}

// Constructs initial vertex cover
void constructVertexCover() {
    int e;
    int v1, v2;
    // Use loss function score to pick vertices
    double v1score, v2score; 

    uncoveredStackfillPointer = 0;
    coverSize = 0;
    bestWeight = (int)(~0U >> 1);
    currWeight = 0;

    for (e = 0; e < E; e++) {
        v1 = edge[e].v1;
        v2 = edge[e].v2;

        if (vertexCover[v1] == 0 && vertexCover[v2] == 0) { // Edge not covered
            v1score = (double)vertexDegree[v1] / (double)vertexCost[v1];
            v2score = (double)vertexDegree[v2] / (double)vertexCost[v2];
            // Bigger ratio -> lower cost
            if (v1score > v2score) {
                vertexCover[v1] = 1;
                currWeight += vertexCost[v1];
            } else {
                vertexCover[v2] = 1;
                currWeight += vertexCost[v2];
            }
            coverSize++;
        }
    }

    int *savedVertexCover = new int[N + 1]; // Save current best
    memcpy(savedVertexCover, vertexCover, sizeof(int) * (N + 1));
    int savedCoverSize = coverSize;
    llong savedWeight = currWeight;

    // BMS Algorithm
    int times = 50; // Number of iterations of random pick. NOTE: Can be tuneds
    vector<int> blocks(E / 1024 + 1);
    for (int i = 0; i < E / 1024 + 1; i++) {
        blocks[i] = i;
    }

    // Run BMS algorithm to pick vertices
    while (times-- > 0) {
        fill_n(vertexCover, N + 1, 0);
        coverSize = 0;
        currWeight = 0;
        shuffle(blocks.begin(), blocks.end(), default_random_engine(seed));

        for (auto &block : blocks) {
            auto begin = block * 1024;
            auto end = block == E / 1024 ? E : begin + 1024;
            int tempSize = end - begin + 1;
            vector<int> idx(tempSize);

            for (int i = begin; i < end; i++) {
                idx[i - begin] = i;
            }

            while (tempSize > 0) {
                int i = rand() % tempSize;
                Edge e = edge[idx[i]];
                v1 = e.v1;
                v2 = e.v2;

                // BMS: pick random vertex and exchange
                swap(idx[i], idx[--tempSize]);
                if (vertexCover[v1] == 0 && vertexCover[v2] == 0) {
                    v1score = (double)vertexDegree[v1] / (double)vertexCost[v1];
                    v2score = (double)vertexDegree[v2] / (double)vertexCost[v2];

                    if (v1score > v2score) {
                        vertexCover[v1] = 1;
                        currWeight += vertexCost[v1];
                    } else {
                        vertexCover[v2] = 1;
                        currWeight += vertexCost[v2];
                    }

                    coverSize++;
                }
            }
        }

        // Save current best
        if (currWeight < savedWeight) {
            savedWeight = currWeight;
            savedCoverSize = coverSize;
            memcpy(savedVertexCover, vertexCover, sizeof(int) * (N + 1));
        }
    }

    // Update back
    currWeight = savedWeight;
    coverSize = savedCoverSize;
    memcpy(vertexCover, savedVertexCover, sizeof(int) * (N + 1));
    delete[] savedVertexCover;

    for (e = 0; e < E; e++) {
        v1 = edge[e].v1;
        v2 = edge[e].v2;

        if (vertexCover[v1] == 1 && vertexCover[v2] == 0) {
            dscore[v1] -= edgeWeight[e];
        } else if (vertexCover[v2] == 1 && vertexCover[v1] == 0) {
            dscore[v2] -= edgeWeight[e];
        }
    }

    ResetRemoveCand();
    for (int v = 1; v < N + 1; v++) {
        if (vertexCover[v] == 1 && dscore[v] == 0) {
            removeVertex(v);
        }
    }

    updateBestSolution();
}

// Checks if solution is valid
bool isValidSolution() {
    int e, v;

    for (e = 0; e < E; ++e) {
        // Not covered
        if (bestVertexCover[edge[e].v1] != 1 && bestVertexCover[edge[e].v2] != 1) {
            return false;
        }
    }

    return true;
}

int updateTargetSize() {
    int v;
    int best_remove_v;
    double best_dscore;
    double dscore_v;

    best_remove_v = removeCandidates[0];
    best_dscore = (double)(vertexCost[best_remove_v]) / (double)abs(dscore[best_remove_v]);

    if (dscore[best_remove_v] != 0) {
        for (int i = 1; i < removeCandidateSize; i++) {
            v = removeCandidates[i];
            if (dscore[v] == 0) break;

            dscore_v = (double)(vertexCost[v]) / (double)abs(dscore[v]);
            if (dscore_v > best_dscore){
                best_dscore = dscore_v;
                best_remove_v = v;
            }
        }
    }

    removeVertex(best_remove_v);
    return best_remove_v;
}

void clearEdgeWeights() {
    int v, e;
    int newTotalWeight = 0;

    for (v = 1; v < N + 1; v++) {
        dscore[v] = 0;
    }

    for (e = 0; e < E; e++) {
        edgeWeight[e] = edgeWeight[e] * pScale;
        newTotalWeight += edgeWeight[e];

        if (vertexCover[edge[e].v1] + vertexCover[edge[e].v2] == 0) {
            dscore[edge[e].v1] += edgeWeight[e];
            dscore[edge[e].v2] += edgeWeight[e];
        } else if (vertexCover[edge[e].v1] + vertexCover[edge[e].v2] == 1) {
            if (vertexCover[edge[e].v1] == 1) {
                dscore[edge[e].v1] -= edgeWeight[e];
            } else {
                dscore[edge[e].v2] -= edgeWeight[e];
            }
        }
    }

    avgWeight = newTotalWeight / E;
}

void updateEdgeWeight() {
    int i, e;

    for (i = 0; i < uncoveredStackfillPointer; i++) {
        e = uncoveredStack[i];
        edgeWeight[e] += 1;
        dscore[edge[e].v1] += 1;
        dscore[edge[e].v2] += 1;
    }

    deltaTotalWeight += uncoveredStackfillPointer;

    if (mode / 2 == 1) {
        if (deltaTotalWeight >= E) {
            avgWeight += 1;
            deltaTotalWeight -= E;
        }

        if (avgWeight >= threshold) {
            clearEdgeWeights();
        }
    }
}

// removeVertex first vertex during dynamic choose -> Intensification
// Uses deterministic validScore to determine pick
int chooseRemoveV1() {
    int i, v;
    int removeV1 = removeCandidates[0];
    int improvement_remove = validScore[removeV1],improvement_v;

    for (i = 1; i < removeCandidateSize; i++) {
    	v = removeCandidates[i];
    	improvement_v = validScore[v];

        // Pick vertex with minimum valid score -> lower cost
    	if (improvement_v > improvement_remove) {
    		continue;
		}

    	if (improvement_v < improvement_remove) {
    		removeV1 = v;
    		improvement_remove = improvement_v;
		} else if (timeStamp[v] < timeStamp[removeV1]) {
			removeV1 = v;
    		improvement_remove = improvement_v;
		}
	}

	return removeV1;  
}

// removeVertex second vertex during dynamic choose -> Diversification
// Uses loss function to pick vertex
int chooseRemoveV2() {
    int i, v;
    double dscore_v, dscore_remove_v;
    int removeV1 = removeCandidates[rand() % removeCandidateSize];
    int to_try = 50;

    for (i = 1; i < to_try; i++) {

        v = removeCandidates[rand() % removeCandidateSize];
        // Using loss function
        dscore_v = (double)vertexCost[v] / (double)abs(dscore[v]);
        dscore_remove_v = (double)vertexCost[removeV1] / (double)abs(dscore[removeV1]);
        
        if (dscore_v < dscore_remove_v) {
            continue;
        }
        
        if (dscore_v > dscore_remove_v) {
            removeV1 = v;
        } else if (timeStamp[v] < timeStamp[removeV1]) {
            removeV1 = v;
        }
    }

    return removeV1;
}

// Picks vertex to cover uncovered edge
int chooseAddV(int updateV, int removeV1 = 0, int removeV2 = 0) {
    int i, v;
    int addV = 0;
    double improvement = 0.0;
    double dscore_v;

    int tmp_degree = vertexDegree[updateV];
    int *adjp = adjList[updateV];

    for (i = 0; i < tmp_degree; i++) {

        v = adjp[i];
        if (vertexCover[v] == 1) { // Edge covered
            continue;
        }

        dscore_v = (double)dscore[v] / (double)(vertexCost[v]);
        if (dscore_v > improvement) {
                improvement = dscore_v;
                addV = v;
        } else if (dscore_v == improvement) {
            if (timeStamp[v] < timeStamp[addV]) {
                addV = v;
            }
        }
    }

    // Try to pick better update from removed v1
    if (removeV1 != 0) {
        tmp_degree = vertexDegree[removeV1];
        adjp = adjList[removeV1];
        for (i = 0; i < tmp_degree; i++) {
            v = adjp[i];
            if (vertexCover[v] == 1) {
                continue;
            }

            dscore_v = (double)dscore[v] / (double)(vertexCost[v]);
            if (dscore_v > improvement) {
                improvement = dscore_v;
                addV = v;
            } else if (dscore_v == improvement) {
                if (timeStamp[v] < timeStamp[addV]) {
                    addV = v;
                }
            }
        }
    }

    // Try to pick better update from removed v2
    if (removeV2 != 0) {
        tmp_degree = vertexDegree[removeV2];
        adjp = adjList[removeV2];
        for (i = 0; i < tmp_degree; i++) {
            v = adjp[i];
            if (vertexCover[v] == 1) {
                continue;
            }
            dscore_v = (double)dscore[v] / (double)(vertexCost[v]);
            if (dscore_v > improvement) {
                improvement = dscore_v;
                addV = v;
            } else if (dscore_v == improvement) {
                if (timeStamp[v] < timeStamp[addV]) {
                    addV = v;
                }
            }
        }
    }

    return addV;
}

// Performs local search on current VC to update weight
void localSearch() {

    int addV, removeV1 = 0, updateV = 0, removeV2 = 0;
    int noImprovement = 0, dynCount = 0, tempWeight;
    step = 1;
    tryStep = 100; // NOTE: Can be tuned
    int removeDegree = 0;

    avgWeight = 1;
    deltaTotalWeight = 0;
    pScale = 0.3;
    threshold = (int)(0.5 * N);

    // Dynamic choose algorithm
    while (true) {
        tempWeight = currWeight;		
        updateBestSolution();      
        updateV = updateTargetSize();       
        timeStamp[updateV] = step;
        if (step % tryStep == 0) {
            if (getElapsedTime() >= cutoffTime) {
                return;
            }
        }
 
        if (noImprovement < noImproveMax) {
            removeV1 = chooseRemoveV1();
            removeVertex(removeV1);		
            timeStamp[removeV1] = step;

        } else {
            if (noImprovement == noImproveMax) {
                dynCount = 2;
            } 
            
            if (dynCount == 1) {
                noImprovement = 0;
            }

            removeV1 = chooseRemoveV2();
            removeVertex(removeV1);		
            timeStamp[removeV1] = step;
            dynCount--;
        }

        removeDegree = vertexDegree[updateV] + vertexDegree[removeV1];
        // If v1 and v2 total degree < 2 * average degree, increase search space
        // By removing one more vertex
        // NOTE: Can be tuned, but not recommended
        if (removeDegree < 2 * E / N) {   
            removeV2 = chooseRemoveV2();
            removeVertex(removeV2);
            timeStamp[removeV2] = step;
        }   

        // Cover all edges
        while (uncoveredStackfillPointer > 0) {
            addV = chooseAddV(updateV, removeV1, removeV2);
            addVertex(addV);            
            updateEdgeWeight();
            timeStamp[addV] = step;
        }

        step++;
        removeV2 = 0;  

        if (currWeight >= tempWeight) {
            noImprovement += 1;
        }

        removeDegree = 0; 
    }   
}

int main(void) {
    // Learning Parameters -> Tune these parameters
    uint seed = chrono::high_resolution_clock::now().time_since_epoch().count(); // Random seed
    cutoffTime = 1.95; // Set cutoff time
    noImproveMax = 5;

    srand(seed);

    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    start = chrono::steady_clock::now();

    // Build original graph
    constructGraph();

    // Construct initial vertex cover
    constructVertexCover();
    // Run SLS
    localSearch();

    if (isValidSolution()) {
        cout << bestWeight << endl;
        for (int i = 1; i <= N; i++) {
            if (bestVertexCover[i] == 1) {
                printf("%d ", i - 1);
            }
        }

        printf("\n");
    }

    return 0;
}
