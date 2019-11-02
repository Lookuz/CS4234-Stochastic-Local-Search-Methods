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

#define pop(stack) stack[--stack ## _fill_pointer]
#define push(item, stack) stack[stack ## _fill_pointer++] = item

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
double cutoff_time; // Max run time. Note that this only takes into account construction of VC and SLS
int mode;
int try_step;
llong max_steps, step;

// Graph Construction variables
Edge *edge;
int *edge_weight;
int *vertex_cost;
int **v_edges;
int **v_adj;
int *vertex_degree;

// Search Heuristic scoring criteria
int *dscore;
int *valid_score;
llong *time_stamp;

// Best Parameters
int best_cover_size;
int *best_vertex_cover;
double best_comp_time;
llong best_step, best_weight;

// Edge Stack Parameters
int uncov_stack_fill_pointer;
int *uncov_stack;
int *index_in_uncov_stack;

// Computation variables
int avg_weight, delta_total_weight, threshold, c_size, remove_cand_size;
int *vertex_cover;
int *remove_candidates;
int *remove_candidates_index;
double p_scale;
llong curr_weight;

// Returns execution time in seconds
double TimeElapsed() {
    chrono::steady_clock::time_point finish = chrono::steady_clock::now();
    chrono::duration<double> duration = finish - start;
    return duration.count();
}

// Builds Instance of the original graph
int BuildInstance() {
    int v, e;
    int v1, v2;

    cin >> N >> E;

    edge = new Edge[E];
    edge_weight = new int[E];
    uncov_stack = new int[E];
    index_in_uncov_stack = new int[E];
    dscore = new int[N + 1];
    valid_score = new int[N +1]; 
    time_stamp = new llong[N + 1];
    v_edges = new int *[N + 1];
    v_adj = new int *[N + 1];
    vertex_degree = new int[N + 1];
    vertex_cost = new int[N + 1];
    vertex_cover = new int[N + 1];
    remove_candidates = new int[N + 1];
    remove_candidates_index = new int[N + 1];
    best_vertex_cover = new int[N + 1];

    fill_n(vertex_degree, N + 1, 0); // Degree of vertex; for increasing search neighbourhood
    fill_n(vertex_cover, N + 1, 0); // Marks whether vertex in cover
    fill_n(dscore, N + 1, 0); 
    fill_n(time_stamp, N + 1, 0);
    fill_n(edge_weight, E, 1);
    fill_n(valid_score, N + 1, 1000000); // scoring criteria for heuristic

    // Vertex cost
    for (v = 1; v < N + 1; v++) {
        cin >> vertex_cost[v];
    }

    // Edges
    // NOTE: Post-processing done to add 1 to weights
    // Following DIMACS format
    for (e = 0; e < E; e++) {
        cin >> v1 >> v2;
        vertex_degree[v1 + 1]++;
        vertex_degree[v2 + 1]++;

        edge[e].v1 = v1 + 1;
        edge[e].v2 = v2 + 1;
    }

    v_adj[0] = 0;
    v_edges[0] = 0;
    for (v = 1; v < N + 1; v++) {
        v_adj[v] = new int[vertex_degree[v]];
        v_edges[v] = new int[vertex_degree[v]];
    }

    int *v_degree_tmp = new int[N + 1];
    fill_n(v_degree_tmp, N + 1, 0);

    for (e = 0; e < E; e++) {
        v1 = edge[e].v1;
        v2 = edge[e].v2;

        v_edges[v1][v_degree_tmp[v1]] = e;
        v_edges[v2][v_degree_tmp[v2]] = e;

        v_adj[v1][v_degree_tmp[v1]] = v2;
        v_adj[v2][v_degree_tmp[v2]] = v1;

        v_degree_tmp[v1]++;
        v_degree_tmp[v2]++;
    }

    delete[] v_degree_tmp;

    return 0;
}

void ResetRemoveCand() {
    int v, degree, i;
    int j = 0;

    for (v = 1; v < N + 1; v++) {
        if (vertex_cover[v] == 1) {
            remove_candidates[j] = v;
            remove_candidates_index[v] = j;
            j++;

            // Update score criteria: Sum of cost of neighbours - current vertex cost
            // Higher is better -> greater decrease in cost
            valid_score[v] = -vertex_cost[v];
            degree = vertex_degree[v];
            for (i = 0; i < degree; i++) {
            	if (vertex_cover[v_adj[v][i]]==0) {
            		valid_score[v] += vertex_cost[v_adj[v][i]];
				}
			}            
        } else {
            remove_candidates_index[v] = 0;
        }
    }

    remove_cand_size = j;
}

// Set edge to uncovered
inline void Uncover(int e) {
    index_in_uncov_stack[e] = uncov_stack_fill_pointer;
    push(e, uncov_stack);
}

// Cover next uncovered edge
inline void Cover(int e) {
    int index, last_uncov_edge;
    last_uncov_edge = pop(uncov_stack);
    index = index_in_uncov_stack[e];
    uncov_stack[index] = last_uncov_edge;
    index_in_uncov_stack[last_uncov_edge] = index;
}

// Removes a vertex from cover
void Remove(int v) {
    int i, e, n;
    int edge_count = vertex_degree[v];

    vertex_cover[v] = 0;
    c_size--;
    dscore[v] = -dscore[v]; // Flip from gain to loss
    valid_score[v] = 1000000;

    int last_remove_cand_v = remove_candidates[--remove_cand_size];
    int index = remove_candidates_index[v];
    remove_candidates[index] = last_remove_cand_v;
    remove_candidates_index[last_remove_cand_v] = index;
    remove_candidates_index[v] = 0;

    curr_weight -= vertex_cost[v];

    for (i = 0; i < edge_count; i++) {
        e = v_edges[v][i];
        n = v_adj[v][i];

        if (vertex_cover[n] == 0) {
            dscore[n] += edge_weight[e];
            Uncover(e);
        } else {
            dscore[n] -= edge_weight[e];
            valid_score[n] += vertex_cost[v];
        }
    }
}

// Adds vertex into vertex cover
void Add(int v) {
    int i, e, n;
    int edge_count = vertex_degree[v];
   
    vertex_cover[v] = 1; 
    c_size++;
    dscore[v] = -dscore[v];
    curr_weight += vertex_cost[v];
    valid_score[v] = -vertex_cost[v];
    
    remove_candidates[remove_cand_size] = v;
    remove_candidates_index[v] = remove_cand_size++;

    // Update scores
    for (i = 0; i < edge_count; i++) {
        e = v_edges[v][i];
        n = v_adj[v][i];

        if (vertex_cover[n] == 0) { // Edge previously not covered
            dscore[n] -= edge_weight[e];
            Cover(e);
            valid_score[v] += vertex_cost[n];
        } else {
            dscore[n] += edge_weight[e];
            valid_score[n] -= vertex_cost[v];

            if(valid_score[n] == -vertex_cost[n]) {
            	Remove(n);
			}
        }
    }
}

// Updates current best
void UpdateBestSolution() {
    int v;

    if (curr_weight < best_weight) {
        for (v = 1; v < N + 1; v++) {
            best_vertex_cover[v] = vertex_cover[v];
        }
        best_weight = curr_weight;
        best_cover_size = c_size;
        best_comp_time = TimeElapsed();
        best_step = step;
    }
}

// Constructs initial vertex cover
void ConstructVC() {
    int e;
    int v1, v2;
    double v1dd, v2dd;

    uncov_stack_fill_pointer = 0;
    c_size = 0;
    best_weight = (int)(~0U >> 1);
    curr_weight = 0;

    for (e = 0; e < E; e++) {
        v1 = edge[e].v1;
        v2 = edge[e].v2;

        if (vertex_cover[v1] == 0 && vertex_cover[v2] == 0) { // Edge not covered
            v1dd = (double)vertex_degree[v1] / (double)vertex_cost[v1];
            v2dd = (double)vertex_degree[v2] / (double)vertex_cost[v2];
            // Bigger ratio -> lower cost
            if (v1dd > v2dd) {
                vertex_cover[v1] = 1;
                curr_weight += vertex_cost[v1];
            } else {
                vertex_cover[v2] = 1;
                curr_weight += vertex_cost[v2];
            }
            c_size++;
        }
    }

    int *save_v_in_c = new int[N + 1]; // Save current best
    memcpy(save_v_in_c, vertex_cover, sizeof(int) * (N + 1));
    int save_c_size = c_size;
    llong save_weight = curr_weight;

    // BMS Algorithm
    int times = 50; // Number of iterations of random pick
    vector<int> blocks(E / 1024 + 1);
    for (int i = 0; i < E / 1024 + 1; i++) {
        blocks[i] = i;
    }

    // Run BMS algorithm to pick vertices
    while (times-- > 0) {
        fill_n(vertex_cover, N + 1, 0);
        c_size = 0;
        curr_weight = 0;
        shuffle(blocks.begin(), blocks.end(), default_random_engine(seed));

        for (auto &block : blocks) {
            auto begin = block * 1024;
            auto end = block == E / 1024 ? E : begin + 1024;
            int tmpsize = end - begin + 1;
            vector<int> idx(tmpsize);

            for (int i = begin; i < end; i++) {
                idx[i - begin] = i;
            }

            while (tmpsize > 0) {
                int i = rand() % tmpsize;
                Edge e = edge[idx[i]];
                v1 = e.v1;
                v2 = e.v2;

                // BMS: pick random vertex and exchange
                swap(idx[i], idx[--tmpsize]);
                if (vertex_cover[v1] == 0 && vertex_cover[v2] == 0) {
                    v1dd = (double)vertex_degree[v1] / (double)vertex_cost[v1];
                    v2dd = (double)vertex_degree[v2] / (double)vertex_cost[v2];
                    if (v1dd > v2dd) {
                        vertex_cover[v1] = 1;
                        curr_weight += vertex_cost[v1];
                    } else {
                        vertex_cover[v2] = 1;
                        curr_weight += vertex_cost[v2];
                    }

                    c_size++;
                }
            }
        }

        // Save current best
        if (curr_weight < save_weight) {
            save_weight = curr_weight;
            save_c_size = c_size;
            memcpy(save_v_in_c, vertex_cover, sizeof(int) * (N + 1));
        }
    }

    // Update back
    curr_weight = save_weight;
    c_size = save_c_size;
    memcpy(vertex_cover, save_v_in_c, sizeof(int) * (N + 1));
    delete[] save_v_in_c;

    for (e = 0; e < E; e++) {
        v1 = edge[e].v1;
        v2 = edge[e].v2;

        if (vertex_cover[v1] == 1 && vertex_cover[v2] == 0) {
            dscore[v1] -= edge_weight[e];
        } else if (vertex_cover[v2] == 1 && vertex_cover[v1] == 0) {
            dscore[v2] -= edge_weight[e];
        }
    }

    ResetRemoveCand();
    for (int v = 1; v < N + 1; v++) {
        if (vertex_cover[v] == 1 && dscore[v] == 0) {
            Remove(v);
        }
    }

    UpdateBestSolution();
}

// Checks if solution is valid
int CheckSolution() {
    int e, v;

    for (e = 0; e < E; ++e) {
        if (best_vertex_cover[edge[e].v1] != 1 && best_vertex_cover[edge[e].v2] != 1) {
            cout << ", uncovered edge " << e;
            return 0;
        }
    }

    return 1;
}

int UpdateTargetSize() {
    int v;
    int best_remove_v;
    double best_dscore;
    double dscore_v;

    best_remove_v = remove_candidates[0];
    best_dscore = (double)(vertex_cost[best_remove_v]) / (double)abs(dscore[best_remove_v]);

    if (dscore[best_remove_v] != 0) {
        for (int i = 1; i < remove_cand_size; i++) {
            v = remove_candidates[i];
            if (dscore[v] == 0) break;

            dscore_v = (double)(vertex_cost[v]) / (double)abs(dscore[v]);
            if (dscore_v > best_dscore){
                best_dscore = dscore_v;
                best_remove_v = v;
            }
        }
    }

    Remove(best_remove_v);
    return best_remove_v;
}

void ForgetEdgeWeights() {
    int v, e;
    int new_total_weitght = 0;

    for (v = 1; v < N + 1; v++) {
        dscore[v] = 0;
    }

    for (e = 0; e < E; e++) {
        edge_weight[e] = edge_weight[e] * p_scale;
        new_total_weitght += edge_weight[e];

        if (vertex_cover[edge[e].v1] + vertex_cover[edge[e].v2] == 0) {
            dscore[edge[e].v1] += edge_weight[e];
            dscore[edge[e].v2] += edge_weight[e];
        } else if (vertex_cover[edge[e].v1] + vertex_cover[edge[e].v2] == 1) {
            if (vertex_cover[edge[e].v1] == 1) {
                dscore[edge[e].v1] -= edge_weight[e];
            } else {
                dscore[edge[e].v2] -= edge_weight[e];
            }
        }
    }

    avg_weight = new_total_weitght / E;
}

void UpdateEdgeWeight() {
    int i, e;

    for (i = 0; i < uncov_stack_fill_pointer; i++) {
        e = uncov_stack[i];
        edge_weight[e] += 1;
        dscore[edge[e].v1] += 1;
        dscore[edge[e].v2] += 1;
    }

    delta_total_weight += uncov_stack_fill_pointer;

    if (mode / 2 == 1) {
        if (delta_total_weight >= E) {
            avg_weight += 1;
            delta_total_weight -= E;
        }

        if (avg_weight >= threshold) {
            ForgetEdgeWeights();
        }
    }
}

// Remove first vertex during dynamic choose -> Intensification
// Uses deterministic valid_score to determine pick
int ChooseRemoveV1() {
    int i, v;
    int remove_v = remove_candidates[0];
    int improvement_remove = valid_score[remove_v],improvement_v;

    for (i = 1; i < remove_cand_size; i++) {
    	v = remove_candidates[i];
    	improvement_v = valid_score[v];

        // Pick vertex with minimum valid score -> lower cost
    	if (improvement_v > improvement_remove) {
    		continue;
		}

    	if (improvement_v < improvement_remove) {
    		remove_v = v;
    		improvement_remove = improvement_v;
		} else if (time_stamp[v] < time_stamp[remove_v]) {
			remove_v = v;
    		improvement_remove = improvement_v;
		}
	}

	return remove_v;  
}

// Remove second vertex during dynamic choose -> Diversification
// Uses loss function to pick vertex
int ChooseRemoveV2() {
    int i, v;
    double dscore_v, dscore_remove_v;
    int remove_v = remove_candidates[rand() % remove_cand_size];
    int to_try = 50;

    for (i = 1; i < to_try; i++) {

        v = remove_candidates[rand() % remove_cand_size];
        // Using loss function
        dscore_v = (double)vertex_cost[v] / (double)abs(dscore[v]);
        dscore_remove_v = (double)vertex_cost[remove_v] / (double)abs(dscore[remove_v]);
        
        if (dscore_v < dscore_remove_v) {
            continue;
        }
        
        if (dscore_v > dscore_remove_v) {
            remove_v = v;
        } else if (time_stamp[v] < time_stamp[remove_v]) {
            remove_v = v;
        }
    }

    return remove_v;
}

// Picks vertex to cover uncovered edge
int ChooseAddV(int update_v, int remove_v = 0, int remove_v2 = 0) {
    int i, v;
    int add_v = 0;
    double improvement = 0.0;
    double dscore_v;

    int tmp_degree = vertex_degree[update_v];
    int *adjp = v_adj[update_v];

    for (i = 0; i < tmp_degree; i++) {

        v = adjp[i];
        if (vertex_cover[v] == 1) { // Edge covered
            continue;
        }

        dscore_v = (double)dscore[v] / (double)(vertex_cost[v]);
        if (dscore_v > improvement) {
                improvement = dscore_v;
                add_v = v;
        } else if (dscore_v == improvement) {
            if (time_stamp[v] < time_stamp[add_v]) {
                add_v = v;
            }
        }
    }

    // Try to pick better update from removed v1
    if (remove_v != 0) {
        tmp_degree = vertex_degree[remove_v];
        adjp = v_adj[remove_v];
        for (i = 0; i < tmp_degree; i++) {
            v = adjp[i];
            if (vertex_cover[v] == 1) {
                continue;
            }

            dscore_v = (double)dscore[v] / (double)(vertex_cost[v]);
            if (dscore_v > improvement) {
                improvement = dscore_v;
                add_v = v;
            } else if (dscore_v == improvement) {
                if (time_stamp[v] < time_stamp[add_v]) {
                    add_v = v;
                }
            }
        }
    }

    // Try to pick better update from removed v2
    if (remove_v2 != 0) {
        tmp_degree = vertex_degree[remove_v2];
        adjp = v_adj[remove_v2];
        for (i = 0; i < tmp_degree; i++) {
            v = adjp[i];
            if (vertex_cover[v] == 1) {
                continue;
            }
            dscore_v = (double)dscore[v] / (double)(vertex_cost[v]);
            if (dscore_v > improvement) {
                improvement = dscore_v;
                add_v = v;
            } else if (dscore_v == improvement) {
                if (time_stamp[v] < time_stamp[add_v]) {
                    add_v = v;
                }
            }
        }
    }

    return add_v;
}

// Performs local search on current VC to update weight
void LocalSearch() {

    int add_v, remove_v = 0, update_v = 0,remove_v2 = 0;
    int noimprovement = 0, dyn_count = 0,temp_weight;
    step = 1;
    try_step = 100; // NOTE: Can be tuned
    int remove_degree = 0;

    avg_weight = 1;
    delta_total_weight = 0;
    p_scale = 0.3;
    threshold = (int)(0.5 * N);

    // Dynamic choose algorithm
    while (true) {
        temp_weight = curr_weight;		
        UpdateBestSolution();      
        update_v = UpdateTargetSize();       
        time_stamp[update_v] = step;
        if (step % try_step == 0) {
            if (TimeElapsed() >= cutoff_time) {
                return;
            }
        }
 
        if (noimprovement < noImproveMax) {
            remove_v = ChooseRemoveV1();
            Remove(remove_v);		
            time_stamp[remove_v] = step;

        } else {
            if (noimprovement == noImproveMax) {
                dyn_count = 2;
            } 
            
            if (dyn_count == 1) {
                noimprovement = 0;
            }

            remove_v = ChooseRemoveV2();
            Remove(remove_v);		
            time_stamp[remove_v] = step;
            dyn_count--;
        }

        remove_degree = vertex_degree[update_v] + vertex_degree[remove_v];
        // If v1 and v2 total degree < 2 * average degree, increase search space
        // By removing one more vertex
        // NOTE: Can be tuned, but not recommended
        if (remove_degree < 2 * E / N) {   
            remove_v2 = ChooseRemoveV2();
            Remove(remove_v2);
            time_stamp[remove_v2] = step;
        }   

        while (uncov_stack_fill_pointer > 0) {
            add_v = ChooseAddV(update_v, remove_v, remove_v2);
            Add(add_v);            
            UpdateEdgeWeight();
            time_stamp[add_v] = step;
        }

        step++;
        remove_v2 = 0;  

        if (curr_weight >= temp_weight) {
            noimprovement += 1;
        }

        remove_degree = 0; 
    }   
}

int main(void) {
    // Learning Parameters -> Tune these parameters
    uint seed = 0; // Random seed
    cutoff_time = 1.95; // Set cutoff time
    noImproveMax = 5;

    srand(seed);

    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    start = chrono::steady_clock::now();

    // Build original graph
    BuildInstance();

    // Construct initial vertex cover
    ConstructVC();
    // Run SLS
    LocalSearch();

    if (CheckSolution() == 1) {
        cout << best_weight << endl;
        for (int i = 1; i <= N; i++) {
            if (best_vertex_cover[i] == 1) {
                printf("%d ", i - 1);
            }
        }
        printf("\n");
    }

    return 0;
}
