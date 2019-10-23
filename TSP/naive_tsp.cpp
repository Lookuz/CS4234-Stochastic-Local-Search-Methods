#include <bits/stdc++.h>
using namespace std;

typedef pair<double, double> Point;

class GreedyTour {
private:
	int n;

	double distBetweenTwoPoints(Point a, Point b) {
		return sqrt(pow(a.first - b.first, 2) + pow(a.second - b.second, 2));
	}

public:
	vector<Point> points;

	double dist(int a, int b) {
		return distBetweenTwoPoints(points[a], points[b]);
	}

	vector<int> tour() {
		vector<int> tour(n, -1);
		vector<bool> used(n , false);
		int best;

		tour[0] = 0;
		used[0] = true;
		for (int i=1; i<n; ++i) {
			best = -1;
			for (int j=0; j<n; ++j) {
				if (!used[j] && (best == -1 || dist(tour[i-1], j) < dist(tour[i-1], best)))
					best = j;
			}
			tour[i] = best;
			used[best] = true;
		}
		return tour;
	}


	GreedyTour(int n) {
		points.reserve(n);
		this->n = n;
		double x, y;
		for (int i=0; i<n; ++i) {
			cin >> x >> y;
			points[i] = {x, y};
		}
	}
};


int main() {
	int n;
	cin >> n;
	GreedyTour gt(n);
	vector<int> t = gt.tour();
	for (int i=0; i<n; ++i) {
		cout << t[i] << endl;
	}
}