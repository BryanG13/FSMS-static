//#include <ilcplex/ilocplex.h>
//#include "Datagen.h"
#include <string>
#include <fstream>
#include <iostream>
#include <stdlib.h> 
#include <random>
#include <time.h>
#include <omp.h>
#include <stdio.h>
#ifdef _DEBUG
#define _CRTDBG_MAP_ALLOC
#define _CRTDBG_MAP_ALLOC_NEW
#include <crtdbg.h>
#include <assert.h>
#endif


using namespace std;

//void Gen(int N, int M, int C);

inline int iMin(double bd[], int B) {
	double imin = INT32_MAX;
	int ind = -1;
	for (int i = 0; i < B; i++) {
		if (bd[i] < imin) {
			imin = bd[i];
			ind = i;
		}
	}
	return ind;
}
//second smallest of a set
inline double iMin2(double bd[], int B) {
	double first = INT_MAX, second = INT_MAX;
	for (int i = 0; i < B; i++) {
		/* If current element is smaller than first
		then update both first and second */
		if (bd[i] <= first) {
			second = first;
			first = bd[i];
		}

		/* If bd[i] is in between first and second
		then update second */
		else if (bd[i] < second && bd[i] != first) {
			second = bd[i];
		}
	}
	if (second == INT_MAX) return 0;
	else return second;
}

inline int partition(int index[], double dist[], int low, int high) {
	double pivot = dist[high]; // pivot  
	int i = (low - 1); // Index of smaller element 
	int t;
	double t0;

	for (int j = low; j <= high - 1; j++) {
		// If current element is smaller than the pivot  
		if (dist[j] < pivot) {
			i++; // increment index of smaller element  
			t = index[j];
			index[j] = index[i];
			index[i] = t;

			t0 = dist[j];
			dist[j] = dist[i];
			dist[i] = t0;

		}
	}
	t = index[high];
	index[high] = index[i + 1];
	index[i + 1] = t;

	t0 = dist[high];
	dist[high] = dist[i + 1];
	dist[i + 1] = t0;

	return (i + 1);
}

inline void quickSort(int index[], double dist[], int low, int high) {
	if (low < high) {
		/* pi is partitioning index, arr[p] is now
		at right place */
		int pi = partition(index, dist, low, high);

		// Separately sort elements before  
		// partition and after partition  
		quickSort(index, dist, low, pi - 1);
		quickSort(index, dist, pi + 1, high);
	}
}

inline int Qpartition(vector<double>& dist, int low, int high) {
	double pivot = dist[high]; // pivot  
	int i = (low - 1); // Index of smaller element  
	double t0;

	for (int j = low; j <= high - 1; j++) {
		// If current element is smaller than the pivot  
		if (dist[j] < pivot) {
			i++; // increment index of smaller element  
			t0 = dist[j];
			dist[j] = dist[i];
			dist[i] = t0;

		}
	}

	t0 = dist[high];
	dist[high] = dist[i + 1];
	dist[i + 1] = t0;

	return (i + 1);
}

inline void QSort(vector<double>& dist, int low, int high) {
	if (low < high) {
		/* pi is partitioning index, arr[p] is now
		at right place */
		int pi = Qpartition(dist, low, high);

		// Separately sort elements before  
		// partition and after partition  
		QSort(dist, low, pi - 1);
		QSort(dist, pi + 1, high);
	}
}

inline double findMedian(vector<double>& a) {
	// First we sort the array 
	int n = a.size();
	QSort(a, 0, n - 1);

	// check for even case 
	if (n % 2 != 0)
		return (double)a[n / 2];

	return (double)(a[(n - 1) / 2] + a[n / 2]) / 2.0;
}

inline int bestStop(vector<double>& timetable, vector<int>& route, double** traveltimes, double** traveltimep, int** closestPS,
	int p, int N, int dw, int* best_route, int M, int S, int bd, double* freqN, int xt, int best_stop,
	double arrprev, double arrnext, int d_tl, int d_te, int yk[][3], double* arrivals, int R1, int R2, int bus, int trip, double bd2, double fpm) {
	bool in = false, feas = true, inroute;
	int i, j, newj, cc, first, second, current, mand, indexr, indexr0, best_index;
	double sum, ener, ogtend;
	double ttemp, diffT = arrnext - arrprev, Arr, Arrb, D_temp = arrnext, D_sol, tArrb, startb, mF;
	vector<double> times, ttimetable;
	vector<int> troute;
	double UB;
	newj = closestPS[p][0];
	cc = 0;
	ener = INT64_MAX;
	sum = 0;
	first = 0, second = 0;
	indexr = -2;

	int nS = timetable.size();
	double* oldtt = new double[nS];// make copy of time table
	double* oldR = new double[nS];// make copy of route
	for (i = 0; i < nS; i++) {
		oldtt[i] = timetable[i];
		oldR[i] = route[i];
	}
	//cout << "p: " << p << " dat: " << arrnext / 60 << endl;
	while (traveltimep[p][closestPS[p][cc]] < dw) {
		//cout << cc << endl;
		sum = traveltimep[p][closestPS[p][cc]];
		mand = int((closestPS[p][cc] - N) / M);
		//cout << "mandatory : " << mand << endl;

		auto itr = find(best_route, best_route + S, closestPS[p][cc]);
		current = distance(best_route, itr);
		// find best place to insert cc
		in = false;
		int routeS = route.size();
		for (j = 0; j < routeS; j++) {
			if (route[j] == closestPS[p][cc]) {
				in = true;
				indexr = j;
				break;
			}
			else if (route[j] == mand || route[j] == mand + 1 || (route[j] >= N + M * mand && route[j] < N + M * (mand + 1))) {
				auto itr = find(best_route, best_route + S, route[j]);
				ttemp = distance(best_route, itr);
				//cout << ttemp << endl;
				if (ttemp > current) {
					second = route[j];
					indexr = j;
					break;
				}
				first = route[j];
				indexr0 = j;
			}
		}

		times.clear();
		times.push_back(arrnext);
		for (i = 0; i < R1; i++) {
			if (yk[i][0] == bus && yk[i][1] == trip)times.push_back(arrivals[i]);
		}
		if (times.size() != 1) {
			Arrb = findMedian(times);
			Arr = std::max(times.back() - d_tl, times[0]);
			UB = std::min(times[0] + d_te, times.back());
		}
		else {
			Arrb = arrnext;
			//cout << "first \n";
			Arr = arrnext - d_tl;
			UB = arrnext + d_te;
		}
		if (Arrb > UB)Arrb = UB;
		else if (Arrb < Arr)Arrb = Arr;
		startb = bd;
		tArrb = Arrb;
		//for (i = 0; i < times.size(); i++) {
			//cout << int(times[i] / 60 )<< "  ";
		//}
		//cout << endl;
		if (!in) {
			//cout << " stop: " << closestPS[p][cc] << " NOT in yet ---> UB: " <<UB/60 << " LB: "<< Arr/60 << endl;
			sum += traveltimes[first][closestPS[p][cc]] + traveltimes[closestPS[p][cc]][second] - traveltimes[first][second];
			for (i = 0; i < indexr0; i++) {
				startb += traveltimes[route[i]][route[i + 1]];
			}
			startb += (traveltimes[first][closestPS[p][cc]] + traveltimes[closestPS[p][cc]][second]);
			routeS = route.size() - 2;
			for (i = indexr; i < route.size() - 2; i++) {
				startb += traveltimes[route[i]][route[i + 1]];
			}

			ttimetable.clear();
			troute.clear();
			routeS = route.size() - 1;
			for (i = route.size() - 1; i > indexr; i--) {
				troute.insert(troute.begin(), route[i]);
				ttimetable.insert(ttimetable.begin(), tArrb);
				tArrb -= traveltimes[route[i]][route[i - 1]];
			}
			ttimetable.insert(ttimetable.begin(), tArrb);
			troute.insert(troute.begin(), route[indexr]);

			tArrb -= traveltimes[closestPS[p][cc]][second];
			ttimetable.insert(ttimetable.begin(), tArrb);
			troute.insert(troute.begin(), closestPS[p][cc]);

			tArrb -= traveltimes[closestPS[p][cc]][first];
			for (i = indexr0; i > 0; i--) {
				troute.insert(troute.begin(), route[i]);
				ttimetable.insert(ttimetable.begin(), tArrb);
				tArrb -= traveltimes[route[i]][route[i - 1]];
			}
			troute.insert(troute.begin(), route[0]);
			ttimetable.insert(ttimetable.begin(), tArrb);

		}
		else {//if stop is part of the route already, just check xt constraint
			//cout << " stop: " << closestPS[p][cc] << " IN already" << endl;
			routeS = route.size() - 2;
			for (i = 0; i < routeS; i++) {
				startb += traveltimes[route[i]][route[i + 1]];
			}
			ttimetable.clear();
			routeS = route.size() - 1;
			for (i = routeS; i >= 1; i--) {
				ttimetable.insert(ttimetable.begin(), tArrb);
				troute.insert(troute.begin(), route[i]);
				tArrb -= traveltimes[route[i]][route[i - 1]];
			}
			ttimetable.insert(ttimetable.begin(), tArrb);
			troute.insert(troute.begin(), route[0]);
		}
		if (startb > UB) {
			//cout << " route too long for p:" << p << endl;
			sum = INT32_MAX;
		}
		else {
			//cout << " poss dept at m0 " << ttimetable[0] / 60 << " poss arr: " << ttimetable.back()/60  << endl;
			//cout << "FreqN\n";
			//for (i = 0; i < N; i++) {
				//cout << int(freqN[i] / 60) << "  ";
			//}
			//cout << endl;
			//Check if infeasible;
			mF = -1;
			//cout << " start " << timetable[0]/60 << endl;
			int tttS = ttimetable.size();
			for (i = 0; i < tttS; i++) {
				if (troute[i]<N && ttimetable[i] - freqN[troute[i]]> mF && freqN[troute[i]] > 0)mF = ttimetable[i] - freqN[troute[i]];
			}
			//cout << "mF = " << mF / 60  << " xt: "  <<xt/60 << " d_tl: " << d_tl/60<<  endl;

			if (mF - xt > d_tl * fpm || ttimetable.back() - (mF - xt) < Arr) {
				//cout << " p: " << p << " ";
				//cout << " INfeasible for times: dif_mF=" << mF / 60 - xt / 60 << endl;
				//cout << " trip: " << trip << " bd: " << bd / 60 << " LB: " << Arr / 60 << " act arr: " << ttimetable.back() / 60 << endl;
				sum = INT32_MAX;
			}
			else if (mF - xt > 0) {
				//cout << " adjust\n";
				tttS = ttimetable.size();
				for (i = 0; i < tttS; i++) {
					ttimetable[i] -= (mF - xt);
				}
				sum += (mF - xt) * times.size();
			}

			if (ttimetable[0] < bd && trip>0) {
				//cout << "optimal not possible -> ASAP \n";
				//sum = INT32_MAX;
				//*
				ogtend = ttimetable.back();
				ttimetable.clear();
				startb = bd;
				ttimetable.push_back(startb);
				int trS = troute.size();
				for (i = 1; i < trS; i++) {
					startb += traveltimes[troute[i]][troute[i - 1]];
					ttimetable.push_back(startb);
				}
				if (abs(ogtend - ttimetable.back()) > d_tl * fpm || startb > UB || startb < Arr) {
					sum = INT32_MAX;
				}
				else sum += (abs(ogtend - ttimetable.back()) * times.size());
				//*/
			}
			//sum += (abs(Arrb - ttimetable.back()));
			D_temp = ttimetable.back();
			if (sum != INT32_MAX)sum += (abs(D_temp - arrnext));
		}

		if (indexr == -2) cout << "que?" << endl;
		if (ener > sum) {
			ener = sum;
			best_index = indexr;
			newj = closestPS[p][cc];
			inroute = in;
			D_sol = D_temp;
		}
		cc++;
	}
	//if no bus stop is avaibalbe
	if (ener == INT32_MAX) {
		//cout << "----------------------------------- no bus stop available \n";
		delete[] oldtt;
		delete[] oldR;
		return -1;
	}
	//add to route if not part of the route yet (if bestindex is not -1)
	if (!inroute) {
		//cout << " < -------------------   Stop " << newj << " not in route yet\n";
		route.insert(route.begin() + best_index, newj);
		//update timetable
		//cout <<" departure time " << D_sol/60 << endl;
		timetable.push_back(D_sol);
		//cout << route[best_index - 1] << "->" << newj << "\nloop: " <<endl;
		int tS = timetable.size() - 2;
		for (i = tS; i >= 0; i--) {
			timetable[i] = timetable[i + 1] - traveltimes[route[i + 1]][route[i]];
			//cout << route[i - 1] << "->" << route[i] << endl;
		}
	}
	else {
		timetable[timetable.size() - 1] = D_sol;
		//cout << route[best_index - 1] << "->" << newj << "\nloop: " <<endl;
		int tS = timetable.size() - 2;
		for (i = tS; i >= 0; i--) {
			timetable[i] = timetable[i + 1] - traveltimes[route[i + 1]][route[i]];
			//cout << route[i - 1] << "->" << route[i] << endl;
		}
	}
	/*
	cout << "Passenger: " << p << " Stop: " << newj << " Dept: " << int(D_sol / 60) <<" edt: "<<int(deptnext/60)<< endl;
	cout << "current timetable: \n";
	for (i = 0; i < timetable.size(); i++) {
		cout << int(timetable[i] / 60) << " ";
	}
	cout << endl;
	//*/
	//if this makes the next bus infeasible for freq constraint
	if (timetable[0] + xt < bd2) {
		timetable.clear();
		route.clear();
		for (i = 0; i < nS; i++) {
			timetable.push_back(oldtt[i]);
			route.push_back(oldR[i]);
		}
		delete[] oldtt;
		delete[] oldR;
		//cout << "----------------------------- BAD\nEarliest departure time to satisfy freqN: " << int(timetable[0] + xt) / 60 << endl;
		//cout << "Earliest departure time of of this bus is: " << int(bd2 / 60) << endl;
		return -1;
	}
	//cout << " +++++++++++++++++++++++++++++++++++++ ADDED on stop " << newj << " new arr: " << timetable.back()/60<< " \n";
	delete[] oldtt;
	delete[] oldR;
	return newj;
}

inline int bestStop2(vector<double>& timetable, vector<int>& route, double** traveltimes, double** traveltimep, int** closestPS,
	int p, int N, int dw, int* best_route, int M, int S, int bd, double* freqN, double* newfreqN, int xt, int best_stop,
	double deptprev, double deptnext, int d_tl, int d_te, int yk[][3], double* departures, int R1, int R2, int bus, int trip, double bd2, double fpm) {
	bool in = false, feas = true, found, inroute;
	int i, j, newj, cc, first, second, current, mand, indexr, indexr0, best_index, prev, i_m;
	double sum, ener, tsp, temp;
	double ttemp, threshold, diffT = deptnext - deptprev, Arr, Arrb, D_temp = deptnext, D_sol;
	vector<double> times;
	double t_prev = 0, UB;
	newj = closestPS[p][0];
	cc = 0;
	ener = INT64_MAX;
	sum = 0;
	first = 0, second = 0;
	indexr = -2;
	//cout << "p: " << p << endl;
	int nS = timetable.size();
	double* oldtt = new double[nS];// make copy of time table
	double* oldR = new double[nS];// make copy of route
	for (i = 0; i < nS; i++) {
		oldtt[i] = timetable[i];
		oldR[i] = route[i];
	}
	while (traveltimep[p][closestPS[p][cc]] < dw) {
		//cout << cc << endl;
		sum = traveltimep[p][closestPS[p][cc]];
		mand = int((closestPS[p][cc] - N) / M);
		//cout << "------- stop: " << closestPS[p][cc] << endl;
		//cout << "mandatory : " << mand << endl;

		auto itr = find(best_route, best_route + S, closestPS[p][cc]);
		current = distance(best_route, itr);
		// find best place to insert cc
		in = false;
		int rS = route.size();
		for (j = 0; j < rS; j++) {
			if (route[j] == closestPS[p][cc]) {
				in = true;
				indexr = j;
				break;
			}
			else if (route[j] == mand || route[j] == mand + 1 || (route[j] >= N + M * mand && route[j] < N + M * (mand + 1))) {
				auto itr = find(best_route, best_route + S, route[j]);
				ttemp = distance(best_route, itr);
				//cout << ttemp << endl;
				if (ttemp > current) {
					second = route[j];
					indexr = j;
					break;
				}
				first = route[j];
				indexr0 = j;
			}
		}
		//if cc is not part of the route add travel times
		auto itr2 = find(best_route, best_route + S, best_stop);
		prev = distance(best_route, itr2);//index of previous bus stop
		if (current < prev && diffT != 0) {
			sum = INT32_MAX;
		}
		else {
			if (!in) {
				t_prev = timetable[indexr0] + traveltimes[first][closestPS[p][cc]];
				if (t_prev > deptnext + d_te) sum = INT32_MAX;
				else {
					//cout << "earliest dept: " << (deptnext - d_tl)/60 << "earliest current arr: " << t_prev/60<<" stop: " << closestPS[p][cc]<< endl;
					temp = traveltimes[first][closestPS[p][cc]] + traveltimes[closestPS[p][cc]][second] - traveltimes[first][second];
					//cout << " extra travel time: " << temp / 60 << endl;
					feas = true;
					tsp = deptnext - d_tl - t_prev;//difference in time of arrival and desired time of departure at stop cc
					if (tsp < 0)tsp = 0;//if u arrive after edt -> no penalty
					i_m = -1;
					D_temp = -1;
					for (i = 0; i < N; i++) {
						if (i >= mand + 1) {
							if (int(newfreqN[i] + tsp + temp - freqN[i]) > xt && freqN[i] > 0) {
								feas = false;
								break;
							}
							//calculate max (only if feasible)
							if (newfreqN[i] + tsp + temp - freqN[i] > D_temp && freqN[i] > 0) {
								D_temp = newfreqN[i] + tsp + temp - freqN[i];
								i_m = i;
							}
						}
						else {
							if (int(newfreqN[i] + tsp - freqN[i]) > xt && freqN[i] > 0) {
								feas = false;
								break;
							}
							//calculate max (only if feasible)
							if (newfreqN[i] + tsp - freqN[i] > D_temp && freqN[i] > 0) {
								D_temp = newfreqN[i] + tsp - freqN[i];
								i_m = i;
							}
						}
					}
					if (feas) {
						sum += temp;
						if (diffT != 0) {
							//cout << "/////////////////////// D_temp=" << (D_temp) / 60 << endl;
							// time to go from prev to next stop on a full route 
							threshold = 0;
							found = false;
							for (i = 0; i < indexr - 1; i++) {
								if (found || route[i] == best_stop) {
									found = true;
									threshold += traveltimes[route[i]][route[i + 1]];
								}
							}
							threshold += traveltimes[route[i]][closestPS[p][cc]];
							sum += (abs(threshold - diffT));
						}
						if (diffT == 0) {
							//cout <<  "/////////////////////// D_temp=" << (D_temp) / 60 << endl;
							//D_temp = deptnext - (xt - D_temp);
							if (D_temp > 0) {
								double newF = deptnext;
								double coR = -1;
								newF -= traveltimes[first][closestPS[p][cc]];
								if (first < N) {
									if (newF - freqN[first] > coR)coR = newF - freqN[first];
								}
								for (i = indexr0; i > 0; i--) {
									newF -= traveltimes[route[i]][route[i - 1]];
									if (route[i - 1] < N) {
										if (newF - freqN[route[i - 1]] > coR)coR = newF - freqN[route[i - 1]];
									}
								}
								if (coR > xt) {
									newF = deptnext - (coR - xt);
									newF += traveltimes[second][closestPS[p][cc]];
									if (second < N) {
										if (newF - freqN[second] > xt)feas = false;
									}
									rS = route.size() - 1;
									for (i = indexr; i < rS; i++) {
										newF -= traveltimes[route[i]][route[i + 1]];
										if (route[i + 1] < N) {
											if (newF - freqN[route[i + 1]] > xt) {
												feas = false;
												break;
											}
										}
									}
									if (feas && coR - xt <= d_tl * fpm) D_temp = deptnext - (coR - xt);
									else sum = INT32_MAX;
								}
								else D_temp = deptnext;
								//cout << "/////////////////////// D_temp=" << (D_temp) / 60 << endl;
								//cout << "      CoR=" << (coR) / 60 << endl;
							}
							else {
								D_temp = deptnext;
								//cout << "NEG:://///////////////////// D_temp=" << (D_temp) / 60 << endl;
							}

						}
						else {
							if (D_temp > 0) {
								D_temp = xt - D_temp;
								D_temp = std::max(deptnext - d_tl + D_temp, t_prev);
							}
							else D_temp = deptnext;
						}

						if (D_temp > t_prev && diffT != 0) sum = INT32_MAX;
					}
					else sum = INT32_MAX;
				}

			}
			else {//if stop is part of the route already, just check xt constraint
				times.clear();
				times.push_back(deptnext);
				for (i = 0; i < R2; i++) {
					if (yk[i + R1][2] == closestPS[p][cc] && yk[i + R1][0] == bus && yk[i + R1][1] == trip)times.push_back(departures[i]);
				}
				if (times.size() != 1) {
					Arrb = findMedian(times);
					Arr = std::max(times.back() - d_tl, times[0]);
					UB = std::min(times[0] + d_te, times.back());
				}
				else {
					Arrb = deptnext;
					//cout << "first \n";
					Arr = deptnext - d_tl;
					UB = deptnext + d_te;
				}
				if (Arrb > UB)Arrb = UB;
				if (Arrb < Arr)Arrb = Arr;
				t_prev = timetable[indexr];
				if (t_prev > UB) sum = INT32_MAX;
				else {
					//cout << "earliest dept: " << (Arr) / 60 << " current arr: " << t_prev / 60 << " stop: " << closestPS[p][cc];
					tsp = Arr - t_prev;//difference in time of arrival and desired time of departure at stop cc
					if (tsp < 0)tsp = 0;//if u arrive after edt -> no penalty
					feas = true;
					i_m = -1;
					D_temp = -1;
					for (i = 0; i < N; i++) {
						if (int(newfreqN[i] + tsp - freqN[i]) > xt && freqN[i] > 0) {
							feas = false;
							break;
						}
						//calculate max (only if feasible)
						if (newfreqN[i] + tsp - freqN[i] > D_temp && freqN[i] > 0) {
							D_temp = newfreqN[i] + tsp - freqN[i];
							i_m = i;
						}
					}
					//cout << " biggest diff: " << D_temp/60 << endl;
					if (!feas) sum = INT32_MAX;
					else {
						//cout << "D_temp: " << D_temp/60 << endl;
						if (diffT == 0) {
							if (D_temp > 0) {
								//cout << "inroute -- >/////////////////////// D_temp=" << (D_temp) / 60 << endl;
								//D_temp = deptnext;

								double newF = deptnext;
								double coR = -1;
								if (closestPS[p][cc] < N) {
									if (newF - freqN[closestPS[p][cc]] > coR)coR = newF - freqN[closestPS[p][cc]];
								}
								for (i = indexr; i > 0; i--) {
									newF -= traveltimes[route[i]][route[i - 1]];
									if (route[i - 1] < N) {
										if (newF - freqN[route[i - 1]] > coR)coR = newF - freqN[route[i - 1]];
									}
								}
								if (coR > xt) {
									newF = deptnext - (coR - xt);
									rS = route.size() - 1;
									for (i = indexr; i < rS; i++) {
										newF -= traveltimes[route[i]][route[i + 1]];
										if (route[i + 1] < N) {
											if (newF - freqN[route[i + 1]] > xt) {
												feas = false;
												break;
											}
										}
									}
									if (feas && coR - xt <= d_tl * fpm) D_temp = deptnext - (coR - xt);
									else sum = INT32_MAX;
								}
								else D_temp = deptnext;
							}
							else D_temp = deptnext;
						}
						else {
							if (D_temp > 0) {
								D_temp = xt - D_temp;
								//cout << "D_temp: " << D_temp/60 << endl;
								D_temp = std::max(Arr + D_temp, t_prev);
							}
							else D_temp = Arrb;
						}
						if (D_temp > t_prev && diffT != 0) sum = INT32_MAX;
					}
				}

			}
		}
		if (sum < INT32_MAX) {
			double startb = D_temp;
			if (!in) {
				//cout << "NOT IN --> Check --> indexr0: " << indexr0 << " first: " << first <<endl;
				startb -= traveltimes[closestPS[p][cc]][first];
				for (i = indexr0; i > 0; i--) {
					startb -= traveltimes[route[i]][route[i - 1]];
				}
			}
			else {
				//cout << "IN --> Check --> indexr: " << indexr << endl;
				for (i = indexr; i > 0; i--) {
					startb -= traveltimes[route[i]][route[i - 1]];
				}
			}
			//cout << "Check 2\n";
			if (startb < bd && trip>0) {
				sum = INT32_MAX;
			}
		}

		if (indexr == -2) cout << "que?" << endl;
		if (ener > sum) {
			ener = sum;
			best_index = indexr;
			newj = closestPS[p][cc];
			inroute = in;
			D_sol = D_temp;
		}
		cc++;
	}
	//if no bus stop is avaibalbe
	if (ener == INT32_MAX) {
		//cout << " no bus stop available \n";
		delete[] oldtt;
		delete[] oldR;
		return -1;
	}
	//add to route if not part of the route yet (if bestindex is not -1)
	if (!inroute) {
		//cout << " < -------------------   Stop " << newj << " not in route yet\n";
		route.insert(route.begin() + best_index, newj);
		//update timetable
		//cout <<" departure time " << D_sol/60 << endl;
		timetable.insert(timetable.begin() + best_index, D_sol);
		//cout << route[best_index - 1] << "->" << newj << "\nloop: " <<endl;
		int tS = timetable.size();
		for (i = best_index + 1; i < tS; i++) {
			timetable[i] = timetable[i - 1] + traveltimes[route[i - 1]][route[i]];
			//cout << route[i - 1] << "->" << route[i] << endl;
		}
		if (diffT == 0) {
			for (i = best_index - 1; i >= 0; i--) {
				timetable[i] = timetable[i + 1] - traveltimes[route[i + 1]][route[i]];
				//cout << route[i - 1] << "->" << route[i] << endl;
			}
		}
	}
	else {
		//cout << " Stop " << route[best_index] << " already in route\t";
		//update timetable
		//cout << D_sol/60 << endl;
		//cout << " departure time " << D_sol / 60 << endl;
		timetable[best_index] = D_sol;
		int tS = timetable.size();
		for (i = best_index + 1; i < tS; i++) {
			timetable[i] = timetable[i - 1] + traveltimes[route[i - 1]][route[i]];
		}
		if (diffT == 0) {
			for (i = best_index - 1; i >= 0; i--) {
				timetable[i] = timetable[i + 1] - traveltimes[route[i + 1]][route[i]];
				//cout << route[i - 1] << "->" << route[i] << endl;
			}
		}
	}
	/*
	cout << "Passenger: " << p << " Stop: " << newj << " Dept: " << int(D_sol / 60) <<" edt: "<<int(deptnext/60)<< endl;
	cout << "current timetable: \n";
	for (i = 0; i < timetable.size(); i++) {
		cout << int(timetable[i] / 60) << " ";
	}
	cout << endl;
	//*/
	//if this makes the next bus infeasible for freq constraint
	if (timetable[0] + xt < bd2) {
		timetable.clear();
		route.clear();
		for (i = 0; i < nS; i++) {
			timetable.push_back(oldtt[i]);
			route.push_back(oldR[i]);
		}
		delete[] oldtt;
		delete[] oldR;
		//cout << "----------------------------- BAD\nEarliest departure time to satisfy freqN: " << int(timetable[0] + xt) / 60 << endl;
		//cout << "Earliest departure time of of this bus is: " << int(bd2 / 60) << endl;
		return -1;
	}

	delete[] oldtt;
	delete[] oldR;
	return newj;
}

int main() {
	int instance = -300;

	const int nRUN = 3000000;
	int nIt = 5, it = 0;
	//int i, j, k, b, t, p, l, s;
	//double b_next;
	ofstream inst("data/input/Instance_H_" + to_string(instance) + ".txt");
	inst << "---------- Weight factors of the objective function -------- " << endl << endl;
	//WEIGHT FACTORS--------------------------------------------------------------------------
	float c1 = 0.33f;
	inst << "c1: " << c1 << " \t (For travel-time of the buses)" << endl;
	float c2 = 0.33f;
	inst << "c2: " << c2 << " \t (For walking time of the passengers)" << endl;
	float c3 = 1 - c1 - c2;
	inst << "c3: " << c3 << " \t (For the absolute difference in desired arrival time and actual arrival time of the passengers)" << endl;
	inst << endl;
	inst << "---------------------- Parameters -------------------------- " << endl << endl;
	//Define parameters-----------------------------------------------------------------------
	const int B = 12; // number of buses available
	inst << "Number of buses: " << B << endl;
	const int N = 6; // number of mandatory stations
	inst << "Number of mandatory bus stops: " << N << endl;
	const int M = 5; // number of stations in cluster
	inst << "Number optional bus stops per cluster: " << M << " \n --> One cluster between each mandatory stop: " + to_string((N - 1) * M) + " optional stops in total" << endl;
	const int S = (N - 1) * M + N; // amount of Stations
	inst << "Total number of bus stops: " << S << endl;
	const int R = 48; // number of passenger requests
	const int R1 = int(R / 2), R2 = R - R1;
	inst << "Number of passenger requests: " << R << endl;
	//double pm1 = 0, pm2 = 0, pm3 = 1, fpm = 0;

	int C_OG = 20;
	int C = C_OG; // Bus capcity
	inst << "Bus capacity: " << C_OG << " passengers" << endl;
	const int TS = 3600 * 4.2;
	inst << "Planning horizon: " << TS << "s" << endl;
	int OGxt = 60 * 20;
	inst << "Minimum time between two buses departing from a mandatory stop: " << OGxt << "s" << endl;
	const float pspeed = 1.0f; // passengers speed in meter per scond
	const float bspeed = 40.0f / 3.6f; //bus speed in m/s
	const int dw = 20 * 60; // threshold of individual walking time in sec
	inst << "Maximum walking time for any passenger: " << dw << " seconds" << endl;
	const int d_dl = 15 * 60;
	const int d_de = 5 * 60;
	const int d_ae = 15 * 60;
	const int d_al = 5 * 60;
	inst << "Maximum amount of time a passenger can arrive too early: " << d_ae << " seconds" << endl;
	inst << "Maximum amount of time a passenger can arrive too late: " << d_al << " seconds" << endl;
	inst << "Maximum amount of time a passenger can depart too early: " << d_de << " seconds" << endl;
	inst << "Maximum amount of time a passenger can depart too late: " << d_dl << " seconds" << endl;
	//const int M0 = 10000; // Big M 

	// Read in locations 
	double** passengers = new double* [R];
	for (int i = 0; i < R; i++) {
		passengers[i] = new double[2];
	}
	ifstream filep("data/input/passengers" + to_string(R) + ".txt");
	int i0 = 0;
	while (i0 < R) {
		filep >> passengers[i0][0] >> passengers[i0][1]; // extracts 2 floating point values seperated by whitespace
		i0++;
	}

	double** mandatory = new double* [N];//mandatory Stations
	for (int i = 0; i < N; i++) {
		mandatory[i] = new double[2];
	}
	ifstream filem("data/input/mandatory.txt");
	i0 = 0;
	while (i0 < N) {
		filem >> mandatory[i0][0] >> mandatory[i0][1]; // extracts 2 floating point values seperated by whitespace
		i0++;
	}

	double** optional = new double* [(N - 1) * M]; // optinal stations
	for (int i = 0; i < (N - 1) * M; i++) {
		optional[i] = new double[2];
	}
	ifstream fileo("data/input/optional" + to_string(M) + ".txt");
	i0 = 0;
	while (i0 < (N - 1) * M) {
		fileo >> optional[i0][0] >> optional[i0][1]; // extracts 2 floating point values seperated by whitespace
		i0++;
	}

	// Arrival times of the passengers 
	double arrivals[R1];
	ifstream filea("data/input/arrivals" + to_string(R) + ".txt");
	inst << endl << "Desired arrival times of the passengers in seconds: " << endl;
	i0 = 0;
	while (i0 < R1) {
		filea >> arrivals[i0];
		inst << "p_" << i0 + 1 << ": \t" << arrivals[i0] << endl;
		i0++;
	}
	// Departure times of the passengers 
	double departures[R2];
	ifstream filed("data/input/departures" + to_string(R) + ".txt");
	inst << endl << "Desired departure times of the passengers in seconds: " << endl;
	i0 = 0;
	while (i0 < R2) {
		filed >> departures[i0];
		inst << "p_" << i0 + 1 + R1 << ": \t" << departures[i0] << endl;
		i0++;
	}

	//calculate travel time using manhattan distance
	double** traveltimep = new double* [R]; // travel times of people between passangers and stations
	for (int i = 0; i < R; i++) {
		traveltimep[i] = new double[S];
	}
	double** traveltimes = new double* [S];
	for (int i = 0; i < S; i++) {
		traveltimes[i] = new double[S];
	}// travel times of buses between stations
	for (int i = 0; i < R; i++) {
		for (int j = 0; j < N; j++) {
			traveltimep[i][j] = (abs(passengers[i][0] - mandatory[j][0]) + abs(passengers[i][1] - mandatory[j][1])) * 1000 / pspeed;
		}

		for (int j = N; j < S; j++) {
			traveltimep[i][j] = (abs(passengers[i][0] - optional[j - N][0]) + abs(passengers[i][1] - optional[j - N][1])) * 1000 / pspeed;
		}
	}


	inst << endl << "Walking time between passengers and bus stops in seconds: " << "\npassengers correspond with the rows, bus stops correspond with the columns \nthe mandatory stops are listed first, then the optional stops are listed" << endl;
	for (int i = 0; i < R; i++) {
		for (int j = 0; j < S; j++) {
			inst << int(traveltimep[i][j]) << "\t";
		}
		inst << endl;
	}

	for (int i = 0; i < N; i++) {
		for (int j = 0; j < N; j++) {
			traveltimes[i][j] = (abs(mandatory[i][0] - mandatory[j][0]) + abs(mandatory[i][1] - mandatory[j][1])) * 1000 / bspeed;
		}
		for (int j = N; j < S; j++) {
			traveltimes[i][j] = (abs(mandatory[i][0] - optional[j - N][0]) + abs(mandatory[i][1] - optional[j - N][1])) * 1000 / bspeed;
		}
	}

	for (int i = N; i < S; i++) {
		for (int j = 0; j < N; j++) {
			traveltimes[i][j] = (abs(optional[i - N][0] - mandatory[j][0]) + abs(optional[i - N][1] - mandatory[j][1])) * 1000 / bspeed;
		}
		for (int j = N; j < S; j++) {
			traveltimes[i][j] = (abs(optional[i - N][0] - optional[j - N][0]) + abs(optional[i - N][1] - optional[j - N][1])) * 1000 / bspeed;
		}
	}
	inst << endl << "Travel time between bus stops in seconds: " << endl;
	for (int i = 0; i < S; i++) {
		for (int j = 0; j < S; j++) {
			inst << int(traveltimes[i][j]) << "\t";
		}
		inst << endl;
	}
	inst.close();

	//remove memory
	for (int i = 0; i < N; i++) {
		delete[] mandatory[i];
	}
	delete[] mandatory;

	for (int i = 0; i < (N - 1) * M; i++) {
		delete optional[i];
	}
	delete[] optional;

	for (int i = 0; i < R; i++) {
		delete[] passengers[i];
	}
	delete[] passengers;
	//exit(0);

	//************************************************* PRE PROCESSING ********************************************************

	double* tempdist = new double[S];
	int* index = new int[S];
	int** closestS = new int* [S];
	for (int i = 0; i < S; i++) {
		closestS[i] = new int[S];
	}
	//std::cout << "Stops: \n";
	for (int i = 0; i < S; i++) {
		//initialize and copy distance of cities to temp array
		for (int j = 0; j < S; j++) {
			if (j != i) tempdist[j] = traveltimes[i][j];
			else tempdist[j] = 100000;
			index[j] = j;
		}

		//sort according to dist
		quickSort(index, tempdist, 0, S - 1);

		//keep track of best neighbors 
		for (int l = 0; l < S; l++) {
			closestS[i][l] = index[l]; //index
			//std::cout << index[l] << " ";
		}
		//std::cout << " \n";
	}

	int** closestPS = new int* [R];
	for (int i = 0; i < R; i++) {
		closestPS[i] = new int[S];
	}
	//std::cout << "Passengers: \n";
	for (int p = 0; p < R; p++) {
		//initialize and copy distance of cities to temp array
		for (int j = 0; j < S; j++) {
			tempdist[j] = traveltimep[p][j];
			index[j] = j;
		}
		//sort according to dist
		quickSort(index, tempdist, 0, S - 1);

		//keep track of best neighbors 
		for (int j = 0; j < S; j++) {
			closestPS[p][j] = index[j];
			//std::cout << index[j] << " ";
		}
	}

	//remove memory
	delete[] index;
	delete[] tempdist;

	default_random_engine generator0;
	//generator0.seed(400005550007);
	//uniform_int_distribution<int> rRequests(0, R - 1);
	//uniform_int_distribution<int> rStations(0, S - 1);
	///uniform_int_distribution<int> oneto100(1, 100);
	uniform_int_distribution<int> NEXT(0, M);
	// ---------------- Shortest route
	double short_route = 0;
	for (int i = 0; i < N - 1; i++) {
		short_route += traveltimes[i][i + 1];
	}
	//------- Determine best route
	int best_route[S];
	//*

	best_route[0] = 0;
	std::cout << best_route[0] << " ";

	int ma = 0;
	int oc = 0;
	int nopt = 100;

	for (int i = 1; i < S; i++) {
		if (oc < M) {
			best_route[i] = N + ma * M + oc;
			oc++;
		}
		else {
			oc = 0;
			ma++;
			best_route[i] = ma;
		}
		//std::cout << best_route[i] << " ";
	}
	//std::cout << endl;

	int start, end, nextindex, cc, mid, temp0;
	double currentcost, ncost, totE = 0, dE0;
	for (int i = 0; i < N - 1; i++) {
		std::uniform_int_distribution<int> NEXT(i * (M + 1), (M + 1) * i + M + 1); //look only in a cluster (mandatory stops included)
		for (int t = 0; t < nopt; t++) {//number of opt operations
			int j = NEXT(generator0);
			while (j == (M + 1) * i + M + 1) {
				j = NEXT(generator0);
			}
			int l = NEXT(generator0);
			// two nodes cannot be the same of both be the mandatory stops at once
			while (l == j || l == (M + 1) * i + M + 1) {
				l = NEXT(generator0);
			}

			if (j > l) {
				start = l;
				end = j;
			}
			else {
				start = j;
				end = l;
			}
			nextindex = end + 1;
			currentcost = traveltimes[best_route[start]][best_route[start + 1]] + traveltimes[best_route[end]][best_route[nextindex]];
			ncost = traveltimes[best_route[start]][best_route[end]] + traveltimes[best_route[start + 1]][best_route[nextindex]];
			//std::cout << " Current cost: " << currentcost << " New Cost: " << newcost << " \n";
			//--------------------------------------------------------------------SA --------------------------------------------------------------------------
			dE0 = (ncost - currentcost);
			if (dE0 < 0) {
				//currentcost = ncost;
				totE -= -dE0;
				mid = (end - start) / 2;
				//2opt
				for (cc = 1; cc <= mid; cc++) {
					temp0 = best_route[start + cc];
					best_route[start + cc] = best_route[end + 1 - cc];
					best_route[end + 1 - cc] = temp0;
				}
			}
		}
	}

	currentcost = 0;
	for (int i = 0; i < S; i++) {
		std::cout << best_route[i] << " ";
		if (i != S - 1) {
			currentcost += traveltimes[i][i + 1];
		}
	}
	cout << "\nTime big route: " << int(currentcost / 60) << " min" << endl;
	cout << "Time short route: " << int(short_route / 60) << " min" << endl;
	//std::cout << endl << "Reduction: " << totE << endl;
	//exit(0);
	//*/

	//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++Start runs++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
	//list of lists: each element in higher list corresponds with a passenger, each passenger gets a list of length three
	//this list assigns passenger as follows: p_i= [bus, trip, bus stop]


	//vector<vector<int>> ysol(R);
	int** b_ysol = new int* [R];
	for (int i = 0; i < R; i++) {
		//ysol[i] = new int[3];
		b_ysol[i] = new int[3];
	}


	//routing: [bus, trip,stops]
	//vector<vector<vector<int>>> xsol(B);
	vector<vector<vector<int>>> b_xsol(B);

	//D: [bus, trip,departure time]
	//vector<vector<vector<double>>> Dsol(B);
	vector<vector<vector<double>>> b_Dsol(B);



	//------------------- RUNS ------------------------
	//uniform_real_distribution<double> PM1(0, 1);
	//uniform_real_distribution<double> PM2(0, 1);

	uniform_real_distribution<float> r01(0, 1);


	//string logres = "", logresBest = "";

	vector<double> itObj;
	vector<double> itRT;
	//#pragma omp parallel for 
	//int run = 0;
	double u_cost = INT32_MAX, u_RT;
	for (int iit = 0; iit < nIt; iit++) {
		cout << " ++++++++++++++++++++++Iteration: " << iit + 1 << endl;
		vector<float> lPM1;
		vector<float> lPM2;
		vector<float> lPM3;
		vector<float> lFPM;
		vector<float> lXT;
		vector<float> lC;

		vector<float> b_lPM1;
		vector<float> b_lPM2;
		vector<float> b_lPM3;
		vector<float> b_lFPM;
		vector<float> b_lXT;
		vector<float> b_lC;

		vector < vector<float>> lPM1b;
		vector < vector<float>> lPM2b;
		vector < vector<float>> lPM3b;
		vector < vector<float>> lFPMb;
		vector < vector<float>> lXTb;
		vector < vector<float>> lCb;

		vector<double> Costb;
		//int infeastemp = 0;
		double best_cost = INT32_MAX, bb_cost = INT32_MAX;
		double tstart_time = clock();

		// +++++++++++++++++++++++++   LNS params +++++++++++++++++++++++++++++
		double Ts = 1000, T_end = 0.01;
		//double alph = 0.985;
		const double nhp = 0.125;
		//int LL = 30;
		const int des = 10;
		//double Tmax = Ts;
		const double lam = 10;
		int r_i = 0, stop_it = 50000;
		//private(generator, PM, gXT, PlanB1, PlanB2)
		random_device r;
		std::vector<std::default_random_engine> generators;
		normal_distribution<float> PM(0.6, 0.25);
		uniform_real_distribution<float> gXT(0.6, 1);
		uniform_real_distribution<float> gC(0.25, 1);
		uniform_real_distribution<float> PlanB1(0.95, 1);
		uniform_real_distribution<float> PlanB2(0, 0.05);
		uniform_real_distribution<float> PlanB3(0.35, 0.45);
		//int nN;
		for (int i = 0, nN = omp_get_max_threads(); i < nN; ++i) {
			generators.emplace_back(default_random_engine(r()));
		}
		std::atomic<bool> INFEASS0(false);
		//omp_set_num_threads(1);
		//int give = 0;
#pragma omp parallel firstprivate(traveltimes, traveltimep, arrivals, departures,closestPS,closestS, S,M,N,B,short_route, best_route,C,TS,OGxt,dw,d_dl,d_de,d_ae,d_al,c1,c2,c3)
		{
			//double countInfeas1 = 0, countInfeas2 = 0, countFeas = 0;
			default_random_engine& generator = generators[omp_get_thread_num()];
			//generator.seed((omp_get_thread_num()) * 800051150);
			//int iii, stop;
			int xt;
			double UBxt;
			//int LL = 30;

			int i, j, b, t, p, l, s;
			double pm1, pm2, pm3, fpm;
			double b_next;
			vector<int> route;
			vector<float> dPM10;
			vector<float> dPM20;
			vector<float> dPM30;
			vector<float> dFPM0;
			vector<float> dXT0;
			vector<float> dC0;
			int temp;
			vector<double> IFC;
			int FCi = 0;
			//double dE;
			vector<double> timetable;
			vector<double> tempt;
			double timewindow, timewindow2;
			//double Arr;


			int trips[B]; //keeps track of which trip each bus is at needs to be updated
			int best_stop;
			double freqN[N];
			double newfreqN[N];

			double bd[B];
			int yk[R][3];
			double startopt;

			int countp, p1, p2, cp1, cp2;
			bool in, in2;
			double threshold, tt;

			double cost, b_cost;
			double l_arr, l_dep;

			int b_it = 0;

			double minF = INT16_MAX, min_al = INT16_MAX, min_ae = INT16_MAX, min_dl = INT16_MAX, min_de = INT16_MAX;
			int nS, dst;
			double diffa1, diffa2, diffd1, diffd2, diffF;
			double difBD, maxFW, maxRW;//max time to arrive or depart earlier
			//add addtional passenger with DAT
			//*
			double extra = 0, b_extra = 0;
			int indexpt[R1];
			int indexpt2[R2];
			double temparrivals[R1];
			double tempdept[R2];
			//routing: [bus, trip,stops]
			vector<vector<vector<int>>> xk(B);
			//D: [bus, trip,departure time]
			vector<vector<vector<double>>> Dk(B);
			bool INFEAS1 = false, INFEAS2 = false, INFEAS3 = false, INFEAS4 = false;


			//generator.seed(7851 * (omp_get_thread_num()));
			while (!INFEASS0) {
				for (s = 0; s < B; s++) {
					xk[s].clear();
					Dk[s].clear();
				}
				//if (!INFEASS0) {
				//cout << run << endl;
				//generator.seed(48441 * (omp_get_thread_num()+countInfeas1+countInfeas2));
				//cout << run << " parallel "<< endl;

				//std::cout << "\n************************************************************************** Run number: " << run + 1 << endl;
				//logres = "";
				for (p = 0; p < R; p++) {
					yk[p][0] = -1;
					yk[p][1] = -1;
					yk[p][2] = -1;

				}

				for (p = 0; p < R1; p++) {
					indexpt[p] = p;
					temparrivals[p] = arrivals[p];
				}

				for (p = 0; p < R2; p++) {
					indexpt2[p] = p;
					tempdept[p] = departures[p];
				}
				quickSort(indexpt, temparrivals, 0, R1 - 1);
				quickSort(indexpt2, tempdept, 0, R2 - 1);
				best_stop = 0;
				startopt = tempdept[0] - 1000;
				threshold = 0, tt = 0;
				cost = 0, b_cost = 0;

				route.clear();

				timetable.clear();
				tempt.clear();
				//cout << "check\n";
				dPM10.clear();
				dPM20.clear();
				dPM30.clear();
				dFPM0.clear();
				dXT0.clear();
				dC0.clear();
				//cout << "Try again \n";
				/*
				for (b = 0; b < B; b++) {
					pm1 = PM(generator);
					pm2 = PM(generator);
					pm3 = PM(generator);
					fpm = PM(generator);

					if (pm1 > 1)pm1 = PlanB1(generator);
					if (pm1 < 0)pm1 = PlanB2(generator);
					if (pm2 > 1)pm2 = PlanB1(generator);
					if (pm2 < 0)pm2 = PlanB2(generator);
					if (pm3 > 1)pm3 = PlanB1(generator);
					if (pm3 < 0)pm3 = PlanB2(generator);
					if (fpm > 1)fpm = PlanB1(generator);
					if (fpm < 0)fpm = PlanB2(generator);


					dPM10.push_back(pm1);
					dPM20.push_back(pm2);
					dPM30.push_back(pm3);
					dFPM0.push_back(fpm);
					dXT0.push_back(gXT(generator));
				}
				*/
				l_arr = arrivals[indexpt[0]], l_dep = departures[indexpt2[0]] + short_route * 0.75;
				//logres += "Run: " + to_string(run + 1) + "\t";
				//start_time = clock();
				//************************************Initial Solution***************************************
				for (i = 0; i < N; i++) {
					freqN[i] = -INT16_MAX;
				}
				countp = p1 = p2 = 0;
				for (b = 0; b < B; b++) {
					trips[b] = 0;
					bd[b] = startopt;//start of optimization
				}
				timetable.push_back(0);

				p1 = p2 = countp = 0;
				b = 0;
				b_next = 0.0;
				//cout << " END of PH: " << int(TS + startopt) / 60 << endl;
				b_it = -1;

				while (timetable.back() < TS + startopt && p1 + p2 < R) {//until TS is over+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++	
					b_it++;

					pm1 = PM(generator);
					pm2 = PM(generator);
					pm3 = PM(generator);
					fpm = PM(generator);

					if (pm1 > 1)pm1 = 1;
					if (pm1 < 0)pm1 = 0;
					if (pm2 > 1)pm2 = 1;
					if (pm2 < 0)pm2 = 0;
					if (pm3 > 1)pm3 = 1;
					if (pm3 < 0)pm3 = 0;
					if (fpm > 1)fpm = 1;
					if (fpm < 0)fpm = 0;

					UBxt = gXT(generator);
					xt = int(UBxt * OGxt);

					dPM10.push_back(pm1);
					dPM20.push_back(pm2);
					dPM30.push_back(pm3);
					dFPM0.push_back(fpm);
					dXT0.push_back(UBxt);

					float Cc = gC(generator);
					dC0.push_back(Cc);
					C = max(5, int(Cc * C_OG));

					//xt = OGxt;
					//if (infeastemp > 100) fpm = 1;
					//cout << " xt: " << xt / 60 << endl;
					//determine which bus is available first
					b = iMin(bd, B);
					b_next = iMin2(bd, B);
					//cout << "++++++ || Bus: " << b << " bd: " << int(bd[b] / 60) << " trip: " << trips[b] << " || ++++++\n";
					//for (i = 0; i < B; i++) cout << int(bd[i] / 60) << " ";
					//cout << endl;
					//cout << "bd1: " << int(bd[b]/60) << " bd2: " << int(b_next/60) << endl;
					//Make route only with mandatory stops, ASAP
					route.clear();
					timetable.clear();
					tempt.clear();
					tt = bd[b];
					timetable.push_back(tt);
					route.push_back(0);
					for (i = 1; i < N; i++) {
						route.push_back(i);
						tt += traveltimes[i - 1][i];
						timetable.push_back(tt);
					}
					//Assignement: First look at R1
					timewindow = timewindow2 = INT32_MAX;
					cp1 = cp2 = 0;

					//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ CASE I ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
					if (l_arr < l_dep && p1 < R1 || p2 == R2) {
						//cout << "R1" << endl;
						p = 0;
						while (cp1 + cp2 < C && countp < R && p < R1 && (int)(arrivals[indexpt[p]] - timewindow) <= d_ae + d_al) {
							//cout << " check start\n";
							//cout << cp1 + cp2 << "<" << C << "  " << countp << "<" << R << "  " << (int)(arrivals[indexpt[p]] - timewindow) << "< " << d_ae + d_al << endl;
							if (traveltimep[indexpt[p]][closestPS[indexpt[p]][0]] > dw) {
								std::cout << " Infeasible solution, for walking times " << endl;
								//cout << "stop: " << closestPS[indexpt[p]][0] << endl;
								exit(0);
							}
							if (temparrivals[indexpt[p]] == -1) {
								//cout << "passenger already in solution \n";
								//cout << "p: " << p << " indexpt: " << indexpt[p] << endl;
								p++;
								if (p > R1)break;
								continue;//if this is already in the solution, continue to next passenger
							}
							if (cp1 == 0)timewindow = arrivals[indexpt[p]];

							//Assign bus stop to passenger
							//choose best stop and update route
							if (cp1 == 0) {
								//cout << " check 2 \n";
								best_stop = bestStop(timetable, route, traveltimes, traveltimep, closestPS, indexpt[p], N,
									dw, best_route, M, S, bd[b], freqN, xt, best_stop, arrivals[indexpt[p]],
									arrivals[indexpt[p]], d_ae, d_al, yk, arrivals, R1, R2, b, trips[b], b_next, fpm);
								//cout << " check stop 0\n";
								if (best_stop == -1) {
									//cout << "passenger " << indexpt[p] << " --> Skip this one, not good for bus stop\n";
									p++;
									//cout << "Next passenger " << p1 << endl;
									if (p > R1)break;
									continue;
								}
								//cout << " --- FIRST passenger added : p= " << indexpt[p] << "\n";
								//Assign bus to passenger
								yk[indexpt[p]][0] = b;
								yk[indexpt[p]][1] = trips[b];
								yk[indexpt[p]][2] = best_stop;
								temparrivals[indexpt[p]] = -1;
								tempt.push_back(arrivals[indexpt[p]]);
								p++;
								p1++;
								cp1++;
								countp++;
								if (p > R1)break;
							}
							else {
								temp = bestStop(timetable, route, traveltimes, traveltimep, closestPS, indexpt[p], N, dw,
									best_route, M, S, bd[b], freqN, xt, best_stop, tempt.back(),
									arrivals[indexpt[p]], d_ae, d_al, yk, arrivals, R1, R2, b, trips[b], b_next, fpm);
								//cout << " check stop n: " << temp <<"\n";
								if (temp == -1) {
									//cout << "passenger " << indexpt[p] << " --> Skip this one, not good for bus stop\n";
									p++;//next stop of a passenger with later edt is before a previous stop with a passenger with earlier edt, not possible OR edts are too different
									if (p > R1)break;
									continue;
								}
								else {
									// time to go from prev to next stop on a full route 
									best_stop = temp;
									//Assign bus to passenger
									yk[indexpt[p]][0] = b;
									yk[indexpt[p]][1] = trips[b];
									yk[indexpt[p]][2] = best_stop;
									temparrivals[indexpt[p]] = -1;
									tempt.push_back(arrivals[indexpt[p]]);
									p++;
									p1++;
									cp1++;
									countp++;
									if (p > R1)break;
									//cout << "-- NEXT passenger added : p= " << indexpt[p] << "\n";
									//cout << " indexpt: " << indexpt[p] << " arrivals p: " << arrivals[indexpt[p]] <<  endl;
									//cout << " p: " << p << " indexpt: " << indexpt[p] << endl;
								}
							}
						}
						//cout << " check end\n";
						//cout << "timetable:" << timetable.size() << " route: " << route.size() << " Passengers added: " << tempt.size() << endl;

					}
					// //++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ CASE II ++++++++++++++++++++++++++++++++++++++++++++ Now look at R2
					//*
					if ((l_arr >= l_dep && p2 < R2) || cp1 == 0) {
						//cout << "R2" << endl;
						//cout << timetable.size() << endl;
						timetable.clear();
						tt = bd[b];
						timetable.push_back(tt);
						for (i = 1; i < N; i++) {
							tt += traveltimes[i - 1][i];
							timetable.push_back(tt);
						}

						p = 0;
						while (cp2 < C && countp < R && p < R2) {
							//cout << p2 << "<" << C << "  " << countp << "<" << R << " " << p << "< " << R2 << endl;
							//cout << "passenger " << indexpt2[p] + R1 << "  ------------- \n";
							if (traveltimep[R1 + indexpt2[p]][closestPS[R1 + indexpt2[p]][0]] > dw) {
								std::cout << " Infeasible solution, for walking times " << endl;
								exit(0);
							}
							if (tempdept[indexpt2[p]] == -1) {
								//cout << "passenger already in solution \n";
								p++;
								continue;//if this is already in the solution, continue to next passenger
							}
							t = 0;
							int ttS = timetable.size();
							for (i = 0; i < ttS; i++) {
								if (route[i] < N) {
									newfreqN[t] = timetable[i];
									t++;
								}
							}
							if (cp2 == 0) {
								best_stop = bestStop2(timetable, route, traveltimes, traveltimep, closestPS, indexpt2[p] + R1, N,
									dw, best_route, M, S, bd[b], freqN, newfreqN, xt, best_stop, departures[indexpt2[p]],
									departures[indexpt2[p]], d_de, d_dl, yk, departures, R1, R2, b, trips[b], b_next, fpm);
								if (best_stop == -1) {
									//cout << "passenger " << indexpt2[p] + R1 << " --> Skip this one, not good for bus stop\n";
									p++;
									//cout << "Next passenger " << p1 << endl;
									continue;
								}
								//cout << " --- FIRST passenger added : p= " << indexpt2[p] + R1 << "\n";
								//Assign bus to passenger
								yk[R1 + indexpt2[p]][0] = b;
								yk[R1 + indexpt2[p]][1] = trips[b];
								//Assign bus stop to passenger
								//choose best stop and update route
								//cout << "  Best stop: " << best_stop << endl;
								//cout << "Passenger: " << R1 + indexpt2[p] << " edt: " << int(departures[indexpt2[p]] / 60) << " stop: " << best_stop << endl;
								tempt.push_back(departures[indexpt2[p]]);
								tempdept[indexpt2[p]] = -1;
								yk[R1 + indexpt2[p]][2] = best_stop;
								cp2++;
								p2++;
								countp++;
								p++;
							}
							else {
								temp = bestStop2(timetable, route, traveltimes, traveltimep, closestPS, indexpt2[p] + R1, N, dw,
									best_route, M, S, bd[b], freqN, newfreqN, xt, best_stop, tempt.back(),
									departures[indexpt2[p]], d_de, d_dl, yk, departures, R1, R2, b, trips[b], b_next, fpm);

								if (temp == -1) {
									//cout << "Passenger: " << R1 + indexpt2[p] << " edt: "<< int(departures[indexpt2[p]] / 60) << "Skip this one, not good for bus stop\n";
									p++;//next stop of a passenger with later edt is before a previous stop with a passenger with earlier edt, not possible OR edts are too different
									continue;
								}
								else {
									// time to go from prev to next stop on a full route 
									best_stop = temp;
									//Assign bus to passenger
									yk[R1 + indexpt2[p]][0] = b;
									yk[R1 + indexpt2[p]][1] = trips[b];
									//Assign bus stop to passenger
									yk[R1 + indexpt2[p]][2] = best_stop;
									//cout << "Passenger: " << R1 + indexpt2[p] << " edt: " << int(departures[indexpt2[p]] / 60) << " stop: " << best_stop << endl;
									tempt.push_back(departures[indexpt2[p]]);
									tempdept[indexpt2[p]] = -1;
									cp2++;
									p2++;
									countp++;
									p++;
									//cout << "-- NEXT passenger added : p= " << indexpt2[p] + R1 << "\n";
								}
							}
						}
						int temptS = tempt.size();
						if (p1 < R1 && l_arr >= l_dep && temptS == 0) {
							//++++++++++++++++++++++++++++++++ CASE I ++++++++++++++++++++++++++++++++++++++++++++
							//cout << "R1 again" << endl;
							p = 0;
							while (cp1 + cp2 < C && countp < R && p < R1 && (int)(arrivals[indexpt[p]] - timewindow) <= d_ae + d_al) {
								//cout << cp1 + cp2 << "<" << C << "  " << countp << "<" << R << "  " << (int)(arrivals[indexpt[p]] - timewindow) << "< " << d_ae + d_al << endl;
								if (traveltimep[indexpt[p]][closestPS[indexpt[p]][0]] > dw) {
									std::cout << " Infeasible solution, for walking times " << endl;
									exit(0);
								}
								if (temparrivals[indexpt[p]] == -1) {
									//cout << "passenger already in solution \n";
									//cout << "p: " << p << " indexpt: " << indexpt[p] << endl;
									p++;
									if (p > R1)break;
									continue;//if this is already in the solution, continue to next passenger
								}
								if (cp1 == 0)timewindow = arrivals[indexpt[p]];
								//Assign bus stop to passenger
								//choose best stop and update route
								if (cp1 == 0) {
									best_stop = bestStop(timetable, route, traveltimes, traveltimep, closestPS, indexpt[p], N,
										dw, best_route, M, S, bd[b], freqN, xt, best_stop, arrivals[indexpt[p]],
										arrivals[indexpt[p]], d_ae, d_al, yk, arrivals, R1, R2, b, trips[b], b_next, fpm);
									//cout << " check\n";
									if (best_stop == -1) {
										//cout << "passenger " << indexpt[p]  << " --> Skip this one, not good for bus stop\n";
										p++;
										//cout << "Next passenger " << p1 << endl;
										if (p > R1)break;
										continue;
									}
									//cout << " --- FIRST passenger added\n";
									//Assign bus to passenger
									yk[indexpt[p]][0] = b;
									yk[indexpt[p]][1] = trips[b];
									yk[indexpt[p]][2] = best_stop;
									temparrivals[indexpt[p]] = -1;
									tempt.push_back(arrivals[indexpt[p]]);
									p++;
									p1++;
									cp1++;
									countp++;
									if (p > R1)break;
									//cout << " --- FIRST passenger added : p= " << indexpt[p] << "\n";
								}
								else {
									temp = bestStop(timetable, route, traveltimes, traveltimep, closestPS, indexpt[p], N, dw,
										best_route, M, S, bd[b], freqN, xt, best_stop, tempt.back(),
										arrivals[indexpt[p]], d_ae, d_al, yk, arrivals, R1, R2, b, trips[b], b_next, fpm);
									//cout << " check\n";
									if (temp == -1) {
										//cout << "passenger " << indexpt[p] << " --> Skip this one, not good for bus stop\n";
										p++;//next stop of a passenger with later edt is before a previous stop with a passenger with earlier edt, not possible OR edts are too different
										if (p > R1)break;
										continue;

									}
									else {
										// time to go from prev to next stop on a full route 
										best_stop = temp;
										//Assign bus to passenger
										yk[indexpt[p]][0] = b;
										yk[indexpt[p]][1] = trips[b];
										yk[indexpt[p]][2] = best_stop;
										temparrivals[indexpt[p]] = -1;
										tempt.push_back(arrivals[indexpt[p]]);
										p++;
										p1++;
										cp1++;
										countp++;
										if (p > R1)break;
										//cout << "-- NEXT passenger added : p= " << indexpt[p] << "\n";
									}
								}

							}

						}
						//cout << "timetable:" << timetable.size() << " route: " << route.size() << " Passengers added: " << tempt.size() << endl;
					}
					//*/
					int temptS = tempt.size();
					if (temptS == 0) {
						timetable.clear();
						timetable.push_back(max(freqN[0] + xt, bd[b]));
						tt = -1;
						for (i = 1; i < N; i++) {
							timetable.push_back(timetable[i - 1] + traveltimes[i - 1][i]);
							if (timetable[i] - freqN[i] > tt)tt = timetable[i] - freqN[i];
						}
						if (tt > xt) {
							for (i = 0; i < N; i++) {
								timetable[i] -= (tt - xt);
							}
						}
					}
					else {
						//add addtional passenger with DAT

						minF = INT16_MAX, min_al = INT16_MAX, min_ae = INT16_MAX, min_dl = INT16_MAX, min_de = INT16_MAX;
						nS = timetable.size() - 1;

						for (p = 0; p < R1; p++) {
							if (yk[p][0] == b && yk[p][1] == trips[b]) {
								//cout << "passenger " << p  << ": dat=" << int(arrivals[p] / 60) << " arr=" << int(timetable[nS] / 60) << endl;
								diffa1 = d_ae - (arrivals[p] - timetable[nS]);
								diffa2 = d_al - (timetable[nS] - arrivals[p]);
								if (arrivals[p] >= timetable[nS] && min_ae > diffa1) {
									min_ae = diffa1;
								}
								if (arrivals[p] <= timetable[nS] && min_al > diffa2) {
									min_al = diffa2;
								}
							}
						}

						dst = -1;
						int routeS = route.size(), timetableS = timetable.size();
						for (p = 0; p < R2; p++) {
							dst = -1;
							for (i = 0; i < routeS; i++) {
								if (yk[p + R1][0] == b && yk[p + R1][1] == trips[b] && yk[p + R1][2] == route[i]) {
									dst = i;
									break;
								}
							}
							if (dst != -1) {
								//cout << "passenger " << p +R1 << ": edt=" << int(departures[p] / 60) << " dept=" << int(timetable[dst] / 60) << " at stop: " <<route[dst] << endl;
								diffd1 = d_de - (departures[p] - timetable[dst]);
								diffd2 = d_dl - (timetable[dst] - departures[p]);
								if (departures[p] >= timetable[dst] && min_de > diffd1) {
									min_de = diffd1;
								}
								if (departures[p] <= timetable[dst] && min_dl > diffd2) {
									min_dl = diffd2;
								}
							}
						}
						if (freqN[0] != -INT16_MAX) {
							for (i = 0; i < timetableS; i++) {
								if (route[i] < N && freqN[route[i]] < timetable[i]) {
									diffF = xt - (timetable[i] - freqN[route[i]]);
									if (minF > diffF) minF = diffF;
								}
							}
						}

						//cout << " min diff al: " << int(min_al/60) << " min diff dl: " << int(min_dl/60) << " min diff Freq: " << int(minF / 60) << endl;
						//cout << " min diff ae: " << int(min_ae/60) << " min diff de: " << int(min_de/60) << endl;
						difBD = timetable[0] - bd[b];
						maxFW = min(min(min_al, min_dl), minF) * pm1; // max time to depart later 
						maxRW = min(min(min_ae, min_de), difBD) * pm2;//max time to arrive or depart earlier
						//add addtional passenger with DAT
						//*
						extra = 0;
						//cout << "Max time FW: " << int(maxFW/60) << " max time RW: " << int(maxRW/60) << "\nStart R1\n";
						//cout << "R1: " << cp1 << " R2: " << cp2 << endl;

						for (p = 0; p < R1; p++) {
							if (temparrivals[p] != -1) {
								//cout << "for p_" << p << " dat: "<<arrivals[p]/60<< " arrval: " << timetable.back()/60<<endl;
								i = 0;
								b_cost = INT32_MAX;
								s = -1;
								if (arrivals[p] >= timetable.back()) {
									if (arrivals[p] - timetable.back() <= d_ae) extra = 0;
									else extra = (arrivals[p] - timetable.back()) - d_ae;
								}
								else {
									if (timetable.back() - arrivals[p] <= d_al) extra = 0;
									else extra = d_al - (timetable.back() - arrivals[p]);
								}
								while (traveltimep[p][closestPS[p][i]] < dw * pm3) {
									//cout << "try stop: " << closestPS[p][i] << endl;
									routeS = route.size() - 1;
									for (t = 0; t < routeS; t++) {
										in = false;
										if (closestPS[p][i] == route[t]) {
											in = true;
											break;
										}
									}
									in2 = false;
									if (in && arrivals[p] - timetable.back() - maxFW <= d_ae && timetable.back() - maxRW - arrivals[p] <= d_al) {
										in2 = true;
									}

									if (in2 && cp1 + cp2 < C) {
										//cout << " ++++++++++++ passenger " << p << " (dat=" << int(arrivals[p] / 60) << ") stop " << closestPS[p][i] << " (tt=" << int(timetable.back() / 60) << ") possible extra: " << int(extra / 60) << endl;
										cost = c2 * traveltimep[p][closestPS[p][i]] + c3 * abs(timetable.back() - arrivals[p]) + c3 * (cp1 + cp2) * (abs(extra));
										if (b_cost > cost) {
											b_cost = cost;
											s = route[t];
										}
									}
									i++;
								}
								if (b_cost != INT32_MAX) {
									//cout << "Added DAT \t";
									//cout << "Passenger: " << p << " arr: " << arrivals[p] / 60 << endl;
									yk[p][0] = b;
									yk[p][1] = trips[b];
									yk[p][2] = s;
									//cout << "Passenger: " << R1 + p << endl;
									temparrivals[p] = -1;//indicate this passenger is onboard already
									p1++;
									cp1++;
									countp++;
									//break;

									//update timetable
									//cout << " move tt with " << int(extra / 60) << endl;
									timetableS = timetable.size();
									for (l = 0; l < timetableS; l++) {
										timetable[l] += extra;
									}
									//update intermediary parameters
									minF = INT16_MAX, min_al = INT16_MAX, min_ae = INT16_MAX, min_dl = INT16_MAX, min_de = INT16_MAX;
									nS = timetable.size() - 1;
									for (int p11 = 0; p11 < R1; p11++) {
										if (yk[p11][0] == b && yk[p11][1] == trips[b]) {
											diffa1 = d_ae - (arrivals[p11] - timetable[nS]);
											diffa2 = d_al - (timetable[nS] - arrivals[p11]);
											if (arrivals[p11] >= timetable[nS] && min_ae > diffa1) {
												min_ae = diffa1;
											}
											if (arrivals[p11] <= timetable[nS] && min_al > diffa2) {
												min_al = diffa2;
											}
										}
									}
									for (int p22 = 0; p22 < R2; p22++) {
										dst = -1;
										routeS = route.size();
										for (l = 0; l < routeS; l++) {
											if (yk[p22 + R1][0] == b && yk[p22 + R1][1] == trips[b] && yk[p22 + R1][2] == route[l]) {
												dst = l;
												break;
											}
										}
										if (dst != -1) {
											diffd1 = d_de - (departures[p22] - timetable[dst]);
											diffd2 = d_dl - (timetable[dst] - departures[p22]);
											if (departures[p22] >= timetable[dst] && min_de > diffd1) {
												min_de = diffd1;
											}
											if (departures[p22] <= timetable[dst] && min_dl > diffd2) {
												min_dl = diffd2;
											}
										}
									}
									if (freqN[0] != -INT16_MAX) {
										timetableS = timetable.size();
										for (l = 0; l < timetableS; l++) {
											if (route[l] < N && freqN[route[l]] < timetable[l]) {
												diffF = xt - (timetable[l] - freqN[route[l]]);
												if (minF > diffF) minF = diffF;
											}
										}
									}
									//cout << " min diff al: " << int(min_al/60) << " min diff dl: " << int(min_dl/60) << endl;
									//cout << " min diff ae: " << int(min_ae/60) << " min diff de: " << int(min_de/60) << " min diff Freq: " << int(minF/60) << endl;
									difBD = timetable[0] - bd[b];
									maxFW = min(min(min_al, min_dl), minF) * pm1; // max time to depart later 
									maxRW = min(min(min_ae, min_de), difBD) * pm2;//max time to arrive or depart earlier
									//cout << "  Added passenger " << p << " --> NEW Max time FW: " << int(maxFW/60) << " max time RW: " << int(maxRW/60) << endl;

								}
							}
						}

						//add addtional passenger with EDT
						///*
						//cout << "Start R2\nNEW Max time FW : " << int(maxFW / 60) << " max time RW : " << int(maxRW / 60) << endl;
						b_extra = 0;
						for (p = 0; p < R2; p++) {
							if (tempdept[p] != -1) {
								//cout << "try p_" << p+R1 << " dept: "<<departures[p]/60<<endl;
								i = 0;
								b_cost = INT32_MAX;
								s = -1;
								while (traveltimep[R1 + p][closestPS[p + R1][i]] < dw * pm3) {
									routeS = route.size() - 1;
									//if (R1 + p == 36)cout << closestPS[p + R1][i] << endl;
									for (t = 0; t < routeS; t++) {
										in = false;
										if (closestPS[p + R1][i] == route[t]) {
											//cout << "bus stop " << closestPS[p + R1][i] << " position " << t << endl;
											in = true;
											break;
										}
									}
									in2 = false;
									if (in && departures[p] - timetable[t] - maxFW <= d_de && timetable[t] - maxRW - departures[p] <= d_dl) {
										in2 = true;
									}
									//if (in2) cout << "bus stop " << closestPS[p + R1][i] << " position " << t << " length of tt: " << timetable.size() << endl;

									if (in2 && cp1 + cp2 < C) {
										//cout << "bus stop " << closestPS[p + R1][i] << " position " << t << " length of tt: " << timetable.size() << endl;
										if (departures[p] >= timetable[t]) {
											if (departures[p] - timetable[t] <= d_de)extra = 0;
											else extra = (departures[p] - timetable[t]) - d_de;
										}
										else {
											if (timetable[t] - departures[p] <= d_dl)extra = 0;
											else extra = d_dl - (timetable[t] - departures[p]);
										}
										//cout << "walking time " << traveltimep[R1 + p][closestPS[p + R1][i]] / 60 << endl;
										//cout << " ++++++++++++ passenger " << p+R1 << " (edt="<< int(departures[p]/60) << ") stop " << closestPS[p + R1][i] <<" (tt="<< int(timetable[t]/60) << ") possible extra: " << int(extra / 60)<< endl;
										cost = c2 * traveltimep[R1 + p][closestPS[p + R1][i]] + c3 * abs(timetable[t] - departures[p]) + c3 * (cp1 + cp2) * (abs(extra));
										if (b_cost > cost) {
											b_cost = cost;
											s = route[t];
											b_extra = extra;
										}
									}
									i++;
								}
								if (b_cost != INT32_MAX) {
									//cout << "Added EDT \t";
									//cout << "Passenger: " << R1 + p << " dept: " << departures[p] / 60 << endl;
									yk[p + R1][0] = b;
									yk[p + R1][1] = trips[b];
									yk[p + R1][2] = s;
									//cout << "Passenger: " << R1 + p << endl;
									tempdept[p] = -1;//indicate this passenger is onboard already
									p2++;
									cp2++;
									countp++;
									//break;
									//update timetable
									//cout << " move tt with " << int(b_extra / 60) << endl;
									timetableS = timetable.size();
									for (l = 0; l < timetableS; l++) {
										timetable[l] += b_extra;
									}
									//update intermediary parameters
									minF = INT16_MAX, min_al = INT16_MAX, min_ae = INT16_MAX, min_dl = INT16_MAX, min_de = INT16_MAX;
									nS = timetable.size() - 1;
									for (int p11 = 0; p11 < R1; p11++) {
										if (yk[p11][0] == b && yk[p11][1] == trips[b]) {
											diffa1 = d_ae - (arrivals[p11] - timetable[nS]);
											diffa2 = d_al - (timetable[nS] - arrivals[p11]);
											if (arrivals[p11] >= timetable[nS] && min_ae > diffa1) {
												min_ae = diffa1;
											}
											if (arrivals[p11] <= timetable[nS] && min_al > diffa2) {
												min_al = diffa2;
											}
										}
									}
									for (int p22 = 0; p22 < R2; p22++) {
										dst = -1;
										routeS = route.size();
										for (l = 0; l < routeS; l++) {
											if (yk[p22 + R1][0] == b && yk[p22 + R1][1] == trips[b] && yk[p22 + R1][2] == route[l]) {
												dst = l;
												break;
											}
										}
										if (dst != -1) {
											diffd1 = d_de - (departures[p22] - timetable[dst]);
											diffd2 = d_dl - (timetable[dst] - departures[p22]);
											if (departures[p22] >= timetable[dst] && min_de > diffd1) {
												min_de = diffd1;
											}
											if (departures[p22] <= timetable[dst] && min_dl > diffd2) {
												min_dl = diffd2;
											}
										}
									}
									if (freqN[0] != -INT16_MAX) {
										timetableS = timetable.size();
										for (l = 0; l < timetableS; l++) {
											if (route[l] < N && freqN[route[l]] < timetable[l]) {
												diffF = xt - (timetable[l] - freqN[route[l]]);
												if (minF > diffF) minF = diffF;
											}
										}
									}

									difBD = timetable[0] - bd[b];
									maxFW = min(min(min_al, min_dl), minF) * pm1; // max time to depart later 
									maxRW = min(min(min_ae, min_de), difBD) * pm2;//max time to arrive or depart earlier
									//cout << "    min diff al: " << int(min_al/60) << " min diff dl: " << int(min_dl/60) << endl;
									//cout << "    min diff ae: " << int(min_ae/60) << " min diff de: " << int(min_de/60) << " min diff Freq: " << int(minF/60) << endl;
									//cout << "  Added passenger " << p + R1 << " --> NEW Max time FW: " << int(maxFW / 60) << " max time RW: " << int(maxRW / 60) << endl;
								}
							}
						}
						//cout << "AFTER --> R1: " << cp1 << " R2: " << cp2 << endl;
						//*/

					}
					//cout << "R1+R2 done  Nroute: " << route.size() << " N_timetable: " << timetable.size() << endl;
					//update trip of bus b
					trips[b]++;
					//update bd of bus b
					bd[b] = timetable.back() + short_route;
					//update varaibles
					xk[b].push_back(route);
					Dk[b].push_back(timetable);
					//update frequency at mandatory 
					//cout << "xt constraints: \n";
					//cout << " ******* TIMETABLE: ";
					int timetableS = timetable.size();
					for (i = 0; i < timetableS; i++) {
						if (route[i] < N && (freqN[route[i]] < timetable[i] || freqN[route[i]] - timetable[i] > xt)) {
							//if(timetable[i] - freqN[route[i]]+1>xt) cout << int((timetable[i]- freqN[route[i]])) / 60 << " (s: "<< route[i]<< ") ";
							freqN[route[i]] = timetable[i];
							t++;
						}
						//cout << int(timetable[i] / 60) << " ";
					}
					//cout << endl << " FreqN: " ;
					//for (i = 0; i < N; i++) {
						//cout << int(freqN[i] / 60) << "  ";
					//}
					//cout << endl;
					/*
					cout << " timetable: \n";
					for (i = 0; i < timetable.size(); i++) {
						cout << int(timetable[i] / 60) << " ";
					}
					cout << endl;
					//*/
					//cout << "Passengers added to bus: " << cp1 + cp2 << endl;
					//cout << endl << "Number of passenger assigned: R2: " << p2 << " R1: " << p1 << endl << endl;
					if (p2 < R2) {
						for (p = 0; p < R2; p++) {
							if (tempdept[indexpt2[p]] != -1) {
								l_dep = departures[indexpt2[p]] + 0.75 * short_route;
								break;
							}
						}
					}
					if (p1 < R1) {
						for (p = 0; p < R1; p++) {
							if (temparrivals[indexpt[p]] != -1) {
								l_arr = arrivals[indexpt[p]];
								break;
							}
						}
					}
				}

				//elapsed_time = (double)(clock() - start_time) / CLK_TCK;
				//iii++;
				INFEAS1 = false, INFEAS2 = false, INFEAS3 = false, INFEAS4 = false;
				//cost = INT32_MAX;
				//cout <<  " thread: " + to_string(omp_get_thread_num()) +  "\n";
				if (countp != R) {
					continue;
				}
				else {
					//if(BG==true) cout << "Fixed one\n";
					//Objective function value
					cost = 0;
					for (p = 0; p < R; p++) {
						b = yk[p][0];
						t = yk[p][1];
						s = yk[p][2];
						//if (p == R1) cout << endl;
						//cout << "Passenger: " << p << "\tBus_" << b << " Trip_" << t << " Stop_" << s;
						//continue;
						//Walking for all passengers
						cost += c2 * traveltimep[p][s];
						if (traveltimep[p][s] > dw) {
							INFEAS1 = true;
							break;
							//cout << "\twalking: " << int(traveltimep[p][s] / 60) << "**";
						}
						//else cout << "\twalking: " << int(traveltimep[p][s] / 60);
						in = false;
						//Travel for all passengers
						int xkS = xk[b][t].size() - 1;
						for (i = 0; i < xkS; i++) {
							if (xk[b][t][i] == s || in) {
								if (!in)l = i;
								in = true;
								cost += c1 * traveltimes[xk[b][t][i]][xk[b][t][i + 1]];
							}
						}
						if (s == N - 1) l = xk[b][t].size() - 1;
						//waiting
						//cout <<"Passenger " << p<<" Stop " << s << " index ";
						//cout << endl << l << "  " << xk[b][t].size() << endl;
						if (p < R1) {
							cost += c3 * abs(arrivals[p] - Dk[b][t].back());
							if (int(arrivals[p] - Dk[b][t].back()) > d_ae || int(Dk[b][t].back() - arrivals[p]) > d_al) {
								INFEAS2 = true;
								break;
								//cout << "\tdat: " << int((arrivals[p]) / 60) << " a: " << int(Dk[b][t].back() / 60) << "-> Diff: " << int((arrivals[p]) / 60) - int(Dk[b][t].back() / 60) <<"**" << endl;
							}
							//else {
								//cout << "\tdat: " << int((arrivals[p]) / 60) << " a: " << int(Dk[b][t].back() / 60) << "-> Diff: " << int((arrivals[p]) / 60) - int(Dk[b][t].back() / 60) << endl;
							//}
						}
						else {
							cost += c3 * abs(departures[p - R1] - Dk[b][t][l]);
							if (int(departures[p - R1] - Dk[b][t][l]) > d_de || int(Dk[b][t][l] - departures[p - R1]) > d_dl) {
								INFEAS3 = true;
								break;
								//cout << "\tedt: " << int((departures[p - R1]) / 60) << " d: " << int(Dk[b][t][l] / 60) << "-> Diff: " << int((departures[p - R1]) / 60) - int(Dk[b][t][l] / 60) <<"**" <<endl;
							}
							//else {
								//cout << "\tedt: " << int((departures[p - R1]) / 60) << " d: " << int(Dk[b][t][l] / 60) << "-> Diff: " << int((departures[p - R1]) / 60) - int(Dk[b][t][l] / 60) << endl;
							//}
						}
					}

					if (!INFEAS1 && !INFEAS2 && !INFEAS3) {
						//cout << "\n----------  Time between bus departures (min) ----------- \n";
						for (i = 0; i < N && !INFEAS4; i++) {
							IFC.clear();
							for (b = 0; b < B; b++) {
								int xkS1 = xk[b].size();
								for (t = 0; t < xkS1; t++) {
									int xkS2 = xk[b][t].size();
									for (l = 0; l < xkS2; l++) {
										if (xk[b][t][l] == i)IFC.push_back(Dk[b][t][l]);
									}
								}
							}
							FCi = IFC.size();
							std::sort(IFC.begin(), IFC.begin() + FCi);
							//cout << "m_" << i << " -> ";
							for (j = 1; j < FCi; j++) {
								if (int(IFC[j] - IFC[j - 1]) > OGxt) {
									//cout << int((FC[i][j] - FC[i][j - 1]) / 60) << "** \t";
									INFEAS4 = true;
									break;
									//infs = " --> between " + to_string(int(FC[i][j - 1] / 60)) + " and " + to_string(int(FC[i][j] / 60));
								}
								//else {
									//cout << int((FC[i][j] - FC[i][j - 1]) / 60) << " \t";
								//}
							}
							//cout << endl;
						}
						//std::cout << "Elapsed time: " << elapsed_time << "s (initial solution)" << endl;
						//cout << "COST: " << cost << "s (initial solution)\n";
					}
					if (INFEAS1 || INFEAS2 || INFEAS3 || INFEAS4) {
						continue;
					}
				}

				//nhp = 0.05;
				//else logres += "cost: " + to_string(cost) + "\trun time: " + to_string(elapsed_time) + "\t";

				//logres += "   pm1: " + to_string(int(pm1 * 100)) + "%  pm2: " + to_string(int(pm2 * 100)) + "%  pm3: " + to_string(int(pm3 * 100)) + "%\n";
				//infeastemp = 0;
				//cout << "Found! one \n";
				//if (!(INFEAS1 || INFEAS2 || INFEAS3 || INFEAS4) && countp == R) {
					//countFeas++;
					//cout << cost << " Ts: " + to_string(Ts) << endl;
				//cout << " thread: " + to_string(omp_get_thread_num()) + " it: " + to_string(iii) + " cost: " + to_string(cost) + "\n";
#pragma omp critical
				{
					Costb.push_back(cost);
					//logresBest = logres;

					lPM1b.push_back(dPM10);
					lPM2b.push_back(dPM20);
					lPM3b.push_back(dPM30);
					lFPMb.push_back(dFPM0);
					lXTb.push_back(dXT0);
					lCb.push_back(dC0);
				}
				INFEASS0 = true;

				//}
				//if(INFEASS0)cout << "thread: "+ to_string(omp_get_thread_num())+" it: "+ to_string(iii)+" cost: "+to_string(cost)+" FEASS: " +to_string(INFEASS0)+"\n";
			}
			//cout << to_string(iii) + "\n";
		}
		best_cost = INT32_MAX;
		int b_c_i = -1;
		int MM = Costb.size();
		int run = MM;
		if (MM == 0) {
			cout << " --------------------- NO FEASIBLE SOLUTION FOUND ---------------------  \n";
			exit(0);
		}
		for (int f = 0; f < MM; f++) {
			if (best_cost > Costb[f]) {
				best_cost = Costb[f];
				b_c_i = f;
			}
		}
		MM = lPM1b[b_c_i].size();
		lPM1.clear();
		lPM2.clear();
		lPM3.clear();
		lFPM.clear();
		lXT.clear();
		lC.clear();
		for (int i = 0; i < MM; i++) {
			lPM1.push_back(lPM1b[b_c_i][i]);
			lPM2.push_back(lPM2b[b_c_i][i]);
			lPM3.push_back(lPM3b[b_c_i][i]);
			lFPM.push_back(lFPMb[b_c_i][i]);
			lXT.push_back(lXTb[b_c_i][i]);
			lC.push_back(lCb[b_c_i][i]);
		}
		//cout << "Search now !!!\n";
		//#pragma omp parallel  for reduction(*:Ts)
		double cost_c = best_cost, dE = 0;
		//int run = 0;
		MM = int(lPM1.size() * 1.5);

		vector<double> prog;
		vector<int> progit;
		prog.push_back(best_cost);
		progit.push_back(Costb.size());

		while (run < stop_it) {
			lPM1b.clear();
			lPM2b.clear();
			lPM3b.clear();
			lFPMb.clear();
			lXTb.clear();
			lCb.clear();

			MM = lPM1.size();
			Costb.clear();

			//cout << "+++++++++++++++++++++++++++ Search parallel again2\n";
			//int give0 = 0;
			std::atomic<bool> INFEASS(false);
#pragma omp parallel firstprivate(MM,traveltimes, traveltimep, arrivals, departures,closestPS,closestS, S,M,N,B,short_route, best_route,C,TS,OGxt,dw,d_dl,d_de,d_ae,d_al,c1,c2,c3,lPM1,lPM2,lPM3,lFPM,lXT,des)
			{
				//double countInfeas1 = 0, countInfeas2 = 0, countFeas = 0;
				//int s = seed[omp_get_thread_num()];
				default_random_engine& generator = generators[omp_get_thread_num()];
				//generator.seed((omp_get_thread_num()) * 800051150);
				//int iii, stoppp;
				int xt;
				double UBxt;
				//int LL = 30;

				int i, j, b, t, p, l, s;
				double pm1, pm2, pm3, fpm;
				double b_next;
				vector<int> route;
				vector<float> dPM10;
				vector<float> dPM20;
				vector<float> dPM30;
				vector<float> dFPM0;
				vector<float> dXT0;
				vector<float> dC0;
				vector<double> IFC;
				int FCi = 0;
				int temp;
				//double dE;
				vector<double> timetable;
				vector<double> tempt;
				double timewindow, timewindow2;
				//double Arr;

				int trips[B]; //keeps track of which trip each bus is at needs to be updated
				int best_stop;
				double freqN[N];
				double newfreqN[N];

				double bd[B];
				int yk[R][3];

				double startopt;

				int countp, p1, p2, cp1, cp2;
				bool in, in2;
				double threshold, tt;

				double l_arr, l_dep;

				int b_it = 0;

				double minF = INT16_MAX, min_al = INT16_MAX, min_ae = INT16_MAX, min_dl = INT16_MAX, min_de = INT16_MAX;
				int nS, dst;
				double diffa1, diffa2, diffd1, diffd2, diffF;
				double difBD, maxFW, maxRW;//max time to arrive or depart earlier
				//add addtional passenger with DAT
				//*
				double extra = 0, b_extra = 0, xxt = 0;
				int indexpt[R1];
				int indexpt2[R2];
				double temparrivals[R1];
				double tempdept[R2];
				vector<vector<vector<int>>> xk(B);
				vector<vector<vector<double>>> Dk(B);
				double cost = 0, b_cost = 0;
				//int SL;
				bool INFEAS1 = false, INFEAS2 = false, INFEAS3 = false, INFEAS4 = false;
				int nLP = MM;
				int dSize = min(des, nLP - 1);
				uniform_int_distribution<int> destroy(0, nLP - 1);

				int* change1 = new int[dSize];
				int key1 = 0;
				//vector<int> change2;
				int* change2 = new int[dSize];
				int key2 = 0;
				//vector<int> change3;
				int* change3 = new int[dSize];
				int key3 = 0;
				//vector<int> change4;
				int* change4 = new int[dSize];
				int key4 = 0;
				//vector<int> change5;
				int* change5 = new int[dSize];
				int key5 = 0;

				int* change6 = new int[dSize];
				int key6 = 0;
				//change1.push_back(key1);
				//change2.push_back(key2);
				//change3.push_back(key3);
				//change4.push_back(key4);
				//change5.push_back(key5);
				//cout << lPM1.size() << endl;
				int* endC1 = change1 + dSize;
				int* endC2 = change2 + dSize;
				int* endC3 = change3 + dSize;
				int* endC4 = change4 + dSize;
				int* endC5 = change5 + dSize;
				int* endC6 = change6 + dSize;
				float Cc = 0.5;
				//cout << "check 1\n";

				//generator.seed(7851 * (omp_get_thread_num()));
				while (!INFEASS) {
					for (s = 0; s < B; s++) {
						xk[s].clear();
						Dk[s].clear();
					}
					//std::cout << "\n************************************************************************** Run number: " << run + 1 << endl;
					//logres = "";
					for (p = 0; p < R; p++) {
						yk[p][0] = -1;
						yk[p][1] = -1;
						yk[p][2] = -1;

					}
					for (p = 0; p < R1; p++) {
						indexpt[p] = p;
						temparrivals[p] = arrivals[p];
					}

					for (p = 0; p < R2; p++) {
						indexpt2[p] = p;
						tempdept[p] = departures[p];
					}
					quickSort(indexpt, temparrivals, 0, R1 - 1);
					quickSort(indexpt2, tempdept, 0, R2 - 1);
					best_stop = 0;
					startopt = tempdept[0] - 1000;
					threshold = 0, tt = 0;

					cost = 0, b_cost = 0;
					route.clear();

					timetable.clear();
					tempt.clear();
					//cout << "check\n";
					dPM10.clear();
					dPM20.clear();
					dPM30.clear();
					dFPM0.clear();
					dXT0.clear();
					dC0.clear();
					//cout << "  thread number: " + to_string(omp_get_thread_num()) + " loop number: " + to_string(iii + 1) + " \n";

					//vector<int> change1;
					key1 = destroy(generator);
					key2 = destroy(generator);
					key3 = destroy(generator);
					key4 = destroy(generator);
					key5 = destroy(generator);
					key6 = destroy(generator);
					change1[0] = key1;
					change2[0] = key2;
					change3[0] = key3;
					change4[0] = key4;
					change5[0] = key5;
					change6[0] = key6;
					//change1.push_back(key1);
					//change2.push_back(key2);
					//change3.push_back(key3);
					//change4.push_back(key4);
					//change5.push_back(key5);
					//cout << lPM1.size() << endl;
					for (i = 1; i < dSize; i++) {
						key1 = destroy(generator);
						while (std::find(change1, endC1, key1) != endC1) key1 = destroy(generator);
						change1[i] = key1;

						key2 = destroy(generator);
						while (std::find(change2, endC2, key2) != endC2) key2 = destroy(generator);
						change2[i] = key2;

						key3 = destroy(generator);
						while (std::find(change3, endC3, key3) != endC3) key3 = destroy(generator);
						change3[i] = key3;

						key4 = destroy(generator);
						while (std::find(change4, endC4, key4) != endC4) key4 = destroy(generator);
						change4[i] = key4;

						key5 = destroy(generator);
						while (std::find(change5, endC5, key5) != endC5) key5 = destroy(generator);
						change5[i] = key5;

						key6 = destroy(generator);
						while (std::find(change6, endC6, key6) != endC6) key6 = destroy(generator);
						change6[i] = key6;
					}
					for (b = 0; b < nLP; b++) {
						if (std::find(change1, endC1, b) != endC1) {
							normal_distribution<float> nPM1(lPM1[b], nhp);
							//cout << "check 2\n";
							pm1 = nPM1(generator);
							if (pm1 > 1)pm1 = 1;
							if (pm1 < 0)pm1 = 0;
							pm1 = round(pm1 * 20.0) / 20.0;
							dPM10.push_back(pm1);
						}
						else {
							pm1 = lPM1[b];
							dPM10.push_back(pm1);
						}
						if (std::find(change2, endC2, b) != endC2) {
							normal_distribution<float> nPM2(lPM2[b], nhp);

							pm2 = nPM2(generator);

							if (pm2 > 1)pm2 = 1;
							if (pm2 < 0)pm2 = 0;
							pm2 = round(pm2 * 20.0) / 20.0;
							dPM20.push_back(pm2);
						}
						else {
							pm2 = lPM2[b];
							dPM20.push_back(pm2);
						}
						if (std::find(change3, endC3, b) != endC3) {
							normal_distribution<float> nPM3(lPM3[b], nhp);

							pm3 = nPM3(generator);

							if (pm3 > 1)pm3 = 1;
							if (pm3 < 0)pm3 = 0;
							pm3 = round(pm3 * 20.0) / 20.0;
							dPM30.push_back(pm3);
						}
						else {
							pm3 = lPM3[b];
							dPM30.push_back(pm3);
						}
						if (std::find(change4, endC4, b) != endC4) {
							normal_distribution<float> nFPM(lFPM[b], nhp);

							fpm = nFPM(generator);

							if (fpm > 1)fpm = 1;
							if (fpm < 0)fpm = 0;
							fpm = round(fpm * 20.0) / 20.0;
							dFPM0.push_back(fpm);
						}
						else {
							fpm = lFPM[b];
							dFPM0.push_back(fpm);
						}
						if (std::find(change5, endC5, b) != endC5) {
							normal_distribution<float> nXT(lXT[b], nhp);
							xxt = nXT(generator);

							if (xxt > 1)xxt = 1;
							//if (xxt < 0.4)xxt = PlanB3(generator);

							if (xxt < 0.4)xxt = PlanB3(generator);

							xxt = round(xxt * 20.0) / 20.0;
							dXT0.push_back(xxt);
							xt = int(xxt * OGxt);
						}
						else {
							xxt = lXT[b];
							dXT0.push_back(xxt);
							xt = int(xxt * OGxt);
						}

						if (std::find(change6, endC6, b) != endC6) {
							normal_distribution<float> nC(lC[b], nhp);
							Cc = nC(generator);

							if (Cc > 1)Cc = 1;
							//if (xxt < 0.4)xxt = PlanB3(generator);

							if (Cc < 0.25)Cc = 0.25;

							Cc = round(Cc * 20.0) / 20.0;
							dC0.push_back(Cc);
							C = max(5, int(Cc * C_OG));
						}
						else {
							Cc = lC[b];
							dC0.push_back(Cc);
							C = max(5, int(Cc * C_OG));
						}
					}
					l_arr = arrivals[indexpt[0]], l_dep = departures[indexpt2[0]] + short_route * 0.75;
					//logres += "Run: " + to_string(run + 1) + "\t";
					//start_time = clock();
					//************************************Initial Solution***************************************
					for (i = 0; i < N; i++) {
						freqN[i] = -INT16_MAX;
					}
					countp = p1 = p2 = 0;
					for (b = 0; b < B; b++) {
						trips[b] = 0;
						bd[b] = startopt;//start of optimization
					}
					timetable.push_back(0);

					p1 = p2 = countp = 0;
					b = 0;
					b_next = 0.0;
					//cout << " END of PH: " << int(TS + startopt) / 60 << endl;
					b_it = -1;
					//cout << "  thread number: " + to_string(omp_get_thread_num()) + " loop number: " + to_string(iii + 1) + " \n";
					//if (!INFEASS) {

					while (timetable.back() < TS + startopt && p1 + p2 < R) {//until TS is over+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++	
						b_it++;
						if (b_it < nLP) {
							pm1 = dPM10[b_it];
							pm2 = dPM20[b_it];
							pm3 = dPM30[b_it];
							fpm = dFPM0[b_it];
							xt = int(dXT0[b_it] * OGxt);
							C = max(5, int(dC0[b_it] * C_OG));
						}
						else {
							pm1 = PM(generator);
							pm2 = PM(generator);
							pm3 = PM(generator);
							fpm = PM(generator);

							if (pm1 > 1)pm1 = 1;
							if (pm1 < 0)pm1 = 0;
							if (pm2 > 1)pm2 = 1;
							if (pm2 < 0)pm2 = 0;
							if (pm3 > 1)pm3 = 1;
							if (pm3 < 0)pm3 = 0;
							if (fpm > 1)fpm = 1;
							if (fpm < 0)fpm = 0;

							UBxt = gXT(generator);
							xt = int(UBxt * OGxt);

							dPM10.push_back(pm1);
							dPM20.push_back(pm2);
							dPM30.push_back(pm3);
							dFPM0.push_back(fpm);
							dXT0.push_back(UBxt);

							float Cc = gC(generator);
							dC0.push_back(Cc);

							C = max(5, int(Cc * C_OG));
						}


						//xt = OGxt;
						//if (infeastemp > 100) fpm = 1;
						//cout << " xt: " << xt / 60 << endl;
						//determine which bus is available first
						b = iMin(bd, B);
						b_next = iMin2(bd, B);
						//cout << "++++++ || Bus: " << b << " bd: " << int(bd[b] / 60) << " trip: " << trips[b] << " || ++++++\n";
						//for (i = 0; i < B; i++) cout << int(bd[i] / 60) << " ";
						//cout << endl;
						//cout << "bd1: " << int(bd[b]/60) << " bd2: " << int(b_next/60) << endl;
						//Make route only with mandatory stops, ASAP
						route.clear();
						timetable.clear();
						tempt.clear();
						tt = bd[b];
						timetable.push_back(tt);
						route.push_back(0);
						for (i = 1; i < N; i++) {
							route.push_back(i);
							tt += traveltimes[i - 1][i];
							timetable.push_back(tt);
						}
						//Assignement: First look at R1
						timewindow = timewindow2 = INT32_MAX;
						cp1 = cp2 = 0;

						//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ CASE I ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
						if (l_arr < l_dep && p1 < R1 || p2 == R2) {
							//cout << "R1" << endl;
							p = 0;
							while (cp1 + cp2 < C && countp < R && p < R1 && (int)(arrivals[indexpt[p]] - timewindow) <= d_ae + d_al) {
								//cout << " check start\n";
								//cout << cp1 + cp2 << "<" << C << "  " << countp << "<" << R << "  " << (int)(arrivals[indexpt[p]] - timewindow) << "< " << d_ae + d_al << endl;
								if (traveltimep[indexpt[p]][closestPS[indexpt[p]][0]] > dw) {
									std::cout << " Infeasible solution, for walking times " << endl;
									exit(0);
								}
								if (temparrivals[indexpt[p]] == -1) {
									//cout << "passenger already in solution \n";
									//cout << "p: " << p << " indexpt: " << indexpt[p] << endl;
									p++;
									if (p > R1)break;
									continue;//if this is already in the solution, continue to next passenger
								}
								if (cp1 == 0)timewindow = arrivals[indexpt[p]];

								//Assign bus stop to passenger
								//choose best stop and update route
								if (cp1 == 0) {
									//cout << " check 2 \n";
									best_stop = bestStop(timetable, route, traveltimes, traveltimep, closestPS, indexpt[p], N,
										dw, best_route, M, S, bd[b], freqN, xt, best_stop, arrivals[indexpt[p]],
										arrivals[indexpt[p]], d_ae, d_al, yk, arrivals, R1, R2, b, trips[b], b_next, fpm);
									//cout << " check stop 0\n";
									if (best_stop == -1) {
										//cout << "passenger " << indexpt[p] << " --> Skip this one, not good for bus stop\n";
										p++;
										//cout << "Next passenger " << p1 << endl;
										if (p > R1)break;
										continue;
									}
									//cout << " --- FIRST passenger added : p= " << indexpt[p] << "\n";
									//Assign bus to passenger
									yk[indexpt[p]][0] = b;
									yk[indexpt[p]][1] = trips[b];
									yk[indexpt[p]][2] = best_stop;
									temparrivals[indexpt[p]] = -1;
									tempt.push_back(arrivals[indexpt[p]]);
									p++;
									p1++;
									cp1++;
									countp++;
									if (p > R1)break;
								}
								else {
									temp = bestStop(timetable, route, traveltimes, traveltimep, closestPS, indexpt[p], N, dw,
										best_route, M, S, bd[b], freqN, xt, best_stop, tempt.back(),
										arrivals[indexpt[p]], d_ae, d_al, yk, arrivals, R1, R2, b, trips[b], b_next, fpm);
									//cout << " check stop n: " << temp <<"\n";
									if (temp == -1) {
										//cout << "passenger " << indexpt[p] << " --> Skip this one, not good for bus stop\n";
										p++;//next stop of a passenger with later edt is before a previous stop with a passenger with earlier edt, not possible OR edts are too different
										if (p > R1)break;
										continue;
									}
									else {
										// time to go from prev to next stop on a full route 
										best_stop = temp;
										//Assign bus to passenger
										yk[indexpt[p]][0] = b;
										yk[indexpt[p]][1] = trips[b];
										yk[indexpt[p]][2] = best_stop;
										temparrivals[indexpt[p]] = -1;
										tempt.push_back(arrivals[indexpt[p]]);
										p++;
										p1++;
										cp1++;
										countp++;
										if (p > R1)break;
										//cout << "-- NEXT passenger added : p= " << indexpt[p] << "\n";
										//cout << " indexpt: " << indexpt[p] << " arrivals p: " << arrivals[indexpt[p]] <<  endl;
										//cout << " p: " << p << " indexpt: " << indexpt[p] << endl;
									}
								}
							}
							//cout << " check end\n";
							//cout << "timetable:" << timetable.size() << " route: " << route.size() << " Passengers added: " << tempt.size() << endl;

						}
						// //++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ CASE II ++++++++++++++++++++++++++++++++++++++++++++ Now look at R2
						//*
						if ((l_arr >= l_dep && p2 < R2) || cp1 == 0) {
							//cout << "R2" << endl;
							//cout << timetable.size() << endl;
							timetable.clear();
							tt = bd[b];
							timetable.push_back(tt);
							for (i = 1; i < N; i++) {
								tt += traveltimes[i - 1][i];
								timetable.push_back(tt);
							}

							p = 0;
							while (cp2 < C && countp < R && p < R2) {
								//cout << p2 << "<" << C << "  " << countp << "<" << R << " " << p << "< " << R2 << endl;
								//cout << "passenger " << indexpt2[p] + R1 << "  ------------- \n";
								if (traveltimep[R1 + indexpt2[p]][closestPS[R1 + indexpt2[p]][0]] > dw) {
									std::cout << " Infeasible solution, for walking times " << endl;
									exit(0);
								}
								if (tempdept[indexpt2[p]] == -1) {
									//cout << "passenger already in solution \n";
									p++;
									continue;//if this is already in the solution, continue to next passenger
								}
								t = 0;
								int ttS = timetable.size();
								for (i = 0; i < ttS; i++) {
									if (route[i] < N) {
										newfreqN[t] = timetable[i];
										t++;
									}
								}
								if (cp2 == 0) {
									best_stop = bestStop2(timetable, route, traveltimes, traveltimep, closestPS, indexpt2[p] + R1, N,
										dw, best_route, M, S, bd[b], freqN, newfreqN, xt, best_stop, departures[indexpt2[p]],
										departures[indexpt2[p]], d_de, d_dl, yk, departures, R1, R2, b, trips[b], b_next, fpm);
									if (best_stop == -1) {
										//cout << "passenger " << indexpt2[p] + R1 << " --> Skip this one, not good for bus stop\n";
										p++;
										//cout << "Next passenger " << p1 << endl;
										continue;
									}
									//cout << " --- FIRST passenger added : p= " << indexpt2[p] + R1 << "\n";
									//Assign bus to passenger
									yk[R1 + indexpt2[p]][0] = b;
									yk[R1 + indexpt2[p]][1] = trips[b];
									//Assign bus stop to passenger
									//choose best stop and update route
									//cout << "  Best stop: " << best_stop << endl;
									//cout << "Passenger: " << R1 + indexpt2[p] << " edt: " << int(departures[indexpt2[p]] / 60) << " stop: " << best_stop << endl;
									tempt.push_back(departures[indexpt2[p]]);
									tempdept[indexpt2[p]] = -1;
									yk[R1 + indexpt2[p]][2] = best_stop;
									cp2++;
									p2++;
									countp++;
									p++;
								}
								else {
									temp = bestStop2(timetable, route, traveltimes, traveltimep, closestPS, indexpt2[p] + R1, N, dw,
										best_route, M, S, bd[b], freqN, newfreqN, xt, best_stop, tempt.back(),
										departures[indexpt2[p]], d_de, d_dl, yk, departures, R1, R2, b, trips[b], b_next, fpm);

									if (temp == -1) {
										//cout << "Passenger: " << R1 + indexpt2[p] << " edt: "<< int(departures[indexpt2[p]] / 60) << "Skip this one, not good for bus stop\n";
										p++;//next stop of a passenger with later edt is before a previous stop with a passenger with earlier edt, not possible OR edts are too different
										continue;
									}
									else {
										// time to go from prev to next stop on a full route 
										best_stop = temp;
										//Assign bus to passenger
										yk[R1 + indexpt2[p]][0] = b;
										yk[R1 + indexpt2[p]][1] = trips[b];
										//Assign bus stop to passenger
										yk[R1 + indexpt2[p]][2] = best_stop;
										//cout << "Passenger: " << R1 + indexpt2[p] << " edt: " << int(departures[indexpt2[p]] / 60) << " stop: " << best_stop << endl;
										tempt.push_back(departures[indexpt2[p]]);
										tempdept[indexpt2[p]] = -1;
										cp2++;
										p2++;
										countp++;
										p++;
										//cout << "-- NEXT passenger added : p= " << indexpt2[p] + R1 << "\n";
									}
								}
							}
							int temptS = tempt.size();
							if (p1 < R1 && l_arr >= l_dep && temptS == 0) {
								//++++++++++++++++++++++++++++++++ CASE I ++++++++++++++++++++++++++++++++++++++++++++
								//cout << "R1 again" << endl;
								p = 0;
								while (cp1 + cp2 < C && countp < R && p < R1 && (int)(arrivals[indexpt[p]] - timewindow) <= d_ae + d_al) {
									//cout << cp1 + cp2 << "<" << C << "  " << countp << "<" << R << "  " << (int)(arrivals[indexpt[p]] - timewindow) << "< " << d_ae + d_al << endl;
									if (traveltimep[indexpt[p]][closestPS[indexpt[p]][0]] > dw) {
										std::cout << " Infeasible solution, for walking times " << endl;
										exit(0);
									}
									if (temparrivals[indexpt[p]] == -1) {
										//cout << "passenger already in solution \n";
										//cout << "p: " << p << " indexpt: " << indexpt[p] << endl;
										p++;
										if (p > R1)break;
										continue;//if this is already in the solution, continue to next passenger
									}
									if (cp1 == 0)timewindow = arrivals[indexpt[p]];
									//Assign bus stop to passenger
									//choose best stop and update route
									if (cp1 == 0) {
										best_stop = bestStop(timetable, route, traveltimes, traveltimep, closestPS, indexpt[p], N,
											dw, best_route, M, S, bd[b], freqN, xt, best_stop, arrivals[indexpt[p]],
											arrivals[indexpt[p]], d_ae, d_al, yk, arrivals, R1, R2, b, trips[b], b_next, fpm);
										//cout << " check\n";
										if (best_stop == -1) {
											//cout << "passenger " << indexpt[p]  << " --> Skip this one, not good for bus stop\n";
											p++;
											//cout << "Next passenger " << p1 << endl;
											if (p > R1)break;
											continue;
										}
										//cout << " --- FIRST passenger added\n";
										//Assign bus to passenger
										yk[indexpt[p]][0] = b;
										yk[indexpt[p]][1] = trips[b];
										yk[indexpt[p]][2] = best_stop;
										temparrivals[indexpt[p]] = -1;
										tempt.push_back(arrivals[indexpt[p]]);
										p++;
										p1++;
										cp1++;
										countp++;
										if (p > R1)break;
										//cout << " --- FIRST passenger added : p= " << indexpt[p] << "\n";
									}
									else {
										temp = bestStop(timetable, route, traveltimes, traveltimep, closestPS, indexpt[p], N, dw,
											best_route, M, S, bd[b], freqN, xt, best_stop, tempt.back(),
											arrivals[indexpt[p]], d_ae, d_al, yk, arrivals, R1, R2, b, trips[b], b_next, fpm);
										//cout << " check\n";
										if (temp == -1) {
											//cout << "passenger " << indexpt[p] << " --> Skip this one, not good for bus stop\n";
											p++;//next stop of a passenger with later edt is before a previous stop with a passenger with earlier edt, not possible OR edts are too different
											if (p > R1)break;
											continue;

										}
										else {
											// time to go from prev to next stop on a full route 
											best_stop = temp;
											//Assign bus to passenger
											yk[indexpt[p]][0] = b;
											yk[indexpt[p]][1] = trips[b];
											yk[indexpt[p]][2] = best_stop;
											temparrivals[indexpt[p]] = -1;
											tempt.push_back(arrivals[indexpt[p]]);
											p++;
											p1++;
											cp1++;
											countp++;
											if (p > R1)break;
											//cout << "-- NEXT passenger added : p= " << indexpt[p] << "\n";
										}
									}

								}

							}
							//cout << "timetable:" << timetable.size() << " route: " << route.size() << " Passengers added: " << tempt.size() << endl;
						}
						//*/
						int temptS = tempt.size();
						if (temptS == 0) {
							timetable.clear();
							timetable.push_back(max(freqN[0] + xt, bd[b]));
							tt = -1;
							for (i = 1; i < N; i++) {
								timetable.push_back(timetable[i - 1] + traveltimes[i - 1][i]);
								if (timetable[i] - freqN[i] > tt)tt = timetable[i] - freqN[i];
							}
							if (tt > xt) {
								for (i = 0; i < N; i++) {
									timetable[i] -= (tt - xt);
								}
							}
						}
						else {
							//add addtional passenger with DAT

							minF = INT16_MAX, min_al = INT16_MAX, min_ae = INT16_MAX, min_dl = INT16_MAX, min_de = INT16_MAX;
							nS = timetable.size() - 1;

							for (p = 0; p < R1; p++) {
								if (yk[p][0] == b && yk[p][1] == trips[b]) {
									//cout << "passenger " << p  << ": dat=" << int(arrivals[p] / 60) << " arr=" << int(timetable[nS] / 60) << endl;
									diffa1 = d_ae - (arrivals[p] - timetable[nS]);
									diffa2 = d_al - (timetable[nS] - arrivals[p]);
									if (arrivals[p] >= timetable[nS] && min_ae > diffa1) {
										min_ae = diffa1;
									}
									if (arrivals[p] <= timetable[nS] && min_al > diffa2) {
										min_al = diffa2;
									}
								}
							}

							dst = -1;
							int routeS = route.size(), timetableS = timetable.size();
							for (p = 0; p < R2; p++) {
								dst = -1;
								for (i = 0; i < routeS; i++) {
									if (yk[p + R1][0] == b && yk[p + R1][1] == trips[b] && yk[p + R1][2] == route[i]) {
										dst = i;
										break;
									}
								}
								if (dst != -1) {
									//cout << "passenger " << p +R1 << ": edt=" << int(departures[p] / 60) << " dept=" << int(timetable[dst] / 60) << " at stop: " <<route[dst] << endl;
									diffd1 = d_de - (departures[p] - timetable[dst]);
									diffd2 = d_dl - (timetable[dst] - departures[p]);
									if (departures[p] >= timetable[dst] && min_de > diffd1) {
										min_de = diffd1;
									}
									if (departures[p] <= timetable[dst] && min_dl > diffd2) {
										min_dl = diffd2;
									}
								}
							}
							if (freqN[0] != -INT16_MAX) {
								for (i = 0; i < timetableS; i++) {
									if (route[i] < N && freqN[route[i]] < timetable[i]) {
										diffF = xt - (timetable[i] - freqN[route[i]]);
										if (minF > diffF) minF = diffF;
									}
								}
							}

							//cout << " min diff al: " << int(min_al/60) << " min diff dl: " << int(min_dl/60) << " min diff Freq: " << int(minF / 60) << endl;
							//cout << " min diff ae: " << int(min_ae/60) << " min diff de: " << int(min_de/60) << endl;
							difBD = timetable[0] - bd[b];
							maxFW = min(min(min_al, min_dl), minF) * pm1; // max time to depart later 
							maxRW = min(min(min_ae, min_de), difBD) * pm2;//max time to arrive or depart earlier
							//add addtional passenger with DAT
							//*
							extra = 0;
							//cout << "Max time FW: " << int(maxFW/60) << " max time RW: " << int(maxRW/60) << "\nStart R1\n";
							//cout << "R1: " << cp1 << " R2: " << cp2 << endl;

							for (p = 0; p < R1; p++) {
								if (temparrivals[p] != -1) {
									//cout << "for p_" << p << " dat: "<<arrivals[p]/60<< " arrval: " << timetable.back()/60<<endl;
									i = 0;
									b_cost = INT32_MAX;
									s = -1;
									if (arrivals[p] >= timetable.back()) {
										if (arrivals[p] - timetable.back() <= d_ae) extra = 0;
										else extra = (arrivals[p] - timetable.back()) - d_ae;
									}
									else {
										if (timetable.back() - arrivals[p] <= d_al) extra = 0;
										else extra = d_al - (timetable.back() - arrivals[p]);
									}
									while (traveltimep[p][closestPS[p][i]] < dw * pm3) {
										//cout << "try stop: " << closestPS[p][i] << endl;
										routeS = route.size() - 1;
										for (t = 0; t < routeS; t++) {
											in = false;
											if (closestPS[p][i] == route[t]) {
												in = true;
												break;
											}
										}
										in2 = false;
										if (in && arrivals[p] - timetable.back() - maxFW <= d_ae && timetable.back() - maxRW - arrivals[p] <= d_al) {
											in2 = true;
										}

										if (in2 && cp1 + cp2 < C) {
											//cout << " ++++++++++++ passenger " << p << " (dat=" << int(arrivals[p] / 60) << ") stop " << closestPS[p][i] << " (tt=" << int(timetable.back() / 60) << ") possible extra: " << int(extra / 60) << endl;
											cost = c2 * traveltimep[p][closestPS[p][i]] + c3 * abs(timetable.back() - arrivals[p]) + c3 * (cp1 + cp2) * (abs(extra));
											if (b_cost > cost) {
												b_cost = cost;
												s = route[t];
											}
										}
										i++;
									}
									if (b_cost != INT32_MAX) {
										//cout << "Added DAT \t";
										//cout << "Passenger: " << p << " arr: " << arrivals[p] / 60 << endl;
										yk[p][0] = b;
										yk[p][1] = trips[b];
										yk[p][2] = s;
										//cout << "Passenger: " << R1 + p << endl;
										temparrivals[p] = -1;//indicate this passenger is onboard already
										p1++;
										cp1++;
										countp++;
										//break;

										//update timetable
										//cout << " move tt with " << int(extra / 60) << endl;
										timetableS = timetable.size();
										for (l = 0; l < timetableS; l++) {
											timetable[l] += extra;
										}
										//update intermediary parameters
										minF = INT16_MAX, min_al = INT16_MAX, min_ae = INT16_MAX, min_dl = INT16_MAX, min_de = INT16_MAX;
										nS = timetable.size() - 1;
										for (int p11 = 0; p11 < R1; p11++) {
											if (yk[p11][0] == b && yk[p11][1] == trips[b]) {
												diffa1 = d_ae - (arrivals[p11] - timetable[nS]);
												diffa2 = d_al - (timetable[nS] - arrivals[p11]);
												if (arrivals[p11] >= timetable[nS] && min_ae > diffa1) {
													min_ae = diffa1;
												}
												if (arrivals[p11] <= timetable[nS] && min_al > diffa2) {
													min_al = diffa2;
												}
											}
										}
										for (int p22 = 0; p22 < R2; p22++) {
											dst = -1;
											routeS = route.size();
											for (l = 0; l < routeS; l++) {
												if (yk[p22 + R1][0] == b && yk[p22 + R1][1] == trips[b] && yk[p22 + R1][2] == route[l]) {
													dst = l;
													break;
												}
											}
											if (dst != -1) {
												diffd1 = d_de - (departures[p22] - timetable[dst]);
												diffd2 = d_dl - (timetable[dst] - departures[p22]);
												if (departures[p22] >= timetable[dst] && min_de > diffd1) {
													min_de = diffd1;
												}
												if (departures[p22] <= timetable[dst] && min_dl > diffd2) {
													min_dl = diffd2;
												}
											}
										}
										if (freqN[0] != -INT16_MAX) {
											timetableS = timetable.size();
											for (l = 0; l < timetableS; l++) {
												if (route[l] < N && freqN[route[l]] < timetable[l]) {
													diffF = xt - (timetable[l] - freqN[route[l]]);
													if (minF > diffF) minF = diffF;
												}
											}
										}
										//cout << " min diff al: " << int(min_al/60) << " min diff dl: " << int(min_dl/60) << endl;
										//cout << " min diff ae: " << int(min_ae/60) << " min diff de: " << int(min_de/60) << " min diff Freq: " << int(minF/60) << endl;
										difBD = timetable[0] - bd[b];
										maxFW = min(min(min_al, min_dl), minF) * pm1; // max time to depart later 
										maxRW = min(min(min_ae, min_de), difBD) * pm2;//max time to arrive or depart earlier
										//cout << "  Added passenger " << p << " --> NEW Max time FW: " << int(maxFW/60) << " max time RW: " << int(maxRW/60) << endl;

									}
								}
							}

							//add addtional passenger with EDT
							///*
							//cout << "Start R2\nNEW Max time FW : " << int(maxFW / 60) << " max time RW : " << int(maxRW / 60) << endl;
							b_extra = 0;
							for (p = 0; p < R2; p++) {
								if (tempdept[p] != -1) {
									//cout << "try p_" << p+R1 << " dept: "<<departures[p]/60<<endl;
									i = 0;
									b_cost = INT32_MAX;
									s = -1;
									while (traveltimep[R1 + p][closestPS[p + R1][i]] < dw * pm3) {
										routeS = route.size() - 1;
										//if (R1 + p == 36)cout << closestPS[p + R1][i] << endl;
										for (t = 0; t < routeS; t++) {
											in = false;
											if (closestPS[p + R1][i] == route[t]) {
												//cout << "bus stop " << closestPS[p + R1][i] << " position " << t << endl;
												in = true;
												break;
											}
										}
										in2 = false;
										if (in && departures[p] - timetable[t] - maxFW <= d_de && timetable[t] - maxRW - departures[p] <= d_dl) {
											in2 = true;
										}
										//if (in2) cout << "bus stop " << closestPS[p + R1][i] << " position " << t << " length of tt: " << timetable.size() << endl;

										if (in2 && cp1 + cp2 < C) {
											//cout << "bus stop " << closestPS[p + R1][i] << " position " << t << " length of tt: " << timetable.size() << endl;
											if (departures[p] >= timetable[t]) {
												if (departures[p] - timetable[t] <= d_de)extra = 0;
												else extra = (departures[p] - timetable[t]) - d_de;
											}
											else {
												if (timetable[t] - departures[p] <= d_dl)extra = 0;
												else extra = d_dl - (timetable[t] - departures[p]);
											}
											//cout << "walking time " << traveltimep[R1 + p][closestPS[p + R1][i]] / 60 << endl;
											//cout << " ++++++++++++ passenger " << p+R1 << " (edt="<< int(departures[p]/60) << ") stop " << closestPS[p + R1][i] <<" (tt="<< int(timetable[t]/60) << ") possible extra: " << int(extra / 60)<< endl;
											cost = c2 * traveltimep[R1 + p][closestPS[p + R1][i]] + c3 * abs(timetable[t] - departures[p]) + c3 * (cp1 + cp2) * (abs(extra));
											if (b_cost > cost) {
												b_cost = cost;
												s = route[t];
												b_extra = extra;
											}
										}
										i++;
									}
									if (b_cost != INT32_MAX) {
										//cout << "Added EDT \t";
										//cout << "Passenger: " << R1 + p << " dept: " << departures[p] / 60 << endl;
										yk[p + R1][0] = b;
										yk[p + R1][1] = trips[b];
										yk[p + R1][2] = s;
										//cout << "Passenger: " << R1 + p << endl;
										tempdept[p] = -1;//indicate this passenger is onboard already
										p2++;
										cp2++;
										countp++;
										//break;
										//update timetable
										//cout << " move tt with " << int(b_extra / 60) << endl;
										timetableS = timetable.size();
										for (l = 0; l < timetableS; l++) {
											timetable[l] += b_extra;
										}
										//update intermediary parameters
										minF = INT16_MAX, min_al = INT16_MAX, min_ae = INT16_MAX, min_dl = INT16_MAX, min_de = INT16_MAX;
										nS = timetable.size() - 1;
										for (int p11 = 0; p11 < R1; p11++) {
											if (yk[p11][0] == b && yk[p11][1] == trips[b]) {
												diffa1 = d_ae - (arrivals[p11] - timetable[nS]);
												diffa2 = d_al - (timetable[nS] - arrivals[p11]);
												if (arrivals[p11] >= timetable[nS] && min_ae > diffa1) {
													min_ae = diffa1;
												}
												if (arrivals[p11] <= timetable[nS] && min_al > diffa2) {
													min_al = diffa2;
												}
											}
										}
										for (int p22 = 0; p22 < R2; p22++) {
											dst = -1;
											routeS = route.size();
											for (l = 0; l < routeS; l++) {
												if (yk[p22 + R1][0] == b && yk[p22 + R1][1] == trips[b] && yk[p22 + R1][2] == route[l]) {
													dst = l;
													break;
												}
											}
											if (dst != -1) {
												diffd1 = d_de - (departures[p22] - timetable[dst]);
												diffd2 = d_dl - (timetable[dst] - departures[p22]);
												if (departures[p22] >= timetable[dst] && min_de > diffd1) {
													min_de = diffd1;
												}
												if (departures[p22] <= timetable[dst] && min_dl > diffd2) {
													min_dl = diffd2;
												}
											}
										}
										if (freqN[0] != -INT16_MAX) {
											timetableS = timetable.size();
											for (l = 0; l < timetableS; l++) {
												if (route[l] < N && freqN[route[l]] < timetable[l]) {
													diffF = xt - (timetable[l] - freqN[route[l]]);
													if (minF > diffF) minF = diffF;
												}
											}
										}

										difBD = timetable[0] - bd[b];
										maxFW = min(min(min_al, min_dl), minF) * pm1; // max time to depart later 
										maxRW = min(min(min_ae, min_de), difBD) * pm2;//max time to arrive or depart earlier
										//cout << "    min diff al: " << int(min_al/60) << " min diff dl: " << int(min_dl/60) << endl;
										//cout << "    min diff ae: " << int(min_ae/60) << " min diff de: " << int(min_de/60) << " min diff Freq: " << int(minF/60) << endl;
										//cout << "  Added passenger " << p + R1 << " --> NEW Max time FW: " << int(maxFW / 60) << " max time RW: " << int(maxRW / 60) << endl;
									}
								}
							}
							//cout << "AFTER --> R1: " << cp1 << " R2: " << cp2 << endl;
							//*/

						}
						//cout << "R1+R2 done  Nroute: " << route.size() << " N_timetable: " << timetable.size() << endl;
						//update trip of bus b
						trips[b]++;
						//update bd of bus b
						bd[b] = timetable.back() + short_route;
						//update varaibles
						xk[b].push_back(route);
						Dk[b].push_back(timetable);
						//update frequency at mandatory 
						//cout << "xt constraints: \n";
						//cout << " ******* TIMETABLE: ";
						int timetableS = timetable.size();
						for (i = 0; i < timetableS; i++) {
							if (route[i] < N && (freqN[route[i]] < timetable[i] || freqN[route[i]] - timetable[i] > xt)) {
								//if(timetable[i] - freqN[route[i]]+1>xt) cout << int((timetable[i]- freqN[route[i]])) / 60 << " (s: "<< route[i]<< ") ";
								freqN[route[i]] = timetable[i];
								t++;
							}
							//cout << int(timetable[i] / 60) << " ";
						}
						//cout << endl << " FreqN: " ;
						//for (i = 0; i < N; i++) {
							//cout << int(freqN[i] / 60) << "  ";
						//}
						//cout << endl;
						/*
						cout << " timetable: \n";
						for (i = 0; i < timetable.size(); i++) {
							cout << int(timetable[i] / 60) << " ";
						}
						cout << endl;
						//*/
						//cout << "Passengers added to bus: " << cp1 + cp2 << endl;
						//cout << endl << "Number of passenger assigned: R2: " << p2 << " R1: " << p1 << endl << endl;
						if (p2 < R2) {
							for (p = 0; p < R2; p++) {
								if (tempdept[indexpt2[p]] != -1) {
									l_dep = departures[indexpt2[p]] + 0.75 * short_route;
									break;
								}
							}
						}
						if (p1 < R1) {
							for (p = 0; p < R1; p++) {
								if (temparrivals[indexpt[p]] != -1) {
									l_arr = arrivals[indexpt[p]];
									break;
								}
							}
						}
					}
					//elapsed_time = (double)(clock() - start_time) / CLK_TCK;
					//cout << "  thread number: " + to_string(omp_get_thread_num()) + " loop number: " + to_string(iii + 1) + " \n";
					//iii++;
					INFEAS1 = false, INFEAS2 = false, INFEAS3 = false, INFEAS4 = false;
					if (countp != R) {
						//countInfeas1++;
						//infeastemp++;
						continue;
					}
					else {
						//if(BG==true) cout << "Fixed one\n";
						//Objective function value
						cost = 0;
						for (p = 0; p < R; p++) {
							b = yk[p][0];
							t = yk[p][1];
							s = yk[p][2];
							//if (p == R1) cout << endl;
							//cout << "Passenger: " << p << "\tBus_" << b << " Trip_" << t << " Stop_" << s;
							//continue;
							//Walking for all passengers
							cost += c2 * traveltimep[p][s];
							if (traveltimep[p][s] > dw) {
								INFEAS1 = true;
								break;
								//cout << "\twalking: " << int(traveltimep[p][s] / 60) << "**";
							}
							//else cout << "\twalking: " << int(traveltimep[p][s] / 60);
							in = false;
							//Travel for all passengers
							int xkS = xk[b][t].size() - 1;
							for (i = 0; i < xkS; i++) {
								if (xk[b][t][i] == s || in) {
									if (!in)l = i;
									in = true;
									cost += c1 * traveltimes[xk[b][t][i]][xk[b][t][i + 1]];
								}
							}
							if (s == N - 1) l = xk[b][t].size() - 1;
							//waiting
							//cout <<"Passenger " << p<<" Stop " << s << " index ";
							//cout << endl << l << "  " << xk[b][t].size() << endl;
							if (p < R1) {
								cost += c3 * abs(arrivals[p] - Dk[b][t].back());
								if (int(arrivals[p] - Dk[b][t].back()) > d_ae || int(Dk[b][t].back() - arrivals[p]) > d_al) {
									INFEAS2 = true;
									break;
									//cout << "\tdat: " << int((arrivals[p]) / 60) << " a: " << int(Dk[b][t].back() / 60) << "-> Diff: " << int((arrivals[p]) / 60) - int(Dk[b][t].back() / 60) <<"**" << endl;
								}
								//else {
									//cout << "\tdat: " << int((arrivals[p]) / 60) << " a: " << int(Dk[b][t].back() / 60) << "-> Diff: " << int((arrivals[p]) / 60) - int(Dk[b][t].back() / 60) << endl;
								//}
							}
							else {
								cost += c3 * abs(departures[p - R1] - Dk[b][t][l]);
								if (int(departures[p - R1] - Dk[b][t][l]) > d_de || int(Dk[b][t][l] - departures[p - R1]) > d_dl) {
									INFEAS3 = true;
									break;
									//cout << "\tedt: " << int((departures[p - R1]) / 60) << " d: " << int(Dk[b][t][l] / 60) << "-> Diff: " << int((departures[p - R1]) / 60) - int(Dk[b][t][l] / 60) <<"**" <<endl;
								}
								//else {
									//cout << "\tedt: " << int((departures[p - R1]) / 60) << " d: " << int(Dk[b][t][l] / 60) << "-> Diff: " << int((departures[p - R1]) / 60) - int(Dk[b][t][l] / 60) << endl;
								//}
							}
						}

						if (!INFEAS1 && !INFEAS2 && !INFEAS3) {
							//vector<vector<double>> FC(N);
							//cout << "\n----------  Time between bus departures (min) ----------- \n";
							for (i = 0; i < N && !INFEAS4; i++) {
								IFC.clear();
								for (b = 0; b < B; b++) {
									int xkS1 = xk[b].size();
									for (t = 0; t < xkS1; t++) {
										int xkS2 = xk[b][t].size();
										for (l = 0; l < xkS2; l++) {
											if (xk[b][t][l] == i)IFC.push_back(Dk[b][t][l]);
										}
									}
								}
								FCi = IFC.size();
								std::sort(IFC.begin(), IFC.begin() + FCi);
								//cout << "m_" << i << " -> ";
								for (j = 1; j < FCi; j++) {
									if (int(IFC[j] - IFC[j - 1]) > OGxt) {
										//cout << int((FC[i][j] - FC[i][j - 1]) / 60) << "** \t";
										INFEAS4 = true;
										break;
										//infs = " --> between " + to_string(int(FC[i][j - 1] / 60)) + " and " + to_string(int(FC[i][j] / 60));
									}
									//else {
										//cout << int((FC[i][j] - FC[i][j - 1]) / 60) << " \t";
									//}
								}
								//cout << endl;
							}
							//std::cout << "Elapsed time: " << elapsed_time << "s (initial solution)" << endl;
							//cout << "COST: " << cost << "s (initial solution)\n";
						}
						if (INFEAS1 || INFEAS2 || INFEAS3 || INFEAS4) {
							//countInfeas2++;
							//infeastemp++;
							//nhp = 0.02;
							continue;
						}
					}
					//if (!(INFEAS1 || INFEAS2 || INFEAS3 || INFEAS4) && countp == R) {
#pragma omp critical
					{
						Costb.push_back(cost);
						//logresBest = logres;
						lPM1b.push_back(dPM10);
						lPM2b.push_back(dPM20);
						lPM3b.push_back(dPM30);
						lFPMb.push_back(dFPM0);
						lXTb.push_back(dXT0);
						lCb.push_back(dC0);
					}
					INFEASS = true;
				}
				delete[] change1;
				//delete endC1;
				delete[] change2;
				//delete endC2;
				delete[] change3;
				//delete endC3;
				delete[] change4;
				//delete endC4;
				delete[] change5;
				//delete endC5;
				delete[] change6;
			}
			cost_c = INT32_MAX;
			b_c_i = -1;
			MM = Costb.size();
			run += MM;
			for (int f = 0; f < MM; f++) {
				//cout << Costb[f] <<"  index:" << f << endl;
				if (cost_c > Costb[f]) {
					cost_c = Costb[f];
					b_c_i = f;
				}
			}
			//cout << "MM: " << MM << endl;
			MM = lPM1b[b_c_i].size();

			//if (run % 10 == 0) cout << best_cost << " Ts: " + to_string(Ts) << " run: " << run + 1 << endl;
			dE = best_cost - cost_c;
			if (best_cost > cost_c) {
				best_cost = cost_c;
				lPM1.clear();
				lPM2.clear();
				lPM3.clear();
				lFPM.clear();
				lXT.clear();
				lC.clear();

				MM = lPM1b[b_c_i].size();
				for (int i = 0; i < MM; i++) {
					lPM1.push_back(lPM1b[b_c_i][i]);
					lPM2.push_back(lPM2b[b_c_i][i]);
					lPM3.push_back(lPM3b[b_c_i][i]);
					lFPM.push_back(lFPMb[b_c_i][i]);
					lXT.push_back(lXTb[b_c_i][i]);
					lC.push_back(lCb[b_c_i][i]);
				}
				if (bb_cost > best_cost) {
					bb_cost = best_cost;
					b_lPM1.clear();
					b_lPM2.clear();
					b_lPM3.clear();
					b_lFPM.clear();
					b_lXT.clear();
					b_lC.clear();
					MM = lPM1b[b_c_i].size();
					for (int i = 0; i < MM; i++) {

						b_lPM1.push_back(lPM1b[b_c_i][i]);
						b_lPM2.push_back(lPM2b[b_c_i][i]);
						b_lPM3.push_back(lPM3b[b_c_i][i]);
						b_lFPM.push_back(lFPMb[b_c_i][i]);
						b_lXT.push_back(lXTb[b_c_i][i]);
						b_lC.push_back(lCb[b_c_i][i]);
					}
				}
				prog.push_back(best_cost);
				progit.push_back(run);
			}
			else if (r01(generator0) <= exp(dE / Ts)) {
				//update best paramters
				best_cost = cost_c;
				lPM1.clear();
				lPM2.clear();
				lPM3.clear();
				lFPM.clear();
				lXT.clear();
				lC.clear();
				MM = lPM1b[b_c_i].size();
				for (int i = 0; i < MM; i++) {
					lPM1.push_back(lPM1b[b_c_i][i]);
					lPM2.push_back(lPM2b[b_c_i][i]);
					lPM3.push_back(lPM3b[b_c_i][i]);
					lFPM.push_back(lFPMb[b_c_i][i]);
					lXT.push_back(lXTb[b_c_i][i]);
					lC.push_back(lCb[b_c_i][i]);
				}
				prog.push_back(cost_c);
				progit.push_back(run);
			}
			if (run % 1000 == 0) cout << best_cost << " Ts: " + to_string(Ts) << " run: " << run + 1 << endl;
			//cout << " check\n";
			//cout << "d: -->" << dPM1.size() << endl;
			Ts = T_end + lam * log(1 + r_i);
			//cout << "T: "<< Ts <<"r_i: " << r_i<< endl;

			if (dE < 0) r_i++;
			else if (dE > 0)r_i = 0;
			//if (!(INFEAS1 || INFEAS2 || INFEAS3 || INFEAS4))logrestot += logres;
			// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ HEURISTIC ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
			//for (it = 0; it < nIt; it++) {
			//}
		}
		ofstream progp("data/output/progress_" + to_string(instance) + ".txt");
		ofstream progitp("data/output/progressit_" + to_string(instance) + ".txt");
		for (int f = 0; f < prog.size(); f++) {
			progp << prog[f] << endl;
			progitp << progit[f] << endl;
		}

		progp.close();
		progitp.close();

		//int LL = 30;

		int i, b, t, p, l, s, temp, xt;
		double pm1, pm2, pm3, fpm;
		double b_next;
		vector<int> route;
		//double dE;
		vector<double> timetable;
		vector<double> tempt;
		double timewindow, timewindow2;
		//double Arr;

		int trips[B]; //keeps track of which trip each bus is at needs to be updated
		int best_stop;
		double freqN[N];
		double newfreqN[N];

		double bd[B];

		int yk[R][3];
		/*
		vector<vector<int>> yk(R);
		for (p = 0; p < R; p++) {
			vector<int>  yk2(3);
			yk[p] = yk2;
		}
		//*/

		double startopt;

		int countp, p1, p2, cp1, cp2;
		bool in, in2;
		double threshold, tt;

		double l_arr, l_dep;

		int b_it = 0;

		double minF = INT16_MAX, min_al = INT16_MAX, min_ae = INT16_MAX, min_dl = INT16_MAX, min_de = INT16_MAX;
		int nS, dst;
		double diffa1, diffa2, diffd1, diffd2, diffF;
		double difBD, maxFW, maxRW;//max time to arrive or depart earlier
		//add addtional passenger with DAT
		//*
		double extra = 0, b_extra = 0;
		//std::cout << "\n************************************************************************** Run number: " << run + 1 << endl;
		//logres = "";
		for (p = 0; p < R; p++) {
			yk[p][0] = -1;
			yk[p][1] = -1;
			yk[p][2] = -1;

		}
		int indexpt[R1];
		int indexpt2[R2];
		double temparrivals[R1];
		double tempdept[R2];
		for (p = 0; p < R1; p++) {
			indexpt[p] = p;
			temparrivals[p] = arrivals[p];
		}

		for (p = 0; p < R2; p++) {
			indexpt2[p] = p;
			tempdept[p] = departures[p];
		}
		quickSort(indexpt, temparrivals, 0, R1 - 1);
		quickSort(indexpt2, tempdept, 0, R2 - 1);
		best_stop = 0;
		startopt = tempdept[0] - 1000;
		threshold = 0, tt = 0;

		double cost = 0, b_cost = 0;
		//routing: [bus, trip,stops]
		vector<vector<vector<int>>> xk(B);
		route.clear();

		//D: [bus, trip,departure time]
		vector<vector<vector<double>>> Dk(B);
		timetable.clear();
		tempt.clear();
		//cout << "check\n";
		int SL = lPM1.size();
		//cout << "  thread number: " + to_string(omp_get_thread_num()) + " loop number: " + to_string(iii + 1) + " \n";

		l_arr = arrivals[indexpt[0]], l_dep = departures[indexpt2[0]] + short_route * 0.75;
		//logres += "Run: " + to_string(run + 1) + "\t";
		//start_time = clock();
		//************************************Initial Solution***************************************
		for (i = 0; i < N; i++) {
			freqN[i] = -INT16_MAX;
		}
		countp = p1 = p2 = 0;
		for (b = 0; b < B; b++) {
			trips[b] = 0;
			bd[b] = startopt;//start of optimization
		}
		timetable.push_back(0);

		p1 = p2 = countp = 0;
		b = 0;
		b_next = 0.0;
		//cout << " END of PH: " << int(TS + startopt) / 60 << endl;
		b_it = -1;
		while (timetable.back() < TS + startopt && p1 + p2 < R) {//until TS is over+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++	
			b_it++;
			//if (nRUN > 1) {
			//if (b_it < dPM1.size()) {
			pm1 = b_lPM1[b_it];
			pm2 = b_lPM2[b_it];
			pm3 = b_lPM3[b_it];
			fpm = b_lFPM[b_it];
			xt = int(b_lXT[b_it] * OGxt);
			C = max(5, int(b_lC[b_it] * C_OG));
			//}
			//}
			//xt = OGxt;
			//if (infeastemp > 100) fpm = 1;
			//cout << " xt: " << xt / 60 << endl;
			//determine which bus is available first
			b = iMin(bd, B);
			b_next = iMin2(bd, B);
			//cout << "++++++ || Bus: " << b << " bd: " << int(bd[b] / 60) << " trip: " << trips[b] << " || ++++++\n";
			//for (i = 0; i < B; i++) cout << int(bd[i] / 60) << " ";
			//cout << endl;
			//cout << "bd1: " << int(bd[b]/60) << " bd2: " << int(b_next/60) << endl;
			//Make route only with mandatory stops, ASAP
			route.clear();
			timetable.clear();
			tempt.clear();
			tt = bd[b];
			timetable.push_back(tt);
			route.push_back(0);
			for (i = 1; i < N; i++) {
				route.push_back(i);
				tt += traveltimes[i - 1][i];
				timetable.push_back(tt);
			}
			//Assignement: First look at R1
			timewindow = timewindow2 = INT32_MAX;
			cp1 = cp2 = 0;

			//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ CASE I ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
			if (l_arr < l_dep && p1 < R1 || p2 == R2) {
				//cout << "R1" << endl;
				p = 0;
				while (cp1 + cp2 < C && countp < R && p < R1 && (int)(arrivals[indexpt[p]] - timewindow) <= d_ae + d_al) {
					//cout << " check start\n";
					//cout << cp1 + cp2 << "<" << C << "  " << countp << "<" << R << "  " << (int)(arrivals[indexpt[p]] - timewindow) << "< " << d_ae + d_al << endl;
					if (traveltimep[indexpt[p]][closestPS[indexpt[p]][0]] > dw) {
						std::cout << " Infeasible solution, for walking times " << endl;
						exit(0);
					}
					if (temparrivals[indexpt[p]] == -1) {
						//cout << "passenger already in solution \n";
						//cout << "p: " << p << " indexpt: " << indexpt[p] << endl;
						p++;
						if (p > R1)break;
						continue;//if this is already in the solution, continue to next passenger
					}
					if (cp1 == 0)timewindow = arrivals[indexpt[p]];

					//Assign bus stop to passenger
					//choose best stop and update route
					if (cp1 == 0) {
						//cout << " check 2 \n";
						best_stop = bestStop(timetable, route, traveltimes, traveltimep, closestPS, indexpt[p], N,
							dw, best_route, M, S, bd[b], freqN, xt, best_stop, arrivals[indexpt[p]],
							arrivals[indexpt[p]], d_ae, d_al, yk, arrivals, R1, R2, b, trips[b], b_next, fpm);
						//cout << " check stop 0\n";
						if (best_stop == -1) {
							//cout << "passenger " << indexpt[p] << " --> Skip this one, not good for bus stop\n";
							p++;
							//cout << "Next passenger " << p1 << endl;
							if (p > R1)break;
							continue;
						}
						//cout << " --- FIRST passenger added : p= " << indexpt[p] << "\n";
						//Assign bus to passenger
						yk[indexpt[p]][0] = b;
						yk[indexpt[p]][1] = trips[b];
						yk[indexpt[p]][2] = best_stop;
						temparrivals[indexpt[p]] = -1;
						tempt.push_back(arrivals[indexpt[p]]);
						p++;
						p1++;
						cp1++;
						countp++;
						if (p > R1)break;
					}
					else {
						temp = bestStop(timetable, route, traveltimes, traveltimep, closestPS, indexpt[p], N, dw,
							best_route, M, S, bd[b], freqN, xt, best_stop, tempt.back(),
							arrivals[indexpt[p]], d_ae, d_al, yk, arrivals, R1, R2, b, trips[b], b_next, fpm);
						//cout << " check stop n: " << temp <<"\n";
						if (temp == -1) {
							//cout << "passenger " << indexpt[p] << " --> Skip this one, not good for bus stop\n";
							p++;//next stop of a passenger with later edt is before a previous stop with a passenger with earlier edt, not possible OR edts are too different
							if (p > R1)break;
							continue;
						}
						else {
							// time to go from prev to next stop on a full route 
							best_stop = temp;
							//Assign bus to passenger
							yk[indexpt[p]][0] = b;
							yk[indexpt[p]][1] = trips[b];
							yk[indexpt[p]][2] = best_stop;
							temparrivals[indexpt[p]] = -1;
							tempt.push_back(arrivals[indexpt[p]]);
							p++;
							p1++;
							cp1++;
							countp++;
							if (p > R1)break;
							//cout << "-- NEXT passenger added : p= " << indexpt[p] << "\n";
							//cout << " indexpt: " << indexpt[p] << " arrivals p: " << arrivals[indexpt[p]] <<  endl;
							//cout << " p: " << p << " indexpt: " << indexpt[p] << endl;
						}
					}
				}
				//cout << " check end\n";
				//cout << "timetable:" << timetable.size() << " route: " << route.size() << " Passengers added: " << tempt.size() << endl;
			}
			// //++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ CASE II ++++++++++++++++++++++++++++++++++++++++++++ Now look at R2
			//*
			if ((l_arr >= l_dep && p2 < R2) || cp1 == 0) {
				//cout << "R2" << endl;
				//cout << timetable.size() << endl;
				timetable.clear();
				tt = bd[b];
				timetable.push_back(tt);
				for (i = 1; i < N; i++) {
					tt += traveltimes[i - 1][i];
					timetable.push_back(tt);
				}

				p = 0;
				while (cp2 < C && countp < R && p < R2) {
					//cout << p2 << "<" << C << "  " << countp << "<" << R << " " << p << "< " << R2 << endl;
					//cout << "passenger " << indexpt2[p] + R1 << "  ------------- \n";
					if (traveltimep[R1 + indexpt2[p]][closestPS[R1 + indexpt2[p]][0]] > dw) {
						std::cout << " Infeasible solution, for walking times " << endl;
						exit(0);
					}
					if (tempdept[indexpt2[p]] == -1) {
						//cout << "passenger already in solution \n";
						p++;
						continue;//if this is already in the solution, continue to next passenger
					}
					t = 0;
					for (i = 0; i < timetable.size(); i++) {
						if (route[i] < N) {
							newfreqN[t] = timetable[i];
							t++;
						}
					}
					if (cp2 == 0) {
						best_stop = bestStop2(timetable, route, traveltimes, traveltimep, closestPS, indexpt2[p] + R1, N,
							dw, best_route, M, S, bd[b], freqN, newfreqN, xt, best_stop, departures[indexpt2[p]],
							departures[indexpt2[p]], d_de, d_dl, yk, departures, R1, R2, b, trips[b], b_next, fpm);
						if (best_stop == -1) {
							//cout << "passenger " << indexpt2[p] + R1 << " --> Skip this one, not good for bus stop\n";
							p++;
							//cout << "Next passenger " << p1 << endl;
							continue;
						}
						//cout << " --- FIRST passenger added : p= " << indexpt2[p] + R1 << "\n";
						//Assign bus to passenger
						yk[R1 + indexpt2[p]][0] = b;
						yk[R1 + indexpt2[p]][1] = trips[b];
						//Assign bus stop to passenger
						//choose best stop and update route
						//cout << "  Best stop: " << best_stop << endl;
						//cout << "Passenger: " << R1 + indexpt2[p] << " edt: " << int(departures[indexpt2[p]] / 60) << " stop: " << best_stop << endl;
						tempt.push_back(departures[indexpt2[p]]);
						tempdept[indexpt2[p]] = -1;
						yk[R1 + indexpt2[p]][2] = best_stop;
						cp2++;
						p2++;
						countp++;
						p++;
					}
					else {
						temp = bestStop2(timetable, route, traveltimes, traveltimep, closestPS, indexpt2[p] + R1, N, dw,
							best_route, M, S, bd[b], freqN, newfreqN, xt, best_stop, tempt.back(),
							departures[indexpt2[p]], d_de, d_dl, yk, departures, R1, R2, b, trips[b], b_next, fpm);

						if (temp == -1) {
							//cout << "Passenger: " << R1 + indexpt2[p] << " edt: "<< int(departures[indexpt2[p]] / 60) << "Skip this one, not good for bus stop\n";
							p++;//next stop of a passenger with later edt is before a previous stop with a passenger with earlier edt, not possible OR edts are too different
							continue;
						}
						else {
							// time to go from prev to next stop on a full route 
							best_stop = temp;
							//Assign bus to passenger
							yk[R1 + indexpt2[p]][0] = b;
							yk[R1 + indexpt2[p]][1] = trips[b];
							//Assign bus stop to passenger
							yk[R1 + indexpt2[p]][2] = best_stop;
							//cout << "Passenger: " << R1 + indexpt2[p] << " edt: " << int(departures[indexpt2[p]] / 60) << " stop: " << best_stop << endl;
							tempt.push_back(departures[indexpt2[p]]);
							tempdept[indexpt2[p]] = -1;
							cp2++;
							p2++;
							countp++;
							p++;
							//cout << "-- NEXT passenger added : p= " << indexpt2[p] + R1 << "\n";
						}
					}
				}

				if (p1 < R1 && l_arr >= l_dep && tempt.size() == 0) {
					//++++++++++++++++++++++++++++++++ CASE I ++++++++++++++++++++++++++++++++++++++++++++
					//cout << "R1 again" << endl;
					p = 0;
					while (cp1 + cp2 < C && countp < R && p < R1 && (int)(arrivals[indexpt[p]] - timewindow) <= d_ae + d_al) {
						//cout << cp1 + cp2 << "<" << C << "  " << countp << "<" << R << "  " << (int)(arrivals[indexpt[p]] - timewindow) << "< " << d_ae + d_al << endl;
						if (traveltimep[indexpt[p]][closestPS[indexpt[p]][0]] > dw) {
							std::cout << " Infeasible solution, for walking times " << endl;
							exit(0);
						}
						if (temparrivals[indexpt[p]] == -1) {
							//cout << "passenger already in solution \n";
							//cout << "p: " << p << " indexpt: " << indexpt[p] << endl;
							p++;
							if (p > R1)break;
							continue;//if this is already in the solution, continue to next passenger
						}
						if (cp1 == 0)timewindow = arrivals[indexpt[p]];
						//Assign bus stop to passenger
						//choose best stop and update route
						if (cp1 == 0) {
							best_stop = bestStop(timetable, route, traveltimes, traveltimep, closestPS, indexpt[p], N,
								dw, best_route, M, S, bd[b], freqN, xt, best_stop, arrivals[indexpt[p]],
								arrivals[indexpt[p]], d_ae, d_al, yk, arrivals, R1, R2, b, trips[b], b_next, fpm);
							//cout << " check\n";
							if (best_stop == -1) {
								//cout << "passenger " << indexpt[p]  << " --> Skip this one, not good for bus stop\n";
								p++;
								//cout << "Next passenger " << p1 << endl;
								if (p > R1)break;
								continue;
							}
							//cout << " --- FIRST passenger added\n";
							//Assign bus to passenger
							yk[indexpt[p]][0] = b;
							yk[indexpt[p]][1] = trips[b];
							yk[indexpt[p]][2] = best_stop;
							temparrivals[indexpt[p]] = -1;
							tempt.push_back(arrivals[indexpt[p]]);
							p++;
							p1++;
							cp1++;
							countp++;
							if (p > R1)break;
							//cout << " --- FIRST passenger added : p= " << indexpt[p] << "\n";
						}
						else {
							temp = bestStop(timetable, route, traveltimes, traveltimep, closestPS, indexpt[p], N, dw,
								best_route, M, S, bd[b], freqN, xt, best_stop, tempt.back(),
								arrivals[indexpt[p]], d_ae, d_al, yk, arrivals, R1, R2, b, trips[b], b_next, fpm);
							//cout << " check\n";
							if (temp == -1) {
								//cout << "passenger " << indexpt[p] << " --> Skip this one, not good for bus stop\n";
								p++;//next stop of a passenger with later edt is before a previous stop with a passenger with earlier edt, not possible OR edts are too different
								if (p > R1)break;
								continue;

							}
							else {
								// time to go from prev to next stop on a full route 
								best_stop = temp;
								//Assign bus to passenger
								yk[indexpt[p]][0] = b;
								yk[indexpt[p]][1] = trips[b];
								yk[indexpt[p]][2] = best_stop;
								temparrivals[indexpt[p]] = -1;
								tempt.push_back(arrivals[indexpt[p]]);
								p++;
								p1++;
								cp1++;
								countp++;
								if (p > R1)break;
								//cout << "-- NEXT passenger added : p= " << indexpt[p] << "\n";
							}
						}

					}

				}
				//cout << "timetable:" << timetable.size() << " route: " << route.size() << " Passengers added: " << tempt.size() << endl;
			}
			//*/

			if (tempt.size() == 0) {
				timetable.clear();
				timetable.push_back(freqN[0] + xt);
				tt = -1;
				for (i = 1; i < N; i++) {
					timetable.push_back(timetable[i - 1] + traveltimes[i - 1][i]);
					if (timetable[i] - freqN[i] > tt)tt = timetable[i] - freqN[i];
				}
				if (tt > xt) {
					for (i = 0; i < N; i++) {
						timetable[i] -= (tt - xt);
					}
				}
			}
			else {
				//add addtional passenger with DAT
				minF = INT16_MAX, min_al = INT16_MAX, min_ae = INT16_MAX, min_dl = INT16_MAX, min_de = INT16_MAX;
				nS = timetable.size() - 1;

				for (p = 0; p < R1; p++) {
					if (yk[p][0] == b && yk[p][1] == trips[b]) {
						//cout << "passenger " << p  << ": dat=" << int(arrivals[p] / 60) << " arr=" << int(timetable[nS] / 60) << endl;
						diffa1 = d_ae - (arrivals[p] - timetable[nS]);
						diffa2 = d_al - (timetable[nS] - arrivals[p]);
						if (arrivals[p] >= timetable[nS] && min_ae > diffa1) {
							min_ae = diffa1;
						}
						if (arrivals[p] <= timetable[nS] && min_al > diffa2) {
							min_al = diffa2;
						}
					}
				}

				dst = -1;
				for (p = 0; p < R2; p++) {
					dst = -1;
					for (i = 0; i < route.size(); i++) {
						if (yk[p + R1][0] == b && yk[p + R1][1] == trips[b] && yk[p + R1][2] == route[i]) {
							dst = i;
							break;
						}
					}
					if (dst != -1) {
						//cout << "passenger " << p +R1 << ": edt=" << int(departures[p] / 60) << " dept=" << int(timetable[dst] / 60) << " at stop: " <<route[dst] << endl;
						diffd1 = d_de - (departures[p] - timetable[dst]);
						diffd2 = d_dl - (timetable[dst] - departures[p]);
						if (departures[p] >= timetable[dst] && min_de > diffd1) {
							min_de = diffd1;
						}
						if (departures[p] <= timetable[dst] && min_dl > diffd2) {
							min_dl = diffd2;
						}
					}
				}
				if (freqN[0] != -INT16_MAX) {
					for (i = 0; i < timetable.size(); i++) {
						if (route[i] < N && freqN[route[i]] < timetable[i]) {
							diffF = xt - (timetable[i] - freqN[route[i]]);
							if (minF > diffF) minF = diffF;
						}
					}
				}

				//cout << " min diff al: " << int(min_al/60) << " min diff dl: " << int(min_dl/60) << " min diff Freq: " << int(minF / 60) << endl;
				//cout << " min diff ae: " << int(min_ae/60) << " min diff de: " << int(min_de/60) << endl;
				difBD = timetable[0] - bd[b];
				maxFW = min(min(min_al, min_dl), minF) * pm1; // max time to depart later 
				maxRW = min(min(min_ae, min_de), difBD) * pm2;//max time to arrive or depart earlier
				//add addtional passenger with DAT
				//*
				extra = 0;
				//cout << "Max time FW: " << int(maxFW/60) << " max time RW: " << int(maxRW/60) << "\nStart R1\n";
				//cout << "R1: " << cp1 << " R2: " << cp2 << endl;

				for (p = 0; p < R1; p++) {
					if (temparrivals[p] != -1) {
						//cout << "for p_" << p << " dat: "<<arrivals[p]/60<< " arrval: " << timetable.back()/60<<endl;
						i = 0;
						b_cost = INT32_MAX;
						s = -1;
						if (arrivals[p] >= timetable.back()) {
							if (arrivals[p] - timetable.back() <= d_ae) extra = 0;
							else extra = (arrivals[p] - timetable.back()) - d_ae;
						}
						else {
							if (timetable.back() - arrivals[p] <= d_al) extra = 0;
							else extra = d_al - (timetable.back() - arrivals[p]);
						}
						while (traveltimep[p][closestPS[p][i]] < dw * pm3) {
							//cout << "try stop: " << closestPS[p][i] << endl;
							for (t = 0; t < route.size() - 1; t++) {
								in = false;
								if (closestPS[p][i] == route[t]) {
									in = true;
									break;
								}
							}
							in2 = false;
							if (in && arrivals[p] - timetable.back() - maxFW <= d_ae && timetable.back() - maxRW - arrivals[p] <= d_al) {
								in2 = true;
							}

							if (in2 && cp1 + cp2 < C) {
								//cout << " ++++++++++++ passenger " << p << " (dat=" << int(arrivals[p] / 60) << ") stop " << closestPS[p][i] << " (tt=" << int(timetable.back() / 60) << ") possible extra: " << int(extra / 60) << endl;
								cost = c2 * traveltimep[p][closestPS[p][i]] + c3 * abs(timetable.back() - arrivals[p]) + c3 * (cp1 + cp2) * (abs(extra));
								if (b_cost > cost) {
									b_cost = cost;
									s = route[t];
								}
							}
							i++;
						}
						if (b_cost != INT32_MAX) {
							//cout << "Added DAT \t";
							//cout << "Passenger: " << p << " arr: " << arrivals[p] / 60 << endl;
							yk[p][0] = b;
							yk[p][1] = trips[b];
							yk[p][2] = s;
							//cout << "Passenger: " << R1 + p << endl;
							temparrivals[p] = -1;//indicate this passenger is onboard already
							p1++;
							cp1++;
							countp++;
							//break;

							//update timetable
							//cout << " move tt with " << int(extra / 60) << endl;
							for (l = 0; l < timetable.size(); l++) {
								timetable[l] += extra;
							}
							//update intermediary parameters
							minF = INT16_MAX, min_al = INT16_MAX, min_ae = INT16_MAX, min_dl = INT16_MAX, min_de = INT16_MAX;
							nS = timetable.size() - 1;
							for (int p11 = 0; p11 < R1; p11++) {
								if (yk[p11][0] == b && yk[p11][1] == trips[b]) {
									diffa1 = d_ae - (arrivals[p11] - timetable[nS]);
									diffa2 = d_al - (timetable[nS] - arrivals[p11]);
									if (arrivals[p11] >= timetable[nS] && min_ae > diffa1) {
										min_ae = diffa1;
									}
									if (arrivals[p11] <= timetable[nS] && min_al > diffa2) {
										min_al = diffa2;
									}
								}
							}
							for (int p22 = 0; p22 < R2; p22++) {
								dst = -1;
								for (l = 0; l < route.size(); l++) {
									if (yk[p22 + R1][0] == b && yk[p22 + R1][1] == trips[b] && yk[p22 + R1][2] == route[l]) {
										dst = l;
										break;
									}
								}
								if (dst != -1) {
									diffd1 = d_de - (departures[p22] - timetable[dst]);
									diffd2 = d_dl - (timetable[dst] - departures[p22]);
									if (departures[p22] >= timetable[dst] && min_de > diffd1) {
										min_de = diffd1;
									}
									if (departures[p22] <= timetable[dst] && min_dl > diffd2) {
										min_dl = diffd2;
									}
								}
							}
							if (freqN[0] != -INT16_MAX) {
								for (l = 0; l < timetable.size(); l++) {
									if (route[l] < N && freqN[route[l]] < timetable[l]) {
										diffF = xt - (timetable[l] - freqN[route[l]]);
										if (minF > diffF) minF = diffF;
									}
								}
							}
							//cout << " min diff al: " << int(min_al/60) << " min diff dl: " << int(min_dl/60) << endl;
							//cout << " min diff ae: " << int(min_ae/60) << " min diff de: " << int(min_de/60) << " min diff Freq: " << int(minF/60) << endl;
							difBD = timetable[0] - bd[b];
							maxFW = min(min(min_al, min_dl), minF) * pm1; // max time to depart later 
							maxRW = min(min(min_ae, min_de), difBD) * pm2;//max time to arrive or depart earlier
							//cout << "  Added passenger " << p << " --> NEW Max time FW: " << int(maxFW/60) << " max time RW: " << int(maxRW/60) << endl;

						}
					}
				}

				//add addtional passenger with EDT
				///*
				//cout << "Start R2\nNEW Max time FW : " << int(maxFW / 60) << " max time RW : " << int(maxRW / 60) << endl;
				b_extra = 0;
				for (p = 0; p < R2; p++) {
					if (tempdept[p] != -1) {
						//cout << "try p_" << p+R1 << " dept: "<<departures[p]/60<<endl;
						i = 0;
						b_cost = INT32_MAX;
						s = -1;
						while (traveltimep[R1 + p][closestPS[p + R1][i]] < dw * pm3) {
							//if (R1 + p == 36)cout << closestPS[p + R1][i] << endl;
							for (t = 0; t < route.size() - 1; t++) {
								in = false;
								if (closestPS[p + R1][i] == route[t]) {
									//cout << "bus stop " << closestPS[p + R1][i] << " position " << t << endl;
									in = true;
									break;
								}
							}
							in2 = false;
							if (in && departures[p] - timetable[t] - maxFW <= d_de && timetable[t] - maxRW - departures[p] <= d_dl) {
								in2 = true;
							}
							//if (in2) cout << "bus stop " << closestPS[p + R1][i] << " position " << t << " length of tt: " << timetable.size() << endl;

							if (in2 && cp1 + cp2 < C) {
								//cout << "bus stop " << closestPS[p + R1][i] << " position " << t << " length of tt: " << timetable.size() << endl;
								if (departures[p] >= timetable[t]) {
									if (departures[p] - timetable[t] <= d_de)extra = 0;
									else extra = (departures[p] - timetable[t]) - d_de;
								}
								else {
									if (timetable[t] - departures[p] <= d_dl)extra = 0;
									else extra = d_dl - (timetable[t] - departures[p]);
								}
								//cout << "walking time " << traveltimep[R1 + p][closestPS[p + R1][i]] / 60 << endl;
								//cout << " ++++++++++++ passenger " << p+R1 << " (edt="<< int(departures[p]/60) << ") stop " << closestPS[p + R1][i] <<" (tt="<< int(timetable[t]/60) << ") possible extra: " << int(extra / 60)<< endl;
								cost = c2 * traveltimep[R1 + p][closestPS[p + R1][i]] + c3 * abs(timetable[t] - departures[p]) + c3 * (cp1 + cp2) * (abs(extra));
								if (b_cost > cost) {
									b_cost = cost;
									s = route[t];
									b_extra = extra;
								}
							}
							i++;
						}
						if (b_cost != INT32_MAX) {
							//cout << "Added EDT \t";
							//cout << "Passenger: " << R1 + p << " dept: " << departures[p] / 60 << endl;
							yk[p + R1][0] = b;
							yk[p + R1][1] = trips[b];
							yk[p + R1][2] = s;
							//cout << "Passenger: " << R1 + p << endl;
							tempdept[p] = -1;//indicate this passenger is onboard already
							p2++;
							cp2++;
							countp++;
							//break;
							//update timetable
							//cout << " move tt with " << int(b_extra / 60) << endl;
							for (l = 0; l < timetable.size(); l++) {
								timetable[l] += b_extra;
							}
							//update intermediary parameters
							minF = INT16_MAX, min_al = INT16_MAX, min_ae = INT16_MAX, min_dl = INT16_MAX, min_de = INT16_MAX;
							nS = timetable.size() - 1;
							for (int p11 = 0; p11 < R1; p11++) {
								if (yk[p11][0] == b && yk[p11][1] == trips[b]) {
									diffa1 = d_ae - (arrivals[p11] - timetable[nS]);
									diffa2 = d_al - (timetable[nS] - arrivals[p11]);
									if (arrivals[p11] >= timetable[nS] && min_ae > diffa1) {
										min_ae = diffa1;
									}
									if (arrivals[p11] <= timetable[nS] && min_al > diffa2) {
										min_al = diffa2;
									}
								}
							}
							for (int p22 = 0; p22 < R2; p22++) {
								dst = -1;
								for (l = 0; l < route.size(); l++) {
									if (yk[p22 + R1][0] == b && yk[p22 + R1][1] == trips[b] && yk[p22 + R1][2] == route[l]) {
										dst = l;
										break;
									}
								}
								if (dst != -1) {
									diffd1 = d_de - (departures[p22] - timetable[dst]);
									diffd2 = d_dl - (timetable[dst] - departures[p22]);
									if (departures[p22] >= timetable[dst] && min_de > diffd1) {
										min_de = diffd1;
									}
									if (departures[p22] <= timetable[dst] && min_dl > diffd2) {
										min_dl = diffd2;
									}
								}
							}
							if (freqN[0] != -INT16_MAX) {
								for (l = 0; l < timetable.size(); l++) {
									if (route[l] < N && freqN[route[l]] < timetable[l]) {
										diffF = xt - (timetable[l] - freqN[route[l]]);
										if (minF > diffF) minF = diffF;
									}
								}
							}

							difBD = timetable[0] - bd[b];
							maxFW = min(min(min_al, min_dl), minF) * pm1; // max time to depart later 
							maxRW = min(min(min_ae, min_de), difBD) * pm2;//max time to arrive or depart earlier
							//cout << "    min diff al: " << int(min_al/60) << " min diff dl: " << int(min_dl/60) << endl;
							//cout << "    min diff ae: " << int(min_ae/60) << " min diff de: " << int(min_de/60) << " min diff Freq: " << int(minF/60) << endl;
							//cout << "  Added passenger " << p + R1 << " --> NEW Max time FW: " << int(maxFW / 60) << " max time RW: " << int(maxRW / 60) << endl;
						}
					}
				}
				//cout << "AFTER --> R1: " << cp1 << " R2: " << cp2 << endl;
				//*/

			}
			//cout << "R1+R2 done  Nroute: " << route.size() << " N_timetable: " << timetable.size() << endl;
			//update trip of bus b
			trips[b]++;
			//update bd of bus b
			bd[b] = timetable.back() + short_route;
			//update varaibles
			xk[b].push_back(route);
			Dk[b].push_back(timetable);
			//update frequency at mandatory 
			//cout << "xt constraints: \n";
			//cout << " ******* TIMETABLE: ";
			for (i = 0; i < timetable.size(); i++) {
				if (route[i] < N && (freqN[route[i]] < timetable[i] || freqN[route[i]] - timetable[i] > xt)) {
					//if(timetable[i] - freqN[route[i]]+1>xt) cout << int((timetable[i]- freqN[route[i]])) / 60 << " (s: "<< route[i]<< ") ";
					freqN[route[i]] = timetable[i];
					t++;
				}
				//cout << int(timetable[i] / 60) << " ";
			}
			if (p2 < R2) {
				for (p = 0; p < R2; p++) {
					if (tempdept[indexpt2[p]] != -1) {
						l_dep = departures[indexpt2[p]] + 0.75 * short_route;
						break;
					}
				}
			}
			if (p1 < R1) {
				for (p = 0; p < R1; p++) {
					if (temparrivals[indexpt[p]] != -1) {
						l_arr = arrivals[indexpt[p]];
						break;
					}
				}
			}
		}

		double telapsed_time = (double)(clock() - tstart_time) / CLK_TCK;

		itObj.push_back(best_cost);
		itRT.push_back(telapsed_time);

		if (u_cost > best_cost) {
			u_cost = best_cost;
			u_RT = telapsed_time;
			for (int b = 0; b < B; b++) {
				vector<vector<int>> xsol1(xk[b].size());
				vector<vector<double>> Dsol1(Dk[b].size());
				for (int t = 0; t < xk[b].size(); t++) {
					vector<int> xsol2(xk[b][t].size());
					vector<double> Dsol2(Dk[b][t].size());
					for (int i = 0; i < xk[b][t].size(); i++) {
						xsol2[i] = xk[b][t][i];
						Dsol2[i] = Dk[b][t][i];
					}
					xsol1[t] = xsol2;
					Dsol1[t] = Dsol2;
				}
				b_Dsol[b] = Dsol1;
				b_xsol[b] = xsol1;
			}
			for (int p = 0; p < R; p++) {
				b_ysol[p][0] = yk[p][0];
				b_ysol[p][1] = yk[p][1];
				b_ysol[p][2] = yk[p][2];
			}
		}
		cout << " Number of good feasible attempts: " << run << endl;
		cout << "\tcost: " << itObj[iit] << "\truntime: " << itRT[iit] << endl;
	}



	//Print
	ofstream runs_p("data/output/runs_" + to_string(instance) + ".txt");
	double avgObj = 0, avgIt = 0;
	for (int i = 0; i < itObj.size(); i++) {
		runs_p << itObj[i] << " " << itRT[i] << endl;
		avgObj += itObj[i];
		avgIt += itRT[i];
	}
	avgObj = avgObj / itObj.size();
	avgIt = avgIt / itObj.size();
	runs_p.close();

	ofstream xsol_p("data/output/xsol_" + to_string(instance) + ".txt");
	ofstream ysol_p("data/output/ysol_" + to_string(instance) + ".txt");
	ofstream dsol_p("data/output/dsol_" + to_string(instance) + ".txt");
	cout << "\n";
	int onb = 0;
	double cost;
	for (int i = 0; i < b_xsol.size(); i++) {
		cout << "+++++++++++++++++ Bus " << i << endl;
		xsol_p << "BUS " << i << endl;
		dsol_p << "BUS " << i << endl;
		for (int j = 0; j < b_xsol[i].size(); j++) {
			onb = 0;
			cout << "---- trip " << j << endl;
			cout << "Passengers: ";
			for (int p = 0; p < R; p++) {
				if (b_ysol[p][0] == i && b_ysol[p][1] == j) {
					cout << "p_" << p << " ";
					onb++;
				}
			}
			cout << " ---> " << onb << " onboard";
			cout << "\nBus stops: \n";
			for (int k = 0; k < b_xsol[i][j].size(); k++) {
				cout << b_xsol[i][j][k] << "\t";
				xsol_p << b_xsol[i][j][k] << "\t";
			}
			cout << endl;
			xsol_p << endl;
			for (int k = 0; k < b_xsol[i][j].size(); k++) {
				if (k == 0 && j != 0) {
					if (b_Dsol[i][j][k] + 10 < int(b_Dsol[i][j - 1][b_Dsol[i][j - 1].size() - 1] + short_route))cout << round(b_Dsol[i][j][k] / 60 * 100) / 100 << "**\t";
					else cout << round(b_Dsol[i][j][k] / 60) << "\t";
				}
				else cout << round(b_Dsol[i][j][k] / 60) << "\t";
				dsol_p << b_Dsol[i][j][k] << "\t";
			}
			cout << endl;
			dsol_p << endl;
		}
		cout << endl;
	}
	//Objective function value
	ysol_p << "Bus" << "\t" << "Trip" << "\t" << "stop" << endl;
	for (int p = 0; p < R; p++) {
		int b = b_ysol[p][0];
		int t = b_ysol[p][1];
		int s = b_ysol[p][2];
		if (p == R1) cout << endl;
		cout << "Passenger: " << p << "\tBus_" << b << " Trip_" << t << " Stop_" << s;
		ysol_p << b << "\t" << t << "\t" << s << endl;
		//continue;
		//Walking for all passengers
		if (traveltimep[p][s] > dw) {
			cout << "\twalking: " << int(traveltimep[p][s] / 60) << "**";
		}
		else cout << "\twalking: " << int(traveltimep[p][s] / 60);
		bool in = false;
		//Travel for all passengers
		double ttimep = 0;
		int l;
		for (int i = 0; i < b_xsol[b][t].size() - 1; i++) {
			if (b_xsol[b][t][i] == s || in) {
				if (!in)l = i;
				in = true;
				cost += c1 * traveltimes[b_xsol[b][t][i]][b_xsol[b][t][i + 1]];
				ttimep += traveltimes[b_xsol[b][t][i]][b_xsol[b][t][i + 1]];
			}
		}
		if (s == N - 1) l = b_xsol[b][t].size() - 1;
		cout << "\ttravel: " << int(ttimep / 60);
		//waiting
		//cout <<"Passenger " << p<<" Stop " << s << " index ";
		//cout << endl << l << "  " << xk[b][t].size() << endl;
		if (p < R1) {
			cost += c3 * abs(arrivals[p] - b_Dsol[b][t].back());
			if (arrivals[p] - b_Dsol[b][t].back() > d_ae || b_Dsol[b][t].back() - arrivals[p] > d_al) {
				cout << "\tdat: " << int((arrivals[p]) / 60) << " a: " << int(b_Dsol[b][t].back() / 60) << "-> Diff: " << int((arrivals[p]) / 60) - int(b_Dsol[b][t].back() / 60) << "**" << endl;
			}
			else {
				cout << "\tdat: " << int((arrivals[p]) / 60) << " a: " << int(b_Dsol[b][t].back() / 60) << "-> Diff: " << int((arrivals[p]) / 60) - int(b_Dsol[b][t].back() / 60) << endl;
			}
		}
		else {
			cost += c3 * abs(departures[p - R1] - b_Dsol[b][t][l]);
			if (departures[p - R1] - b_Dsol[b][t][l] > d_de || b_Dsol[b][t][l] - departures[p - R1] > d_dl) {
				cout << "\tedt: " << int((departures[p - R1]) / 60) << " d: " << int(b_Dsol[b][t][l] / 60) << "-> Diff: " << int((departures[p - R1]) / 60) - int(b_Dsol[b][t][l] / 60) << "**" << endl;
			}
			else {
				cout << "\tedt: " << int((departures[p - R1]) / 60) << " d: " << int(b_Dsol[b][t][l] / 60) << "-> Diff: " << int((departures[p - R1]) / 60) - int(b_Dsol[b][t][l] / 60) << endl;
			}
		}
	}

	xsol_p.close();
	ysol_p.close();
	dsol_p.close();

	vector<vector<double>> FC(N);
	cout << "\n----------  Time between bus departures (min) ----------- \n";
	string infs = "";
	for (int i = 0; i < N; i++) {
		for (int b = 0; b < B; b++) {
			for (int t = 0; t < b_xsol[b].size(); t++) {
				for (int l = 0; l < b_xsol[b][t].size(); l++) {
					if (b_xsol[b][t][l] == i)FC[i].push_back(b_Dsol[b][t][l]);
				}
			}
		}
		std::sort(FC[i].begin(), FC[i].begin() + FC[i].size());
		cout << "m_" << i << " -> ";
		for (int j = 1; j < FC[i].size(); j++) {
			if (int(FC[i][j] - FC[i][j - 1]) > OGxt) {
				cout << int((FC[i][j] - FC[i][j - 1]) / 60) << "** \t";
			}
			else {
				cout << int((FC[i][j] - FC[i][j - 1]) / 60) << " \t";
			}
		}
		cout << endl;
	}
	cout << "\nBEST: \n+++++++++++++ COST: " << u_cost << "\tRuntime: " << u_RT << endl;
	cout << "Average Cost: " << avgObj << "\tAverate RT: " << avgIt << endl;

	//remove memory

	for (int i = 0; i < S; i++) {
		delete[] closestS[i];
		delete[] traveltimes[i];
	}
	for (int i = 0; i < R; i++) {
		delete[] closestPS[i];
		delete[] traveltimep[i];
		delete[] b_ysol[i];
	}
	delete[] closestPS;
	delete[] closestS;
	delete[] traveltimes;
	delete[] traveltimep;
	delete[] b_ysol;
}
