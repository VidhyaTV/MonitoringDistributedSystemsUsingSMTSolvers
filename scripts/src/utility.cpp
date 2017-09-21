/*
  utility.cpp - class Utility
                for utility functionality
*/

#include <random>
#include <sstream>
#include <fstream>  // for ifstream
#include <numeric>  // for accumulate()
#include <tuple>

#include "utility.h"

/*
  Utility - umbrella class for utility function
*/


vector<snapshot_diff_count> Utility::makeFullAccumHistogram(vector<int> data){
    int max, min;
    int size;
    int total;       // total number of snapshot found
    int num_of_values;  // number of values in histogram
    vector<snapshot_diff_count> result;
    
    size = data.size();

    if(size <= 0)
        return result;

    // total snapshots
    total = size;
    
    // get max and min
    max = min = data.at(0);    

    #ifdef _DEBUG
    ofstream data_out("debug/data_out");
    #endif
        
    for (int i = 0; i < size; i++){
        int temp = data.at(i);
        
        if(max < temp)
            max = temp;
        if(min > temp)
            min = temp;
            
        #ifdef _DEBUG
        data_out << temp << endl;
        #endif
        
    }
    
    
    num_of_values = max - min + 1;

    
    cout << " *** total = " << total << " max = " << max << "  min = " << min << endl;
    
    result = vector<snapshot_diff_count>(num_of_values, snapshot_diff_count());

    // init
    for(int i = 0; i < num_of_values; i++){
        result.at(i).value = i + min;
        result.at(i).count = 0;
        result.at(i).fraction = 0.0;
    }

    // scan values to insert into bins
    for(int i = 0; i < size; i++){
        int your_value = data.at(i);
        
        result.at(your_value - min).count ++;
        result.at(your_value - min).fraction = (1.0*result.at(your_value - min).count)/(1.0*total);
        
    }
    
    // make accumulative 
    for(int i = 1; i < num_of_values; i++){
        result.at(i).count = result.at(i).count + result.at(i-1).count;
        result.at(i).fraction = (1.0*result.at(i).count)/(1.0*total);
    }
    
    return result;
    
}


void Utility::saveFullAccumHistogram(vector<snapshot_diff_count> hist, ofstream& os){
    int size = hist.size();
    int total;
    int i;


    if(size == 0){
        total = 0;
        
        // fist line is total number of snapshot found    
        os << "# total snapshot: " << total << endl;
        os << "# value   " << "count    " << "fraction" << "false negative fraction" << endl;
        return;
    }

    total = hist.at(size-1).count;

    // fist line is total number of snapshot found    
    os << "# params:" << endl;
    os << "#    epsilon: " << epsilon << endl;
    os << "#    number_of_processes: " << number_of_processes << endl;
    os << "#    localPredRate (beta): " << localPredRate << endl;
    os << "#    delta: " << delta << endl;
    os << "#    run_up_to: " << run_up_to << endl;
    os << "#    prob_matrix: " << prob_matrix_file_name << endl;
    os << "#    topology: " << topology_file_name << endl;
    
    os << "# result: "<< endl;
    os << "#    total snapshot: " << total << endl;
    os << "# value   " << "count    " << "fraction" << endl;

    // following lines are: value - count - fraction
    for(i = 0; i < size; i++){
        //stringstream stream;
        //string mystr;
        float falsePositiveRate;

        os.width(10);
        os << hist.at(i).value << "     ";
        os.width(10);
        os << hist.at(i).count << "     ";
        
        //stream << fixed << setprecision(3) << hist.at(i).fraction;
        //mystr = stream2.str();
        //os << mystr << endl;

        os.width(10);
        os << hist.at(i).fraction << "     ";
        os.width(10);
        falsePositiveRate = 1.0 - hist.at(i).fraction;
        os << falsePositiveRate << endl;
    }
    
}



/*
  GetRandomNumberInRange() - return an integer which is uniformly randomly selected 
                             within the range specified, inclusive
*/

int Utility::GetRandomNumberInRange(
  int a,  // range lower bound
  int b   // range upper bound
){


	if (a > b) {
		printf("Error in GetRandomNumberInRange(): a > b in random range(a,b)???\n");
		exit(1);
	}
	
	std::random_device rd;
	std::mt19937 mt(rd());
	
	// a distribution that takes randomness and produces values in specified range
	std::uniform_int_distribution<> distx(a, b);
	int result = distx(mt);
	//printf("random %d\n", result);
	//	if (result > 100000) printf("Warning: random number produces negative number %d, [a,b]=[%d,%d] \n",result,a,b);
	return result;
}

/*
  Variance() - compute variance of a vector
*/
double Utility::Variance(const vector<double>& vi) {
  double avg = accumulate(begin(vi), end(vi), 0.0) / vi.size();
  double ss = 0;
  for (auto x : vi) ss += (x - avg)*(x-avg);
  return ss / vi.size();
}

/* 
  Transpose() - compute transpose of a matrix
*/
vector<vector<double>> Utility::Transpose(const vector<vector<double>>& m_in) {
  if (m_in.size() == 0) {
	  printf("Warning Transpose empty matrix\n");
	  return vector<vector<double>>();
  }
  int m = m_in[0].size();
  int n = m_in.size();
  vector<vector<double>> m_out(m, vector<double>(n, 0));
  for (int i = 0; i < n; i++)
	  for (int j = 0; j < m; j++)
		  m_out[j][i] = m_in[i][j];
  return m_out;
}

/*
  split() - split a string into multiple substring using specified delimiter
            result is stored in a parameter as well returned by function
            CREDITS: http://stackoverflow.com/questions/236129/split-a-string-in-c
*/

std::vector<std::string> & Utility::split(const std::string &s, char delim, std::vector<std::string> &elems) {
  std::stringstream ss(s);
  std::string item;
  while (std::getline(ss, item, delim)) {
	  elems.push_back(item);
  }
  return elems;
}

/* 
  split() - split a string into multipe substring using specifed delimiter
            return set of substrings
*/
std::vector<std::string> Utility::split(const std::string &s, char delim) {
  std::vector<std::string> elems;
  split(s, delim, elems);
  return elems;
}

/* 
  AllPairShortestPaths() - compute shortest paths between all pairs of nodes in a graph
*/
distance_matrix Utility::AllPairShortestPaths(const adjacency_matrix& G) {
  distance_matrix D = G;

  int n = (int)G.size();
  for (int k = 0; k < n; k++)
	  for (int i = 0; i < n; i++)
		  for (int j = 0; j < n; j++)
			  if (D[i][k] + D[k][j] < D[i][j]) D[i][j] = D[i][k] + D[k][j];
  return D;
}


/* 
  ReadGraph() - obtain graph from topo
                  + generate graph according to specified topo 
                  + or read graph from input file
*/  
adjacency_matrix Utility::ReadGraph(const string& topo) {
  adjacency_matrix G;
  
  if (topo == "CompleteGraph") {
	  for (int i = 0; i < number_of_processes; i++) {
		  vector<int> one_row;
		  for (int j = 0; j < number_of_processes; j++)
		  {
			  if (i == j) one_row.push_back(0);
			  else one_row.push_back(1);
		  }
		  G.push_back(one_row);
	  }
  } 
  else if(topo =="Tree"){

  }
  else if (topo == "Star") {

  }
  else if (topo == "Random Connected Graph") {

  }
  else {
	  ifstream in(topo);
	  if (!in.is_open()) { printf("Can't read the topology.graph file.\n"); exit(1); }
	  string content;
	  while (getline(in, content)) {
		  vector<string> split_comma = split(content, ',');
		  vector<int> one_row;
		  for (string& s : split_comma) {
			  one_row.push_back(atoi(s.c_str()));
		  }
		  G.push_back(one_row);
	  }
  }
  
  if (G.size() != number_of_processes) {
	  printf("Error in ReadGraph: G.size() != number_of_processes\n ");
	  exit(1);
  }
  
  return G;
}

/*
  ReadProbabilityMatrix() - read probability matrix
*/

probability_matrix Utility::ReadProbabilityMatrix(const string& prob) {
  probability_matrix P;	  
  string checkcluster = "test";
  
  if (prob.length() >= 7) 
	  checkcluster = prob.substr(0, 7);

  if (prob == "Random") {
	  for (int i = 0; i < number_of_processes; i++) {
		  vector<double> one_row;
		  for (int j = 0; j < number_of_processes; j++)
		  {
			  if (i == j) one_row.push_back(1);
			  else one_row.push_back(1);
		  }
		  P.push_back(one_row);
	  }
  }
  else if (checkcluster == "Cluster") {
	  vector<string> split_semicolon = split(prob, ';');
	
	  for (string& s : split_semicolon) {
			  cout << s << " ";
		  }
	  printf("\n");
	  string s0 = split_semicolon[1];
	  string s1 = split_semicolon[2];

	  vector<string> split_eq_s0 = split(s0, ':');
	  vector<string> split_eq_s1 = split(s1, ':');

	  double beta = stod(split_eq_s0[1]);
	  double k = stod(split_eq_s1[1]);
	
	
	  if (number_of_processes %((int)k) != 0) {
		  printf("Warning: n mod k != 0\n");
	  }

	  double prob_incluster = k*beta / number_of_processes;
	  double prob_outcluster = k*(1-beta)/(number_of_processes*(k-1));

	  cout << prob_incluster << " " << prob_outcluster << endl;
		  
	  //assign probability matrix
    for (int i = 0; i < number_of_processes; i++) {
	    vector<double> one_row;
	    int num_members_in_cluster = (number_of_processes / (int)k);
	    int q = i / num_members_in_cluster;

	    for (int j = 0; j < number_of_processes; j++)
	    {
		    if (j/num_members_in_cluster == q) one_row.push_back(prob_incluster);
		    else one_row.push_back(prob_outcluster);
	    }
	    P.push_back(one_row);
    }
  }
  else {
	  ifstream in(prob);
	  if (!in.is_open()) { printf("Can't read the probability_matrix.in file.\n"); exit(1); }
	  string content;
	  while (getline(in, content)) {
		  vector<string> split_comma = split(content, ',');
		  vector<double> one_row;
		  for (string& s : split_comma) {
			  one_row.push_back(atof(s.c_str()));
		  }
		  P.push_back(one_row);
	  }
  }
  
  //normalize probability
  for (int i = 0; i < number_of_processes;i++) {
	  double sum_row = 0;
	  for (int j = 0; j < number_of_processes; j++) {
		  sum_row += P[i][j];
	  }
	  for (int j = 0; j < number_of_processes; j++) {
		  P[i][j] = P[i][j] / sum_row;
	  }
  }
  if (P.size() != number_of_processes) {
	  printf("Error in ReadProbabilityMatrix: P.size() != number_of_processes\n ");
	  exit(1);
  }
  
  return P;
}



// do not use default parameter for size here since its declaration already has default param
// default param can only be declared once

int Utility::GetIndexOfWeightedRandom(const vector<double>& arr, int size){ 
  std::random_device rd;
  std::default_random_engine generator(rd());
  std::uniform_real_distribution<double> distribution(0.0, 1.0);
  double val = distribution(generator);
  double sum = 0;

  for (int i = 0; i < size; i++) {
	  sum += arr[i];
	  if (val <= sum) {
		  //printf("i = %d; random= %f \n", i,val);
		  return i;
	  }
  }
  printf("WARNING: GetIndexOfWeightedRandom should not reah here\n "); 
  return 0;
}

int Utility::GetIndexOfWeightedNormalDistribution(double std_percent, int size = number_of_processes) {
  if (std_percent < 0 || std_percent > 1) {
	  printf("std_percent is invalid\n : %f", std_percent);
	  exit(1);
  }
  std::random_device rd;
  std::default_random_engine generator(rd());
  //std::uniform_real_distribution<double> distribution(0.0, 1.0);
  std::normal_distribution<> distribution((number_of_processes) / 2.0, std_percent*(number_of_processes));
  double val = distribution(generator);
  if (val <= 0) return 0;
  if (val >= number_of_processes-1) return number_of_processes-1;
  return  int(std::round(val));
}



/*
main(){
  for(int i = 0; i < 20; i++){
    printf("i = %2d rand = %d\n", i, Utility::GetRandomNumberInRange(1, 5));
  }
}

*/
