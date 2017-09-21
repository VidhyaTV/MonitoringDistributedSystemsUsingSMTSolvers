#include <vector>
#include <string>
#include <sstream>
#include <numeric>
#include <random>
#include <algorithm> // for for_each
#include <iomanip>
#include <fstream>

#include "Process.h"
#include "utility.h"
#include "runsimulation.h"

using namespace std;

#define INF 1000000	  //infinity


/*
  Define and assigned global variable in main.cpp
*/

int number_of_processes = 10;   // number of processes/nodes

int delta = 1;          // minimum message delay      
int epsilon = 100;       // uncertainty windows
int delta_max = delta;  
double alpha = 0.05;     // message rate

int run_up_to = 100000; // total number of physical clock cycles in simulation
int absolute_time;      // index of physical clock cycles

distance_matrix D;
probability_matrix prob_matrix;
string topology_file_name;
string prob_matrix_file_name;

double localPredRate = 0.1;   // randomly generate localPredicate according to this parameter
int num_of_runs = 10;       // number of run for each experiments

int glob_true_interval;
int interval=5;

int run=0;
int num_of_gates=0;


/* utility function for paring commandline argument */

enum optionCode{
    DELTA,
    EPSILON,
    ALPHA,
    RUN_UP_TO,
    NUMBER_OF_PROCESSES,
    PROBABILITY_MATRIX_FILE,
    LOCAL_PRED_RATE,
    NUM_OF_BINS,
    NUM_OF_RUNS,
    TOPOLOGY_FILE,
	INTERVAL,
    UNDEFINED
};

optionCode getOptionCode(const string optionString){
    if(optionString == "-d") return DELTA;
    if(optionString == "-e") return EPSILON;
    if(optionString == "-a") return ALPHA;  
    if(optionString == "-u") return RUN_UP_TO;
    if(optionString == "-p") return NUMBER_OF_PROCESSES;
    if(optionString == "-m") return PROBABILITY_MATRIX_FILE;
    if(optionString == "-l") return LOCAL_PRED_RATE;
    if(optionString == "-b") return NUM_OF_BINS;
    if(optionString == "-r") return NUM_OF_RUNS;
    if(optionString == "-t") return TOPOLOGY_FILE;
    if(optionString == "-v") return INTERVAL;
    
    return UNDEFINED;
}

vector<string> splitArg(const string& s){
    vector<string> result;   
    string item1, item2;
    
    item1 = s.substr(0,2);
    result.push_back(item1);
    item2 = s.substr(2,string::npos);
    result.push_back(item2);
    
    //cout << "   item1 = " << item1 << "  item2 = " << item2 << endl;
    
    return result;
}

int parseArg(int argc, char* argv[]){
    int i;
    vector<string> currentArg;
    
    for(i = 1; i < argc; i++){
        //cout << "arg_" << i << " = " << argv[i] << endl;

        currentArg = splitArg(argv[i]);

        
        switch(getOptionCode(currentArg.at(0))){
        case DELTA:
            delta = atoi(currentArg.at(1).c_str());
            cout.width(30);
            cout << "delta = " << delta << endl;
            break;
        case EPSILON:
            epsilon = atoi(currentArg.at(1).c_str());
            cout.width(30);
            cout << "epsilon = " << epsilon << endl;
            break;
        case ALPHA:
            alpha = atof(currentArg.at(1).c_str());
            cout.width(30);
            cout << "alpha = " << alpha << endl;
            break;
        case RUN_UP_TO:
            run_up_to = atoi(currentArg.at(1).c_str());
            cout.width(30);
            cout << "run_up_to = " << run_up_to << endl;
            break;
        case NUMBER_OF_PROCESSES:
            number_of_processes = atoi(currentArg.at(1).c_str());
            cout.width(30);
            cout << "number_of_processes = " << number_of_processes << endl;
            break;
        case PROBABILITY_MATRIX_FILE:
            prob_matrix_file_name = currentArg.at(1);
            cout.width(30);
            cout << "prob_matrix_file_name = " << prob_matrix_file_name << endl;
            break;
        case LOCAL_PRED_RATE:
            localPredRate = atof(currentArg.at(1).c_str());
            cout.width(30);
            cout << "localPredRate = " << localPredRate << endl;
            break;
        case NUM_OF_BINS:
			/*
            num_of_bins = atoi(currentArg.at(1).c_str());
            cout.width(30);
            cout << "num_of_bins = " << num_of_bins << endl;
			*/
            break;
        case NUM_OF_RUNS:
            num_of_runs = atoi(currentArg.at(1).c_str());
            cout.width(30);
            cout << "num_of_runs = " << num_of_runs << endl;
            break;
        case TOPOLOGY_FILE:
            topology_file_name = currentArg.at(1);
            cout.width(30);
            cout << "topology_file_name = " << topology_file_name << endl;
            break;
        case INTERVAL:
            interval = atoi(currentArg.at(1).c_str());
            cout.width(30);
            cout << "interval = " << interval << endl;
            break;
        default:
            cout << "ERROR: undefined option" << currentArg.at(0) << endl;
            exit(1);   
        }
    }
    return 0;
}

/* main function */

int main(int argc, char* argv[]) {
     
	// parsing commandline argument
	parseArg(argc, argv);
	
	glob_true_interval=interval;

   	for(int i = 0; i < num_of_runs; i++)
	{
		/************code for predicate printing***********/
		ofstream wcp_predicate("predicate_a"+std::to_string(alpha)+"_e"+std::to_string(epsilon)+"_l"+std::to_string(localPredRate)+"_d"+std::to_string(delta)+"_v"+std::to_string(glob_true_interval)+"_run"+std::to_string(i)+".xml",ios::out | ios::app);
		
		num_of_gates=0;
		
		run=i;

		wcp_predicate<<"<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
		wcp_predicate<<"<system_run id=\""<<i<<"\">\n";
		//wcp_predicate<<"(set-option :produce-unsat-cores true)\n";
		//wcp_predicate<<"(set-option :produce-models true)\n";

		//for(int pr=0; pr < number_of_processes; pr++)
		{
			//wcp_predicate<<"<xs:element name=\"x\""<<pr<<" type=\"xs:boolean\"/>\n";
			//wcp_predicate<<"<xs:element name=\"l\""<<pr<<" type=\"xs:nonNegativeInteger\"/>\n";
			//wcp_predicate<<"<xs:element name=\"c\""<<pr<<" type=\"xs:nonNegativeInteger\"/>\n";
			//wcp_predicate<<"(declare-const x"<<pr<<" Bool)\n";
			//wcp_predicate<<"(declare-const l"<<pr<<" Int)\n";
			//wcp_predicate<<"(assert (>= l"<<pr<<" 0))\n";
			//wcp_predicate<<"(declare-const c"<<pr<<" Int)\n";
			//wcp_predicate<<"(assert (>= c"<<pr<<" 0))\n";
		}
		for(int pr=0; pr < number_of_processes; pr++)
		{
			for(int pr1=0; pr1 < number_of_processes; pr1++)
			{
				if(pr1!=pr)
				{
					//wcp_predicate<<"(0 <= (l"<<pr<<"- l"<<pr1<<") <= "<<epsilon<<") OR (0 <= (l"<<pr1<<"- l"<<pr<<") <= "<<epsilon<<")";
					//wcp_predicate<<"(assert (or (and (< (- l"<<pr<<" l"<<pr1<<") "<<4*epsilon<<") (>= (- l"<<pr<<" l"<<pr1<<") 0)) (and (< (- l"<<pr1<<" l"<<pr<<") "<<4*epsilon<<") (> (- l"<<pr1<<" l"<<pr<<") 0))))\n";
					num_of_gates=num_of_gates+3;//2 ands + 1 or
				}
			}	
		}

		//wcp_predicate<<"(assert ";
		
		for(int pr=0; pr < number_of_processes-1; pr++)
		{
			//wcp_predicate<<"(and (= x"<<pr<<" true) ";
			num_of_gates=num_of_gates+1;
		}
		//wcp_predicate<<"print predicate to detect here\n";
		
		//wcp_predicate<<"(= x"<<number_of_processes-1<<" true)";
		for(int pr=0; pr < number_of_processes; pr++)
		{
			//wcp_predicate<<")";
		}
		//wcp_predicate<<"\n";
		
		wcp_predicate<<"<sys epsilon=\""<<epsilon<<"\" number_of_processes=\""<<number_of_processes<<"\"/>\n";
		wcp_predicate.close();
		/**************************************************/	
		
		//cout <<"\nAlpha:"<<alpha<<"_Epsilon:"<<epsilon<<"_LocalPredRate:"<<localPredRate<<"_Delta:"<<delta<<"_Intervallength:"<<glob_true_interval<<"_Run"<<i<<endl;
		RunSimulation::run(RAND_UNICAST, "Delay-n3,run10,alpha0d1,eps10,delta1");
		
		/************code for predicate printing***********/
		ofstream wcp_predicate_1("predicate_a"+std::to_string(alpha)+"_e"+std::to_string(epsilon)+"_l"+std::to_string(localPredRate)+"_d"+std::to_string(delta)+"_v"+std::to_string(glob_true_interval)+"_run"+std::to_string(i)+".xml",ios::out | ios::app);
		
		//wcp_predicate<<"(check-sat)(get-model)(get-unsat-core)(get-info :all-statistics)\n";
		//wcp_predicate_1<<"(check-sat)(get-info :all-statistics)\n";
		wcp_predicate_1<<"</system_run>\n";
		wcp_predicate_1.close();
		/**************************************************/		
		cout<<"num_of_gates:"<<num_of_gates<<"\n";
		
    }
}

        





