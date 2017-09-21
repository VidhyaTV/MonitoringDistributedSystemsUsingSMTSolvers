/*
  runsimulation.cpp - implementation of runsimulation class
*/

#include "runsimulation.h"
 
/* 
  InitiProcess() - initialize all processes with ID starting from 0
*/
vector<Process> RunSimulation::InitProcess() {
	vector<Process> vp;
	for (int i = 0; i < number_of_processes; i++) {
    	// Duong: here Process(i) is constructor
		vp.push_back(Process(i));
	}
	return vp;
}

/*
  InitiAllConfiguration() - initialize simulation paramters from input file
                            initialize global variables
*/
void InitAllConfiguration(const string& parameter_file_name) {
	delta_max = delta;
	D = Utility::AllPairShortestPaths(Utility::ReadGraph(topology_file_name));
	prob_matrix = Utility::ReadProbabilityMatrix(prob_matrix_file_name);
}

void RunSimulation::run(int type, const string& s){
	
	//ofstream wcp_compare_out("wcp_compare",ios::out | ios::app);  // output file containing global snapshot of weak conjunctive predicate
	InitAllConfiguration("parameters.in.linux");//setup all required initial configuration-HLC's global token, HVC's global token
	vector<Process> vp = InitProcess();//create required(number_of_processes) number of objects of type Process
 	
	// simulation main loop 
 
	for (absolute_time = 0; absolute_time < run_up_to; absolute_time++) //for every run, abbsolute time is like every click of the clock
	{	
		for_each(begin(vp), end(vp), [](Process& p) {p.UnlockTime(); p.ReceiveMsg(); });//for each process in the vector of processes:
												//set time_locked=false=>for updating process's phy time,
												//receive messages 
		for_each(begin(vp), end(vp), [&vp, &type](Process& p)//for each process in the vector of processes:
		{
			// sending message according to desired distribution
			switch(type)
			{
				case RAND_UNICAST:			
					p.SendMsg(vp[Utility::GetIndexOfWeightedRandom(prob_matrix[p.GetId()])]);
					break;
				default:
					break;
	    		}
		});	

		//for each process in the vector of processes: perform dummy local event which just updates HLC values of the process

		//for_each(begin(vp), end(vp), [](Process& p) { p.UpdateLocalEvent(); });	

		// for Garg's algorithm //[list of variables to be used inside the for loop]
		
		//for_each(begin(vp), end(vp), [&vp, &wcp_compare_out, &maxTimeDiffList,&tn,&first,&success,&success1,&ftime,&otn](Process& p) 
		for_each(begin(vp), end(vp), [&vp](Process& p) 
		{
			// At each time, process will randomly generate candidate,
			 //i.e. states where local predicates are true.
			p.RandGenCand();
			// At each clock cycle, process will check to see if it has the global token
			// by matching its ID and token's ID
			//   If match: process the token
			 //  If not match: do nothing
			
		});		
	}

	for_each(begin(vp), end(vp), [](Process& p) { p.PrintLogicalTime(); });
	
	//wcp_compare_out.close();
	
    return ;
  
}

