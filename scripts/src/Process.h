/*
    process.h - class Process and class Message
*/

#ifndef  PROCESS_H
#define  PROCESS_H


#include <set>
#include <vector>
#include <queue>    // std::queue
#include <numeric>  // for accumulate()

#include "clock.h"

using namespace std;


/*
  External global variables
*/

extern int number_of_processes;
extern double alpha;
extern distance_matrix D;
extern double localPredRate;
extern int glob_true_interval;

/*******variables for predicate printing********/
extern int num_of_gates;
extern int run;
extern int delta;
extern int epsilon;

/*
  message - structure of a message communicated between processes
*/
struct message{
	message(int arrival_time, const HVC& sender_at,const HLC& lsender_at,int phy_sender_at, int sender_id) : arrival_time(arrival_time), sender_at(sender_at),lsender_at(lsender_at), phy_sender_at(phy_sender_at),sender_id(sender_id){}

	int arrival_time;
	HVC sender_at;
	int sender_id;
	HLC lsender_at;
	int phy_sender_at;

  // define the operator <() which is used to order messages in mailbox (i.e. set<message>)
	bool operator < (const message& rhs) const {
		if (arrival_time != rhs.arrival_time) return arrival_time < rhs.arrival_time;
		return sender_id < rhs.sender_id;
	}
};
/*
  Process - class for a process/node in a distributed system
*/

class Process {
private:
	bool time_locked = 0;   // to control RefreshClock() from updating multiple 
	                        // times within one physical clock cycle. 
	                        // When time_locked = false, RefreshClock() will update augmented_time
	                        // when time_locked = true, RefreshClock() does nothing
	                        
	int my_time_now = 0;  // time of process at current physical clock cycle
	
	int id =-1;             // process' ID.
	set<message> mail_box;  // collection of messages a process received, ordered by time of reception
	
	HVC augmented_time;     // hybrid vector clock
	HLC logical_time;     	// hybrid logical clock
	
	int true_interval=0;	// interval size
	
	/**variable for handling interval split due to communication**/
	int true_interval_bkup=0;
	bool remember_to_start_true_interval_after_break=false;
	bool interval_ended_due_to_comm=false;
	/************************************************************/
	
	HLC first_true_logical_time;
	HLC first_false_logical_time;
	
	int first_true_physical_time;
	int first_false_physical_time;
	
	bool new_true_start=false;//variable to track first true point
	bool report_first_time=true;

	int GetTimeNow() const ;
	void RefreshClock();
public:
  // Constructor
	Process(){ }
	Process(int id) : id(id)
	{
	//augmented_time = HVC(vector<int>(number_of_processes, my_time_now-epsilon),1); 
	//augmented_time.setHVCElement(my_time_now,id);
	//augmented_time = HVC(vector<int>(number_of_processes, 0),1); 
	logical_time=HLC(vector<int>(2,0));//each assigned to 0
	first_true_logical_time=HLC(vector<int>(2,-1));//each assigned to -1
	
	/************code for predicate printing***********/

	first_false_logical_time=HLC(vector<int>(2,-1));//each assigned to -1
	
	first_true_physical_time=0;
	first_false_physical_time=0;

	/*************************************************/

	my_time_now = epsilon;
	report_first_time=true;
	remember_to_start_true_interval_after_break=false;
	interval_ended_due_to_comm=false;
  	}  
	
	/************code for predicate printing***********/
	void PrintLogicalTime();//function to print the max logical time of the process
	/*************************************************/

  // gets and sets
	int GetId() { return id; }

  // methods for message communication
	void SendMsg(Process& k);
	void ReceiveMsg();
	void UpdateLocalEvent();
	void BroadcastMsg(vector<Process>& vp);
	void PushMsg(const message& m);
	void UnlockTime() { time_locked = false; }
	// generate next candidate at random to propose for Garg's algorithm
	int RandGenCand();

};


#endif
