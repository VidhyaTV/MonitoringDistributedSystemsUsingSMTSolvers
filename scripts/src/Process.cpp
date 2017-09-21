
#include <random>
#include <algorithm>
#include <numeric>
#include <iostream>
#include <fstream>

using namespace std;

#include "Process.h"

/* send message to a set of processes */
void Process::BroadcastMsg(vector<Process>& vp) 
{
	for (int k = 0; k < number_of_processes; k++) {
		if (k != id) SendMsg(vp[k]);
	}
}
/* send message to a process */
void Process::SendMsg(Process& k)  
{
	//cout<<"send message\n";

	//send message based on alpha or communication frequency
	if (Utility::GetRandomNumberInRange(1, 100)*1.0 <= alpha * 100) {
		
		my_time_now = GetTimeNow();
		RefreshClock();
		
		//code for HVC bound -Sorrachai    		
		// D is distance matrix
		int distance = D[id][k.id];
		int time_delay_msg = 0;
		for (int i = 0; i < distance; i++) {
			time_delay_msg += PhysicalTime::GetDelayMessageTime();
		}

		/************code for predicate printing***********/
		//HLC algorithm		
		vector<int> lc=logical_time.getHLC();	//get the current HLC value(l and c) of the process
		
		int l_final=lc[0];			//buffer variable for the l value	
		lc[0]=max(l_final,my_time_now);		//l is assigned to the max among process' l or the physical time
		if(lc[0]==l_final)			//if the updated l was obtained from the previous l value
		{	lc[1]=lc[1]+1;			//increment the c value by 1
		}
		else					//if the updated l was obtained from the physical time
		{	lc[1]=0;			//reset the c value		
		}
		logical_time.setHLC(lc);
		
		/************code for predicate printing***********/
		ofstream wcp_predicate("predicate_a"+std::to_string(alpha)+"_e"+std::to_string(epsilon)+"_l"+std::to_string(localPredRate)+"_d"+std::to_string(delta)+"_v"+std::to_string(glob_true_interval)+"_run"+std::to_string(run)+".xml",ios::out | ios::app);
		//wcp_predicate<<"<message type=\"send\" process=\""<<id<<"\"><sender_time><l>"<<logical_time.getHLCElement(0)<<"</l><c>"<<logical_time.getHLCElement(1)<<"</c></sender_time><to>"<<k.id<<"</to></message>\n";
		wcp_predicate<<"<message type=\"send\" process=\""<<id<<"\"><sender_time>"<<my_time_now<<"</sender_time><to>"<<k.id<<"</to></message>\n";
		
		wcp_predicate.close();			
		/**************************************************/
		
		if(first_true_logical_time.getHLCElement(0)!=-1)//end the interval in case of communication only if one exists
		{
			true_interval_bkup=true_interval;
			true_interval=0;			
			interval_ended_due_to_comm=true;
		}
		/*****************************************************/	

		k.PushMsg(message(time_delay_msg + absolute_time,augmented_time, logical_time.getHLC(),my_time_now, id));//push the message to process k's mailbox with updated hlc
	}
}
/*local event that updates process' HLC*/
void Process::UpdateLocalEvent()  {

	my_time_now = GetTimeNow();		//get physical time
	
	/************code to correct HLC/HVC***********/
	if (!time_locked)//update HLC only of not done already during this program step
	{
		//HLC algorithm		
		vector<int> lc=logical_time.getHLC();	//get the current HLC value(l and c) of the process
		
		int l_final=lc[0];			//buffer variable for the l value	
		lc[0]=max(l_final,my_time_now);		//l is assigned to the max among process' l or the physical time
		if(lc[0]==l_final)			//if the updated l was obtained from the previous l value
		{	lc[1]=lc[1]+1;			//increment the c value by 1
		}
		else					//if the updated l was obtained from the physical time
		{	lc[1]=0;			//reset the c value		
		}
		/********************************************************/

		logical_time.setHLC(lc);		//update process' hlc value
	}
	//cout<<"localevent\n";
	RefreshClock();
}
/*receive messages */
void Process::ReceiveMsg(){
	//cout<<"receive message\n";
	//read only those messages that have arrival time less than current physical time
	if (!mail_box.empty() && begin(mail_box)->arrival_time <= PhysicalTime::GetAbsoluteTime()) {
		my_time_now = GetTimeNow();				//get physical time
		RefreshClock();
		
		//read all messages that have arrival time less than current physical time
		while (!mail_box.empty() && begin(mail_box)->arrival_time <= PhysicalTime::GetAbsoluteTime()) 
		{
			auto m_itr = begin(mail_box);			//pointer to message
			//vector<int> m_at = m_itr->sender_at.getHVC();	//get sending process' HVC
			
			/************code for predicate printing***********/
			//for (int i = 0; i < (int)m_at.size(); i++) {	//updating HVC
			//for (int i = 0; i < number_of_processes; i++) {	//updating HVC
			/**************************************************/	
			//augmented_time.setHVCElement(max(m_at[i], augmented_time.getHVC()[i]),i);
			//}
			
			/************code for predicate printing***********/
			/**HLC**/
			vector<int> message_lc= m_itr->lsender_at.getHLC();//get sending process' hlc	
			int message_phyc= m_itr->phy_sender_at;//get sending process' physical clock
			
			vector<int> lc=logical_time.getHLC();		//process' hlc
			
			int l_final, buffvar;
			l_final=lc[0];								//store l value's copy as l_final
			buffvar=max(message_lc[0],my_time_now);		//get max over sender's l present in the message 
														//and current physical time, and store it as buffvar
			lc[0]=max(l_final,buffvar);					//get max over process' l and buffvar, 
														//and update the process' l to it
			
			if((lc[0]==l_final)&&(lc[0]==message_lc[0]))//if the new l value is same as old l value
			{											//and the sender's l value
				lc[1]=max(lc[1],message_lc[1])+1;		//then find the max value among the sender's c 
														//and process', and update the process' c to this plus one
				//cout<<"All are equal\n";	
			}
			else if(lc[0]==l_final)						//if the new l value is same as the old l value
			{
				lc[1]=lc[1]+1;							//then increment c by 1
				//cout<<"Got from older value\n";		
			}
			else if(lc[0]==message_lc[0])				//if the new l value is same as the 
			{											//sender's l value in the message then
				lc[1]=message_lc[1]+1;					//set c to the sender's c plus 1
				//cout<<"Got from message\n";
			}
			else										//if the new l value was obtained from the physical time
			{	//cout<<"Got from phy time\n";	
				lc[1]=0;								//then reset c value to 0
			}
			logical_time.setHLC(lc);			//update the process' HLC with these new l and c values
			/*************************************************************************************/
			if(first_true_logical_time.getHLCElement(0)!=-1)//end the interval in case of communication only if one exists
			{
			true_interval_bkup=true_interval;
			true_interval=0;//end interval when communication happens
			interval_ended_due_to_comm=true;
			}
			/************code for predicate printing***********/
			ofstream wcp_predicate("predicate_a"+std::to_string(alpha)+"_e"+std::to_string(epsilon)+"_l"+std::to_string(localPredRate)+"_d"+std::to_string(delta)+"_v"+std::to_string(glob_true_interval)+"_run"+std::to_string(run)+".xml",ios::out | ios::app);
			
			//wcp_predicate<<"(assert (! (=> (>= l"<<id<<" "<<(4*lc[0])+lc[1]<<") (not (<= "<<"l"<<m_itr->sender_id<<" "<<(4*message_lc[0])+message_lc[1]<<"))) :named constraint_msgAtp"<<id<<"_at_l"<<lc[0]<<"_at_c"<<lc[1]<<"_fromp"<<m_itr->sender_id<<"))\n";

			//wcp_predicate<<"<message type=\"receive\" process=\""<<id<<"\"><from>"<<m_itr->sender_id<<"</from><sender_time><l>"<<message_lc[0]<<"</l><c>"<<message_lc[1]<<"</c></sender_time><receiver_time><l>"<<logical_time.getHLCElement(0)<<"</l><c>"<<logical_time.getHLCElement(1)<<"</c></receiver_time></message>\n";
			wcp_predicate<<"<message type=\"receive\" process=\""<<id<<"\"><from>"<<m_itr->sender_id<<"</from><sender_time>"<<message_phyc<<"</sender_time><receiver_time>"<<my_time_now<<"</receiver_time></message>\n";
			
			num_of_gates=num_of_gates+3;//1 not, 1(2) implies, 
			wcp_predicate.close();			
			/**************************************************/
			mail_box.erase(m_itr);				//erase the read message
		}//end of while
	}
}
void Process::PushMsg(const message& m){
	mail_box.insert(m);
}
int Process::GetTimeNow() const {
	//cout<<"at p"<<id<<" getting mytime\n";
	if (time_locked) 
	{
		//cout<<my_time_now<<"\n";
		return my_time_now;
	}
	else
	{
		//cout<<max(my_time_now+1,PhysicalTime::GetTimeNow())<<"\n";
		return max(my_time_now+1,PhysicalTime::GetTimeNow());
	}
}

// RefreshClock is called whenever process sends or receives messages
void Process::RefreshClock() {
	if (time_locked) return;
	/*
	for (int i = 0; i < number_of_processes; i++) {
		if (i == id) continue;
		if (augmented_time.getHVC()[i] < my_time_now - epsilon ) {
			//cout<<"didnt hear for long so updating\n";
			augmented_time.setHVCElement(my_time_now - epsilon, i);
		}
	}
	augmented_time.setHVCElement(my_time_now, id);
	*/
	time_locked = true;
}

/************code for predicate printing***********/
void Process::PrintLogicalTime()
{
	my_time_now=GetTimeNow();
	ofstream wcp_predicate("predicate_a"+std::to_string(alpha)+"_e"+std::to_string(epsilon)+"_l"+std::to_string(localPredRate)+"_d"+std::to_string(delta)+"_v"+std::to_string(glob_true_interval)+"_run"+std::to_string(run)+".xml",ios::out | ios::app);
	
	//code to report last interval depending on what is set first_false_logical_time or first_true_logical_time
	if((first_false_logical_time.getHLCElement(0)!=-1) && (first_true_logical_time.getHLCElement(0)!=-1))
	{
		cout<<"both cant be true!\n";
		return;
	}
	
	//if predicate was never true, then no interval would have been reported so report a full false interval
	if((first_false_logical_time.getHLCElement(0)==-1) && (first_true_logical_time.getHLCElement(0)==-1))
	{
		
		cout<<"predicate was never true at p"<<id<<"\n";
		//wcp_predicate<<"(assert (! (=> ";
		//wcp_predicate<<"(and (<= "<<(4*first_false_logical_time.getHLCElement(0))+first_false_logical_time.getHLCElement(1)<<"  l"<<id<<") (< l" << id <<" "<<(4*logical_time.getHLCElement(0))+logical_time.getHLCElement(1)<<")) ";
		//wcp_predicate<<" (= x"<<id<<" false)) :named constraint_falseintervalatp"<<id<<"_atl"<<logical_time.getHLCElement(0)-1<<"))\n";
		num_of_gates=num_of_gates+3;//1 and, 1(2) imlies
		//wcp_predicate<<"(assert (< l"<<id<<" "<<(4*logical_time.getHLCElement(0))+logical_time.getHLCElement(1)<<"))\n";
		
		//wcp_predicate<<"<interval associated_variable=\"x\" value=\"false\" process=\""<<id<<"\"><start_time><l>"<<first_false_logical_time.getHLCElement(0)<<"</l><c>"<<first_false_logical_time.getHLCElement(1)<<"</c></start_time><end_time><l>"<<logical_time.getHLCElement(0)<<"</l><c>"<<logical_time.getHLCElement(1)<<"</c></end_time></interval>\n";	
		
		wcp_predicate<<"<interval process=\""<<id<<"\"><start_time>"<<first_false_physical_time<<"</start_time><end_time>"<<my_time_now<<"</end_time><associated_variable name=\"x\" value=\"false\" old_value=\"false\"/></interval>\n";	
	
		wcp_predicate.close();
		
		return;
	}

	//if predicate was last known to be false
	if (first_false_logical_time.getHLCElement(0)!=-1)
	{
		//wcp_predicate<<"(assert (! (=> ";
		//wcp_predicate<<"(and (<= "<<(4*first_false_logical_time.getHLCElement(0))+first_false_logical_time.getHLCElement(1)<<"  l"<<id<<") (< l" << id <<" "<<(4*logical_time.getHLCElement(0))+logical_time.getHLCElement(1)<<"))  ";
		//wcp_predicate<<" (= x"<<id<<" false)) :named constraint_falseintervalatp"<<id<<"_atl"<<logical_time.getHLCElement(0)-1<<"))\n";
		//num_of_gates=num_of_gates+3;//1 and, 1(2) imlies
		//wcp_predicate<<"(assert (< l"<<id<<" "<<(4*logical_time.getHLCElement(0))+logical_time.getHLCElement(1)<<"))\n";
		
		//wcp_predicate<<"<interval associated_variable=\"x\" value=\"false\" process=\""<<id<<"\"><start_time><l>"<<first_false_logical_time.getHLCElement(0)<<"</l><c>"<<first_false_logical_time.getHLCElement(1)<<"</c></start_time><end_time><l>"<<logical_time.getHLCElement(0)<<"</l><c>"<<logical_time.getHLCElement(1)<<"</c></end_time></interval>\n";	
		
		wcp_predicate<<"<interval process=\""<<id<<"\"><start_time>"<<first_false_physical_time<<"</start_time><end_time>"<<my_time_now<<"</end_time><associated_variable name=\"x\" value=\"false\" old_value=\"true\"/></interval>\n";	
		
		wcp_predicate.close();
		
		first_false_logical_time.setHLCElement(-1,0);
		first_false_logical_time.setHLCElement(-1,1);
		first_false_physical_time=0;
		return;
	}
	
	//if predicate was last known to be true
	if (first_true_logical_time.getHLCElement(0)!=-1)
	{
		if (first_true_logical_time.getHLCElement(0)==logical_time.getHLCElement(0))
		{
			if (first_true_logical_time.getHLCElement(1)<logical_time.getHLCElement(1))
			{
				//wcp_predicate<<"(assert (! (=> (and (<= "<<(4*first_true_logical_time.getHLCElement(0))+first_true_logical_time.getHLCElement(1)<<" l"<<id<<") (< l" << id <<" "<<(4*logical_time.getHLCElement(0))+logical_time.getHLCElement(1)<<"))";
				//wcp_predicate<<"(= x"<<id<<" true)";
				//wcp_predicate<<") :named constraint_trueinterval"<<id<<"_"<<logical_time.getHLCElement(0)<<"))\n";
				num_of_gates=num_of_gates+3;//1 and, 1(2) imlies
				//wcp_predicate<<"(assert (< l"<<id<<" "<<(4*logical_time.getHLCElement(0))+logical_time.getHLCElement(1)<<"))\n";
				
				//wcp_predicate<<"<interval associated_variable=\"x\" value=\"true\" process=\""<<id<<"\"><start_time><l>"<<first_true_logical_time.getHLCElement(0)<<"</l><c>"<<first_true_logical_time.getHLCElement(1)<<"</c></start_time><end_time><l>"<<logical_time.getHLCElement(0)<<"</l><c>"<<logical_time.getHLCElement(1)<<"</c></end_time></interval>\n";

				wcp_predicate<<"<interval process=\""<<id<<"\"><start_time>"<<first_true_physical_time<<"</start_time><end_time>"<<my_time_now<<"</end_time><associated_variable name=\"x\" value=\"true\" old_value=\"false\"/></interval>\n";
				
				wcp_predicate.close();
				
				first_true_logical_time.setHLCElement(-1,0);
				first_true_logical_time.setHLCElement(-1,1);
				first_true_physical_time=0;
				return;
			}
			else if((first_true_logical_time.getHLCElement(1)==logical_time.getHLCElement(1)))
			{
				//wcp_predicate<<"(assert (! (=> (= "<<(4*first_true_logical_time.getHLCElement(0))+first_true_logical_time.getHLCElement(1)<<" l"<<id<<")";
				//wcp_predicate<<"(= x"<<id<<" true)";
				//wcp_predicate<<") :named constraint_trueinterval"<<id<<"_"<<logical_time.getHLCElement(0)<<"))\n";
				num_of_gates=num_of_gates+3;//1 and, 1(2) imlies
				//wcp_predicate<<"(assert (<= l"<<id<<" "<<(4*logical_time.getHLCElement(0))+logical_time.getHLCElement(1)<<"))\n";
			
				//wcp_predicate<<"<interval associated_variable=\"x\" value=\"true\" process=\""<<id<<"\"><start_time><l>"<<first_true_logical_time.getHLCElement(0)<<"</l><c>"<<first_true_logical_time.getHLCElement(1)<<"</c></start_time><end_time><l>"<<logical_time.getHLCElement(0)<<"</l><c>"<<logical_time.getHLCElement(1)<<"</c></end_time></interval>\n";
				
				wcp_predicate<<"<interval process=\""<<id<<"\"><start_time>"<<first_true_physical_time<<"</start_time><end_time>"<<my_time_now<<"</end_time><associated_variable name=\"x\" value=\"true\" old_value=\"false\"/></interval>\n";
				wcp_predicate.close();
				
				first_true_logical_time.setHLCElement(-1,0);
				first_true_logical_time.setHLCElement(-1,1);
				first_true_physical_time=0;
				return;
			}
			else{cout<<"code that should not be executed \n";return;}
		}
		else
		{
			//wcp_predicate<<"(assert (! (=> (and (<= "<<(4*first_true_logical_time.getHLCElement(0))+first_true_logical_time.getHLCElement(1)<<" l"<<id<<") (< l" << id <<" "<<(4*logical_time.getHLCElement(0))+logical_time.getHLCElement(1)<<"))";
			//wcp_predicate<<"(= x"<<id<<" true)";
			//wcp_predicate<<") :named constraint_trueinterval"<<id<<"_"<<logical_time.getHLCElement(0)-1<<"))\n";
			num_of_gates=num_of_gates+3;//1 and, 1(2) imlies
			//wcp_predicate<<"(assert (< l"<<id<<" "<<(4*logical_time.getHLCElement(0))+logical_time.getHLCElement(1)<<"))\n";
		
			//wcp_predicate<<"<interval associated_variable=\"x\" value=\"true\" process=\""<<id<<"\"><start_time><l>"<<first_true_logical_time.getHLCElement(0)<<"</l><c>"<<first_true_logical_time.getHLCElement(1)<<"</c></start_time><end_time><l>"<<logical_time.getHLCElement(0)<<"</l><c>"<<logical_time.getHLCElement(1)<<"</c></end_time></interval>\n";	
			
			wcp_predicate<<"<interval process=\""<<id<<"\"><start_time>"<<first_true_physical_time<<"</start_time><end_time>"<<my_time_now<<"</end_time><associated_variable name=\"x\" value=\"true\" old_value=\"false\"/></interval>\n";	
			wcp_predicate.close();
			
			first_true_logical_time.setHLCElement(-1,0);
			first_true_logical_time.setHLCElement(-1,1);
			first_true_physical_time=0;
			return;
		}
	}	
}
/**************************************************/

/*
  Process:RandGenCand() - randomly make local predicate true
    randomly generate a number.
    If the number <= pre-determined rate
	HLC:	Remember the HLC value as the interval start point
    Else
	HLC:	if an interval has started end it and store the interval as a candidate
*/
int Process::RandGenCand(){
	//if the previous interval has ended
	if(true_interval<=0)
	{
		if(interval_ended_due_to_comm)//interval ended due to communication
		{
			//report first piece of split interval. i.e. till first_false_logical_time, 
			ofstream wcp_predicate("predicate_a"+std::to_string(alpha)+"_e"+std::to_string(epsilon)+"_l"+std::to_string(localPredRate)+"_d"+std::to_string(delta)+"_v"+std::to_string(glob_true_interval)+"_run"+std::to_string(run)+".xml",ios::out | ios::app);
			report_first_time=false;
			//wcp_predicate<<"(assert (! (=> (and (<= "<<(4*first_true_logical_time.getHLCElement(0))+first_true_logical_time.getHLCElement(1)<<" l"<<id<<") (< l"<< id <<" "<<(4*logical_time.getHLCElement(0))+logical_time.getHLCElement(1)<<"))";
			//wcp_predicate<<"(= x"<<id<<" true)";
			//wcp_predicate<<") :named constraint_trueinterval"<<id<<"_"<<logical_time.getHLCElement(0)-1<<"))\n";
			//wcp_predicate<<"<interval associated_variable=\"x\" value=\"true\" process=\""<<id<<"\"><start_time><l>"<<first_true_logical_time.getHLCElement(0)<<"</l><c>"<<first_true_logical_time.getHLCElement(1)<<"</c></start_time><end_time><l>"<<logical_time.getHLCElement(0)<<"</l><c>"<<logical_time.getHLCElement(1)<<"</c></end_time></interval>\n";

			wcp_predicate<<"<interval process=\""<<id<<"\"><misc>splitduetocommunication</misc><start_time>"<<first_true_physical_time<<"</start_time><end_time>"<<my_time_now<<"</end_time><associated_variable name=\"x\" value=\"true\" old_value=\"false\"/></interval>\n";
			
			num_of_gates=num_of_gates+3;//1 and, 1(2) implies
			wcp_predicate.close();
			new_true_start=false;
			/*
			first_false_logical_time.setHLCElement(-1,0);
			first_false_logical_time.setHLCElement(-1,1);
			first_true_logical_time.setHLCElement(-1,0);
			first_true_logical_time.setHLCElement(-1,1);
			remember_to_start_true_interval_after_break=true;		//because you dont know the next logical time in advance
			*/
			first_true_logical_time.setHLCElement(logical_time.getHLCElement(0),0);
			first_true_logical_time.setHLCElement(logical_time.getHLCElement(1),1);
			first_true_physical_time=my_time_now;
			
			new_true_start = true;
			if(true_interval_bkup>=1)
			{true_interval=true_interval_bkup-1;}
			interval_ended_due_to_comm=false;
			return 1;
		}
		else
		{
			/*
			//start the second piece of true interval caused by split due to communication (if any)
			if((remember_to_start_true_interval_after_break))
			{
				//just update first_true_logical_time,
				UpdateLocalEvent();
				first_true_logical_time.setHLCElement(logical_time.getHLCElement(0),0);
				first_true_logical_time.setHLCElement(logical_time.getHLCElement(1),1);
				new_true_start = true;
				true_interval=true_interval_bkup-1;
				remember_to_start_true_interval_after_break=false;
			}
			else//else toss coin again
			{
			*/
				// create a new candidate and push it into the queue if pred becomes true
				if(Utility::GetRandomNumberInRange(1, 100)*1.0 <= localPredRate * 100)
				{
					//set interval size to the global interval size provided in simulation.sh
					true_interval=glob_true_interval;
					//if previous true interval just ended and local predicate became true again
					//if((first_true_logical_time.getHLCElement(0)!=-1) && (first_true_logical_time.getHLCElement(0) < logical_time.getHLCElement(0)))
					if(first_true_logical_time.getHLCElement(0)!=-1)
					{
						//cout<<"At P"<<id<<",code that should execute rarely,first_true_logical_time is ("<<first_true_logical_time.getHLCElement(0)<<","<<first_true_logical_time.getHLCElement(1)<<") at logical_time=("<<logical_time.getHLCElement(0)<<","<<logical_time.getHLCElement(1)<<")\n";
					}
					else
					{				
						//report end of false interval for predicate detection
						/************code for predicate printing***********/
						if((first_false_logical_time.getHLCElement(0)!=-1) || (report_first_time))
						{
							UpdateLocalEvent();
							report_first_time=false;
							ofstream wcp_predicate("predicate_a"+std::to_string(alpha)+"_e"+std::to_string(epsilon)+"_l"+std::to_string(localPredRate)+"_d"+std::to_string(delta)+"_v"+std::to_string(glob_true_interval)+"_run"+std::to_string(run)+".xml",ios::out | ios::app);
							//wcp_predicate<<"(assert (! (=> ";
							wcp_predicate<<"<interval process=\""<<id<<"\">";
							if(first_false_logical_time.getHLCElement(0)==-1) 	
							{
								//wcp_predicate<<"(and (<= 0  l"<<id<<") (< l" << id <<" "<<(4*logical_time.getHLCElement(0))+logical_time.getHLCElement(1)<<")) ";
								//wcp_predicate<<"<start_time><l>"<<0<<"</l><c>"<<0<<"</c></start_time><end_time><l>"<<logical_time.getHLCElement(0)<<"</l><c>"<<logical_time.getHLCElement(1)<<"</c></end_time></interval>\n";
								wcp_predicate<<"<start_time>"<<0<<"</start_time><end_time>"<<my_time_now<<"</end_time><associated_variable name=\"x\" value=\"false\" old_value=\"true\"/></interval>\n";
							}
							else
							{						
								//wcp_predicate<<"(and (<= "<<(4*first_false_logical_time.getHLCElement(0))+first_false_logical_time.getHLCElement(1)<<"  l"<<id<<") (< l" << id <<" "<<(4*logical_time.getHLCElement(0))+logical_time.getHLCElement(1)<<")) ";
								//wcp_predicate<<"<start_time><l>"<<first_false_logical_time.getHLCElement(0)<<"</l><c>"<<first_false_logical_time.getHLCElement(1)<<"</c></start_time><end_time><l>"<<logical_time.getHLCElement(0)<<"</l><c>"<<logical_time.getHLCElement(1)<<"</c></end_time></interval>\n";
								wcp_predicate<<"<start_time>"<<first_false_physical_time<<"</start_time><end_time>"<<my_time_now<<"</end_time><associated_variable name=\"x\" value=\"false\" old_value=\"true\"/></interval>\n";
							}
							//wcp_predicate<<" (= x"<<id<<" false)) :named constraint_falseinterval_atp"<<id<<"_atl"<<logical_time.getHLCElement(0)-1<<"))\n";

							num_of_gates=num_of_gates+3;//1 and, 1(2) implies
							first_false_logical_time.setHLCElement(-1,0);
							first_false_logical_time.setHLCElement(-1,1);
							
							first_false_physical_time=0;
													
							//remember the current logical time as the first_true_logical_time to mark the interval start point
							first_true_logical_time.setHLCElement(logical_time.getHLCElement(0),0);
							first_true_logical_time.setHLCElement(logical_time.getHLCElement(1),1);
							
							first_true_physical_time=my_time_now;
						
							//set to true if a new true starting point for the interval is obtained
							new_true_start=true;
							wcp_predicate.close();
							
						/**************************************************/
						}
						else{cout<<"this piece of code should not execute\n";}
						
					}//end of else where the previous true interval was succesfully recorded and new one started
					
					return 1;
				}//end of if where the predicate became true
				else
				{
					if(new_true_start)
					{
						UpdateLocalEvent();
					}
					//if an interval has started and the HLC value corresponding to the start point is set (not the default value)
					if((first_true_logical_time.getHLCElement(0)!=-1)&&(new_true_start))
					{	
						//if the start and end points of the interval are not same
						//if(first_true_logical_time.getHLCElement(0)!=logical_time.getHLCElement(0))
						if((first_true_logical_time.getHLCElement(0)!=logical_time.getHLCElement(0))||(first_true_logical_time.getHLCElement(1)!=logical_time.getHLCElement(1)))
						{					
							/************code for predicate printing***********/					
							ofstream wcp_predicate("predicate_a"+std::to_string(alpha)+"_e"+std::to_string(epsilon)+"_l"+std::to_string(localPredRate)+"_d"+std::to_string(delta)+"_v"+std::to_string(glob_true_interval)+"_run"+std::to_string(run)+".xml",ios::out | ios::app);
							
							if((logical_time.getHLCElement(1)!=-1)&&(logical_time.getHLCElement(0)!=0))
							{
								report_first_time=false;
								//wcp_predicate<<"(assert (! (=> (and (<= "<<(4*first_true_logical_time.getHLCElement(0))+first_true_logical_time.getHLCElement(1)<<" l"<<id<<") (< l"<< id <<" "<<(4*logical_time.getHLCElement(0))+logical_time.getHLCElement(1)<<"))";
								//wcp_predicate<<"(= x"<<id<<" true)";
								//wcp_predicate<<") :named constraint_trueinterval"<<id<<"_"<<logical_time.getHLCElement(0)-1<<"))\n";
								//wcp_predicate<<"<interval associated_variable=\"x\" value=\"true\" process=\""<<id<<"\"><start_time><l>"<<first_true_logical_time.getHLCElement(0)<<"</l><c>"<<first_true_logical_time.getHLCElement(1)<<"</c></start_time><end_time><l>"<<logical_time.getHLCElement(0)<<"</l><c>"<<logical_time.getHLCElement(1)<<"</c></end_time></interval>\n";	
								wcp_predicate<<"<interval process=\""<<id<<"\"><start_time>"<<first_true_physical_time<<"</start_time><end_time>"<<my_time_now<<"</end_time><associated_variable name=\"x\" value=\"true\" old_value=\"false\"/></interval>\n";	
								num_of_gates=num_of_gates+3;//1 and, 1(2) implies
							}
							//this if loop below with its content is not required outside this container if loop i.e.first if within the parent else, because if it was false continuously this variable (first_false_logical_time) need not be changed unless it became true in between
							if(first_false_logical_time.getHLCElement(0)==-1)//this if cond is not required since this if loop is actually inside a loop where a true interv requires reporting, which means pred became false just now so its value will be -1 and has to be set to current logical clock value
							{
								first_false_logical_time.setHLCElement(logical_time.getHLCElement(0),0);
								first_false_logical_time.setHLCElement(logical_time.getHLCElement(1),1);
								
								first_false_physical_time=my_time_now;
							}
							else
							{
								cout<<"code that should not execute because first_false_logical_time should be -1 but it is ("<<first_false_logical_time.getHLCElement(0)<<","<<first_false_logical_time.getHLCElement(1)<<") and first_true_logical_time=("<<first_true_logical_time.getHLCElement(0)<<","<<first_true_logical_time.getHLCElement(1)<<") at logical_time=("<<logical_time.getHLCElement(0)<<","<<logical_time.getHLCElement(1)<<")\n";
							}
							wcp_predicate.close();
							/*************************************************/
							new_true_start=false;			// reset interval start							
							first_true_logical_time.setHLCElement(-1,0);
							first_true_logical_time.setHLCElement(-1,1);
							first_true_physical_time=0;
						}
						else
						{
							cout<<"code that should not execute because local pred cannot become true and false at the same step\n";
						}
					}//end of if where recorded start of true interval looks valid i.e. not -1		
					else
					{
						//cout<<"false continuously, first_true_logical_time should be -1 and it is ("<<first_true_logical_time.getHLCElement(0)<<",new_true_start should be false and it is="<<new_true_start<<")\n";
					}
					return 1;
				}//end of else //where predicate did not become true
			//}
		}
	}//end of if where true_interval became <=0
	else	//if the true interval has not ended yet
	{		
		//decrementing interval size
		true_interval--;
		//cout<<"At P"<<id<<", true_interval="<<true_interval<<"\n";
		return 1;
	}
}
