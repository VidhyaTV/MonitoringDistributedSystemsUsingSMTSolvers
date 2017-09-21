int Process::RandGenCand(){
	//if the previous interval has ended
	if(true_interval<=0)
	{
		//interval ended due to communication'
		if(some variable to denote end due to communication)
		{
			//report first piece of split interval. i.e. till first_false_logical_time, 
			//set new_true_start to false (check if any other variable has to be set)
			
			//remember_to_start_true_interval_after_break			//because you dont know the next logical time in advance
			
			//set "some variable to denote end due to communication" to false
			
		}		
		//interval ended after gradual decline
		else
		{
			//start the second piece of true interval caused by split due to communication
			if((remember_to_start_true_interval_after_break))
			{
				//just update first_true_logical_time, 
				//new_true_start = true;
				//true_interval=true_interval_bkup;
				//remember_to_start_true_interval_after_break=false;
			}
			else//then toss coin again
			{
				// create a new candidate and push it into the queue if pred becomes true
				if(Utility::GetRandomNumberInRange(1, 100)*1.0 <= localPredRate * 100)
				{
					
				}//end of if where the predicate became true
				else//pred was false, report end of true interval one has started already
				{
					
					new_true_start=false;			// reset interval start
					return 1;
				}//end of else //where predicate did not become true
			}
		}
	}//end of if where true_interval became <=0
	else	//if the true interval has not ended yet
	{		
		//decrementing interval size
		true_interval--;
		return 1;
	}
}
