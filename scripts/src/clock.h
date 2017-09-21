#ifndef CLOCK_H
#define CLOCK_H

/*
  clock.h - classes and functions related to time, clock
            e.g. PhysicalTime, HVC
*/

#include "utility.h"

extern int absolute_time;
extern int epsilon;
extern int delta;
extern int delta_max;

/*
  PhysicalTime - class for simulation of physical time/clock

	        absolute_time 
    0 -----+-----+-----+-----+-----+-----+-----+-----+-----+-----> run_up_to
            -eps | +eps
            <----+---->
             ^
             |
            PhysicalClock::GetTimeNow() is some randome value within [absolute_time-eps; absolute_time+eps]
             |
             v
            Process::GetTimeNow() = PhysicalClock:GetTimeNow()
             |
             v
            my_time_now = Process:GetTimeNow()

*/

class PhysicalTime {
public:
	static int GetTimeNow() {
		return Utility::GetRandomNumberInRange(absolute_time-epsilon,absolute_time+epsilon);
	}
	
	static int GetDelayMessageTime() {
		return Utility::GetRandomNumberInRange(delta, delta_max);
	}
	
	static int GetAbsoluteTime() { 
	  return absolute_time; 
	}

};


/*
  HVC - class for Hybrid Vector Clock
*/

class HVC {
private:
	vector<int> hvc;
	int active_size;

public:
  // Constructors
  
	HVC(){};
	HVC(const HVC &in){ 
	  hvc = in.hvc; 
	  active_size = in.active_size; 
	};
	HVC(const vector<int> & hvc, int active_size) :hvc(hvc), active_size(active_size) {}

  // gets and sets
  vector<int> getHVC() const{
    return hvc;
  } 
  int getActiveSize(){
    return active_size;
  }
  void setHVC(const vector<int> &someHVC){
    hvc = someHVC;
  } 
  void setHVCElement(int time, int pos){
    hvc.at(pos) = time;
  }
  void setActiveSize(int as){
    active_size = as;
  }
  /* 
    happenBefore() - get the logical temporal relationship between this HVC and some other HVC
        return value: 1 if this HVC happens before other HVC
                     -1 if other HVC happens before this HVC
                      0 if concurrent (neither one happens before the other)
  */
  int happenBefore(
    const HVC & they,   // the other HVC to be compared
    int size            // number of elements in vector clock = number of processes
  ){
  
    bool youHappenBefore = true;
    bool theyHappenBefore = true;
    int i;

    for (i = 0; i < size; i++){
      if(hvc.at(i) < they.hvc.at(i))
        theyHappenBefore = false;
      if(hvc.at(i) > they.hvc.at(i))
        youHappenBefore = false;
    }
    /* result
                             theyHappenBefore
                                T     F
                              +----+-----+
                            T | 0  |  1  |
         youHappenBefore      +----+-----+
                            F | -1 |  0  |
                              +----+-----+
    */
    if(youHappenBefore == theyHappenBefore)
      // concurrent
      return 0;

    if(youHappenBefore)
      // you really happen before other HVC
      return 1;
    else
      // they happens before you
      return -1;

  }

};
/*
  HLC - class for Hybrid Logical Clock
*/

class HLC {
private:
	vector<int> hlc;

public:
  // Constructors
  
	HLC(){};
	HLC(const HLC &in){ 
	  hlc = in.hlc; 	 
	};
	HLC(const vector<int> hlc) :hlc(hlc){}

  // getters and setters
  
  vector<int> getHLC() const{
    return hlc;
  }
  
  void setHLC(const vector<int> &someHLC){
    hlc = someHLC;
  }
  void setHLCElement(int value, int pos){
    hlc.at(pos) = value;
  }
  int getHLCElement(int pos){
    return hlc.at(pos);
  }

};
#endif
