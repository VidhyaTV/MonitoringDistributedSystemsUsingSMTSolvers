//skeleton from tutorialspoint-Java SAX Parser  
//package com.tutorialspoint.xml;

import java.io.File;
import java.io.FileWriter;
import java.io.BufferedWriter;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import java.util.Deque;
import java.util.ArrayDeque;

import java.util.Set;
import java.util.HashSet;

class MessageSendSruct
{
	int msgid;
	int pt;
	int l;
	int c;
	MessageSendSruct(int mid, int ptvalue, int lvalue, int cvalue)
	{
		msgid=mid;
		pt=ptvalue;
		l=lvalue;
		c=cvalue;
	}
	int getMsgid(){return msgid;}
	int getPt(){return pt;}
	int getL(){return l;}
	int getC(){return c;}
}
class Process
{
	int id;
	int l;
	int c;
	int pt;
	
	//variable to remember previous interval's end (current interval's start) when a message is received/sent
	int prev_l;
	int prev_c;
	int prev_pt;
	
	//queue to remember l,c values corresponding to message sends
	Deque<MessageSendSruct> lclog;
	int msg_counter;
	
	boolean reported_interval_already;//variable to track first ever interval reported at a process
	
	Process(int unique_id, int lvalue, int cvalue, int phytime)
	{
		id=unique_id;
		l=lvalue;
		c=cvalue;
		pt=phytime;
		
		msg_counter=0;
		prev_l=0;
		prev_c=0;
		prev_pt=0;
		lclog = new ArrayDeque<MessageSendSruct>();
		
		reported_interval_already=false;
	}
	
	void setId(int passed_id){id=passed_id;}
	void setL(int passed_l){l=passed_l;}
	void setC(int passed_c)
	{
		c=passed_c;
		if(TraceParser.highest_C_seensofar<c)
		{
			TraceParser.highest_C_seensofar=c;
		}
	}
	void setPt(int passed_pt){pt=passed_pt;}
	
	void setOldL(int passed_l){prev_l=passed_l;}
	void setOldC(int passed_c){prev_c=passed_c;}
	void setOldPt(int passed_pt){prev_pt=passed_pt;}
	
	int getId(){return id;}
	int getL(){return l;}
	int getC(){return c;}
	int getPt(){return pt;}
	
	int getOldL(){return prev_l;}
	int getOldC(){return prev_c;}
	int getOldPt(){return prev_pt;}
	
	boolean getReportedIntervalAlready(){return reported_interval_already;}
	void setReportedIntervalAlready(){reported_interval_already=true;}
	
	void updateClock(int physicalTime, boolean sendmsg)
	{
		if (pt==physicalTime)//typically gets executed only msg send cases
		{
			//prev_c=getC();
			setOldC(getC());
			//update only c
			int updatedcvalue=getC()+1;
			setC(updatedcvalue);
		}
		else
		{
			if(l>=physicalTime)//typically gets executed only msg send cases-- because for msg recieve it is handled in "characters(..)" function
			{
				System.out.println("at p"+id+", l:"+l+",physicaltime:"+physicalTime+",prevpt:"+prev_pt);
				//prev_c=getC();
				setOldC(getC());
				int updatedcvalue=getC()+1;
				setC(updatedcvalue);
				//if(pt<physicalTime)
				if(getPt()<physicalTime)
				{						
					//prev_pt=pt;
					setOldPt(getPt());
					//pt=physicalTime;
					setPt(physicalTime);
				}
			}
			else//can get executed during msg send/receive
			{
				//prev_l=l;
				setOldL(getL());
				//prev_c=c;
				setOldC(getC());
				//prev_pt=pt;
				setOldPt(getPt());
				//update l
				//l=physicalTime;
				setL(physicalTime);
				//c=0;
				setC(0);
				//pt=physicalTime;
				setPt(physicalTime);
			}
		}
		if(sendmsg)
		{
			//push message id, l, c into queue
			MessageSendSruct newmsg= new MessageSendSruct(msg_counter++,getPt(),getL(),getC());
			lclog.add(newmsg);
		}
	}
	MessageSendSruct getLCfromQueue(int passed_phytime)
	{
		while(lclog.peek().getPt()!=passed_phytime)
		{
			System.out.println(passed_phytime+","+lclog.peek().getPt());
			System.out.println("FIFO VIOLATED...popping..");
			lclog.pop();
		}
		MessageSendSruct msgptlc=lclog.peek();
		if(msgptlc!=null)
		{
			if(passed_phytime == msgptlc.getPt())
			{
				System.out.println("FOUND MATCHING SEND");
				return lclog.pop();
			}
			else
			{	
				System.out.println("CODE THAT SHOULD NOT EXECUTE");
				System.exit(0);
			}
			return lclog.peek();
		}
		else
		{
			System.out.println("SEND QUEUE EMPTY");
			System.exit(0);
			return msgptlc;
		}
	}
}
class SysAtHand
{
	int epsilon;
	int number_of_processes;
	void SetEpsilon(int eps){epsilon=eps;}
	void SetNumberOfProcesses(int nproc){number_of_processes=nproc;}
	int GetEpsilon(){return epsilon;}
	int GetNumberOfProcesses(){return number_of_processes;}
}
public class TraceParser 
{
	static int highest_C_seensofar=0;
	public static void main(String[] args) 
	{
		try 
		{	
			//File inputFile = new File("../print_traces_forpredicate_detection_xml_singleboolvariable_x/predicate_a0.010000_e10_l0.100000_d100_v10_run0.xml");
			File inputFile = new File("../predicate_a0.100000_e100_l0.100000_d10_v1_run2.xml");
			SAXParserFactory factory = SAXParserFactory.newInstance();
			SAXParser saxParser = factory.newSAXParser();
			UserHandler userhandler = new UserHandler();
			saxParser.parse(inputFile, userhandler); 
		} 
		catch (Exception e) 
		{
			e.printStackTrace();
		}
	}
}
class UserHandler extends DefaultHandler
{
	boolean bmsender_time = false;
	boolean bmsgto = false;
	boolean bmsgfrom = false;
	boolean bmreceiver_time = false;
	boolean bstart_time=false;
	boolean bend_time=false;
	boolean bmisc=false;
	
	int proc_id=-1;//variable to remember process id
	
	int sender_time=-1;// variable to remember sender time for message RECEIVE
	int senderid=-1;// variable to remember sender id for message RECEIVE
	
	SysAtHand sysathand=new SysAtHand();
	
	Map<Integer, Process> mapofprocesses = new HashMap<Integer, Process>();//map of processes with process id as the key and Process instance as value
	
	Set<String> variableNameSet = new HashSet<String>();
	
	//variables for printing z3 constraints for intervals
	String intervalConstraint="";
	int bracescount=0;
	
	void printEpsConstraints(int eps,int nproc)
	{
		try
		{
			File file = new File("constraints.smt2");
			FileWriter fw = new FileWriter(file.getAbsoluteFile());
			BufferedWriter bw = new BufferedWriter(fw);
			for(int pr=0; pr < nproc; pr++)
			{
				bw.append("(declare-const l"+pr+" Int)\n(assert (>= l"+pr+" 0))\n");
			}
			for(int pr=0; pr < nproc; pr++)
			{
				for(int pr1=0; pr1 < nproc; pr1++)
				{
					if(pr1!=pr)
					{
						bw.append("(assert (or (and (< (- l"+pr+" l"+pr1+") "+22*eps+") (>= (- l"+pr+" l"+pr1+") 0)) (and (< (- l"+pr1+" l"+pr+") "+22*eps+") (> (- l"+pr1+" l"+pr+") 0))))\n");
					}
				}	
			}
			bw.close(); // Be sure to close BufferedWriter
		}
		catch (Exception exc) 
		{
			System.out.println(exc);
		}
	}
	void printFinalConstraints()
	{
		try
		{
			//print z3 constraint
			File file = new File("constraints.smt2");
			FileWriter fw = new FileWriter(file.getAbsoluteFile(),true);
			BufferedWriter bw = new BufferedWriter(fw);
			int nproc= sysathand.GetNumberOfProcesses();
			for(int pr=0; pr < nproc; pr++)
			{
				Process proc= mapofprocesses.get(pr);
				bw.append("(assert (< l"+pr+" "+((22*proc.getL())+proc.getC())+"))\n");
			}
			//PREDICATE TO DETECT
			bw.append("(assert ");		
			for(int pr=0; pr < nproc-1; pr++)
			{
				//bw.append("(and (= var1_"+pr+" 1) ");
				bw.append("(and (= x_"+pr+" true) ");
			}
			//bw.append("(= var1_"+(nproc-1)+" 1)");
			bw.append("(= x_"+(nproc-1)+" true)");
			for(int pr=0; pr < nproc; pr++)
			{
				bw.append(")");
			}
			bw.append("\n");
			bw.append("(check-sat)(get-info :all-statistics)\n");
			bw.close();
			System.out.println("\n Highest c value seen so far in this run:"+TraceParser.highest_C_seensofar);
		}
		catch (Exception e) 
		{
			e.printStackTrace();
		}
	}
	
	@Override
	public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException 
	{
		if (qName.equalsIgnoreCase("message")) 
		{
			String type = attributes.getValue("type");
			String process = attributes.getValue("process");
			System.out.println("message " + type + " event at process " +process);
			proc_id=Integer.parseInt(process);
		} 
		else if(qName.equalsIgnoreCase("sys"))
		{
			int eps = Integer.parseInt(attributes.getValue("epsilon"));
			int nproc = Integer.parseInt(attributes.getValue("number_of_processes"));
			//System.out.println("System: epsilon=" + eps + ", number_of_processes=" +nproc);
			sysathand.SetEpsilon(eps);
			sysathand.SetNumberOfProcesses(nproc);
			
			//create |l1-l2|<=epsilon constraints
			printEpsConstraints(eps,nproc);
			//create nproc number of instances of class process and assign ids to them
			for (int i=0; i<nproc; i++)
			{
				Process proc = new Process(i,0,0,0);
				mapofprocesses.put(i,proc);
			}
		}
		else if (qName.equalsIgnoreCase("sender_time")) 
		{
			bmsender_time = true;
		} 
		else if (qName.equalsIgnoreCase("to")) 
		{
			bmsgto = true;
		} 
		else if (qName.equalsIgnoreCase("from")) 
		{
			bmsgfrom = true;
		}
		else if (qName.equalsIgnoreCase("receiver_time")) 
		{
			bmreceiver_time = true;
		}
		else if (qName.equalsIgnoreCase("interval")) 
		{
			String process = attributes.getValue("process");
			//System.out.println("Interval at process " +process);
			proc_id=Integer.parseInt(process);
		} 
		else if (qName.equalsIgnoreCase("start_time")) 
		{
			bstart_time = true;
		} 
		else if (qName.equalsIgnoreCase("end_time")) 
		{
			bend_time = true;
		}
		else if (qName.equalsIgnoreCase("associated_variable")) 
		{
			String name = attributes.getValue("name");
			String value = attributes.getValue("value");
			String old_value = attributes.getValue("old_value");
			//System.out.println("associated variable " + name + ": value=" +value + " oldvalue=" +old_value);
			try
			{
				//print z3 constraint
				File file = new File("constraints.smt2");
				FileWriter fw = new FileWriter(file.getAbsoluteFile(),true);
				BufferedWriter bw = new BufferedWriter(fw);
				
				String variablename=""+name+"_"+proc_id+"";
				if(!variableNameSet.contains(variablename))//if variable was not declared already
				{
					//assuming variables are either boolean or integers starting with initial value 0
					if(value.equalsIgnoreCase("true")||value.equalsIgnoreCase("false"))
					{
						bw.append("(declare-const "+variablename+" Bool)\n");
					}
					else if(value.equalsIgnoreCase("0"))
					{
						bw.append("(declare-const "+variablename+" Int)\n");
					}
					else
					{
						System.out.println("Scanned value was neither boolean or integer\n");
						System.exit(0);
					}
					variableNameSet.add(variablename);
				}
				intervalConstraint=intervalConstraint+" (and (= "+variablename+" "+value+") ";
				bracescount++;
				bw.close(); // Be sure to close BufferedWriter
				//System.out.println("End Element :" + qName+"\n");
			}
			catch (Exception e) 
			{
				e.printStackTrace();
			}
		}
		else if (qName.equalsIgnoreCase("misc")) 
		{
			bmisc = true;
		}
	}

	@Override
	public void endElement(String uri, String localName, String qName) throws SAXException 
	{
		if (qName.equalsIgnoreCase("message")) 
		{
			System.out.println("End Element :" + qName+ "\n");
		}
		else if(qName.equalsIgnoreCase("associated_variable")) 
		{
			//System.out.println("End Element :" + qName);
		}
		else if(qName.equalsIgnoreCase("misc")) 
		{
			//System.out.println("End Element :" + qName);
		}
		else if(qName.equalsIgnoreCase("interval")) 
		{
			try
			{
				Process proc= mapofprocesses.get(proc_id);
				//print z3 constraint
				File file = new File("constraints.smt2");
				FileWriter fw = new FileWriter(file.getAbsoluteFile(),true);
				BufferedWriter bw = new BufferedWriter(fw);
				bw.append(intervalConstraint+" true");//last element of innermost and is true
				while(bracescount>0)
				{
					bw.append(")");
					bracescount--;
				}
				bw.append("):named constraint_interval_"+proc_id+"_atl"+proc.getL()+"_c"+proc.getC()+"))\n");
				bw.close(); // Be sure to close BufferedWriter	
				intervalConstraint="";
				
				proc_id=-1;
				//System.out.println("End Element :" + qName+"\n");
			}
			catch (Exception e) 
			{
				e.printStackTrace();
			}
		}
		else if(qName.equalsIgnoreCase("system_run"))
		{
			//print final constraints
			printFinalConstraints();
		}
	}

	@Override
	public void characters(char ch[], int start, int length) throws SAXException 
	{
		if (bmsender_time) 
		{
			sender_time=Integer.parseInt(new String(ch, start, length));
			System.out.println("Sender time: "+ sender_time);
			bmsender_time = false;
		} 
		else if (bmsgto) 
		{
			int msgto=Integer.parseInt(new String(ch, start, length));
			System.out.println("Message to: " + msgto);
			Process proc= mapofprocesses.get(proc_id);
			if(proc_id!=msgto)
			{
				proc.updateClock(sender_time,true);
			}
			else
			{
				proc.updateClock(sender_time,false);//no reporting required for intra-process communication, so logging corresponding l,c values in the queue is not required
			}
			mapofprocesses.put(proc_id,proc);
			proc_id=-1;
			sender_time=-1;
			System.out.println("Clock updated after message send, l="+ proc.getL()+",c="+proc.getC());
			bmsgto = false;
		} 
		else if (bmsgfrom) 
		{
			senderid=Integer.parseInt(new String(ch, start, length));
			System.out.println("Message from: " +senderid );
			bmsgfrom = false;
		} 
		else if (bmreceiver_time) 
		{	
			int receiver_time=Integer.parseInt(new String(ch, start, length));
			System.out.println("Receiver time: " + receiver_time);
			//get max of sendertime,receiver_time
			//update clock using that max
			Process proc= mapofprocesses.get(proc_id);
			
			if(proc_id!=senderid)
			{
				//get sender l,c by popping sender's dequeue
				Process senderproc= mapofprocesses.get(senderid);
				MessageSendSruct correspSendLC = senderproc.getLCfromQueue(sender_time);
				
				//l.j := max(l0.j, l.m, pt.j)
				int maxofall=Math.max(Math.max(correspSendLC.getL(),receiver_time),proc.getL());
				
				//HLC update l,c on msg receive
				if(maxofall==proc.getL())
				{
					proc.setOldL(proc.getL());
					proc.setOldC(proc.getC());
					proc.setL(proc.getL());
					proc.setC(proc.getC()+1);
					proc.setPt(receiver_time);
				}
				else if(maxofall==receiver_time)
				{
					System.out.println("CLOCK UPDATED");//
					proc.updateClock(receiver_time,false);
				}
				else//Elseif (l.j=l.m) then c.j := c.m + 1//hlc code
				{
					//System.out.println("CODE THAT SHOULD NOT EXECUTE OFTEN??");
					//System.exit(0);
					proc.setOldL(proc.getL());
					proc.setOldC(proc.getC());
					proc.setL(correspSendLC.getL());
					proc.setC(correspSendLC.getC()+1);
					proc.setPt(receiver_time);
				}
				mapofprocesses.put(proc_id,proc);//update the process instance in the map corresponding the key-process id
				int proc_l=proc.getL();
				int proc_c=proc.getC();
				System.out.println("Clock updated after message receive, l="+ proc_l+",c="+proc_c);
				
				//print z3 constraint
				try
				{
					File file = new File("constraints.smt2");
					FileWriter fw = new FileWriter(file.getAbsoluteFile(),true);
					BufferedWriter bw = new BufferedWriter(fw);
					//bw.append("(assert (! (=> (>= l"+id+" "+(22*proc_l)+proc_c+") (not (<= "+"l"+senderid+" "+(22*message_lc[0])+message_lc[1]+"))) :named constraint_msgAtp"+proc_id+"_at_l"+proc_l+"_at_c"+proc_c+"_fromp"+senderid+"))\n");
					bw.append("(assert (! (=> (>= l"+proc_id+" "+((22*proc_l)+proc_c)+") (not (<= "+"l"+ senderid +" "+((22*correspSendLC.getL())+correspSendLC.getC())+"))) :named constraint_msgAtp"+proc_id+"_at_l"+proc_l+"_at_c"+proc_c+"_fromp"+ senderid +"))\n");
					bw.close(); // Be sure to close BufferedWriter
				}			
				catch (Exception e) 
				{
					e.printStackTrace();
				}
			}
			else
			{
				proc.updateClock(receiver_time,false);			
				mapofprocesses.put(proc_id,proc);//update the process instance in the map corresponding the key-process id
				int proc_l=proc.getL();
				int proc_c=proc.getC();
				System.out.println("Clock updated after message receive, l="+ proc_l+",c="+proc_c);
			}
			bmreceiver_time = false;
			proc_id=-1;
			sender_time=-1;
			senderid=-1;
		}
		else if (bstart_time) 
		{
			//System.out.println("Interval start time: "+ new String(ch, start, length));
			bstart_time = false;
		} 
		else if (bend_time) 
		{
			int end_time=Integer.parseInt(new String(ch, start, length));
			//System.out.println("Interval end time: " + end_time);
			Process proc= mapofprocesses.get(proc_id);
			int hlc_l=0;
			int hlc_c=0;
			if(bmisc)
			{
				//use previous l, c values stored before communication
				//use last known l, c values
				hlc_l=proc.getOldL();
				hlc_c=proc.getOldC();
				//no need to update clocks because the clock was already updated at message send/recieve which actually caused this interval end point
				bmisc = false;
			}
			else if(!(proc.getReportedIntervalAlready()))//for the first interval reported at any process
			{
				//hlc_l=0;//default values are 0s
				//hlc_c=0;
				proc.updateClock(end_time,false);
				System.out.println("At "+proc_id+"Clock updated after local predicate change, l="+ proc.getL()+",c="+proc.getC());
				mapofprocesses.put(proc_id,proc);
			}
			else
			{
				//remember last known l, c values
				hlc_l=proc.getL();
				hlc_c=proc.getC();
				proc.updateClock(end_time,false);
				mapofprocesses.put(proc_id,proc);
				System.out.println("At "+proc_id+" Clock updated after local predicate change, l="+ proc.getL()+",c="+proc.getC());
			}			
			try
			{
				intervalConstraint=intervalConstraint+"(assert (! (=> (and (<= "+((22*hlc_l)+hlc_c)+" l"+proc_id+") (< l"+ proc_id +" "+((22*proc.getL())+proc.getC())+"))";
				end_time=-1;
				//System.out.println("End Element :" + qName+"\n");
				
				proc.setReportedIntervalAlready();	
			}
			catch (Exception e) 
			{
				e.printStackTrace();
			}
			bend_time = false;
		}
		else if (bmisc) 
		{
			//System.out.println("misc: " + new String(ch, start, length));
		} 
	}
}
