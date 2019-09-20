
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileFilter;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.HashMap;










import java.util.Scanner;

import javax.jws.WebMethod;
import javax.jws.WebParam;
import javax.jws.WebResult;
import javax.jws.WebService;
import javax.jws.soap.SOAPBinding;
import javax.jws.soap.SOAPBinding.ParameterStyle;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import org.w3c.dom.Document;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;

import unbbayes.TextModeRunner;
import unbbayes.TextModeRunner.QueryNodeNameAndArguments;
//import unbbayes.io.mebn.UbfIO;
import unbbayes.io.mebn.*;
import unbbayes.io.mebn.exceptions.IOMebnException;
import unbbayes.prs.INode;
import unbbayes.prs.Node;
import unbbayes.prs.mebn.InputNode;
import unbbayes.prs.bn.ProbabilisticNetwork;
import unbbayes.prs.bn.ProbabilisticNode;
import unbbayes.prs.mebn.Argument;
import unbbayes.prs.mebn.MultiEntityBayesianNetwork;
import unbbayes.prs.mebn.OrdinaryVariable;
import unbbayes.prs.mebn.ResidentNode;
import unbbayes.prs.mebn.entity.CategoricalStateEntity;
import unbbayes.prs.mebn.entity.Entity;
import unbbayes.prs.mebn.entity.ObjectEntity;
import unbbayes.prs.mebn.entity.ObjectEntityInstance;
import unbbayes.prs.mebn.entity.ObjectEntityInstanceOrdereable;
import unbbayes.prs.mebn.exception.MEBNException;
import unbbayes.prs.mebn.kb.KnowledgeBase;
import unbbayes.prs.mebn.kb.powerloom.PowerLoomKB;
import unbbayes.prs.mebn.ssbn.LiteralEntityInstance;
import unbbayes.prs.mebn.ssbn.OVInstance;
import unbbayes.prs.mebn.ssbn.Query;
import unbbayes.util.Debug;
import unbbayes.util.extension.bn.inference.IInferenceAlgorithm;
import unbbayes.util.extension.bn.inference.IInferenceAlgorithmListener;
import unbbayes.prs.bn.JunctionTreeAlgorithm;

import java.io.BufferedWriter;


/**
 * Main endpoint of the web service for prognos reasoner.
 * @author Rommel Carvalho
 * TODO stop using hard coded variable names.
 */
@WebService
@SOAPBinding(parameterStyle=ParameterStyle.BARE)
public class CopyOfMEBNReasoning {

	

	private MultiEntityBayesianNetwork mebn;

	private KnowledgeBase knowledgeBase;

	private ProbabilisticNetwork net;

	private TextModeRunner textModeRunner;

	private MebnUtil mebnUtil;
	
	
private double sumProbab=0;



private void CPT_Print( JunctionTreeAlgorithm d, HashMap<ProbabilisticNode, Integer> hashmap, HashMap<ResidentNode, Integer> hashmapMarg, ArrayList<Node> nodeList, int depth, int firstNodeIndx, int firstNodeState, ProbabilisticNode rvnode,ProbabilisticNetwork netcopy,ProbabilisticNode probfirstNode, ResidentNode firstNode, List<INode> ResNodeList )
{
	
	if ( depth<ResNodeList.size() )
	{
		//System.out.println( "depth " + depth );
		
		ResidentNode residentnode;
		String varname="";
	//	System.out.println(	ResNodeList.get(depth).getClass().toString() );

		
		if( ResNodeList.get(depth).getClass().toString().equals( "class unbbayes.prs.mebn.InputNode" ) )
			//(((InputNode)(ResNodeList.get(depth))).getResidentNodePointer()).getResidentNode();
			{
			residentnode = (ResidentNode)(((InputNode)(ResNodeList.get(depth))).getResidentNodePointer()).getResidentNode();
			//Make a list with the arguments (logical variables) of the INPUT node to be used in the potential function probability table
			varname=((InputNode)(ResNodeList.get(depth))).getArgumentList().get(0).getOVariable().getName();
			for(int i1=1;i1<((InputNode)(ResNodeList.get(depth))).getArgumentList().size();i1++)
				varname+="."+((InputNode)(ResNodeList.get(depth))).getArgumentList().get(i1).getOVariable().getName();	
			}
		else
			{
			residentnode = ( ResidentNode )( ResNodeList.get(depth) );
			//Make a list with the arguments (logical variables) of the RESIDENT node to be used in the potential function probability table
			varname+=residentnode.getArgumentList().get(0).getOVariable().getName();
			for(int i1=1;i1<residentnode.getArgumentList().size();i1++)
				varname+="."+residentnode.getArgumentList().get(i1).getOVariable().getName();
			}

		//ProbabilisticNode probnode = (ProbabilisticNode) nodeList.get(depth);
		ProbabilisticNode probnode = null;
		
		for(Node probnode2:nodeList)
		{
			probnode = (ProbabilisticNode) probnode2;
			if(  residentnode.getName().length()<=probnode.getName().length()  )
				if ( (residentnode.getName().equals(probnode.getName().substring(0,residentnode.getName().length()))))
					break;
		}
	
		//System.out.println( "resident name: " + residentnode.getName() + " probabilistic name: "+ probnode.getName());

		
		for(int k=0; k<probnode.getStatesSize(); k++)
		{
			hashmap.put(probnode,k);
			hashmapMarg.put( residentnode,k );
			//Insert in the table function  the "if any"+logical variables(argumentlist)+condition(r.v.=state)
			firstNode.setTableFunction(firstNode.getTableFunction() + "if any "+varname+" have ("+residentnode.getName()+"="+probnode.getStateAt(k)+")\n[\n");
			
			CPT_Print( d, hashmap, hashmapMarg, nodeList, depth+1, firstNodeIndx, firstNodeState, rvnode, netcopy, probfirstNode, firstNode, ResNodeList );
			firstNode.setTableFunction(firstNode.getTableFunction()+"]\nelse ");
		}
		
		
			firstNode.setTableFunction(firstNode.getTableFunction()+"[ \n");
		
		int[] jointprcoord = new int[nodeList.size()+1];

		int  stateK=0;
		float val=0;
		for(stateK=0; stateK < rvnode.getStatesSize()-1; stateK++ )
		{
			jointprcoord[firstNodeIndx]=stateK;
			val+=(float)Math.round(1000.0/(float)rvnode.getStatesSize())/1000.0;
			firstNode.setTableFunction(firstNode.getTableFunction()+rvnode.getStateAt(stateK)+"="+ Math.round(1000.0/(float)rvnode.getStatesSize())/1000.0  +",\n");
		}
		jointprcoord[firstNodeIndx]=stateK;
		firstNode.setTableFunction(firstNode.getTableFunction()+rvnode.getStateAt(stateK)+"="+ (float)(1.0-Math.round(1000.0*val)/1000.0) +"\n]\n");

				
	}
	else
		{
			//sumProbab+=d.getJointProbability(hashmap);
			//System.out.println("\n node indices start:  "+ firstNodeIndx );
			//for ( Integer key : hashmap.values() ) {
			int[] jointprcoord = new int[nodeList.size()+1];

			if (ResNodeList.size()==0)	 firstNode.setTableFunction(firstNode.getTableFunction()+"[ \n");

			int k=0;
			int indx=0;
			for ( ProbabilisticNode nodename : hashmap.keySet() ) 
			{
					
				//for ( Integer key : hashmap.values() )				
					//jointpr[k++]=key;
					jointprcoord[indx=  rvnode.getProbabilityFunction().getVariableIndex(nodename)]=  hashmap.get( nodename );
				//	System.out.println( "node:  " + nodename.getName() + ",  variable index: " + ((ProbabilisticNode) (netcopy.getNode(rvnode.getName()))).getProbabilityFunction().getVariableIndex(nodename)+", state: "+ hashmap.get(nodename) + ",  state name: "+((ProbabilisticNode) (netcopy.getNode(nodename.getName()))).getStateAt(hashmap.get(nodename)));
				}

			int stateK=0,imax=-1;
			double val=0,val1=0,max=-1.0,decr=(double) 0.0;

			for(  stateK=0; stateK < rvnode.getStatesSize()-1; stateK++ )
			{
				jointprcoord[firstNodeIndx]=stateK;
				val1=Math.round(1000.0*rvnode.getProbabilityFunction().getValue( jointprcoord ))/1000.0;
				val+=val1;
				if (val1==0)
					decr+=0.001;
				else if(val1 > max)
				{
					imax=stateK;
					max=val1;
				}
			}
			val=Math.round(1000.0*val)/1000.0;

			val1=1-val;

			if ( val1==0 )
				decr+=0.001;
			else if(val1>max)
			{
				imax=stateK;
				max=val1;
			}

			stateK=0;
			val=0;
			val1=0;

			for( stateK=0; stateK < rvnode.getStatesSize()-1; stateK++ )
			{
				jointprcoord[firstNodeIndx]=stateK;
				val1= Math.round(1000.0*rvnode.getProbabilityFunction().getValue( jointprcoord ))/1000.0;
				val+=val1;

				if (val1==0)
					val1 = 0.001;

				else if(stateK==imax)
					val1-=decr;

				firstNode.setTableFunction(firstNode.getTableFunction()+rvnode.getStateAt(stateK)+"="+ val1  +",\n");
			}

			val=Math.round(1000.0*val) / 1000.0;
			val1=1-val;
			if (val1==0)
				val1 = 0.001;
			else if(stateK==imax)
				val1-=decr;

			firstNode.setTableFunction(firstNode.getTableFunction() + rvnode.getStateAt(stateK)+"="+ val1 +"\n");

			//float val1 =   childnode.getProbabilityFunction().getValue( jointprcoord );
		    //System.out.println( "------ probability  : " + val1);

			if (ResNodeList.size()==0) 
				firstNode.setTableFunction(firstNode.getTableFunction()+"] \n");

		}
}


//Function that 1) normalizes the cucmulative potetntial table (firstnode) and 2) copies the result to all the SSBN nodes (rvNode)
private void CPT_Print2(JunctionTreeAlgorithm d,HashMap<ProbabilisticNode, Integer> hashmap, HashMap<ProbabilisticNode, Integer> hashmapMarg, ArrayList<Node> nodeList, int depth, int firstNodeIndx, int firstNodeState, ProbabilisticNode childnode,ProbabilisticNetwork netcopy,ProbabilisticNode firstNode,ResidentNode resNode, NodeList nlist11)
{
	if ( depth<nodeList.size() )
	{

		ProbabilisticNode node = (ProbabilisticNode) nodeList.get(depth);

		for(int k=0; k<node.getStatesSize(); k++)
		{
			hashmap.put(node,k);
			hashmapMarg.put(node,k);
			CPT_Print2( d, hashmap, hashmapMarg, nodeList, depth+1, firstNodeIndx, firstNodeState, childnode, netcopy, firstNode,resNode , nlist11);
		}

	}
	else
		{
			//sumProbab+=d.getJointProbability(hashmap);
			//System.out.println("\n node indices start:  "+ firstNodeIndx);
			//for ( Integer key : hashmap.values() ) {
			int[] jointprcoord = new int[nodeList.size() + 1];

			//jointprcoord[firstNodeIndx]=firstNodeState;
			//System.out.println( "node:  " + childnode.getName() + " state no: " + firstNodeState + ",  state name: " + childnode.getStateAt(firstNodeState)   );

			int k=0;
			int indx=0;
			ProbabilisticNode rvNode1=null;

			for ( ProbabilisticNode nodename : hashmap.keySet() )
				jointprcoord[indx=  childnode.getProbabilityFunction().getVariableIndex(nodename)] =  hashmap.get(nodename);


			float val1=0;
			float val2=0;
			int stateK;

			for(  stateK=0; stateK<firstNode.getStatesSize();stateK++  )
			{
				jointprcoord[firstNodeIndx]=stateK;
				val1 += firstNode.getProbabilityFunction().getValue(jointprcoord);
			}

			if (val1==0) 
				val1=(float)0.00001;
			
			for(  stateK=0; stateK<firstNode.getStatesSize() -1; stateK++  )
			{
				jointprcoord[firstNodeIndx]=stateK;
				val2 += ( firstNode.getProbabilityFunction().getValue( jointprcoord )/val1 );
				firstNode.getProbabilityFunction().setValue( jointprcoord, firstNode.getProbabilityFunction().getValue( jointprcoord )/val1);
				System.out.println( "node:  " + firstNode.getName() + ",  variable index: " + firstNodeIndx+", state: "+ stateK + ",  state name: "+ firstNode.getStateAt(stateK));
				System.out.println( firstNode.getProbabilityFunction().getValue(jointprcoord) );
			}

			jointprcoord[firstNodeIndx] = stateK;

			firstNode.getProbabilityFunction().setValue( jointprcoord, 1-val2);

			System.out.println(  "node: " + firstNode.getName()  +  ",  variable index: "  +  firstNodeIndx + ", state: "  +  stateK + ", state name: "  +   firstNode.getStateAt(stateK)  );
			System.out.println( firstNode.getProbabilityFunction().getValue(jointprcoord) );

			//System.out.println( firstNode.getProbabilityFunction().getValue(jointprcoord) );
			//System.out.println( ((ProbabilisticNode) (netcopy.getNode(childnode.getName()))).getProbabilityFunction().getValue() );
			//System.out.println( "node:  " + childnode.getName()  + " joint "  +  d.getJointProbability(hashmap) + ", partial joint   "  +  d.getJointProbability(hashmapMarg) );
			//((ProbabilisticNode) (netcopy.getNode(childnode.getName()))).getProbabilityFunction().setValue(   jointprcoord,d.getJointProbability(hashmap)/(d.getJointProbability(hashmapMarg)+(float)0.0000) );

			System.out.println( "resident node name:  " + resNode.getName() );


			for(Node prnode :  netcopy.getNodes())
			{
				
				ProbabilisticNode rvNode = (ProbabilisticNode) prnode;
				

				String delims = "[ _ ]+";
				String[] tokens = rvNode.getName().split(  delims   );
				String rvname= tokens[0];
				//Search for corresponding resident node (resNode) to the current random variable node (rvNode) 
				//*********UPDATE NODE PT***************
				
				
				
					
					
//					jointprcoordfirstnode[firstNode.getProbabilityFunction().getVariableIndex((Node)childnode.getProbabilityFunction().getVariableAt(kp))]=jointprcoord[kp];
					
				
				
				boolean samenodes=true;

				if(  resNode.getName().equals( rvname )  && resNode.getParents().size()==rvNode.getParents().size()   ){

					System.out.println(  "name resident node in: "+resNode.getName()  );
					System.out.println(  "name rv node in: "+rvNode.getName()  );
					
					for(  int kp=0; kp<jointprcoord.length ; kp++  )
					{
					String str1=firstNode.getProbabilityFunction().getVariableAt(kp).getName();
					String str2=rvNode.getProbabilityFunction().getVariableAt(kp).getName();
					

					String[] tokens1 = str1.split( delims );

					String rvname1= tokens1[0];

					String[] tokens2 = str2.split( delims );

					String rvname2= tokens2[0];

					if(!rvname1.equals(rvname2))
						samenodes=false;
					}
					if(samenodes==true)//if rvNode (SSBN node) and cumulative potential probability table node have the same of order of states then proceed to copy the result to rvNode for all states 
						//TODO: make the order of the states invariable
					for(  stateK=0; stateK<rvNode.getStatesSize() ; stateK++  )
					{
						jointprcoord[firstNodeIndx]=stateK;
								
						System.out.println( " *****  "   );
						for(int kp=0;kp<jointprcoord.length;kp++)
						{	
							System.out.print( "---  " + jointprcoord[kp]  );
							
							System.out.println(  "\nfirst node table value " + firstNode.getProbabilityFunction().getVariableAt(kp).getName());		
							System.out.println(  "\nchild node table value " + rvNode.getProbabilityFunction().getVariableAt(kp).getName());
						}
						System.out.println( " *****  "   );

						System.out.println(  "df  " + firstNode.getProbabilityFunction().getValue(jointprcoord)   );
	
						
						
						rvNode.getProbabilityFunction().setValue(   jointprcoord, firstNode.getProbabilityFunction().getValue(jointprcoord)  );
					}
				}
			}
		}
}


private void CPT_Print3(JunctionTreeAlgorithm d,HashMap<ProbabilisticNode, Integer> hashmap, HashMap<ProbabilisticNode, Integer> hashmapMarg, ArrayList<Node> nodeList, int depth, int firstNodeIndx, int firstNodeState, ProbabilisticNode childnode,ProbabilisticNetwork netcopy,ProbabilisticNode firstNode,ResidentNode resNode)
{

	

			int k=0;
			int indx=0;
			ProbabilisticNode rvNode1=null;

			
			//System.out.println( firstNode.getProbabilityFunction().getValue(jointprcoord) );

			
			//System.out.println( ((ProbabilisticNode) (netcopy.getNode(childnode.getName()))).getProbabilityFunction().getValue() );
			//System.out.println( "node:  " + childnode.getName()  + " joint "  +  d.getJointProbability(hashmap) + ", partial joint   "  +  d.getJointProbability(hashmapMarg) );
			//((ProbabilisticNode) (netcopy.getNode(childnode.getName()))).getProbabilityFunction().setValue(   jointprcoord,d.getJointProbability(hashmap)/(d.getJointProbability(hashmapMarg)+(float)0.0000) );

			System.out.println( "resident node name:  "+ resNode.getName() );

			int i1=2;
			if(  resNode.getName().equals("doublesingle") || resNode.getName().equals("malefemale")  )
				rvNode1 = (ProbabilisticNode) net.getNode( resNode.getName() + "__/PL-KERNEL-KB/PL-USER/GENERATIVE_MODULE_1/FINDINGS_MODULE_1/DANCE1" );
			else
				rvNode1 = (ProbabilisticNode) net.getNode( resNode.getName() + "__t"+i1 );

			while(rvNode1!=null)
			//while(i1<195)
			{
				//	System.out.println("------ probability  :   "+ val1+"   i1: "+i1);
				//	System.out.println("difference "+ (rvNode1.getProbabilityFunction().getValue(jointprcoord)-firstNode.getProbabilityFunction().getValue(jointprcoord)) );
				//	System.out.println("before "+ rvNode1.getProbabilityFunction().getValue(jointprcoord) );
				//rvNode1.loadProbabilityFunction(firstNode.getProbabilityFunction());
				
				
			//	System.out.println(  "before"  +  rvNode1.getMarginalAt(0) );
				
				rvNode1.restoreMarginal();
								
				//System.out.println(  "after "+ rvNode1.getMarginalAt(0)  );
				
				//System.out.println("difference "+ (rvNode1.getProbabilityFunction().getValue(jointprcoord)-firstNode.getProbabilityFunction().getValue(jointprcoord)) );

				i1++;

				if(  resNode.getName().equals("doublesingle") || resNode.getName().equals("malefemale")  )
					{
						rvNode1 = (ProbabilisticNode) net.getNode( resNode.getName() + "__/PL-KERNEL-KB/PL-USER/GENERATIVE_MODULE_1/FINDINGS_MODULE_1/DANCE1" );
						break;
					}
				else
					rvNode1 = (ProbabilisticNode) net.getNode( resNode.getName() + "__t"+i1 );
			}

}

private void JointProbPrint(  JunctionTreeAlgorithm d,HashMap<ProbabilisticNode, Integer> hashmap, HashMap<ProbabilisticNode, Float> hashmapMarg, ArrayList<Node> nodeList, int depth, int firstNodeIndx, int firstNodeState, ProbabilisticNode childnode,ProbabilisticNetwork netcopy,ProbabilisticNode firstNode  )
{
	 if (depth<nodeList.size())
	{
		System.out.println(" depth: " + depth);
		System.out.println(" node list size: " + nodeList.size());
		ProbabilisticNode node = (ProbabilisticNode) nodeList.get(depth);

		for(int k=0;  k  <  node.getStatesSize() ;  k++)
		{
			hashmap.put(node,k);
			hashmapMarg.put(node,node.getMarginalAt(k));
			JointProbPrint(d, hashmap, hashmapMarg, nodeList, depth+1, firstNodeIndx, firstNodeState, childnode, netcopy, firstNode);
		}
	}
	else
		{
			sumProbab+=d.getJointProbability(hashmap);
			//System.out.println("\n node indices start:  "+ firstNodeIndx);
			//for ( Integer key : hashmap.values() ) {
			int[] jointprcoord = new int[nodeList.size()+1];
			jointprcoord[firstNodeIndx]=firstNodeState;

			//if( (childnode.hasEvidence())==true)
			System.out.println( "node:  " + childnode.getName() + ",   index:  "+firstNodeIndx + ", state: "+ firstNodeState + ",  state name: "+((ProbabilisticNode) (netcopy.getNode(childnode.getName()))).getStateAt(firstNodeState));

			int indx;
			for ( ProbabilisticNode nodename : hashmap.keySet() ) 
			{
				//for ( Integer key : hashmap.values() )				
				//jointpr[k++]=key;
				jointprcoord[  indx= (  (ProbabilisticNode)  (netcopy.getNode(childnode.getName()))).getProbabilityFunction().getVariableIndex(nodename)]=  hashmap.get(nodename);

				System.out.println( "******node:  " + nodename.getName() + ",  variable index: " + indx+", state: "+ hashmap.get(nodename) + ",  state name: "+((ProbabilisticNode) (netcopy.getNode(nodename.getName()))).getStateAt(hashmap.get(nodename)));

			}

			//System.out.println( ((ProbabilisticNode) (netcopy.getNode(childnode.getName()))).getProbabilityFunction().getValue() );

			System.out.println( "sgf nnode:  " + childnode.getName()  + " joint "  +  d.getJointProbability(hashmap) + ", partial joint   "  +  d.getJointProbability(hashmap) );
			//((ProbabilisticNode) (netcopy.getNode(childnode.getName()))).getProbabilityFunction().setValue(   jointprcoord,d.getJointProbability(hashmap)/(d.getJointProbability(hashmapMarg)+(float)0.0000) );

			float val = d.getJointProbability(hashmap);

			/*if(nodeList.size()==0)
				val2 = prodmarg*childnode.getProbabilityFunction().getValue( jointprcoord )*childnode.getProbabilityFunction().getValue( jointprcoord );
			else
				val2=prodmarg*childnode.getProbabilityFunction().getValue( jointprcoord )*childnode.getProbabilityFunction().getValue( jointprcoord )*childnode.getProbabilityFunction().getValue( jointprcoord );*/

			System.out.println(  "\n"+nodeList.size() );

			System.out.println(  "\n" + firstNode.getProbabilityFunction().getVariablesSize() );

			System.out.println(  " node:  " +  firstNode.getName()   );

			int[] jointprcoordfirstnode= new int[nodeList.size()+1];
			
			boolean samenodes=true;
			
			for(int kp=0;kp<jointprcoord.length;kp++)
			{	
				System.out.print( "  " + jointprcoord[kp]  );
				
				System.out.println(  "\nfirst node table value " + firstNode.getProbabilityFunction().getVariableAt(kp).getName());		
				System.out.println(  "\nchild node table value " + childnode.getProbabilityFunction().getVariableAt(kp).getName());
				
				String str1=firstNode.getProbabilityFunction().getVariableAt(kp).getName();
				String str2=childnode.getProbabilityFunction().getVariableAt(kp).getName();


				String delims = "[ _ ]+";

				String[] tokens1 = str1.split( delims );

				String rvname1= tokens1[0];

				String[] tokens2 = str2.split( delims );

				String rvname2= tokens2[0];


				if(!rvname1.equals(rvname2))
					samenodes=false;
				
//				jointprcoordfirstnode[firstNode.getProbabilityFunction().getVariableIndex((Node)childnode.getProbabilityFunction().getVariableAt(kp))]=jointprcoord[kp];
				
			}
			
	//		System.out.println(  "\nchild node table value " + childnode.getProbabilityFunction().getValue(jointprcoord) +" name="+childnode.getName()+ "----- size =  "+childnode.getProbabilityFunction().tableSize()+"   "+firstNode.getProbabilityFunction().tableSize());
		//	System.out.println(  "\nfirst node table value " + firstNode.getProbabilityFunction().getValue(jointprcoord) +" name="+firstNode.getName() + "----- size =  "+firstNode.getProbabilityFunction().tableSize());

			if(samenodes==true)
				firstNode.getProbabilityFunction().setValue( jointprcoord, val +  firstNode.getProbabilityFunction().getValue(jointprcoord)  );


			//firstNode.getProbabilityFunction().setValue(jointprcoord, val + firstNode.getProbabilityFunction().getValue(jointprcoord));
			//System.out.println( " node:  " +  firstNode.getName() +  "  " + ((ProbabilisticNode) (netcopy.getNode(childnode.getName()))).getProbabilityFunction().getValue(jointprcoord) );
			System.out.println("\n node indices end:  "  +  val  );
	
			System.out.println(" ");
			//((ProbabilisticNode) (netcopy.getNode(childnode.getName())))., d.getJointProbability(hashmap));
			//System.out.println(depth  +   " prob: " +  d.getJointProbability(hashmap));
		}


}


public void listFilesForFolder(final File folder) {

    for (final File fileEntry : folder.listFiles()) {
        if (fileEntry.isDirectory()) 
        {
            listFilesForFolder(fileEntry);
        }
        else 
        {
            System.out.println(fileEntry.getName());
        }
    }

}

public void MEBNRunInference() throws Exception {

	textModeRunner = new TextModeRunner();

	File mebnFile = new File("C:/Users/gchantas/Desktop/unbbayes-4.18.10/examples/Salsa/MEBNSalsa.ubf");
	//File mebnFile = new File("C:/Users/gchantas/Desktop/unbbayes-3.52.7-BETA/MebnLearning/LearnedMEBNs/TsamikoFirstTrainedSeparateStylesFineTunedMultiTrain3samples01.ubf");
	//File mebnFile = new File("C:/Users/gchantas/Desktop/unbbayes-3.52.7-BETA/MebnLearning/LearnedMEBNs/TsamikoFirstTrained.ubf");
	//File mebnFile = new File("C:/Users/gchantas/Desktop/unbbayes-3.52.7-BETA/examples/mebn/TsamikoSequenceStyleCorrect.ubf");
	
	//File mebnFile = new File("MEBNsCrossValidation/MEBN_BNTrained1out.ubf");
	//File mebnFile = new File("C:/Users/gchantas/Desktop/unbbayes-4.17.8/examples/test.ubf");
	//File mebnFile = new File("C:/Users/gchantas/Desktop/unbbayes-4.17.8/examples/TsamikoInActionStepStyleSeparate.ubf");
	//File mebnFile = new File("C:/Users/gchantas/Documents/codePrognos/PrognosReasoning/resources/mebn/uc3-v7.ubf");

	if ( mebnFile == null || !mebnFile.exists() ) {
		System.out.println( "File " + mebnFile + " does not exist" );
		System.exit(0);
	}

	System.out.println( "Opening File = " + mebnFile.getAbsolutePath() );
	UbfIO ubf = UbfIO.getInstance();

	mebn = ubf.loadMebn(mebnFile);
	QueryInfo queryJob = new QueryInfo();
	List<EvidenceInfo> evidenceList = new ArrayList<EvidenceInfo>();

	// load kb
	mebnUtil = new MebnUtil(mebn);
	initKB();
	
	//File evFile = new File("C:/Users/gchantas/Desktop/unbbayes-3.52.7-BETA/examples/mebn/Recording4_Session2_WomanDoubleStep.plm.txt");
	//File evFile = new File("C:/Users/gchantas/Desktop/unbbayes-3.52.7-BETA/examples/mebn/Recording1_Session2_SingleStep.plm.txt");
	//File evFile = new File("C:/Users/gchantas/Desktop/unbbayes-3.52.7-BETA/examples/mebn/Recording5_Session2_DoubleStep.plm.txt");
	
	File evFile = new File("C:/Users/gchantas/workspace2/ReadSalsa/resultsTranscriptions");
//	File evFile = new File("C:/Users/gchantas/Desktop/unbbayes-3.52.7-BETA/recordings/tens/Recording2-31-40.txt");
	File resultFile = new File("C:/Users/gchantas/Desktop/unbbayes-3.52.7-BETA/recordings/result.txt");
	
	mebnUtil.loadFindingsFile(evFile);

	//knowledgeBase=mebnUtil.getKnowledgeBase();

	/*EvidenceInfo arg0 = new EvidenceInfo();

	arg0.setResidentNode("hasDirection");
	
	ArgumentInfo[] arguments = new ArgumentInfo[1];
	
	arguments[0] = new ArgumentInfo();
	arguments[0].setType("0");
	arguments[0].setName("hasDirection");
	
	//=new ArgumentInfo();
	arg0.setArguments(arguments);
	
	arg0.setResidentNode("hasDirection");
	arg0.setState("leftDirection");
	
	evidenceList.add(arg0);*/ 
	
	/*EvidenceInfo evidence = new EvidenceInfo();

	evidence.setResidentNode("hasDirection");

	System.out.println(" arg length:  " + evidence.getResidentNode());
	ArgumentInfo argument = new ArgumentInfo();
	argument.setType("TimeStep");
	argument.setName("t2");
	ArgumentInfo[] arg = new ArgumentInfo[1];
	ArgumentInfo arg1 = new ArgumentInfo();

	arg1.setName("t15");
	arg1.setType("TimeStep");
	arg[0]=arg1;

	evidence.setArguments(arg);
	System.out.println("arg length: " + evidence.getArguments().length );

	evidence.getArguments()[0].setName("t15");
 //   evidence.getArguments()[0].setType("TimeStep");

	evidence.setState("leftDirection");
	evidenceList.add(evidence);

	evidence.setResidentNode("hasDirection");
*/
	
	ResidentNode queryNode = mebn.getDomainResidentNode( "Step" );
	
//	System.out.println("name state : "+queryNode.get);
	
	//loadEvidence(evidenceList);

	
	List<Query> queryList = new ArrayList<Query>();

	List<OVInstance> ovInstanceList = new ArrayList<OVInstance>(1);
	List<Argument> arglist = queryNode.getArgumentList();
	OrdinaryVariable ov = arglist.get(0).getOVariable();
	OVInstance ovInstance = OVInstance.getInstance( ov, LiteralEntityInstance.getInstance("t1", ov.getValueType()) );
	ovInstanceList.add(ovInstance);
	System.out.println( " ov valueType "+ ov.getValueType() );

	System.out.println(    " arguments queryNode : " + arglist.get(0).getOVariable().getName() );
	Query query = new Query(queryNode, ovInstanceList);
	query.setKb(knowledgeBase);
	query.setMebn(mebn);

	queryList.add(query);

	//System.out.println("queryList "+  );
/*QueryNodeNameAndArguments qr;
qr= new QueryNodeNameAndArguments("hasDirection", "leftDirection");
	
//Collection<TextModeRunner.QueryNodeNameAndArguments> qrCol = new Collection<TextModeRunner.QueryNodeNameAndArguments>[1];

	qrCol.add(qr);*/
	
	net=textModeRunner.executeQueryLaskeyAlgorithm(queryList,knowledgeBase, mebn);

	QueryResultSummary result = new QueryResultSummary();
	
	// Show query result
	
	BufferedWriter bw = new BufferedWriter(new FileWriter(resultFile));

	StringBuffer queryResult = new StringBuffer();
	DecimalFormat df = new DecimalFormat("##.##");
	List<RandomVariableInfo> terroristPersonInfo = new  ArrayList<RandomVariableInfo>();
	RandomVariableInfo rv = new RandomVariableInfo();
	
	System.out.println(" net node count"+ net.getNodeCount() );
	
	
	for (Node node : net.getNodes()) {
		for (int i = 0; i <node.getStatesSize()-1; i++) {
		queryResult.append(node.getName()+" "+ node.getStateAt(i)+"\n");
			queryResult.append( df.format(((ProbabilisticNode)node).getMarginalAt(i)*100) + "%");
			//bw.write( df.format(((ProbabilisticNode)node).getMarginalAt(i)*100) + "%     \n");
		}
		/*if (node.getName().contains("hasDirection")) {
			rv.setName(node.getName());
			rv.setProbability(((ProbabilisticNode)node).getMarginalAt(0));
			result.setShipOfInterestInfo(rv);
		}*/
		queryResult.append("\n\n");
		bw.write("\n");
	}

	//RandomVariableInfo[] rvList = new RandomVariableInfo[terroristPersonInfo.size()];
	/*for (int i = 0; i < rvList.length; i++) {
		rvList[i] = terroristPersonInfo.get(i);
	}*/
	bw.close();
	System.out.println(queryResult);
}


public void MEBNTraining(int generalIter, int FileNumber) throws Exception {
	
	textModeRunner = new TextModeRunner();

	File mebnFile = new File("C:/Users/gchantas/Desktop/unbbayes-3.52.7-BETA/examples/mebn/SalsaMEBN4.ubf");

	
	//File mebnFile = new File("C:/Users/gchantas/Desktop/unbbayes-3.52.7-BETA/MebnLearning/TsamikoMEBN_2_OneStyle.ubf");
	//File mebnFile = new File("C:/Users/gchantas/Desktop/unbbayes-4.17.8/examples/test.ubf");
	//File mebnFile = new File("C:/Users/gchantas/Desktop/unbbayes-4.17.8/examples/TsamikoInActionStepStyleSeparate.ubf");
	//File mebnFile = new File("C:/Users/gchantas/Documents/codePrognos/PrognosReasoning/resources/mebn/uc3-v7.ubf");

	if (mebnFile == null || !mebnFile.exists()) {
		System.out.println("File " + mebnFile + " does not exist");
		mebnFile = new File("mebn/uc3-v7.ubf");
	}

	System.out.println(  "Opening File = " + mebnFile.getAbsolutePath()  );
	UbfIO ubf = UbfIO.getInstance();
	
	mebn = ubf.loadMebn(mebnFile);

	QueryInfo queryJob = new QueryInfo();
	List<EvidenceInfo> evidenceList = new ArrayList<EvidenceInfo>();

	// load kb
	mebnUtil = new MebnUtil(mebn);
	initKB();

	//File folder = new File("C:/Users/gchantas/workspace2/ReadSalsa/resultsTranscriptionsGT");
	File folder = new File("C:/Users/gchantas/workspace2/ReadSalsa/resultsdance_audiooutput");
	File[] listOfFiles = folder.listFiles();
	ArrayList<File> filelist=new ArrayList<File>();

	for (int y1=0;y1<listOfFiles.length;y1+=1)
		filelist.add(listOfFiles[y1]);
	
	//File evFile = new File("C:/Users/gchantas/Desktop/unbbayes-3.52.7-BETA/recordings/tens/Recording2-31-40.txt");
	File resultFile = new File("C:/Users/gchantas/Desktop/unbbayes-3.52.7-BETA/recordings/result.txt");

	mebnUtil.loadFindingsFile(  filelist.get(0)   );
	
	
	
	System.out.println("d "+  filelist.get(0).getName()   );

	ResidentNode queryNode = mebn.getDomainResidentNode("Rhythm1");

	List<Query> queryList = new ArrayList<Query>();

	List<OVInstance> ovInstanceList = new ArrayList<OVInstance>(1);
	List<Argument> arglist = queryNode.getArgumentList();
	OrdinaryVariable ov = arglist.get(0).getOVariable();
	OVInstance ovInstance = OVInstance.getInstance( ov, LiteralEntityInstance.getInstance("T1", ov.getValueType() ));
	ovInstanceList.add(ovInstance);
	System.out.println(" ov valueType "+ ov.getValueType());


	System.out.println(" arguments queryNode : "+ arglist.get(0).getOVariable().getName() );
	Query query = new Query(queryNode, ovInstanceList);
	query.setKb(knowledgeBase);
	query.setMebn(mebn);


	ResidentNode queryNode2 = mebn.getDomainResidentNode("style");


	List<OVInstance> ovInstanceList2 = new ArrayList<OVInstance>(1);
	List<Argument> arglist2 = queryNode2.getArgumentList();
	OrdinaryVariable ov2 = arglist2.get(0).getOVariable();
	OVInstance ovInstance2 = OVInstance.getInstance( ov2, LiteralEntityInstance.getInstance("dance1", ov.getValueType() ));
	ovInstanceList2.add(ovInstance2);
	System.out.println(" ov2 valueType "+ ov2.getValueType());

	System.out.println(" arguments queryNode : "+ arglist2.get(0).getOVariable().getName() );
	Query query2 = new Query(queryNode2, ovInstanceList2);
	query2.setKb(knowledgeBase);
	query2.setMebn(mebn);
	
	//queryList.add(query2);
	queryList.add(query);
	/*String str = null, strXML ="<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n <Features>";

  	Scanner sc = new Scanner(myfile);

	 while( sc.hasNext() )
     {
     	str = sc.nextLine();
     	
     } */
	
	DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
    //Get the DOM Builder
    DocumentBuilder builder = factory.newDocumentBuilder();
    //  System.out.println( str );
    Document document = builder.parse( new FileInputStream(  filelist.get(1).getAbsolutePath()   )  );

    NodeList nlist1 = document.getDocumentElement().getElementsByTagName("Feature");
    
    NodeList nlist2 = document.getDocumentElement().getElementsByTagName("BeatFeature");

   /* for(int i=0; i<nlist2.getLength();  i++)
    {
    	System.out.println(  "d " + nlist2.item(i).getNodeName()  );
    	NodeList nlist= nlist2.item(i).getChildNodes();
    	String label = nlist.item(3).getFirstChild().getNodeValue();
		System.out.println( "1 resident " + label );
		
    }

    if(1==1) return;*/

    ProbabilisticNetwork netcopy = new ProbabilisticNetwork("copynet");
	List<ResidentNode> ResidentNodes1 = mebn.getDomainResidentNodes();
	netcopy=textModeRunner.executeQueryLaskeyAlgorithm(queryList,knowledgeBase, mebn);
	//ProbabilisticNode[] rvNodeFirst = new ProbabilisticNode[ResidentNodes1.size()];


	//Label the nodes that act as cumulative matrices to  
	//for(   ProbabilisticNode rvn2 : rvNodeFirst  )
	//	rvn2.setLabel("empty");


	HashMap<ResidentNode, ProbabilisticNode> rvNodeFirstMap = new HashMap<ResidentNode, ProbabilisticNode>();



	for(Node prnode :  netcopy.getNodes())
	{
		ProbabilisticNode rvNode;
		rvNode = (ProbabilisticNode) prnode;
		String delims = "[ _ 1 2 3 4]+";
		String[] tokens = rvNode.getName().split( delims );

		String rvname= tokens[0];

		//for(String str1:tokens)
		//	System.out.println(  str1 + "  size " + netcopy.getNodes().size()   );

		for(  ResidentNode resNode2 : ResidentNodes1 )
		{
			if(  rvname.matches(  resNode2.getName()+"*" )  &&   resNode2.getParents().size() == rvNode.getParents().size()   )
			{
				System.out.println("init rv name:  "+rvNode.getName()+"  res name " + resNode2.getName() + "   rv name "+ rvname + "  sizeres " + resNode2.getParents().size() + "  sizerv  " + rvNode.getParents().size()   );

				rvNodeFirstMap.put(  resNode2, (ProbabilisticNode)(rvNode.clone())  );
				
			}
		}
	}

	
	List<ResidentNode> ResidentNodes = mebn.getDomainResidentNodes();

	ProbabilisticNode rvNode;
	ProbabilisticNetwork net1 = null;

	JunctionTreeAlgorithm  dfg=null,dfg1=null;

	ArrayList<JunctionTreeAlgorithm> JTreeAlg = new ArrayList<JunctionTreeAlgorithm>();
	ArrayList<HashMap<ProbabilisticNode, Integer>> mapEvidenceList = new ArrayList<HashMap<ProbabilisticNode, Integer>>();
	ArrayList<ProbabilisticNetwork> netList = new ArrayList<ProbabilisticNetwork>();

	HashMap<ProbabilisticNode, Integer> mapEvidence = null;
	
//************************************************************************************************************************
	
for (int EMiter=1;EMiter<2;EMiter++)
{
	//Initialize sum nodes to zero
	for (  ProbabilisticNode prnode:rvNodeFirstMap.values()   )
		for( int k1=0; k1<prnode.getProbabilityFunction().tableSize(); k1++ )
			prnode.getProbabilityFunction().setValue(k1, 0);


for (int kl=0;kl<filelist.size()/2;kl++)
{

	DocumentBuilderFactory factory1 = DocumentBuilderFactory.newInstance();

	//Get the DOM Builder
    DocumentBuilder builder1 = factory1.newDocumentBuilder();
    
    System.out.println( filelist.get(1+2*kl).getAbsolutePath() );
      
    Document document1 = builder1.parse( new FileInputStream(  filelist.get(1+2*kl).getAbsolutePath()  )  );

    NodeList nlist11 = document1.getDocumentElement().getElementsByTagName("Feature");

		mebnUtil.removeAllFindings();
		mebnUtil.loadFindingsFile(   filelist.get(2*kl)  );

		if (EMiter==1){
			net1 = textModeRunner.executeQueryLaskeyAlgorithm(queryList,knowledgeBase, mebn);
			netList.add(net1);
			dfg1 = new JunctionTreeAlgorithm();
			JTreeAlg.add(dfg1);
			HashMap<ProbabilisticNode, Integer> mapev=new HashMap<ProbabilisticNode, Integer>();
			mapEvidenceList.add(mapev);
		}

		dfg=JTreeAlg.get(kl);
		net=netList.get(kl);
		mapEvidence=mapEvidenceList.get(kl);
		
	//Store evidence in hashmap : mapEvidence
		
	if(EMiter==1)
		for (  Node rvnode : net.getNodes()   )
			if ( ((ProbabilisticNode) rvnode).hasEvidence() == true) //Node is observed variable (evidence)
				mapEvidence.put(  (ProbabilisticNode) rvnode, ((ProbabilisticNode) rvnode).getEvidence()  );

	//System.out.println("name resident node: "+resNode.getName());
	
    //net = textModeRunner.executeQueryLaskeyAlgorithm(queryList,knowledgeBase, mebn);
	dfg.setNet(net);
	dfg.run();

	netcopy = net;

	//Retrieve evidence (.run() (unfortunately) deletes them)

	for (  ProbabilisticNode rvnode: mapEvidence.keySet()  )
		rvnode.addFinding( mapEvidence.get(rvnode) );
	
	net.updateEvidences();
	
	//dfg.updateCPTBasedOnCliques();
	//dfg.run();
	//net.resetEvidences();
	/*ArrayList<Node> nodesCopy = new ArrayList<Node>();
	nodesCopy = net. .getNodesCopy();*/
	//netcopy = net;

	System.out.println(  " net node count"+ net.getNodeCount()   );


	for(  Node prnode : netcopy.getNodes()   )
	{
		//System.out.println(  "name resident node in: "+resNode.getName()  );
		System.out.println(" net size  "+netcopy.getNodes().size());

			ResidentNode resNode=null;
			rvNode = (ProbabilisticNode) prnode;
			String delims = "[ _ ]+";
			String[] tokens = rvNode.getName().split( delims );
			String rvname= tokens[0];

			//Search for corresponding resident node (resNode) to the current random variable node (rvNode) 
			boolean found=false;
			for(  ResidentNode resNode2 : ResidentNodes1 )
				if(  resNode2.getName().equals( rvname  ) && resNode2.getParents().size()==rvNode.getParents().size()   )
				{
					resNode=resNode2;
					found=true;
					break;
				}

			if(found==false) continue;
			//Corresponding resident node  not found
			//if(found==false||rvname.equals("Beat1")||rvname.equals("Beat2")||rvname.equals("Beat3")||rvname.equals("Beat4")) continue;//||rvname.equals("Rhythm1")||rvname.equals("style")||rvname.equals("Rhythm3")||rvname.equals("Rhythm4")||rvname.equals("Step")) continue;

			HashMap<ProbabilisticNode, Integer> map = new HashMap<ProbabilisticNode, Integer>();
			HashMap<ProbabilisticNode, Float> mapMarg = new HashMap<ProbabilisticNode, Float>();

			if (  rvNode.hasEvidence() == false  ) //Node is hidden variable 
			{
				for (  int k1=0; k1<rvNode.getStatesSize(); k1++  )
				{
					map.put(  (ProbabilisticNode) rvNode, k1);

					//mapMarg.put((ProbabilisticNode) rvNode, rvNode.getMarginalAt(k1)); 
					//System.out.println("marg:  "+dfg.getJointProbability(map));

					for( Node rvn:rvNode.getParents() )
						System.out.println(  "node 2.2 name parent "  +  rvn.getExplanationDescription()  +  " "  +  rvn.getName() + " no. parents  " + (rvNode.getParents()).size());

					System.out.println( "resident " + resNode.getName() + ",   random var: " + rvNode.getName() );
			    	System.out.println(  "Opening File = " +    filelist.get(1+kl).getName()  );

			    	if(  rvNode.getParents().size()==0 ){
						System.out.println( "resident: "  +  rvNodeFirstMap.get(resNode).getProbabilityFunction().getValue( k1) );
						rvNodeFirstMap.get(resNode).getProbabilityFunction().setValue( k1, rvNodeFirstMap.get(resNode).getProbabilityFunction().getValue(k1)+rvNode.getMarginalAt(k1) );
					}
					JointProbPrint( dfg, map, mapMarg, rvNode.getParents(), 0, rvNode.getProbabilityFunction().getVariableIndex(rvNode), k1, rvNode, netcopy, rvNodeFirstMap.get(resNode) );

					//System.out.println( "resident " + resNode.getName() + ",   random var: " + rvNode.getName() );
				}
			}
			else //Observed node/variable
			{
				System.out.println( "resident " + resNode.getName() + ",   random var: " + rvNode.getName() );

				if(  rvNode.getParents().size()==0 ){
					System.out.println( "resident: "  +  rvNodeFirstMap.get(resNode).getProbabilityFunction().getValue( rvNode.getEvidence()) );
					rvNodeFirstMap.get(resNode).getProbabilityFunction().setValue( rvNode.getEvidence(), rvNodeFirstMap.get(resNode).getProbabilityFunction().getValue(rvNode.getEvidence())+rvNode.getMarginalAt(rvNode.getEvidence()) );
				}
				else
					JointProbPrint( dfg, map, mapMarg, rvNode.getParents(), 0, rvNode.getProbabilityFunction().getVariableIndex(rvNode), rvNode.getEvidence(), rvNode, netcopy , rvNodeFirstMap.get(resNode) );
			}


		}


	}


for (  int kl=0;kl<filelist.size()/2;kl++  )
{

	dfg=JTreeAlg.get(kl);
	net=netList.get(kl);
	mapEvidence=mapEvidenceList.get(kl);

	//System.out.println("net id "+net.getName()+ "  "+net1.equals(net2)+" "+net3.equals(net2)+" "+net1.equals(net3));
	dfg.run();

	for ( ProbabilisticNode rvnode: mapEvidence.keySet() )
		rvnode.addFinding( mapEvidence.get(rvnode) );

	net.updateEvidences();
	//dfg.setToCalculateJointProbabilityLocally(true);

//	if(EMiter==1) dfg.run();

	netcopy=net;


	//Sum up all probabilities to rvNodeFirstMAP random variables nodes
	for ( ResidentNode resNode : ResidentNodes1 )
	{
		//String rvname= resNode.getName();
		//if(rvname.equals("Beat1")||rvname.equals("Beat2")||rvname.equals("Beat3")||rvname.equals("Beat4")) continue;//

		//if(!resNode.getName().equals("Rhythm1")) continue;
		rvNode = rvNodeFirstMap.get(resNode);
		System.out.println("name  "+resNode.getName());
		HashMap<ProbabilisticNode, Integer> map = new HashMap<ProbabilisticNode, Integer>();
		HashMap<ProbabilisticNode, Integer> mapMarg = new HashMap<ProbabilisticNode, Integer>();
		System.out.println("\n\n\n  EM iteration: " + EMiter+"------------ Conditional table of variable: " + rvNode.getName()+"-----------------------------------------------------------");
		//map.put((ProbabilisticNode) rvNode, k1);
		//System.out.println("parent step 2 "+rvNode.getParents().get(0).getName());

		CPT_Print2( dfg, map, mapMarg, rvNode.getParents(), 0, rvNode.getProbabilityFunction().getVariableIndex(rvNode), rvNode.getEvidence(), rvNode, netcopy , rvNode, resNode, nlist1   );


	}
	

}

}

	for (ResidentNode resNode : ResidentNodes)
	{
		//String rvname= resNode.getName();
		//if(rvname.equals("Beat1")||rvname.equals("Beat2")||rvname.equals("Beat3")||rvname.equals("Beat4")) continue;//

	//	if(!resNode.getName().equals("Rhythm1")) continue;

		rvNode = rvNodeFirstMap.get(resNode);

		HashMap<ProbabilisticNode, Integer> map = new HashMap<ProbabilisticNode, Integer>();

		HashMap<ResidentNode, Integer> mapMarg = new HashMap<ResidentNode, Integer>();
		//map.put((ProbabilisticNode) rvNode, k1);
		System.out.println( "node 1" + resNode.getName() );
		//System.out.println( "node " + resNode.getName() + "  parent  " + resNode.getParentNodes().get(1));
		//System.out.println( "node " + rvNode.getName() + "  parent  " + rvNode.getParents().get(0).getName() );
	

		System.out.println(  "   node 2.1 name" + rvNode.getExplanationDescription() + " " +  rvNode.getName()  );

		for(  Node rvn:rvNode.getParents()  )
			System.out.println( "   node 2.2 name parent " + rvn.getExplanationDescription() + " " +  rvn.getName()  + " no. parents  "+(rvNode.getParents()).size());

		resNode.setTableFunction(" ");
		CPT_Print(   dfg, map, mapMarg, rvNode.getParents(), 0, rvNode.getProbabilityFunction().getVariableIndex(rvNode), rvNode.getEvidence(), rvNode, netcopy , rvNode, resNode, resNode.getParentNodes()   );
		//System.out.println( resNode.getTableFunction() );

	}

	File mebnfile= new File("/Users/gchantas/Desktop/unbbayes-4.18.10/examples/Salsa/MEBNSalsa.ubf");
	ubf.saveMebn(mebnfile, mebn);

	mebnUtil.clearKnowledgeBase();

}


private void initKB() {
		knowledgeBase = PowerLoomKB.getNewInstanceKB();
//		knowledgeBase = textModeRunner.createKnowledgeBase(knowledgeBase, mebn);
}
	/**
	 * TODO allow multiple query
	 * @param queryJob
	 * @return
	 */
	@WebMethod
	@WebResult(name="queryResult", targetNamespace="http://server.reasoning.prognos.seor.gmu.edu/", partName="queryResult")
	public List<QueryResultSummary> runQuery(@WebParam(name="query") QueryInfo queryJob) {
//		System.out.println("Executing run query for queryJob " + queryJob);
		Debug.setDebug(false);
		QueryResultSummary result = new QueryResultSummary();
		try {
			textModeRunner = new TextModeRunner();
			// load ubf/owl
			
			// initialize kb NOT THIS TIME
			//initKB();

			Debug.println(getClass(), "KB initialized");

			// load kb
			mebnUtil = new MebnUtil(mebn);
	
			File evFile = new File("C:/Users/gchantas/Desktop/unbbayes-3.52.7-BETA/examples/mebn/tsamikoEvidence.plm");
			
			mebnUtil.loadFindingsFile(evFile);

			
		
			Debug.println(getClass(), "Evidences loaded");
			
			ResidentNode queryNode = mebn.getDomainResidentNode("isShipOfInterest");
			
			// Create query object
			List<Query> queryList = new ArrayList<Query>();
			for (Integer shipID : queryJob.getShipIDs()) {
				// Set up query
				List<OVInstance> ovInstanceList = new ArrayList<OVInstance>(1);
				List<Argument> arglist = queryNode.getArgumentList();
				OrdinaryVariable ov = arglist.get(0).getOVariable();
				OVInstance ovInstance = OVInstance.getInstance(ov,LiteralEntityInstance.getInstance("ship" + shipID, ov.getValueType()));
				ovInstanceList.add(ovInstance);

				Query query = new Query(queryNode, ovInstanceList);
				
				queryList.add(query);
				Collection<QueryNodeNameAndArguments> queryNodeNamesAndParameters = null;
				QueryNodeNameAndArguments r;
				textModeRunner.callLaskeyAlgorithm(mebn, knowledgeBase, queryNodeNamesAndParameters);

			// run query

			//textModeRunner.executeQueryLaskeyAlgorithm(queryList,knowledgeBase, mebn);
			Debug.println(getClass(), "Query finished");
			
			// Show query result
			StringBuffer queryResult = new StringBuffer();
			DecimalFormat df = new DecimalFormat("##.##");
			List<RandomVariableInfo> terroristPersonInfo = new  ArrayList<RandomVariableInfo>();
			RandomVariableInfo rv = new RandomVariableInfo();
			
			for (Node node : net.getNodes()) {

				rv = new RandomVariableInfo();
				queryResult.append(node.getDescription() + "\n");
				for (int i = 0; i < node.getStatesSize(); i++) {
					queryResult.append(node.getStateAt(i) + " = " + df.format(((ProbabilisticNode)node).getMarginalAt(i)*100) + "%");
					if (i < node.getStatesSize() - 1) {
						queryResult.append(", ");
					}
				}

				if (node.getName().contains("isShipOfInterest")) {
					rv.setName(node.getName());
					rv.setProbability(((ProbabilisticNode)node).getMarginalAt(0));
					result.setShipOfInterestInfo(rv);
				}

				if (node.getName().contains("hasBombPortPlan")) {
					rv.setName(node.getName());
					rv.setProbability(((ProbabilisticNode)node).getMarginalAt(0));
					result.setBombPortPlan(rv);
				}

				if (node.getName().contains("hasExchangeIllicitCargoPlan")) {
					rv.setName(node.getName());
					rv.setProbability(((ProbabilisticNode)node).getMarginalAt(0));
					result.setExchangeIllicitCargoPlan(rv);
				}
				
				if (node.getName().contains("isHijacked")) {
					rv.setName(node.getName());
					rv.setProbability(((ProbabilisticNode)node).getMarginalAt(0));
					result.setHijacked(rv);
				}

				if (node.getName().contains("hasTerroristCrew")) {
					rv.setName(node.getName());
					rv.setProbability(((ProbabilisticNode)node).getMarginalAt(0));
					result.setTerroristCrew(rv);
				}

				if (node.getName().contains("isTerroristPerson")) {
					rv.setName(node.getName());
					rv.setProbability(((ProbabilisticNode)node).getMarginalAt(1));
					terroristPersonInfo.add(rv);
				}

				queryResult.append("\n\n");

			}
			RandomVariableInfo[] rvList = new RandomVariableInfo[terroristPersonInfo.size()];
			for (int i = 0; i < rvList.length; i++) {
				rvList[i] = terroristPersonInfo.get(i);
			}
			result.setTerroristPersonInfo(rvList);
			result.setOutput(queryResult.toString());
		
		}} catch (Exception e) {
			e.printStackTrace();
			result.setOutput("Not able to compute query: " + e.getMessage());
		}

		return Collections.singletonList(result);

	}

	private void loadEvidence(List<EvidenceInfo> evidenceList) throws Exception {
		ResidentNode residentNode;
		ObjectEntity entity;
		ObjectEntityInstanceOrdereable entityOrder;
		ObjectEntityInstance[] arguments;
		Entity state;
		CategoricalStateEntity categoricalState;

		// TODO - Fix this somehow to add what has changed instead of reseting
		// everything and populating again
		mebnUtil.removeAllFindings();
		mebnUtil.removeAllEntityInstances();

		for (EvidenceInfo evidence : evidenceList) {
			residentNode = mebn.getDomainResidentNode(evidence.getResidentNode());
			ArgumentInfo[] arg=evidence.getArguments();
			arguments = new ObjectEntityInstance[arg.length];
			for (int i = 0; i < arguments.length; i++) {
				arguments[i] = mebn.getObjectEntityContainer().getEntityInstanceByName(evidence.getArguments()[i].getName());
				if (arguments[i] == null) {
					
					entity = mebn.getObjectEntityContainer().getObjectEntityByName(evidence.getArguments()[i].getType());
					//entityOrder = (ObjectEntityInstanceOrdereable) entity.addInstance(evidence.getArguments()[i].getName());
					 
					System.out.println("name arg0 : " + evidence.getArguments()[i].getName() );
					mebnUtil.createEntityIntance(entity, evidence.getArguments()[i].getName());

					arguments[i] = mebn.getObjectEntityContainer().getEntityInstanceByName(evidence.getArguments()[i].getName());
				}
			}
			if (evidence.getState().equalsIgnoreCase("true")) {
				state = mebn.getBooleanStatesEntityContainer().getTrueStateEntity();
				mebnUtil.createRandomVariableFinding(residentNode, arguments, state);
			} else if (evidence.getState().equalsIgnoreCase("false")) {
				state = mebn.getBooleanStatesEntityContainer().getFalseStateEntity();
				mebnUtil.createRandomVariableFinding(residentNode, arguments, state);
			} else {
				categoricalState = mebn.getCategoricalStatesEntityContainer().getCategoricalState(evidence.getState());
				mebnUtil.createRandomVariableFinding(residentNode, arguments, categoricalState);
			}
		}
	}

}