import java.io.File;


public class Main {
			/*void setup(){size(640,480);
		  ni.openFileRecording("dfdf"); //= new SimpleOpenNI(this);
		  if(SimpleOpenNI.deviceCount() == 0) ni.openFileRecording("/path/to/yourRecording.oni");
		  ni.enableDepth();
	}
	void draw(){
		  ni.update();
		  image(ni.depthImage(),0,0);
	}*/
	public static void main(String[] args) throws Exception
	{
		
	    MEBNReasoning mr;
	    String[] ovinstances= new String[1];
	    
	    //Tsamiko untrained MEBN.
	    //----->For usage of other MEBNs change the folders and file names accordingly.
	    String MEBNfile="C:/Users/gchantas/Desktop/MEBN_training/MEBNmodel/MEBNMultimodalTsamikoUntrained.ubf";
	    String  PLMfolder="C:/Users/gchantas/Desktop/MEBN_training/TsamikoPLMs";
	    String MEBNoutput="C:/Users/gchantas/Desktop/MEBN_training/MEBNmodel/TsamikoTrained";
	    	    
	    String queryvariablename="";
	    

	    //Salsa
	    //String MEBNfile="C:/Users/gchantas/Desktop/MEBNSalsa/MEBNSalsaUbf/MEBNSalsaManualSyncDependence.ubf";
	    // String  PLMfolder="C:/Users/gchantas/Desktop/MEBNSalsa/SalsaPLMsStandard";
	    //String MEBNoutputfolder="C:/Users/gchantas/Desktop/MEBNSalsa/MEBNSalsaUbf/";
	    // String queryvariablename="rhythmClass";
	    
		int generalEMIter=5;//Should be >1
		int FileNumber=1;//File to be excluded from the dataset (for cross validation). Should be >=0 and max=number of files found in the folder PLMfolder
		
		//ovinstances[0]="T1";
	    //for(generalIter=11;generalIter<=FileNumber+1;generalIter++)
	   mr = new MEBNReasoning();
	    //Tsamiko MEBN inference method. Run this to see results of the inference. MEBN file and test data file are defined in the method
	   int training=0;
	   System.out.println("Give 1 for training and 0 for inference:");
	   training= System.in.read();

	   if(training==0)
	   {
		   System.out.println("Proceed to inference");
		   mr.MEBNRunInference(7,MEBNfile,PLMfolder,MEBNoutput,queryvariablename,ovinstances);
	   }
	   else
	   {
		   System.out.println("Proceed to training");

		   mr.MEBNTraining(generalEMIter, FileNumber , MEBNfile,PLMfolder,MEBNoutput,queryvariablename,ovinstances);
	   
		   String mebnfiletrained = new String( MEBNoutput+ "Newexcl"+FileNumber+".ubf"   );

		   mr.MEBNCorrection(FileNumber,mebnfiletrained,PLMfolder,MEBNoutput);
	   }
	}
}
