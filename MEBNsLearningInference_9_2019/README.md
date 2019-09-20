This Java - Eclipse project implements the learning and inference MEBN algorithm and it was used for the experiments presented in deliverable D4.1. 

To use it add as external jars ALL the jar files residing in the JarFiles folder (see the folder one step above).

The class used to implement the MEBN learning algorithm and the inference is the "MEBNReasoning" class. See the Main class how to use the two methods for learning and inference, respectively.

The MEBReasoning.Training method is used with arguments explained as follows:

1)  generalEMIter: max number of EM iterations (int>0)
2) fileexl: the number of the file to be excluded from the training set (>1 or 0 for no exclusion).
3) MEBNfile: the file (folder/filename) of the MEBN to be trained,
4) PLMfolder: the folder with the PLM files
5) MEBNoutputfolder: the folder in which we want the MEBN output file to saved
6) and 7. queryvariablename and ovinstances: the variable name (resident node) to be queried and a specific logical argument(s) of it (ordinary instance(s)). That are used subsequently in a query to retrieve all the resident nodes of the MEBN which we want to "learn" their probabilities with the EM algorithm. Thus, please be sure that you choose the correct in this context variable and ordinary var. instance(s) in this context.
