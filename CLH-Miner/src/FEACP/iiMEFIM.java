package miners.algorithms.frequentpatterns.efim;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.lang.management.MemoryPoolMXBean;
import java.lang.management.MemoryType;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;


import miners.tools.MemoryLogger;


/* This file is copyright (c) 2012-2015 Souleymane Zida & Philippe Fournier-Viger
* 
* This file is part of the SPMF DATA MINING SOFTWARE
* (http://www.philippe-fournier-viger.com/spmf).
* 
* SPMF is free software: you can redistribute it and/or modify it under the
* terms of the GNU General Public License as published by the Free Software
* Foundation, either version 3 of the License, or (at your option) any later
* version.
* SPMF is distributed in the hope that it will be useful, but WITHOUT ANY
* WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
* A PARTICULAR PURPOSE. See the GNU General Public License for more details.
* You should have received a copy of the GNU General Public License along with
* SPMF. If not, see <http://www.gnu.org/licenses/>.
*/

/**
 * This is an implementation of the EFIM algorithm for
 * mining high-utility itemsets from a transaction database.
 * More information on the EFIM algorithm can be found in that paper: <br\>
 *
 * @author Souleymane Zida, Philippe Fournier-Viger using some code by Alan Souza
 */
public class iiMEFIM {

	/** the set of high-utility itemsets */
    private Itemsets highUtilityItemsets;
    
	/** object to write the output file */
	BufferedWriter writer = null;
	
	/** the number of high-utility itemsets found (for statistics) */
	private int patternCount; 

	/** the start time and end time of the last algorithm execution */
	long startTimestamp;
	long endTimestamp;
	
	/** the minutil threshold */
	int minUtil;
	
	/** if this variable is set to true, some debugging information will be shown */
    final boolean  DEBUG = false;
	
    /** The following variables are the utility-bins array 
	// Recall that each bucket correspond to an item */
    /** utility bin array for sub-tree utility */
	private long[] utilityBinArraySU;   
	/** utility bin array for local utility */
	private long[] utilityBinArrayLU; 
	
	/** a temporary buffer */
	private int [] temp= new int [500];	
	
	/** The total time spent for performing intersections */
	long timeIntersections;
	/** The total time spent for performing database reduction */
	long timeDatabaseReduction;
	/** The total time spent for identifying promising items */
	long timeIdentifyPromisingItems;
	/** The total time spent for sorting */
	long timeSort;
	/** The total time spent for binary search */
	long timeBinarySearch;
	
	static double dbSizeOnMem;

	/** an array that map an old item name to its new name */
    int[] oldNameToNewNames;
    /** an array that map a new item name to its old name */
    int[] newNamesToOldNames;
   
    /** the number of new items */
    int newItemCount;
    /** size of database*/
    int dbTranlen = 0;
    /** size of database after remove transaction*/
    int dbTranMiningLen = 0;
    /** size of Itemset*/
    int itemsetCount = 0;   
       
    /** if true, transaction merging will be performed by the algorithm */
    boolean activateTransactionMerging;

    /** A parameter for transaction merging*/
    final int MAXIMUM_SIZE_MERGING = 1000;
    
    /** number of times a transaction was read */
    long transactionReadingCount;
    /** number of merges */
    long mergeCount;

    /** number of itemsets from the search tree that were considered */
	private long candidateCount;

	/** If true, sub-tree utility pruning will be performed */
	private boolean activateSubtreeUtilityPruning;
	
	/** If true, build Pset */
	private boolean isBuildPsetList = false;
    

	
	public static Map<Integer, UtilityList> mapItemToUtilityList ;
	/** 
	 * Constructor
	 */
    public iiMEFIM() {
		candidateCount = 0;
		minUtil = 0;
	}

    /**
     * Run the algorithm
     * @param minUtil  the minimum utility threshold (a positive integer)
     * @param inputPath  the input file path
     * @param outputPath  the output file path to save the result or null if to be kept in memory
     * @param activateTransactionMerging 
     * @param activateSubtreeUtilityPruning 
     * @param maximumTransactionCount
       * @return the itemsets or null if the user choose to save to file
     * @throws IOException if exception while reading/writing to file
     */
    public Itemsets runAlgorithm(int minUtil, String inputPath, String outputPath,String producClassPath,String productPath, boolean activateTransactionMerging, int maximumTransactionCount, boolean activateSubtreeUtilityPruning) throws IOException {
    	
    	// reset variables for statistics
    	mergeCount=0;
    	transactionReadingCount=0;
		timeIntersections = 0;
		timeDatabaseReduction = 0;
    	
    	// save parameters about activating or not the optimizations
    	this.activateTransactionMerging = activateTransactionMerging;
    	this.activateSubtreeUtilityPruning = activateSubtreeUtilityPruning;
    	
		// record the start time
		startTimestamp = System.currentTimeMillis();
		
		long heapBefore = Runtime.getRuntime().totalMemory();
		
		// read the input file
		Dataset dataset = new Dataset(inputPath,producClassPath,productPath, maximumTransactionCount);

		long heapAfter = Runtime.getRuntime().totalMemory();
		//dbSizeOnMem = (heapAfter-heapBefore)/1024/1024;
		dbSizeOnMem = 0;
		//System.out.println("DBSIZE="+((long) dbSizeOnMem)+"MB");
		
		// save minUtil value selected by the user
		this.minUtil = minUtil;

		// if the user choose to save to file
		// create object for writing the output file
		if(outputPath != null) {
			writer = new BufferedWriter(new FileWriter(outputPath));
		}else {
			// if the user choose to save to memory
			writer = null;
	        this.highUtilityItemsets = new Itemsets("Itemsets");
		}

		// reset the number of itemset found
		patternCount = 0;
		
		// reset the memory usage checking utility
		MemoryLogger.getInstance().reset();
		
		// if in debug mode, show the initial database in the console
		if(DEBUG)
		{
			System.out.println("===== Initial database === ");
			System.out.println(dataset.toString());
		}
		
	    // Scan the database using utility-bin array to calculate the TWU
		// of each item
		dbTranlen = dataset.getTransactions().size();
		itemsetCount = dataset.getMaxItem();
		
		useUtilityBinArrayToCalculateLocalUtilityFirstTime(dataset);
		
		// if in debug mode, show the TWU calculated using the utility-bin array
        if(DEBUG) 
        {
	    	System.out.println("===== TWU OF SINGLE ITEMS === ");
			for (int i = 1; i < utilityBinArrayLU.length; i++)
			{
				System.out.println("item : " + i + " twu: " + utilityBinArrayLU[i]);
			}
			System.out.println();			
        }

	   	// Now, we keep only the promising items (those having a twu >= minutil)
	   	List<Integer> itemsToKeep = new ArrayList<Integer>();
	   	for(int j=1; j< utilityBinArrayLU.length;j++) 
	   	{
	   		if(utilityBinArrayLU[j] >= minUtil) 
	   		{
	   			itemsToKeep.add(j);
	   		}
	   	}
	   	mapItemToUtilityList = new HashMap<Integer, UtilityList>();
	   	List<UtilityList> listOfUtilityLists = new ArrayList<UtilityList>();
	   
	   //Sort promising items according to the increasing order of TWU
	   insertionSort(itemsToKeep, utilityBinArrayLU);
       
	   // Rename promising items according to the increasing order of TWU.
	   // This will allow very fast comparison between items later by the algorithm
	   // This structure will store the new name corresponding to each old name
       oldNameToNewNames = new int[dataset.getMaxItem() + 1];
       // This structure will store the old name corresponding to each new name
       newNamesToOldNames = new int[dataset.getMaxItem() + 1];
       // We will now give the new names starting from the name "1"
       int currentName = 1;
       // For each item in increasing order of TWU
       for (int j=0; j< itemsToKeep.size(); j++)
	   {
    	   // get the item old name
    	   int item = itemsToKeep.get(j);
    	   // give it the new name
		   oldNameToNewNames[item] = currentName;
		   // remember its old name
		   newNamesToOldNames[currentName] = item;
		   // replace its old name by the new name in the list of promising items
		   itemsToKeep.set(j, currentName);
		   // increment by one the current name so that 
		   currentName++;
	   }
       for (int Item : itemsToKeep) {
 			   UtilityList uList = new UtilityList(Item);
 			   mapItemToUtilityList.put(Item, uList);
 			  listOfUtilityLists.add(uList);
 	   }
       
        // remember the number of promising item
		newItemCount = itemsToKeep.size();
		//int itemCountFirstRemove = newItemCount;
		// if in debug mode, print to the old names and new names to the console
		// to check if they are correct
		if (DEBUG) {
			System.out.println(itemsToKeep);
			System.out.println(Arrays.toString(oldNameToNewNames));
			System.out.println(Arrays.toString(newNamesToOldNames));
		}	
		 // We now loop over each transaction from the dataset
		// to remove unpromising items
    	for(int i=0; i< dataset.getTransactions().size();i++)
    	{
    		// Get the transaction
    		Transaction transaction  = dataset.getTransactions().get(i);

    		// Remove unpromising items from the transaction and at the same time
    		// rename the items in the transaction according to their new names
    		// and sort the transaction by increasing TWU order
    		//ad parent for trans
    		transaction.removeUnpromisingItems(i,oldNameToNewNames,newNamesToOldNames);
    	}
		
    	// Now we will sort transactions in the database according to the proposed
    	// total order on transaction (the lexicographical order when transactions
    	// are read backward).
    	long timeStartSorting = System.currentTimeMillis();
    	// We only sort if transaction merging is activated
    	      	
    	
    	

    	// record the total time spent for sorting
    	timeSort = System.currentTimeMillis() - timeStartSorting;
    	
    	// if in debug mode, print the database after sorting and removing promising items
		if(DEBUG)
		{
			System.out.println("===== Database without unpromising items and sorted by TWU increasing order === ");
			System.out.println(dataset.toString());
		}
		
		// initialize the utility-bin array for counting the subtree utility
		dbTranMiningLen = dataset.getTransactions().size();
		if(dbTranMiningLen !=0)
		{
			utilityBinArraySU = new long[newItemCount + 1];			
			// Use an utility-bin array to calculate the sub-tree utility of each item, built Pset
	    	useUtilityBinArrayToCalculateSubtreeUtilityFirstTime(dataset);
	    		    	
	    	// Calculate the set of items that pass the sub-tree utility pruni;ng condition
			List<Integer> itemsToExplore = new ArrayList<Integer>();
	
	    	for (int item : itemsToKeep) {
				if(utilityBinArraySU[item]>minUtil) {				
					if(activateSubtreeUtilityPruning){
						itemsToExplore.add(item);
					}
				}
			}
	    	Collections.sort(itemsToExplore);
	
	    	
			// If in debug mode, show the list of promising items
	    	if(DEBUG)
	    	{
		       	System.out.println("===== List of promising items === ");
		       	System.out.println(itemsToKeep);
	    	}
	
	    	//======
	        // Recursive call to the algorithm
	       	// If subtree utility pruning is activated
	    	if(activateSubtreeUtilityPruning){
	    		// We call the recursive algorithm with the database, secondary items and primary items    		
	    			backtrackingEFIM(dataset.getTransactions(), itemsToKeep, itemsToExplore, 0, mapItemToUtilityList);
	    	}else{
	    		// We call the recursive algorithm with the database and secondary items
	    		backtrackingEFIM(dataset.getTransactions(), itemsToKeep, itemsToKeep, 0,mapItemToUtilityList);
	    	}
		}
		// record the end time
		endTimestamp = System.currentTimeMillis();
		
		//close the output file
		if(writer != null) {
			writer.close();
		}
		
		// check the maximum memory usage
		MemoryLogger.getInstance().checkMemory();
		printPeakHeapUsage();
		
		// return the set of high-utility itemsets
        return highUtilityItemsets;
    }

	/**
	 * Implementation of Insertion sort for sorting a list of items by increasing order of TWU.
	 * This has an average performance of O(n log n)
	 * @param items list of integers to be sorted
	 * @param items list the utility-bin array indicating the TWU of each item.
	 */
    public static void insertionSort(List<Integer> items, long [] utilityBinArrayTWU){
		// the following lines are simply a modified an insertion sort
		
		Map<Integer,ProductInfo> idtoObjMap = Dataset.idToProductInfoMap;
		for(int j=1; j< items.size(); j++){
			Integer itemJ = items.get(j);
			int i = j - 1;
			Integer itemI = items.get(i);
			int comparison = idtoObjMap.get(itemI).getLevel()-idtoObjMap.get(itemJ).getLevel();
			if(comparison == 0){
				comparison = (int)(utilityBinArrayTWU[itemI] - utilityBinArrayTWU[itemJ]);
			}	
			while(comparison > 0){
				items.set(i+1, itemI);
				i--;
				if(i<0){
					break;
				}			
				itemI = items.get(i);
				comparison = idtoObjMap.get(itemI).getLevel()-idtoObjMap.get(itemJ).getLevel();
				// if the twu is equal, we use the lexicographical order to decide whether i is greater
				// than j or not.
				if(comparison == 0){
					comparison = (int)(utilityBinArrayTWU[itemI] - utilityBinArrayTWU[itemJ]);
				}
			}
			items.set(i+1,itemJ);
		}
	}
	 /**
     * Recursive method to find all high-utility itemsets
     * @param the list of transactions containing the current prefix P
	 * @param itemsToKeep the list of secondary items in the p-projected database
	 * @param itemsToExplore the list of primary items in the p-projected database
	 * @param the current prefixLength
     * @throws IOException if error writing to output file
     */

    
    private void backtrackingEFIM( List<Transaction> transactionsOfP,
    		List<Integer> itemsToKeep, List<Integer> itemsToExplore, int prefixLength, Map<Integer,UtilityList> MapOfUtilityLists) throws IOException {

    	// update the number of candidates explored so far
		candidateCount += itemsToExplore.size();
		
        // ========  for each frequent item  e  =============
		for (int j = 0; j < itemsToExplore.size(); j++) {			
			//
			/*Map<Integer,UtilityList> MapCopyULs  =  new HashMap<Integer, UtilityList>();
			for (Integer itemID : MapOfUtilityLists.keySet()) {
				MapCopyULs.put(itemID, new UtilityList(MapOfUtilityLists.get(itemID)));
			}
			*/
			Integer e = itemsToExplore.get(j);
			List<Transaction> transactionsPe = new ArrayList<Transaction>();
			int utilityPe = 0;
			////==================TungCode==================================
			//Union TransactionP vs ULs for get transE
				
				
				int  indexUnionArray1 = 0;
				int  indexUnionArray2 = 0;
			
				List<Transaction> arr1 = transactionsOfP;
				List<Element> arr2 = MapOfUtilityLists.get(e).getElement();
				int transOfPsize = arr1.size();
				int listElementsize = arr2.size();
				while (indexUnionArray1 < transOfPsize && indexUnionArray2 < listElementsize) 
			    { 
			        if (arr1.get(indexUnionArray1).getIndex() < arr2.get(indexUnionArray2).tid) 
			        	indexUnionArray1++; 
			        else if (arr2.get(indexUnionArray2).tid < arr1.get(indexUnionArray1).getIndex()) 
			        	indexUnionArray2++; 
			        else 
			        { 
			        	
			        	Transaction getTrans = arr1.get(indexUnionArray1++);
			        	int[] items = getTrans.getItems();
			        	int[] utilities = getTrans.getUtilities();
			        	int[] newitems = new int[0];		        	
			        	int[] newutilities = new int[0];
			        	int newUtilityTrans = 0;
			        	for (int i = 0; i < items.length; i++) {
							int currentItem = items[i];
							if(!checkisParent(e, currentItem)&&e<currentItem) {
								newitems = Arrays.copyOf(newitems, newitems.length+1);
								newitems[newitems.length-1] =currentItem;
								newutilities= Arrays.copyOf(newutilities, newutilities.length+1);
								newutilities[newutilities.length-1] =utilities[i];
								newUtilityTrans+=utilities[i];
							}
						}
			        	Transaction newTrans = new Transaction(getTrans.index, newitems,newutilities,(int)getTrans.getUtility());
			        	newTrans.setPrefixUtility(getTrans.getPrefixUtility()+arr2.get(indexUnionArray2++).iutils);
			        	newTrans.setTransactionUtility(newUtilityTrans);
			        	transactionsPe.add(newTrans);   
			        	utilityPe+=newTrans.getPrefixUtility();
			        	 
			        } 
			    }
				temp[prefixLength] = e;
				//MapCopyULs.remove(e);
				List<Integer> newItemToKeep = new ArrayList<Integer>(itemsToKeep);
				List<Integer> newItemToExplore = new ArrayList<Integer>(itemsToExplore);
				List<Integer> ListChildOfE = Dataset.getAllChildNewName(oldNameToNewNames,newNamesToOldNames, e);
				
				
				if(utilityPe<minUtil){				
					newItemToExplore.removeAll(ListChildOfE);					
				}
				
				else {
					
				}
				output(prefixLength, utilityPe);	
				newItemToKeep.removeAll(ListChildOfE);				
				
				
				//System.out.println(transactionsPe.size());
				DataTrans dataTrans = useUtilityBinArraysToCalculateUpperBounds(transactionsPe,newItemToKeep,MapOfUtilityLists);
				Map<Integer, UtilityList> reduceUL =  dataTrans.ULsData;
				List<Transaction> reduceTran = dataTrans.Transdata;
				//System.out.println(newTran.size());
				//System.out.println(reduceTran.size());
				long initialTime = System.currentTimeMillis();
				
				// We will create the new list of secondary items
				List<Integer> newItemsToKeep = new ArrayList<Integer>();
				// We will create the new list of primary items
				List<Integer> newItemsToExplore = new ArrayList<Integer>();
				
				// for each item
		    	for (int k = j; k < newItemToKeep.size(); k++) {
		        	Integer itemk =  newItemToKeep.get(k);
		        	
		        	// if the sub-tree utility is no less than min util
		            if(utilityBinArraySU[itemk] >= minUtil) {
		            	// and if sub-tree utility pruning is activated
		            	if(activateSubtreeUtilityPruning){
		            		// consider that item as a primary item
		            		newItemsToExplore.add(itemk);
		            	}
		            	// consider that item as a secondary item
		            	newItemsToKeep.add(itemk);
		            }else if(utilityBinArrayLU[itemk] >= minUtil)
		            {
		            	// otherwise, if local utility is no less than minutil,
		            	// consider this itemt to be a secondary item
		            	newItemsToKeep.add(itemk);
		            }
		        }	
		    	timeIdentifyPromisingItems +=  (System.currentTimeMillis() -  initialTime);
				backtrackingEFIM(reduceTran, newItemsToKeep, newItemsToExplore,prefixLength+1,reduceUL);
			}
			
			
		
			
			////===================End Tung COde===================

	}

 


    /**
     * Check if two transaction are identical
     * @param t1  the first transaction
     * @param t2  the second transaction
     * @return true if they are equal
     */
    private boolean isEqualTo(Transaction t1, Transaction t2) {
    	// we first compare the transaction lenghts
		int length1 = t1.items.length - t1.offset;
		int length2 = t2.items.length - t2.offset;
		// if not same length, then transactions are not identical
    	if(length1 != length2){
    		return false;
    	}
    	// if same length, we need to compare each element position by position,
    	// to see if they are the same
    	int position1 = t1.offset;
		int position2 = t2.offset;
		
		// for each position in the first transaction
		while(position1 < t1.items.length){
			// if different from corresponding position in transaction 2
			// return false because they are not identical
			if(t1.items[position1]  != t2.items[position2]){
				return false;
			}
			// if the same, then move to next position
			position1++;
			position2++;
		}
		// if all items are identical, then return to true
		return true;
	}

   
	/**
	 * Scan the initial database to calculate the local utility of each item
	 * using a utility-bin array
	 * @param dataset the transaction database
	 */
    public void useUtilityBinArrayToCalculateLocalUtilityFirstTime(Dataset dataset) {

		// Initialize utility bins for all items
		utilityBinArrayLU = new long[dataset.getMaxItem() + 1];
		HashSet<Integer> hasParent;
		// Scan the database to fill the utility bins
		// For each transaction
		for (Transaction transaction : dataset.getTransactions()) {
			hasParent = new HashSet<Integer>();
			// for each item
			for(Integer item: transaction.getItems()) {
				// we add the transaction utility to the utility bin of the item
				utilityBinArrayLU[item] += transaction.transactionUtility;
				ProductInfo itemIParent = dataset.idToProductInfoMap.get(item).getParent();
	        	while(itemIParent.getData()!=-1) {
	        		
	        		int dataOfParent = itemIParent.getData();
	        		hasParent.add(dataOfParent);
	        		itemIParent = itemIParent.getParent();
	        	}

			}
			for(Integer item: hasParent) {
				utilityBinArrayLU[item] += transaction.transactionUtility;
			}
		}
	}	
	/**
	 * Scan the initial database to calculate the sub-tree utility of each item
	 * using a utility-bin array
	 * @param dataset the transaction database
	 */
    public void useUtilityBinArrayToCalculateSubtreeUtilityFirstTime(Dataset dataset) {

		// Scan the database to fill the utility-bins of each item
		// For each transaction
		for (int i : mapItemToUtilityList.keySet()) {
			UtilityList UL = mapItemToUtilityList.get(i);
			utilityBinArraySU[i]=(int)UL.sumIutils+(int)UL.sumRutils;
			//System.out.println("Element :" + i);
			/*for (Element j : mapItemToUtilityList.get(i).getElement()) {
				System.out.println("ID: "+j.tid+"u: "+j.iutils+" r: "+j.rutils);
			}
			System.out.println();*/
		}
		
		//System.out.println(utilityBinArraySU.toString());
		
	}
	public Boolean checkisParent(ProductInfo Item1,ProductInfo Item2) {
		if(Item1.getLevel()>Item2.getLevel()) {
			ProductInfo parent = Item1.getParent();
			while(parent.getData()!=-1) {
				if(parent.getData()==Item1.getData()) {
					return true;
				}
				parent=parent.getParent();
			}
			return false;
		}else {
			if(Item1.getLevel()<Item2.getLevel()) {
				ProductInfo parent = Item2.getParent();
				while(parent.getData()!=-1) {
					if(parent.getData()==Item2.getData()) {
						return true;
					}
					parent=parent.getParent();
				}
				return false;
			}else {
				return false;
			}
		}
	}
	/**

    /**
     * Utilize the utility-bin arrays to calculate the sub-tree utility and local utility of all
     * items that can extend itemset P U {e}
     * @param transactions the projected database for P U {e}
     * @param j the position of j in the list of promising items
     * @param itemsToKeep the list of promising items
     */
    private DataTrans useUtilityBinArraysToCalculateUpperBounds(List<Transaction> transactionsPe,
    		 List<Integer> itemsToKeep,Map<Integer,UtilityList> MapOfUtilityLists) {
    	long time1 = System.currentTimeMillis();
    	Collections.sort(transactionsPe, new Comparator<Transaction>(){
			@Override
			/**
			 * Compare two transactions
			 */
			public int compare(Transaction t1, Transaction t2) {
				// we will compare the two transaction items by items starting
				// from the last items.
				int pos1 = t1.items.length - 1;
				int pos2 = t2.items.length - 1;
				
				// if the first transaction is smaller than the second one
				if(t1.items.length < t2.items.length){
					// while the current position in the first transaction is >0
					while(pos1 >=0){
						int subtraction = t2.items[pos2]  - t1.items[pos1];
						if(subtraction !=0){
							return subtraction;
						}
						pos1--;
						pos2--;
					}
					// if they ware the same, they we compare based on length
					return -1;
					
				// else if the second transaction is smaller than the first one
				}else if (t1.items.length > t2.items.length){
					// while the current position in the second transaction is >0
					while(pos2 >=0){
						int subtraction = t2.items[pos2]  - t1.items[pos1];
						if(subtraction !=0){
							return subtraction;
						}
						pos1--;
						pos2--;
					}
					// if they are the same, they we compare based on length
					return 1;

				}else{
				// else if both transactions have the same size
					while(pos2 >=0){
						int subtraction = t2.items[pos2]  - t1.items[pos1];
						if(subtraction !=0){
							return subtraction;
						}
						pos1--;
						pos2--;
					}
					// if they ware the same, they we compare based on length
					return 0;
				}
			}

		});
    	long time2 = System.currentTimeMillis();
    	//System.out.println(time2-time1);
    	Map<Integer,Integer> mapOldIndexToNewIndex = new HashMap<Integer, Integer>();
    	Map<Integer,UtilityList> ReduceMap  = new HashMap<Integer, UtilityList>();
    	// we will record the time used by this method for statistics purpose
		long initialTime = System.currentTimeMillis();
		int sumRemainingUtility;
		int count = 0;
		List<Transaction>transactionsPeAfterProjected = new ArrayList<Transaction>();
		Transaction previousTransaction = null;
		int consecutiveMergeCount = 0;
		
		for (Transaction transaction : transactionsPe) {
			Transaction projectedTransaction = new Transaction(transaction);
			if(previousTransaction==null) {
				previousTransaction = projectedTransaction;
				
			}
			else {
				if (isEqualTo(projectedTransaction, previousTransaction)) {
					if(consecutiveMergeCount==0) {
						int itemsCount = transaction.items.length;
						int[] items = new int[itemsCount];
						System.arraycopy(previousTransaction.items, 0, items, 0, itemsCount);
						int[] utilities = new int[itemsCount];
						System.arraycopy(previousTransaction.utilities, 0, utilities, 0, itemsCount);
						
						int positionPrevious = 0;
						
						
						while(positionPrevious < itemsCount){
							utilities[positionPrevious] += projectedTransaction.utilities[positionPrevious];
							positionPrevious++;
						}
						int sumUtilities = previousTransaction.prefixUtility += projectedTransaction.prefixUtility;
						int index = previousTransaction.getIndex();
						previousTransaction = new Transaction(index,items, utilities, previousTransaction.transactionUtility + projectedTransaction.transactionUtility);
						previousTransaction.prefixUtility = sumUtilities;	
						
					}
					else {
						int positionPrevious = 0;
						int itemsCount = previousTransaction.items.length;
						while(positionPrevious < itemsCount){
							previousTransaction.utilities[positionPrevious] += projectedTransaction.utilities[positionPrevious];
							positionPrevious++;
						}
						
						// make also the sum of transaction utility and prefix utility
						previousTransaction.transactionUtility += projectedTransaction.transactionUtility;
						previousTransaction.prefixUtility += projectedTransaction.prefixUtility;	
					}
					consecutiveMergeCount++;
					
				}
				else {
					transactionsPeAfterProjected.add(previousTransaction);
					previousTransaction = projectedTransaction;
					consecutiveMergeCount = 0;
				}
				
			}
			mapOldIndexToNewIndex.put(transaction.index, previousTransaction.index);
		}
		
		if(previousTransaction != null){
			transactionsPeAfterProjected.add(previousTransaction);
        }
		Map<Integer,Transaction> mapIndexToTrans = new HashMap<Integer, Transaction>();
		for (Transaction transaction2 : transactionsPeAfterProjected) {
			mapIndexToTrans.put(transaction2.index, transaction2);
		}
		// For each promising item > e according to the total order
		for (int j = 0; j < itemsToKeep.size(); j++) {
			Integer item = itemsToKeep.get(j);
			// We reset the utility bins of that item for computing the sub-tree utility and
			// local utility
			utilityBinArraySU[item] = 0;
			utilityBinArrayLU[item] = 0;
			sumRemainingUtility = 0;
			UtilityList newUls = new UtilityList(item);
			Map<Integer,Element> mapIDtoElement = new HashMap<Integer, Element>();
			
			for (Element element : MapOfUtilityLists.get(item).getElement()) {
				Integer newIndex = mapOldIndexToNewIndex.get(element.tid);
				if(newIndex!=null) {
					Element newElement = mapIDtoElement.get(newIndex);
					if(newElement!=null) {
						newElement.iutils += element.iutils;
						newElement.rutils += element.rutils;
						newUls.sumIutils+=element.iutils;
						newUls.sumRutils+=element.rutils;
						utilityBinArraySU[item] += element.iutils;
						
					}
					else {
						newElement = new Element(element);
						mapIDtoElement.put(newIndex,newElement);
						newUls.addElement(newElement);
						//System.out.print(newIndex);	
						Transaction getTrans = mapIndexToTrans.get(newIndex);
			        	int[] items = getTrans.getItems();
			        	int[] utilities = getTrans.getUtilities();
			        	
			        	for (int k = items.length-1; k >=0; k--) {
			        		int currentItem = items[k];
							if(currentItem>item&&!checkisParent(currentItem, item)) {
								sumRemainingUtility+=utilities[k];
							}
						}
			        	
			        	sumRemainingUtility+=newElement.iutils;
			        	utilityBinArraySU[item] += getTrans.getPrefixUtility()+sumRemainingUtility;
						utilityBinArrayLU[item] += getTrans.getPrefixUtility()+getTrans.getUtility();						
					}
				}	
			}
			if(utilityBinArrayLU[item]<minUtil) {
				List<Integer> childOfItem = Dataset.getAllChildNewNameWithOutIt(oldNameToNewNames, newNamesToOldNames, item);
				if(childOfItem.size()>0) {						
					itemsToKeep.removeAll(childOfItem);
					
					utilityBinArraySU[item] = 0;
					utilityBinArrayLU[item] = 0;
				}
				
				
			}
			ReduceMap.put(item, newUls);
		
			
			
			//arr2.removeAll(listElementRemove);

			
			
		}
		
		Collections.sort(transactionsPeAfterProjected, new Comparator<Transaction>() {
			public int compare(Transaction t1,Transaction t2) {
				if(t1.index<t2.index) {
					return -1 ;
				}
				return 1;
			}
		});
		
		
		transactionsPe = new ArrayList<Transaction>(transactionsPeAfterProjected);
		// we update the time for database reduction for statistics purpose
		timeDatabaseReduction += (System.currentTimeMillis() - initialTime);
		return (DataTrans) new DataTrans(transactionsPeAfterProjected, ReduceMap);
    }



    /**
     * Save a high-utility itemset to file or memory depending on what the user chose.
     * @param itemset the itemset
     * @throws IOException if error while writting to output file
     */
    private void output(int tempPosition, int utility) throws IOException {
        patternCount++;
    
       // System.out.println(patternCount);
        
        // if user wants to save the results to memory
		if (writer == null) {
			// we copy the temporary buffer into a new int array
			int[] copy = new int[tempPosition+1];
			System.arraycopy(temp, 0, copy, 0, tempPosition+1);
			// we create the itemset using this array and add it to the list of itemsets
			// found until now
			highUtilityItemsets.addItemset(new Itemset(copy, utility),copy.length); 
		} else {
			// if user wants to save the results to file
			// create a stringuffer
			StringBuffer buffer = new StringBuffer();
			// append each item from the itemset to the stringbuffer, separated by spaces
			for (int i = 0; i <= tempPosition; i++) {
				buffer.append(temp[i]);
				if (i != tempPosition) {
					buffer.append(' ');
				}
			}
			// append the utility of the itemset
			buffer.append(" #UTIL: ");
			buffer.append(utility);
			
			// write the stringbuffer to file and create a new line
			// so that we are ready for writing the next itemset.
			
			//writer.write(buffer.toString());
			//writer.newLine();
			System.out.println(buffer.toString());
		}
		
    }


    /**
     * Print out the maximum peak heap usage
     */
    public static void printPeakHeapUsage()
    {
    	try {
            List<MemoryPoolMXBean> pools = ManagementFactory.getMemoryPoolMXBeans();
            // we print the result in the console
			double total = 0;
			for (MemoryPoolMXBean memoryPoolMXBean : pools) {
				if (memoryPoolMXBean.getType() == MemoryType.HEAP) {
					long peakUsed = memoryPoolMXBean.getPeakUsage().getUsed();
					//System.out.println(String.format("Peak used for: %s is %.2f", memoryPoolMXBean.getName(), (double)peakUsed/1024/1024));
					total = total + peakUsed;
				}
			}
			System.out.println(String.format("Total heap peak used: %f MB", ((total)/1024/1024)-dbSizeOnMem));
     
       } catch (Throwable t) {
            System.err.println("Exception in agent: " + t);
       }
    }	 
 
    /**
     * Print statistics about the latest execution of the EFIM algorithm.
     */
	public void printStats() {

		System.out.println("========== iMEFIM - STATS ============");
		System.out.println(" minUtil = " + minUtil);
		System.out.println(" High utility itemsets count: " + patternCount);	
		System.out.println(" Total time ~: " + (endTimestamp - startTimestamp)
				+ " ms");
		System.out.println(" Transaction merge count ~: " + mergeCount);	
		System.out.println(" Transaction read count ~: " + transactionReadingCount);	

		// if in debug mode, we show more information
		if(DEBUG) {
			
			System.out.println(" Time intersections ~: " + timeIntersections
					+ " ms");	
			System.out.println(" Time database reduction ~: " + timeDatabaseReduction
					+ " ms");
			System.out.println(" Time promising items ~: " + timeIdentifyPromisingItems
					+ " ms");
			System.out.println(" Time binary search ~: " + timeBinarySearch
					+ " ms");
			System.out.println(" Time sort ~: " + timeSort	+ " ms");
		}
		System.out.println(" Max memory:" + (MemoryLogger.getInstance().getMaxMemory()-dbSizeOnMem));
		System.out.println(" Candidate count : "             + candidateCount);
		System.out.println("=====================================");
	}
	/**
     * Print statistics about the latest execution of the NewEFIM algorithm to file
     */
	public void printLog(String output) throws IOException 
	{
		BufferedWriter writerlog = new BufferedWriter(new FileWriter(output,true));
		writerlog.newLine();
		writerlog.write("========== iMEFIM - STATS ============"); writerlog.newLine();
		writerlog.write(" minUtil = " + minUtil);writerlog.newLine();
		
		writerlog.write(" Number Transaction = " + dbTranlen);writerlog.newLine();
		writerlog.write(" Number item = " + itemsetCount);writerlog.newLine();
		writerlog.write(" Number Transaction after remove item = " + dbTranMiningLen);writerlog.newLine();
		writerlog.write(" Number item after remove item= " + newItemCount);writerlog.newLine();
		
		writerlog.write(" High utility itemsets count: " + patternCount);writerlog.newLine();	
		writerlog.write(" Total time ~: " + (endTimestamp - startTimestamp)+ " ms");writerlog.newLine();
		writerlog.write(" Transaction merge count ~: " + mergeCount);	writerlog.newLine();
		writerlog.write(" Transaction read count ~: " + transactionReadingCount);	writerlog.newLine();
			
		writerlog.write(" Time intersections ~: " + timeIntersections + " ms");	writerlog.newLine();
		writerlog.write(" Time database reduction ~: " + timeDatabaseReduction + " ms");writerlog.newLine();
		writerlog.write(" Time promising items ~: " + timeIdentifyPromisingItems	+ " ms");writerlog.newLine();
		writerlog.write(" Time binary search ~: " + timeBinarySearch	+ " ms");writerlog.newLine();
		writerlog.write(" Time sort ~: " + timeSort	+ " ms");	writerlog.newLine();
		writerlog.write(" Max memory:" + MemoryLogger.getInstance().getMaxMemory());writerlog.newLine();
		writerlog.write(" Candidate count : "             + candidateCount);writerlog.newLine();
		writerlog.write("=====================================");
		writerlog.close();
		System.out.println("Finish");
	}
	public Boolean checkisParent(int IDItem1,int IDItem2) {
		ProductInfo Item1 = Dataset.idToProductInfoMap.get(newNamesToOldNames[IDItem1]);
		ProductInfo Item2 = Dataset.idToProductInfoMap.get(newNamesToOldNames[IDItem2]);
		if(Item1.getLevel()>Item2.getLevel()) {
			ProductInfo parent = Item1.getParent();
			while(parent.getData()!=-1) {
				if(parent.getData()==Item1.getData()) {
					return true;
				}
				parent=parent.getParent();
			}
			return false;
		}else {
			if(Item1.getLevel()<Item2.getLevel()) {
				ProductInfo parent = Item2.getParent();
				while(parent.getData()!=-1) {
					if(parent.getData()==Item2.getData()) {
						return true;
					}
					parent=parent.getParent();
				}
				return false;
			}else {
				return false;
			}
		}
	}
}
