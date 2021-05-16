package miners.algorithms.frequentpatterns.efim;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
/* This file is copyright (c) 2012-2015 Souleymane Zida, Philippe Fournier-Viger, Alan Souza
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
 * This is the parser class for the dataset.
 * It has actions related to parse a txt based file to a Dataset class.
 *
 * @see AlgoEFIM
 */
public class Dataset {

	/** the list of transactions in this dataset */
	List<Transaction> transactions;
	long totalUtility;
	
	/** the largest item name */
	private int maxItem = 0;

	public static ProductInfo root;
	
	
	
	public static Map<Integer,ProductInfo> idToProductInfoMap = new HashMap<Integer, ProductInfo>();
	
	
	
	
	/**
	 * Constructor
	 * @param datasetPath the path of the file containing the dataset
	 * @param maximumTransactionCount the number of transaction to be read from the input file
	 * @throws IOException exception if error reading the file
	 */
	public Dataset(String datasetPath,String productClassPath,String productPath, int maximumTransactionCount) throws IOException {

    	root = new ProductInfo();
    	
    	//idToProductInfoMap.put(-1,root);
    	
		Map<String, Integer> parentToKeyMap = new HashMap<String, Integer>();
		// convert string name class to key
		
		Map<Integer,ProductInfo> keyToObjectMap = new HashMap<Integer, ProductInfo>();
		
		//convert key to object productinfo
		
		Map<Integer,ProductInfo> keyClassProductToItem = new HashMap<Integer,ProductInfo>();
		// convert IDclassProduct to Object ProductItem
		

		BufferedReader reader = null;
		String line = "";
		reader = new BufferedReader(new FileReader(productClassPath));
		reader.readLine();
		int i =1;
		while((line = reader.readLine()) != null) {
			String[] fields = line.split(",");
			
			if(fields.length>0) {
				String product_family = fields[4];
				Integer  keyOfItemProductFamily = parentToKeyMap.get(product_family);
				if(keyOfItemProductFamily==null) {
					parentToKeyMap.put(product_family, i);
					ProductInfo itemProductFamilyGeted = new ProductInfo(i);
					root.addChildren(itemProductFamilyGeted);
					keyToObjectMap.put(i, itemProductFamilyGeted);
					i++;
					
					
				}
				
				
				
				String product_department = fields[3];
				Integer keyOfItemProductDepartment = parentToKeyMap.get(product_department);
				if(keyOfItemProductDepartment==null) {
					parentToKeyMap.put(product_department, i);
					ProductInfo itemProductDepartmentGeted = new ProductInfo(i);
					keyToObjectMap.get(parentToKeyMap.get(product_family)).addChildren(itemProductDepartmentGeted);
					keyToObjectMap.put(i, itemProductDepartmentGeted);
					i++;
					
				}
				
				
				
				String product_category = fields[2];
				Integer keyOfItemProductCategory = parentToKeyMap.get(product_category);
				if(keyOfItemProductCategory==null) {
					parentToKeyMap.put(product_category, i);
					ProductInfo itemProductCategoryGeted = new ProductInfo(i);
					keyToObjectMap.get(parentToKeyMap.get(product_department)).addChildren(itemProductCategoryGeted);
					keyToObjectMap.put(i, itemProductCategoryGeted);
					i++;
					
				}
				
				
		
				String product_subcategory = fields[1];
				Integer keyOfItemProductSubcategory = parentToKeyMap.get(product_subcategory);
				if(keyOfItemProductSubcategory==null) {
					parentToKeyMap.put(product_subcategory, i);
					ProductInfo itemProductSubcategoryGeted = new ProductInfo(i);
					keyToObjectMap.get(parentToKeyMap.get(product_category)).addChildren(itemProductSubcategoryGeted);
					keyToObjectMap.put(i, itemProductSubcategoryGeted);
					i++;
					
				}
				
				int product_class_id = Integer.parseInt(fields[0]);
				keyClassProductToItem.put(product_class_id, keyToObjectMap.get(parentToKeyMap.get(product_subcategory)));
			}
		}

		reader = new BufferedReader(new FileReader(productPath));
		reader.readLine();
		int countItem = 0;
		while((line = reader.readLine()) != null) {
			countItem++;
			String[] fields = line.split(",");
			if(fields.length>0) {
				int productClassId = Integer.parseInt(fields[0]);
				int productID = Integer.parseInt(fields[1]);
				
				ProductInfo itemProductID = new ProductInfo(productID);
				keyClassProductToItem.get(productClassId).addChildren(itemProductID);
				idToProductInfoMap.put(productID, itemProductID);
				
			}
			
			
		}
		
		int n = countItem;
		keyToObjectMap.forEach((k,v)->{
			int newID = n+v.getData();
			idToProductInfoMap.put(newID, v);
			v.setData(newID);
			if(newID>maxItem) {
				maxItem=newID;
			}
		});
		
		
		
		
		for(Integer item: idToProductInfoMap.keySet()){		
				// create an empty Utieylity List that we will fill later.
				
				// add the item to the list of high TWU items
				//add map level
				
				int currentLevel = 1; 
				ProductInfo parent = idToProductInfoMap.get(item).getParent();
				while(parent.getData()!=-1) {
					currentLevel++;
					parent = parent.getParent();
				}
				idToProductInfoMap.get(item).setLevel(currentLevel);
				
		}
    	
    	// Initialize a list to store transactions in memory
        transactions = new ArrayList<Transaction>();
        totalUtility = 0;
        // Create a buffered reader to read the input file
        
         reader = new BufferedReader(new FileReader(datasetPath));
        
        line = "";
        i=0;
        int index =0;
        // iterate over the lines to build the transaction
        while((line = reader.readLine()) != null) { 
			// if the line is  a comment, is  empty or is  metadata
			if (line.isEmpty() == true || line.charAt(0) == '#' 
					|| line.charAt(0) == '%' || line.charAt(0) == '@') {
				continue;
			}
			
			i++;
			Transaction t = createTransaction(index,line);
			index++;
			totalUtility += t.getUtility();
			// read the transaction
			transactions.add(t);
			
			// if the number of transaction to be read is reached, we stop
        	if(i==maximumTransactionCount) {
        		break;
        	}
			
        }
        //****** Show the number of transactions in this dataset**************************//
        System.out.println("Transaction count :" +  transactions.size());
        reader.close();
    
    }

    /**
     * Create a transaction object from a line from the input file
     * @param line a line from input file
     * @return a transaction
     */
    private Transaction createTransaction(int index,String line) {
    	// split the line into tokens according to the ":" separator
    	String[] split = line.split(":");
    	
    	// Get the transaction utility
    	int transactionUtility = Integer.parseInt(split[1]);
    	
    	// Get the list of items 
        String[] itemsString = split[0].split(" ");
    	
        // Get the list of item utilities
        String[] itemsUtilitiesString = split[2].split(" ");
    	
        //Create array to store the items and their utilities
        int[] items = new  int[itemsString.length];
        int[] utilities = new  int[itemsString.length];

        // for each item
        for (int i = 0; i < items.length; i++) {
        	//store the item
        	items[i] = Integer.parseInt(itemsString[i]);
        	
        	// store its utility in that transaction
        	utilities[i] = Integer.parseInt(itemsUtilitiesString[i]);
            
            // if the item name is larger than the largest item read from the database until now, we remember
        	// its name
        }

		// create the transaction object for this transaction and return it
		return new Transaction(index,items, utilities, transactionUtility);
    }

    /**
     * Get the list of transactions in this database
     * @return the list of transactions
     */
    public List<Transaction> getTransactions() {
        return transactions;
    }


    /**
     * Get the largest item  in this database.
     * @return the largest item
     */
    public int getMaxItem() {
        return maxItem;
    }

   /**
    * Get a string representation of this database
    * @return a string
    */
    public String toString() {
    	// Create a stringbuilder for storing the string
        StringBuilder datasetContent = new StringBuilder();

        // We will append each transaction to this string builder
        for(Transaction transaction : transactions) {
            datasetContent.append(transaction.toString());
            datasetContent.append("\n");
        }
        // Return the string
        return datasetContent.toString();
    }

    public long getTotalUtility()
    {
    	return totalUtility;
    }
    
    public static List<Integer> getAllChildNewName(int[] oldNamesToNewName,int[] newNameToOldName,int i){
    	List<Integer> listChild = new ArrayList<Integer>() ;
    	ProductInfo Node = idToProductInfoMap.get(newNameToOldName[i]);
    	Queue<ProductInfo> queue = new LinkedList<>();
    	queue.add(Node);
    	while(queue.size()!=0) {
    		ProductInfo child = queue.poll();
    		if(oldNamesToNewName[child.getData()]!=0) {
    			listChild.add(oldNamesToNewName[child.getData()]);
    			for (ProductInfo productInfo : child.getChildren()) {
        			queue.add(productInfo);
    			}
    		}
    		
    	}
    	Collections.sort(listChild);
    	return listChild;
    }
    public static List<Integer> getAllChildNewNameWithOutIt(int[] oldNamesToNewName,int[] newNameToOldName,int i){
    	List<Integer> listChild = new ArrayList<Integer>() ;
    	ProductInfo Node = idToProductInfoMap.get(newNameToOldName[i]);
    	Queue<ProductInfo> queue = new LinkedList<>();
    	queue.add(Node);
    	while(queue.size()!=0) {
    		ProductInfo child = queue.poll();
    		if(oldNamesToNewName[child.getData()]!=0) {
    			listChild.add(oldNamesToNewName[child.getData()]);
    			for (ProductInfo productInfo : child.getChildren()) {
        			queue.add(productInfo);
    			}
    		}
    		
    	}
    	listChild.remove(0);
    	Collections.sort(listChild);
    	return listChild;
    }


}
