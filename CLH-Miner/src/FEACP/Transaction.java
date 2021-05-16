package miners.algorithms.frequentpatterns.efim;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/* This file is copyright (c) 2008-2015 Philippe Fournier-Viger
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
 * This class represents a transaction
 * 
 * @author Philippe Fournier-Viger
 */
public class Transaction {

	int index;
	/** a buffer to store items of an itemset */
	public static int[] tempItems = new int[2000];
	/** a buffer to store utilities of an itemset */
	public static int[] tempUtilities = new int[2000];

	/** an offset pointer, used by projected transactions */
	int offset;

	/** an array of items representing the transaction */
	int[] items;
	/** an array of utilities associated to items of the transaction */
	int[] utilities;

	/** the transaction utility of the transaction or projected transaction */
	int transactionUtility;

	public List<Integer> parentList = new ArrayList<Integer>();

	
	public void setTransactionUtility(int transactionUtility) {
		this.transactionUtility = transactionUtility;
	}

	/**
	 * the profit of a given prefix in this transaction (initially 0 if a
	 * transaction is not projected)
	 */
	int prefixUtility;

	/**
	 * Constructor of a transaction
	 * 
	 * @param items              the items in the transaction
	 * @param utilities          the utilities of item in this transaction
	 * @param transactionUtility the transaction utility
	 */
	public Transaction(int[] items, int[] utilities, int transactionUtility) {
		this.items = items;
		this.utilities = utilities;
		this.transactionUtility = transactionUtility;
		this.offset = 0;
		this.prefixUtility = 0;
	}

	public int getPrefixUtility() {
		return prefixUtility;
	}

	public void setPrefixUtility(int prefixUtility) {
		this.prefixUtility = prefixUtility;
	}

	public void setListParent(List<Integer> listParent) {
		this.parentList.clear();
		for (Integer integer : listParent) {
			this.parentList.add(integer);
		}
	}

	public Transaction(int index, int[] items, int[] utilities, int transactionUtility) {
		this.index = index;
		this.items = items;
		this.utilities = utilities;
		this.transactionUtility = transactionUtility;
		this.offset = 0;
		this.prefixUtility = 0;
	}

	/**
	 * Constructor for a projected transaction
	 * 
	 * @param transaction the transaction that will be projected (it may be an
	 *                    original transaction or a previously projected transaction
	 * @param offsetE     an offset over the original transaction for projecting the
	 *                    transaction
	 */
	public Transaction(Transaction transaction, int offsetE) {
		// copy items and utilities from the original transaction
		this.items = transaction.getItems();
		this.utilities = transaction.getUtilities();

		// copy the utility of element e
		int utilityE = this.utilities[offsetE];

		// add the utility of item e to the utility of the whole prefix used to project
		// the transaction
		this.prefixUtility = transaction.prefixUtility + utilityE;

		// we will now calculate the remaining utility.
		// It is the transaction utility minus the profit of the element that was
		// removed
		this.transactionUtility = transaction.transactionUtility - utilityE;
		// and we also need to subtract the utility of all items before e
		// but after the previous offset
		for (int i = transaction.offset; i < offsetE; i++) {
			this.transactionUtility -= transaction.utilities[i];
		}
		// remember the offset for this projected transaction
		this.offset = offsetE + 1;
	}

	public Transaction(Transaction transaction) {
		this.index = transaction.index;
		// copy items and utilities from the original transaction
		this.items = transaction.getItems();
		this.utilities = transaction.getUtilities();

		// copy the utility of element e
		// int utilityE = this.utilities[offsetE];

		// add the utility of item e to the utility of the whole prefix used to project
		// the transaction
		this.prefixUtility = transaction.prefixUtility;

		// we will now calculate the remaining utility.
		// It is the transaction utility minus the profit of the element that was
		// removed
		this.transactionUtility = transaction.transactionUtility;
		// and we also need to subtract the utility of all items before e
		// but after the previous offset
		// System.arraycopy(this.parentList, 0, transaction.parentList, 0,
		// transaction.parentList.size());
		// remember the offset for this projected transaction
	}

	/**
	 * Get a string representation of this transaction
	 */
	public String toString() {
		StringBuilder buffer = new StringBuilder();
		buffer.append("index : " + index + "  ");
		for (int i = offset; i < items.length; i++) {
			buffer.append(items[i]);
			buffer.append("[");
			buffer.append(utilities[i]);
			buffer.append("] ");
		}
		buffer.append(" Remaining Utility:" + transactionUtility);
		buffer.append(" Prefix Utility:" + prefixUtility);
		return buffer.toString();
	}

	/**
	 * Get the array of items in this transaction
	 * 
	 * @return array of items
	 */
	public int[] getItems() {
		return items;
	}

	/**
	 * Get the array of utilities in this transaction
	 * 
	 * @return array of utilities
	 */
	public int[] getUtilities() {
		return utilities;
	}

	/**
	 * get the last position in this transaction
	 * 
	 * @return the last position (the number of items -1 )
	 */
	public int getLastPosition() {
		return items.length - 1;
	}

	/**
	 * This method removes unpromising items from the transaction and at the same
	 * time rename items from old names to new names
	 * 
	 * @param oldNamesToNewNames An array indicating for each old name, the
	 *                           corresponding new name.
	 */
	public void removeUnpromisingItems(int index, int[] oldNamesToNewNames, int[] newNamesToOldNames) {
		// In this method, we used buffers for temporary storing items and their
		// utilities
		// (tempItems and tempUtilities)
		// This is for memory optimization.

		Map<Integer, Element> utilityListParentMap = new HashMap<Integer, Element>();
		// for each item
		int i = 0;
		for (int j = 0; j < items.length; j++) {
			int item = items[j];
			int utility = utilities[j];
			ProductInfo productInfoParent = Dataset.idToProductInfoMap.get(item).getParent();
			while (productInfoParent.getData() != -1) {
				int newNameParent = oldNamesToNewNames[productInfoParent.getData()];
				if (newNameParent != 0) {
					Element elementParent = utilityListParentMap.get(newNameParent);
					if (elementParent == null) {
						Element newElement = new Element(index, utility);
						utilityListParentMap.put(newNameParent, newElement);
					} else {
						Element newElement = new Element(index, elementParent.iutils + utility);
						utilityListParentMap.put(newNameParent, newElement);
					}
				}
				productInfoParent = productInfoParent.getParent();
			}

			// Convert from old name to new name
			int newName = oldNamesToNewNames[item];

			// if the item is promising (it has a new name)
			if (newName != 0) {
				// copy the item and its utility
				tempItems[i] = newName;
				tempUtilities[i] = utilities[j];
				i++;
			} else {
				// else subtract the utility of the item
				transactionUtility -= utilities[j];
			}
		}

		// copy the buffer of items back into the original array
		this.items = new int[i];
		System.arraycopy(tempItems, 0, this.items, 0, i);

		// copy the buffer of utilities back into the original array
		this.utilities = new int[i];
		System.arraycopy(tempUtilities, 0, this.utilities, 0, i);

		// Sort by increasing TWU values
		insertionSort(this.items, this.utilities);

		int sumSU = 0;

		// For each item when reading the transaction backward
		for (int n = this.getItems().length - 1; n >= 0; n--) {
			// get the item
			Integer item = this.getItems()[n];

			// we add the utility of the current item to its sub-tree utility
			sumSU += this.getUtilities()[n];
			// we add the current sub-tree utility to the utility-bin of the item
			Element newElement = new Element(this.getIndex(), this.getUtilities()[n], sumSU);
			// iMEFIM.mapItemToUtilityList.get(item).addElement(newElement);
			iMEFIM.mapItemToUtilityList.get(item).addElement(newElement);
		}

		for (Integer ItemParent : utilityListParentMap.keySet()) {
			int SumRemain = 0;
			for (int k = 0; k < items.length; k++) {
				Boolean isBigThan = ItemParent < items[k];
				Boolean isParent = checkisParent(newNamesToOldNames[items[k]], newNamesToOldNames[ItemParent]);
				if (isBigThan && !isParent) {
					SumRemain += utilities[k];
				}
			}
			Element newElement = new Element(index, utilityListParentMap.get(ItemParent).iutils, SumRemain);
			// utilityListParentMap.put(ItemParent, newElement);
			UtilityList ULs = iMEFIM.mapItemToUtilityList.get(ItemParent);
			ULs.addElement(newElement);
			this.parentList.add(ItemParent);
		}
		Collections.sort(this.parentList);

	}

	public Boolean checkisParent(int IDItem1, int IDItem2) {
		ProductInfo Item1 = Dataset.idToProductInfoMap.get(IDItem1);
		ProductInfo Item2 = Dataset.idToProductInfoMap.get(IDItem2);
		if (Item1.getLevel() > Item2.getLevel()) {
			ProductInfo parent = Item1.getParent();
			while (parent.getData() != -1) {
				if (parent.getData() == Item2.getData()) {
					return true;
				}
				parent = parent.getParent();
			}
			return false;
		} else {
			if (Item1.getLevel() < Item2.getLevel()) {
				ProductInfo parent = Item2.getParent();
				while (parent.getData() != -1) {
					if (parent.getData() == Item1.getData()) {
						return true;
					}
					parent = parent.getParent();
				}
				return false;
			} else {
				return false;
			}
		}
	}

	/**
	 * Implementation of Insertion sort for integers. This has an average
	 * performance of O(n log n)
	 * 
	 * @param items array of integers
	 */
	public static void insertionSort(int[] items, int[] utitilies) {
		for (int j = 1; j < items.length; j++) {
			int itemJ = items[j];
			int utilityJ = utitilies[j];
			int i = j - 1;
			for (; i >= 0 && (items[i] > itemJ); i--) {
				items[i + 1] = items[i];
				utitilies[i + 1] = utitilies[i];
			}
			items[i + 1] = itemJ;
			utitilies[i + 1] = utilityJ;
		}
	}

	public long getUtility() {
		return transactionUtility;
	}

	public int getIndex() {
		return index;
	}
}
