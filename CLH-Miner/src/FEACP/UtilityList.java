package miners.algorithms.frequentpatterns.efim;

import java.util.ArrayList;
import java.util.List;

public class UtilityList {
	 Integer item;  // the item
	 long sumIutils = 0;  // the sum of item utilities
	 long sumRutils = 0;  // the sum of remaining utilities
	 List<Element> elements = new ArrayList<Element>();  // the elements
	 
	/**
	 * Constructor.
	 * @param item the item that is used for this utility list
	 */
	public UtilityList(Integer item){
		this.item = item;
	}
	
	public UtilityList(UtilityList Uls){
		this.item = Uls.item;
		this.sumIutils = Uls.sumIutils;
		this.sumRutils = Uls.sumRutils;
		for (Element element : Uls.getElement()) {
			elements.add(new Element(element));
		}
	}
	
	
	/**
	 * Method to add an element to this utility list and update the sums at the same time.
	 */
	public void addElement(Element element){
		sumIutils += element.iutils;
		sumRutils += element.rutils;
		elements.add(element);
	}
	
	public void RemoveElement(Element element){
		
		sumIutils -= element.iutils;
		sumRutils -= element.rutils;
		elements.remove(element);
	}
	
	/**
	 * Get the support of the itemset represented by this utility-list
	 * @return the support as a number of trnsactions
	 */
	public int getSupport() {
		return elements.size();
	}
	
	public List<Element> getElement(){
		return elements;
	}
	
}
