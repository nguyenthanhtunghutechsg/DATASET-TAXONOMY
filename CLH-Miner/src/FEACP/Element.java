package miners.algorithms.frequentpatterns.efim;

public class Element {
	/** transaction id */
	public int tid ;   
	/** itemset utility */
	public int iutils;   
	/** remaining utility */
	public int rutils; 
	
	
	
	public Element(Element ele) {
		this.tid = ele.tid;
		this.iutils = ele.iutils;
		this.rutils = ele.rutils;
	}
	/**
	 * Constructor.
	 * @param tid  the transaction id
	 * @param iutils  the itemset utility
	 * @param rutils  the remaining utility
	 */
	public Element(int tid, int iutils, int rutils){
		this.tid = tid;
		this.iutils = iutils;
		this.rutils = rutils;
	}
	public Element(int tid){
		this.tid = tid;
		this.iutils = 0;
		this.rutils = 0;
	}
	public Element(int tid,int iutils){
		this.tid = tid;
		this.iutils = iutils;
		this.rutils = 0;
	}
}
