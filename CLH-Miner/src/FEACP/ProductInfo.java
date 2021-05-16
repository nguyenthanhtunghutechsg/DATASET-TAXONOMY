package miners.algorithms.frequentpatterns.efim;

import java.util.ArrayList;
import java.util.List;

public class ProductInfo {
	
	private int data ;
	
	private List<ProductInfo> children = new ArrayList<>();
	
	private ProductInfo parent = null;
	
	private int level;

	public ProductInfo() {
		this.data = -1 ;
	}
	
	
	public int getData() {
		return data;
	}

	public void setData(int data) {
		this.data = data;
	}

	public ProductInfo getParent() {
		return parent;
	}

	public void setParent(ProductInfo parent) {
		this.parent = parent;
	}
	public ProductInfo(int data) {
		this.data = data;
	}
	
	public ProductInfo addChildren(ProductInfo child){
		child.setParent(this);
		this.children.add(child);
		return child;
	}
	
	public void addChildren(List<ProductInfo> children) {
		children.forEach(each->each.setParent(this));
		this.children.addAll(children);
	}
	public List<ProductInfo> getChildren(){
		return children;
	}
	
	public int getLevel() {
		return level;
	}

	public void setLevel(int level) {
		this.level = level;
	}
}
