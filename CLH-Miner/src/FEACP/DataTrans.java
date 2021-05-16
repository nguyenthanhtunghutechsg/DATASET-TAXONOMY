package miners.algorithms.frequentpatterns.efim;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class DataTrans {
	public List<Transaction> Transdata = new ArrayList<Transaction>();
	public Map<Integer,UtilityList> ULsData = new HashMap<Integer, UtilityList>();
	
	public DataTrans(List<Transaction> transdata, Map<Integer, UtilityList> uLsData) {
		Transdata = transdata;
		ULsData = uLsData;
	}


	
	
}
