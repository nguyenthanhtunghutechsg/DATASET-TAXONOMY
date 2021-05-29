package FEAMP;

import java.io.IOException;

import FEAMP2.AlgoEFIM;

public class Main {

	public static void main(String[] args) throws IOException {

//		String TaxonomyPath = "connectTaxonomy.txt";
//		String inputPath = "connect.txt";
		String TaxonomyPath = "liquorTaxonomy.txt";
		String inputPath = "liquor_5.txt";
		AlgoEFIM cl = new AlgoEFIM();
		// CLH_MinerTestP cl = new CLH_MinerTestP();
		// pCLH_Miner cl = new pCLH_Miner();
		cl.runAlgorithm((int)50000 , inputPath, "", TaxonomyPath, Integer.MAX_VALUE);
		cl.printStats();

//2088282/2150177
	}
}
