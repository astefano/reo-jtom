package reospec;

import reospec.stream.types.*;
import reospec.connector.types.*;
import tom.library.sl.VisitFailure;

import java.lang.reflect.Array;
import java.util.*;
import java.util.*;

import reospec.*;

public class TestExample extends TestConnector{
%include { sl.tom }
%include{connector/Connector.tom}
%include {util/ArrayList.tom}

/* 
** TESTS
*/
public static void printAlternator() {
	StreamId sa, sb, sc;
	sa = `sId("sa"); sb = `sId("sb"); sc = `sId("sc");
	Connector ab, ac, bc, alternator, a2;
	ab = `channel(syncDrain(), source(node("a", sa)), source(node("b", sb)));
	ac = `channel(fifo(), source(node("a", sa)), sink(node("c", sc)));
	bc = `channel(sync(), source(node("b", sb)), sink(node("c", sc)));
	//alternator = replicate(ab, merge(ac,bc));
	alternator = getAlternator(`connectorList(ac, bc, ab));
	if(alternator != null) { System.out.println("printAlternator: pretty(alternator) = \n " + pretty(alternator) + "\n\n\n"); }
	a2 = getAlternator(`connectorList(ab, bc, ac));
	if(a2 != null) { System.out.println("printAlternator: pretty(a2) = \n " + pretty(a2) + "\n\n\n"); }		 		 
	ConnectorList a3 = fixpoint(`connectorList(ab, bc, ac));
	if(a3 != null) { System.out.println("printAlternator: pretty(a3) = \n " + pretty(a3) + "\n\n\n"); }		 		 
}

public static void printExclusiveRouter(){
/* Exclusive Router */
	StreamId sa, sb, sc, sd, se, sf, sg;
	sa = `sId("sa"); sb = `sId("sb"); sc = `sId("sc");
	sd = `sId("sd"); se = `sId("se"); sf = `sId("sf"); sg = `sId("sg");
	//channels for exclusive router
	Connector ag, gd, gf, ge, df, ef, db, ec, excR;
	ag = `channel(sync(), source(node("a", sa)), sink(node("g", sg)));
	gd = `channel(lossySync(), source(node("g", sg)), sink(node("d", sd)));	
	gf = `channel(syncDrain(), source(node("g", sg)), source(node("f", sf)));
	ge = `channel(lossySync(), source(node("g", sg)), sink(node("e", se)));
	df = `channel(sync(), source(node("d", sd)), sink(node("f", sf)));
	ef = `channel(sync(), source(node("e", se)), sink(node("f", sf)));
	db = `channel(sync(), source(node("d", sd)), sink(node("b", sb)));
	ec = `channel(sync(), source(node("e", se)), sink(node("c", sc)));	
	//excR = seq(ag, replicate(gf, replicate(seq(gd, replicate(df, db))), seq(ge, replicate(ef, ec))));
	excR = getExclusiveRouter(`connectorList(ag, connectorList(gd, gf, ge), connectorList(df, db), connectorList(ef, ec)));
	if(excR != null) { System.out.println("printExclusiveRouter: pretty(excR) = " + pretty(excR) + "\n\n\n"); }
}	

public static void testingRefAlternatorF() {
	StreamId sa, sb, sc;
	sa = `sId("sa"); sb = `sId("sb"); sc = `sId("sc");
	Connector ab, ac, bc, alternator, alternatorF;
	ab = `channel(syncDrain(), source(node("a", sa)), source(node("b", sb)));
	ac = `channel(fifo(), source(node("a", sa)), sink(node("c", sc)));
	bc = `channel(sync(), source(node("b", sb)), sink(node("c", sc)));
	//alternator = replicate(ab, merge(ac, bc));
	alternator = getAlternator(`connectorList(ac, bc, ab));
	if(alternator != null) {
		System.out.println("testingRefAlternatorF: pretty(alternator) = \n " + pretty(alternator));
		//For alternatorFaulty (switch names for fifo and sync)
		Connector bcF = `channel(fifo(), source(node("b", sb)), sink(node("c", sc)));
		Connector acF = `channel(sync(), source(node("a", sa)), sink(node("c", sc)));
		//alternatorF = replicate(ab, merge(acF, bcF));
		alternatorF = getAlternator(`connectorList(acF, bcF, ab));
		System.out.println("testingRefAlternatorF: pretty(alternatorF) = \n " + pretty(alternatorF));
		Pred resRef = isRefinement(alternatorF, alternator);
		System.out.println("testingRefAlternatorF: pretty(resRef) = \n" + pretty(resRef) + "\n\n\n");
		// TestCASE
		generateTestCases(alternatorF, alternator);		
	} else { System.out.println("testingRefAlternatorF: alternator is null " + "\n\n\n" ); }	
}

public static void testFctCSpec() {
	StreamId sa, sc;
	sa = `sId("sa"); sc = `sId("sc");
    	Connector c = `channel(fifo(), source(node("a", sa)), sink(node("c", sc)));
	CSpec spec = `getSpecBC(c);	
	System.out.println("testFctCSpec: getSpecBC(c) = " + spec);
	spec = evalConstraints(spec);
	System.out.println("testFctCSpec: evaluated = " + spec + " and getPre = " + getPre(spec) + "\n\n\n");
}

public static void testHidden() {
	StreamId sa, sf, sg;
	sa = `sId("sa"); sf = `sId("sf"); sg = `sId("sg");
	Connector ag, gf;
	ag = `channel(sync(), source(node("a", sa)), sink(node("g", sg)));
	gf = `channel(syncDrain(), source(node("g", sg)), source(node("f", sf)));
	System.out.println("testHidden: hidden(g) = " + hidden("sink", "g", normalise(`connectorList(ag, gf))));
	System.out.println("testHidden: hidden(a) = " + hidden("source	", "a", normalise(`connectorList(ag, gf))) + "\n\n\n");
}

public static void testSeq() {
	StreamId sa, sb, sc;
	sa = `sId("sa"); sb = `sId("sb"); sc = `sId("sc");
	Connector ab, ca;  	
	ab = `channel(syncDrain(), source(node("a", sa)), source(node("b", sb)));
	ca = `channel(sync(), source(node("c", sc)), sink(node("a", sa)));
	Connector syncDrainSync = seq(ca, ab);
	System.out.println("testSeq: pretty(Seq(ca, ab)) = " + pretty(syncDrainSync));
}

public static void testConnectorExecution() {
	StreamId sa, sb, sc;
	sa = `sId("sa"); sb = `sId("sb"); sc = `sId("sc");
	Connector ab, ac, bc, alternator;
	ab = `channel(syncDrain(), source(node("a", sa)), source(node("b", sb)));
	ac = `channel(fifo(), source(node("a", sa)), sink(node("c", sc)));
	bc = `channel(sync(), source(node("b", sb)), sink(node("c", sc)));
	alternator = getAlternator(`connectorList(ac, bc, ab));

	ArrayList<String> daValues = new ArrayList<String>();
	ArrayList<Integer> taValues = new ArrayList<Integer>();
	ArrayList<Integer> tbValues = new ArrayList<Integer>();
	ArrayList<String> dbValues = new ArrayList<String>();
	Map<String, ArrayList> env = new HashMap<String, ArrayList>();
	Map<String, ArrayList> env1 = new HashMap<String, ArrayList>();

	if(alternator != null) { 
		System.out.println("testConnectorExecution: pretty(alternator) = \n " + pretty(alternator));  		 	
		/*
		** Executing Alternator:
			First instantiate time and data with values
		*/			
		for (int i = 0; i < 4; i++)
			daValues.add("da" + i);
		for (int i = 0; i < 4; i++)
			{ taValues.add((Integer)((i+1)*10)); tbValues.add((Integer)((i+1)*10)); }  
		for (int i = 0; i < 4; i++)
			dbValues.add("db" + i);

		env.put("da", daValues); env.put("ta", taValues);
		env.put("db", dbValues); env.put("tb", tbValues);

		// this adds for each time sequence t a new sequence between2(t)
		env1 = addBetween(env);
		//printEnv(env1);
		CSpec spec = getSpec(alternator);
		CSpec evalSpecRes = evalSpec(env1, spec);
		System.out.println("testConnectorExecution: evalSpec(env1, spec) = \n" + pretty(evalSpecRes));
		printEnv(env1);	
	} //end if alternator != null
	else { System.out.println("testConnectorExecution: alternator is null " + "\n\n\n"); }		
	
	//another execution, of the channel ac
	daValues.clear();
	taValues.clear();
	env.clear();
	env1.clear();
	for (int i = 0; i < 4; i++)
	{	daValues.add("da" + i); taValues.add((Integer)(3*i)); }
	env.put("da", daValues);
	env.put("ta", taValues);	
	env1 = addBetween(env);
	printEnv(env1);
	CSpec spec2 = evalConstraints((getSpec(getNormalised(ac))));
	Pred pre = getPre(spec2);
	System.out.println("testConnectorExecution: pre = " + pre + "\n evalPred(env1, pre) = " + pretty(evalPred(env1, pre)));
	CSpec evalSpecRes2 = evalSpec(env1, spec2);
	System.out.println("testConnectorExecution: spec2 = " + spec2 + "\n evalSpec(env1, spec2) = " + pretty(evalSpecRes2));
}

public static void testRefinementABC() {
	StreamId sa, sb, sc, sb1, sb2, sc2, sd, se, sf, sg, sh;
	sa = `sId("sa"); sb = `sId("sb"); sb2 = `sId("sb2");
	sc = `sId("sc"); sd = `sId("sd"); se = `sId("se");
	sf = `sId("sf"); sg = `sId("sg"); sh = `sId("sh");

	// pg 17
	Connector ad, db, dc;
	ad = `channel(fifo(), source(node("a", sa)), sink(node("d", sd)));
	db = `channel(sync(), source(node("d", sd)), sink(node("b", sb)));
	dc = `channel(sync(), source(node("d", sd)), sink(node("c", sc)));
	ConnectorList lc = `connectorList(ad, db, dc);

	Connector ad1, de, df, eb, fc; 
	ad1 = `channel(sync(), source(node("a", sa)), sink(node("d", sd)));
	de = `channel(sync(), source(node("d", sd)), sink(node("e", se)));
	df = `channel(sync(), source(node("d", sd)), sink(node("f", sf)));
	eb = `channel(fifo(), source(node("e", se)), sink(node("b", sb)));
	fc = `channel(fifo(), source(node("f", sf)), sink(node("c", sc)));
	ConnectorList la = `connectorList(ad1, de, df, eb, fc);
	ConnectorList la2 = `connectorList(ad1, connectorList(de, eb), connectorList(df, fc));

	Connector eg, fh, gb, hc, gh;  
	eg = `channel(fifo(), source(node("e", se)), sink(node("g", sg)));
	fh = `channel(fifo(), source(node("f", sf)), sink(node("h", sh)));
	gb = `channel(sync(), source(node("g", sg)), sink(node("b", sb)));
	hc = `channel(sync(), source(node("h", sh)), sink(node("c", sc)));
	gh = `channel(syncDrain(), source(node("g", sg)), source(node("h", sh)));

	Connector ABCb = seq(ad, replicate(seq(seq(de, eg), replicate(gb, gh)), seq(seq(df, fh), replicate(hc, gh))));
	if (ABCb != null)
		System.out.println("testRefinementABC: pretty(ABCb) = " + pretty(ABCb) + "\n");
	else 
		System.out.println("testRefinementABC: pretty(ABCb) is null \n");
			
	Connector ABCa = seq(ad, replicate(seq(de, eb), seq(df, fc)));
	if (ABCa != null)
		System.out.println("testRefinementABC: pretty(ABCa) = " + pretty(ABCa) + "\n");
	else 
		System.out.println("testRefinementABC: pretty(ABCa) is null \n");

	Connector ABCc = seq(ad, replicate(db, dc));
	if(ABCc != null)
		System.out.println("testRefinementABC: pretty(ABCc) = " + pretty(ABCc) + "\n");
	else 
		System.out.println("testRefinementABC: ABCc is null \n");	

	/* Refinement Test */	
	if(ABCa != null)
	{ 		
		if (ABCc != null)
			System.out.println("testRefinementABC: connector ABCa = \n"
								+ pretty(ABCa) 
								+ "\n and connector ABCc = \n"
								+ pretty(ABCc)
								+ " is: \n"
								+ pretty(isRefinement(ABCa, ABCc)));
		else System.out.println("testRefinementABC: ABCc is null \n");
		}
	else System.out.println("testRefinementABC: ABCa is null \n");			
}

public static void testLogic() {
	StreamId sa; 
	sa = `sId("sa"); 
	Pred p = `and(False(), D(sa));
	System.out.println("p = " + p);
}

public static void testConnectorRules() {
	Connector ab, bc;
	StreamId sa, sb, sc;
	sa = `sId("sa");  sb = `sId("sb");   sc = `sId("sc");   
	ab = `channel(sync(), source(node("a", sa)), sink(node("b", sb)));
	bc = `channel(sync(), source(node("b", sb)), sink(node("c", sc)));
	System.out.println("ab = " + pretty(ab) + " spec(ab) = " + pretty(getSpec(ab)));
  	System.out.println("seq for ab and bc = " + pretty(seq(ab, bc)));
}

public static void testFixpoint() {
	StreamId sa, sb, sc, sb1, sb2, sc2, sd, se, sf, sg, sh;
	sa = `sId("sa"); sb = `sId("sb"); sb2 = `sId("sb2");
	sc = `sId("sc"); sd = `sId("sd"); se = `sId("se");
	sf = `sId("sf"); sg = `sId("sg"); sh = `sId("sh");

	// pg 17
	Connector ad, db, dc;
	ad = `channel(fifo(), source(node("a", sa)), sink(node("d", sd)));
	db = `channel(sync(), source(node("d", sd)), sink(node("b", sb)));
	dc = `channel(sync(), source(node("d", sd)), sink(node("c", sc)));
	ConnectorList lc = `connectorList(ad, db, dc);
//	ConnectorList result = fixpoint(lc);
//	if(result != null) { System.out.println("testFixpoint: pretty(result) = \n " + pretty(result) + "\n\n\n"); }		 	

	Connector ad1, de, df, eb, fc; 
	ad1 = `channel(sync(), source(node("a", sa)), sink(node("d", sd)));
	de = `channel(sync(), source(node("d", sd)), sink(node("e", se)));
	df = `channel(sync(), source(node("d", sd)), sink(node("f", sf)));
	eb = `channel(fifo(), source(node("e", se)), sink(node("b", sb)));
	fc = `channel(fifo(), source(node("f", sf)), sink(node("c", sc)));
	ConnectorList la = `connectorList(ad1, de, df, eb, fc);
	ConnectorList la2 = `connectorList(ad1, connectorList(de, eb), connectorList(df, fc));
	//ConnectorList result = fixpoint(la);
	//if(result != null) { System.out.println("testFixpoint: pretty(result) = \n " + pretty(result) + "\n\n\n"); }		 	

	Connector eg, fh, gb, hc, gh;  
	eg = `channel(fifo(), source(node("e", se)), sink(node("g", sg)));
	fh = `channel(fifo(), source(node("f", sf)), sink(node("h", sh)));
	gb = `channel(sync(), source(node("g", sg)), sink(node("b", sb)));
	hc = `channel(sync(), source(node("h", sh)), sink(node("c", sc)));
	gh = `channel(syncDrain(), source(node("g", sg)), source(node("h", sh)));
	ConnectorList lb = `connectorList(ad1, de, df, eg, fh, gh, gb, hc);
	//ConnectorList result = fixpoint(lb);
	//if(result != null) { System.out.println("testFixpoint: pretty(result) = \n " + pretty(result) + "\n\n\n"); }		 	

	Connector mn, nm, np;
	StreamId sm, sn, sp;
	sm = `sId("sm");  sn = `sId("sn");   sp = `sId("sp");   
	mn = `channel(fifo(), source(node("m", sm)), sink(node("n", sn)));
	nm = `channel(sync(), source(node("n", sn)), sink(node("m", sm)));
	np = `channel(sync(), source(node("n", sn)), sink(node("p", sp)));	
	ConnectorList feedbackLoop = `connectorList(mn, nm, np);
//	ConnectorList result = fixpoint(feedbackLoop);
//	if(result != null) { System.out.println("testFixpoint: pretty(result) = \n " + pretty(result) + "\n\n\n"); }	

/*
	Connector c1, c2, c3;
	StreamId s1, s2, s3, s4;
	s1 = `sId("sa");  s2 = `sId("sb");   s3 = `sId("sc");   s4 = `sId("sd");
	c1 = `channel(sync(), source(node("a", s1)), sink(node("d", s4)));
	c2 = `channel(sync(), source(node("d", s4)), sink(node("b", s2)));
	c3 = `channel(sync(), source(node("d", s4)), sink(node("c", s3)));
	ConnectorList takeCueReg = `connectorList(c1, c2, c3);
	ConnectorList result = fixpoint(takeCueReg);
	if(result != null) { System.out.println("testFixpoint: pretty(result) = \n " + pretty(result) + "\n\n\n"); }	
*/		 	

/*
	Connector c1, c2, c3;
	StreamId s1, s2, s3, s4;
	s1 = `sId("sa");  s2 = `sId("sb");   s3 = `sId("sc");   s4 = `sId("sd");
	c1 = `channel(sync(), source(node("a", s1)), sink(node("d", s4)));
	c2 = `channel(sync(), source(node("d", s4)), sink(node("b", s2)));
	c3 = `channel(syncDrain(), source(node("d", s4)), source(node("c", s3)));
	ConnectorList writeCueReg = `connectorList(c1, c2, c3);
	ConnectorList result = fixpoint(writeCueReg);
	if(result != null) { System.out.println("testFixpoint: pretty(result) = \n " + pretty(result) + "\n\n\n"); }	
*/

	Connector c1, c2, c3, c4, c5;
	StreamId s1, s2, s3, s4, s5, s6;
	s1 = `sId("sa");  s2 = `sId("sb");   s3 = `sId("sc");   s4 = `sId("sd");   s5 = `sId("se");   s6 = `sId("sf");
	c1 = `channel(sync(), source(node("a", s1)), sink(node("e", s5)));
	c2 = `channel(sync(), source(node("e", s5)), sink(node("b", s2)));
	c3 = `channel(sync(), source(node("c", s3)), sink(node("f", s6)));
	c4 = `channel(sync(), source(node("f", s6)), sink(node("d", s4)));
	c5 = `channel(syncDrain(), source(node("e", s5)), source(node("f", s6)));
	ConnectorList barrier = `connectorList(c1, c2, c5, c3, c4);
	ConnectorList result = fixpoint(barrier);
	if(result != null) { System.out.println("testFixpoint: pretty(result) = \n " + pretty(result) + "\n\n\n"); }	

}
public static void main(String[] args) {
	initDebugFlags();
	//testFixpoint();
	printAlternator();
	//testingRefAlternatorF();
	//printExclusiveRouter();
	//testFctCSpec();	
	//testHidden();	
	//testSeq();
	//testConnectorExecution();
	//testRefinementABC();
	//testLogic();
	//testConnectorRules(); 
}

}
