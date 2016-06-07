package reospec;

import reospec.stream.types.*;
import reospec.connector.types.*;
import tom.library.sl.VisitFailure;

import java.lang.reflect.Array;
import java.util.*;
import java.util.*;

public class TestConnector{
//%include{stream/Stream.tom}
%include { sl.tom }
%include{connector/Connector.tom}
%include {util/ArrayList.tom}

static private boolean debugFlagGen, debugFlagStratSimp, debugFlagStratSimpImpl, debugFlagStratSeq, debugFlagStratRep, debugFlagStratMerge, debugFlagStratFlatten;

public static void initDebugFlags(){
	debugFlagGen = false;
	debugFlagStratSimp = false;
	debugFlagStratSimpImpl = false;
	debugFlagStratSeq = true; //false;
	debugFlagStratRep = false; 
	debugFlagStratMerge = false; 
	debugFlagStratFlatten = false;
}

public static Pred isRefinement(Connector c1, Connector c2) {
	Pred p1 = getPre(getSpec(c1));
	Pred q1 = getPost(getSpec(c1));
	Pred p2 = getPre(getSpec(c2));
	Pred q2 = getPost(getSpec(c2));
	System.out.println("isRefinement: pretty(p1 and q2 => q1) = " + pretty(`implic(andL(p1, q2), q1)));
	try{
	Pred res1 = `Repeat(SimpImplication()).visitLight(`implic(p1, p2));
	Pred res2 = `Repeat(SimpImplication()).visitLight(`implic(andL(p1, q2), q1));
	//System.out.println("res2 = " + res2 + " pretty(res2) = " + pretty(res2));

	return `andL(res1, res2);

	} catch(VisitFailure e) { System.out.println("Refinement: strategy failed"); }

return null;
}

// later change this s.t. it returns a test case (that means that i also need to add in gom... the syntax ...)
// for the moment i only print inside the function the results 
public static void generateTestCases(Connector c1, Connector c2) {
	Pred resRef = isRefinement(c1, c2);
	if (resRef != null) {
		try{
			Pred resRefSimp = `Repeat(SimpResRef()).visitLight(getAndL(resRef));
			System.out.println("generateTestCases: pretty(resRef) after simp is: \n " + pretty(resRefSimp));
			Pred resRefUnfold = unfoldResRef(resRefSimp, 0);
			System.out.println("generateTestCases: pretty(resRefUnfold) after simp is: " + pretty(resRefUnfold));
			} catch(VisitFailure e) { System.out.println("generateTestCases: strategy failed"); }
	} else System.out.println("generateTestCases: resRef is null!!");	
}

public static String symbolicUnfoldPred(Pred p, int i){
%match (p) {
  	   merged(comp(dId(da), tId(x)), comp(dId(db), tId(y)), c) -> { 
  	   //we know that y < between(y) < tail(y) so for an even index i dc[i] is da[i] and for an odd index i dc[i] is db[i]
  	   if(`x.equals("between2(" + `y + ")")) {
  		   String sc = stream2String(getFold(`c)) + "[" + i + "]";
  		   String tc = `y + "[" + i + "]";
  		   String dc = "";  	   
  		   if (i % 2 == 0) dc = `db + "[" + i + "]"; else dc = `da + "[" + i + "]";
  		   String scV = sc + " = (" + tc + " : " + dc + ")";  		   	  	     	     	    
  		   	return scV; }   	   
	}
  	   merged(comp(dId(da), tId(x)), comp(dId(db), tId(y)), c) -> { 
  	   //we know that between(x) < tail(x) so for an even index i dc[i] is db[i] and for an odd index i dc[i] is da[i]
  	   if(`y.equals("between2(" + `x + ")")) {
  		   String sc = stream2String(getFold(`c)) + "[" + i + "]";
  		   String tc = `x + "[" + i + "]";
  		   String dc = "";  	   
  		   if (i % 2 == 0) dc = `da + "[" + i + "]"; else dc = `db + "[" + i + "]";
  		   String scV = sc + " = (" + tc + " : " + dc + ")";  		   	  	     	     	    
  		   	return scV; }   	   
	} 
	}
	return "dontknow";
}

public static Pred unfoldResRef(Pred p, int i){ 
%match (p){
  	  implic(p1, p2) -> {
  		  String cv1 = symbolicUnfoldPred(`p1, i);
  		  String cv2 = symbolicUnfoldPred(`p2, i);
  		  String[] cv1Parts, cv2Parts;
  		  String delimiter = ":";
  		  cv1Parts = cv1.split(delimiter);
  		  cv2Parts = cv2.split(delimiter);
  		  if(cv1Parts != null && cv2Parts != null && cv1Parts.length > 1 && cv2Parts.length > 1) {
  			  //System.out.println("unfoldResRef: cv1Parts[0] = " + cv1Parts[0] + "\n");
  			  if(cv1Parts[0].equals(cv2Parts[0]) && !cv1Parts[1].equals(cv2Parts[1])) {  
  				  System.out.println("unfoldResRef: Counterexample: " + cv1 + " and " + cv2 + "\n"); 
  				  return `False(); } } 
  		  else { System.out.println("cv1Parts or cv2Parts is null or they have length < 1!!! Error."); }  		    		  
  	  } } 
  	return p;
}

public static Map<String, ArrayList> addBetween(Map<String, ArrayList> env) {
	Map<String, ArrayList> env1 = new HashMap<String, ArrayList>();
	Random randomGenerator = new Random();
	Integer b1, b2;
	String tempTimeName; 
	
	Set set = env.entrySet();
    Iterator it = set.iterator();

    while(it.hasNext()){
      Map.Entry me = (Map.Entry)it.next();
      env1.put((String)me.getKey(), (ArrayList)me.getValue());
      //System.out.println("addBetween: " + me.getKey() + " : " + me.getValue() );
      String taName = (String)me.getKey();      
      if (taName.charAt(0) == 't') {
    	  tempTimeName = "between2(" + taName + ")";
    	  ArrayList<Integer> taVal = (ArrayList<Integer>)me.getValue();
    	  ArrayList<Integer> tempTimeValue = new ArrayList<Integer>();  
      	  for (int i = 0; i < taVal.size()-1; i++) {
      		  b1 = taVal.get(i);
      		  b2 = taVal.get(i+1);
      		  if(b2 > b1) 
      		  // show error if b2 < b1 (not valid time seq) or just let it to wellFormedTimeSeq??? 
      		  // and here only take care to populate between only if b2 > b1  
      		  tempTimeValue.add(b1 + 1 + randomGenerator.nextInt(b2 - b1));
      	  }
      	  tempTimeValue.add(taVal.get(taVal.size()-1)+1);
      	  //System.out.println("addBetween: tempTimeValue " +  tempTimeValue.get(0));
      	  env1.put(tempTimeName, tempTimeValue);      	  
      } //if  	  
	} // while
	return env1;
}

public static boolean wellFormedTimeSeq(ArrayList<Integer> t) {
	for(int i = 0; i < t.size()-1; i++) { 
		if (t.get(i) > t.get(i+1)) return false;
		}
return true;
}

public static Pred formInstStream(ArrayList<String> dVals, ArrayList<Integer> tVals) {
	String stream = "";
	Iterator it1 = tVals.iterator();
	Iterator it2 = dVals.iterator();
	while(it1.hasNext() && it2.hasNext()) {				
		stream = stream + "(" + it1.next() + " : " + it2.next().toString() + "), "; 
	}
	stream = stream.substring(0, stream.length()-2);
	// what if they're not of equal size? should return false?
	return `valS(stream);
}

public static Pred evalPred(Map<String, ArrayList> env, Pred p) {
	%match (p){
			valS(x) -> {return `valS(x);}
			D(s) -> {
				String d = getDataName(getUnfold(`s));
				String t = getTimeName(getUnfold(`s));
				ArrayList<String> dVals = env.get(d);
				ArrayList<Integer> tVals = env.get(t);
				// return false if tVals is not a well-def time seq
				if(dVals!=null && tVals!=null)
				if (! wellFormedTimeSeq(tVals)) return `False();
				else { return formInstStream(dVals, tVals); }
			}	
			andL(p1*, eqD(dId(d1), dId(d2)), p2*) -> {
				ArrayList<String> d1Vals = env.get((String)`d1);
				ArrayList<String> d2Vals = env.get((String)`d2);
				// if either one of t1Vals is not instantiated in the env then update env
				if(d1Vals == null && d2Vals != null) {
					//System.out.println("evalPred: eqD d1= "+ `d1 + " is null and d2 isn't = " + `d2);
					d1Vals = (ArrayList<String>)d2Vals.clone();
					env.put(`d1, d1Vals);					
				}
				if(d2Vals == null && d1Vals != null) {
					//System.out.println("evalPred: eqD d1= "+ `d1 + " is nonnull and d2 is null = " + `d2);
					d2Vals = (ArrayList<String>)d1Vals.clone();
					env.put(`d2, d2Vals);
				}
				return evalPred(env, `andL(p1*, p2*));
			}					
			andL(p1*, eqT(tId(t1), tId(t2)), p2*) -> {
				ArrayList<Integer> t1Vals = env.get((String)`t1);
				ArrayList<Integer> t2Vals = env.get((String)`t2);
				// only if both t1Vals and t2Vals are instantiated in env then return true of false ... 			
				if(t1Vals != null && t2Vals != null) {
				//System.out.println("evalPred: non-null eqT t1= "+ `t1 + " and t2 = " + `t2);	
				Iterator it1 = t1Vals.iterator();
				Iterator it2 = t2Vals.iterator();
				while(it1.hasNext() && it2.hasNext()) {				
					if(it1.next() != it2.next()) {
						//System.out.println("eval eq for time t1 = " + `t1 + " and t2 " + `t2 + " returns false"); 
						return `False();}
				}
				if(!it1.hasNext() && !it1.hasNext()) return `True(); else return `False(); }
				// if either one of t1Vals is not instantiated in the env then update env
				if(t2Vals == null && t1Vals != null) {
					//System.out.println("evalPred: eqT t1= "+ `t1 + " is null and t2 isn't = " + `t2);
					t2Vals = (ArrayList<Integer>)t1Vals.clone();
					env.put(`t2, t2Vals);
				}
				if(t1Vals == null && t2Vals != null) {
					//System.out.println("evalPred: eqT t1= "+ `t1 + " is nonnull and t2 is null = " + `t2);
					t1Vals = (ArrayList<Integer>)t2Vals.clone();
					env.put(`t1, t1Vals);
				}
				return evalPred(env, `andL(p1*, p2*));

			}
			eqL(t1, t2) -> {
				ArrayList<Integer> t1Vals = env.get((String)`t1);
				ArrayList<Integer> t2Vals = env.get((String)`t2);
				// return true of false ... 			
				Iterator it1 = t1Vals.iterator();
				Iterator it2 = t2Vals.iterator();
				while(it1.hasNext() && it2.hasNext()) {				
					if(it1.next() != it2.next()) {
						//System.out.println("eval eq for time t1 = " + `t1 + " and t2 " + `t2 + " returns false"); 
						return `False();}
				}
				if(!it1.hasNext() && !it1.hasNext()) return `True(); else return `False();
			}
			eqL(t1, t2, t*) -> {
				Pred p1 = evalPred(env, `eqL(t1, t2));
				Pred p2 = evalPred(env, `eqL(t*));
				return `andL(p1, p2); }
			andL(x) -> {return evalPred(env, `x);}
			andL(x, l*) -> { 
				//System.out.println("eval: andL(x, l*) = " + pretty(`x) + pretty(`l*) + "\n\n"); 
				return `andL(evalPred(env, x), evalPred(env, l*)) ;}
			merged(sa, sb, sc) -> {
				String da = getDataName(getUnfold(`sa));
				String ta = getTimeName(getUnfold(`sa));
				String db = getDataName(getUnfold(`sb));
				String tb = getTimeName(getUnfold(`sb));
				//System.out.println("eval: merged da = " + da + " with db =" + db + "\n\n");
				//System.out.println("eval: merged ta = " + ta + " with tb =" + tb + "\n\n");
				ArrayList<String> daValues = env.get(da);
				ArrayList<Integer> taValues = env.get(ta);
				//System.out.println("eval: merged taValues0 = " + taValues.get(0) + "\n\n");
				
				if (taValues != null && daValues != null) {					
					ArrayList<String> dbValues = env.get(db);
					ArrayList<Integer> tbValues = env.get(tb);
					//System.out.println("eval: merged tbValues0 = " + tbValues.get(0) + "\n\n");
					
					if (tbValues != null && dbValues != null) {
						String dc = getDataName(getUnfold(`sc));
						String tc = getTimeName(getUnfold(`sc));
						ArrayList<Integer> taValuesAux = (ArrayList<Integer>)taValues.clone();
						ArrayList<String> daValuesAux = (ArrayList<String>)daValues.clone();
						ArrayList<Integer> tbValuesAux = (ArrayList<Integer>)tbValues.clone();
						ArrayList<String> dbValuesAux = (ArrayList<String>)dbValues.clone(); 	
						
						ArrayList<Integer> tcValues = new ArrayList<Integer>();
						ArrayList<String> dcValues = new ArrayList<String>();
						
						while(!taValues.isEmpty() && !tbValues.isEmpty()) {
						//while(taValues.size() > 0 && tbValues.size() > 0) {
							//System.out.println("eval: merged tbValues0 = " + tbValues.get(0) + "\n\n");
							if ((Integer)taValues.get(0) < (Integer)tbValues.get(0)) { 
								dcValues.add((String)daValues.get(0)); 
								tcValues.add((Integer)taValues.get(0)); 
								daValues.remove(0); 
								taValues.remove(0); }
							else {
									dcValues.add((String)dbValues.get(0)); 
									tcValues.add((Integer)tbValues.get(0)); 
									dbValues.remove(0); 
									tbValues.remove(0);
								}								
						}
						//System.out.println("eval: merged tcValues0 = " + tcValues.get(0) + "\n\n");
						if(taValues.isEmpty()) {
							while(!tbValues.isEmpty()) {
								dcValues.add((String)dbValues.get(0));
								dbValues.remove(0);
								tcValues.add((Integer)tbValues.get(0));
								tbValues.remove(0); }
						}
						if(tbValues.isEmpty()) {
							while(!taValues.isEmpty()) {
								dcValues.add((String)daValues.get(0));
								daValues.remove(0);
								tcValues.add((Integer)taValues.get(0));
								taValues.remove(0); }
						}	
						//System.out.println("eval: merged dc has as first elem " + dcValues.get(0) + "\n\n");
						env.put(da, daValuesAux);
						env.put(ta, taValuesAux);
						env.put(db, dbValuesAux);
						env.put(tb, tbValuesAux);
						env.put(dc, dcValues);						
						env.put(tc, tcValues);
						//System.out.println("eval: merged tc from env has as first elem " + env.get(tc).get(0) + "\n\n");
						//return `merged(comp(dId(da), tId(ta)), comp(dId(db), tId(tb)), sc); 
						return formInstStream(dcValues, tcValues);
							
					}else { System.out.println("eval: merged: tbValues or dbValues is null. Error!"); }					 
			 }else { System.out.println("eval: merged: taValues or daValues is null. Error!"); }
			}//match merged
}//match
//return `True();
return p;
}

public static CSpec evalSpec(Map<String, ArrayList> env, CSpec spec) {
%match (spec){
			spec(pre(p), post) && andL(_*, False(), _*) << getAndL(evalPred(env, p)) -> { return `spec(pre(False()), post); }
			spec(pre(p), post(q)) && evalPre@andL(_*, !False(), _*) << getAndL(evalPred(env, p)) -> {
				//System.out.println("evalSpec: evalPre = " + `evalPre + "\n");
				return `spec(pre(evalPre), post(evalPred(env, getAndL(q)))); }
			spec(pre(p), post(q)) -> {
				//System.out.println("evalSpec: post = " + `q + "\n");
				return `spec(pre(evalPred(env, p)), post(evalPred(env, getAndL(q)))); }
}
System.out.println("evalSpec: no match for spec = " + spec + "\n");
return spec;
}

public static String getName(Node n) {
	%match(n) { node(name,_) -> { return `name; } }
return null;
}

public static String generate(String type, String s) {return type + s;}

public static String getNodeType(Node n) {
	%match(n) { 
	 source(_) -> { return "source";} 
	 sink(_) -> { return "sink";} 
}
return "dontKnow";
}

public static Boolean equalsS(Pred p1, Pred p2) {
	%match(p1, p2) {
		eqL(), eqL(_) -> { return false; }
		eqL(_), eqL() -> { return false; }
		eqL(t), eqL(t) -> { return true; }
		eqL(t), eqL(!t) -> { return false; }
		eqL(p11*, t, p12*), eqL(p21*, t, p22*) -> { return equalsS(`eqL(p11*, p12*), `eqL(p21*, p22*)); } 
}
return false;
}

// this function returns true if 
// na is the name of a source (type = source) and there's a sink in cl with the same name
// or na is the name of a sink and there's a source in cl with the same name
public static Boolean hidden(String type, String na, ConnectorList cl) {
	%match(cl) {	
		connectorList(_*, c, _*) && connector(R(ins(_*, node(name, _),_*), _),_) << getNormalised(c) -> {if (type == "sink") if (na.equals(`name)) return true;} 	  
		connectorList(_*, c, _*) && connector(R(_, outs(_*, node(name, _),_*)),_) << getNormalised(c) -> {if (type == "source") if (na.equals(`name)) return true;}
  	  } 
	return false;
}

//this function returns true if n is not a name of a stream or of a data from a stream on the nodes from the config of c
public static Boolean localName(String n, Connector c) {
	%match(c) {	
		connector(R(ins(_*, node(_, s), _*), _), _) -> {
			//System.out.println("local name ins n has between at index " + n.indexOf("between"));
			StreamId s2 = getUnfold(`s);
			String s3 = stream2String(`s);
			//System.out.println("localName ins s2 = " + s2);
			if ( (n.equals(s3)) || n.equals(s2) || n.equals(getDataName(s2)) 
			|| n.equals(getTimeName(s2) ) 			
			|| (n.indexOf("between") > -1)) 
			return false;}		
		connector(R(_, outs(_*, node(_, s), _*)), _) -> {
		StreamId s2 = getUnfold(`s);
		String s3 = stream2String(`s);	
		//System.out.println("local name outs n has between at index " + n.indexOf("between"));
		if ( (n.equals(s3)) || n.equals(s2) || n.equals(getDataName(s2)) 
		|| n.equals(getTimeName(s2)) 
		|| (n.indexOf("between") > -1) ) return false;}
  	  } 
	//System.out.println("local name n = " + n + " is local in c = " + pretty(c));
	return true;
}

public static Pred getPre(CSpec spec) {
	%match(spec) { spec(pre(p),_) -> { return `p; } }
return null;
}

public static Pred getPost(CSpec spec) {
	%match(spec) { spec(_,post(p)) -> { return `p; } }
return null;
}

public static CSpec getSpec(Connector c) {
	%match(c) { 
		connector(_, spec) -> { return `spec; }
		channel(t, (source|sink)(node(_, sa)), (source|sink)(node(_, sb))) -> 
			{ return `constraint(t, sa, sb); }
}
return null;
}

public static DataId getDataId(StreamId s) {
	%match(s) {
			comp(dId, _) -> { return `dId; }
		}
	return null;
	}

public static TimeId getTimeId(StreamId s) {
	%match(s) {
			comp(_, tId) -> { return `tId; }
		}
	return null;
	}

public static String getTimeName(StreamId s) {
	%match(s) {
			comp(_, tId(x)) -> { return `x; }
		}
	return null;
	}

public static String getDataName(StreamId s) {
	%match(s) {
			comp(dId(x),_) -> { return `x; }
		}
	return null;
	}

public static StreamId getStreamIdfromDataId(DataId d) {
	%match(d) {
			dId(concString('d', x*)) -> { return `sId("s" + x*); }
		}
	return null;
	}

public static StreamId getStreamIdfromTimeId(TimeId t) {
	%match(t) {
			tId(concString('t', x*)) -> { return `sId("s" + x*); }
		}
	return null;
	}

public static String stream2String(StreamId s) {
	%match(s) {
			sId(str) -> { return `str; }
			comp(_,_) -> { return stream2String(getFold(s)); }
		}
	return null;
	}

public static StreamId getFold(StreamId s) {
	%match(s) {
			comp(dId(concString(_,x*)), tId(concString(_,x*))) -> { return `sId("s" + x*); }
		}
	return s;
	}

public static StreamId getUnfold(StreamId s) {
	%match(s) {
			sId(concString(_,x*)) -> { return `comp(dId("d" + x*), tId("t" + x*)); }
		}
	return s;
	}

public static Connector getConnector(ConnectorList cl) {
%match(ConnectorList cl) {
	connectorList(connector(cf, cs)) -> {return `connector(cf, cs);}
	}
	return null; 
}

public static Connector getNormalised(Connector c) {
	try{
		Connector c1 = `Sequence(Normalise(),BottomUp(Fold())).visitLight(c);
		//System.out.println("getNormalised of c = " + c + " is " + c1);
		return c1;
		} catch (VisitFailure e) {
			System.out.println("getNormalised: strategy failed");
		}
	//System.out.println("getNormalised: strategy failed");	
	return null;
}

public static Pred getAndL(Pred p) {
	try{
		Pred p1 = `Repeat(And2AndL()).visitLight(p);
		//System.out.println("getAndL of p = " + p + " is " + p1);
		return p1;
		} catch (VisitFailure e) {
			System.out.println("getAndL: strategy failed");
		}
	return null;
}

public static Pred getEqL(Pred p) {
	try{
		Pred p1 = `Repeat(GatherEquals()).visitLight(p);
		//System.out.println("getAndL of p = " + p + " is " + p1);
		return p1;
		} catch (VisitFailure e) {
			System.out.println("getEqL: strategy failed");
		}
	return null;
}

public static void printEnv(Map<String, ArrayList> env) {
	Set set = env.entrySet();
    Iterator it = set.iterator();
    System.out.println("printEnv:");
    System.out.println("------------------------------------------------------------");
    while(it.hasNext()){
      Map.Entry me = (Map.Entry)it.next();
      System.out.println(me.getKey() + " : " + me.getValue() ); }
    System.out.println("------------------------------------------------------------");
}

public static String pretty(Object o) {
	%match(TimeId o) {
      tId(name) -> { return `name; }
      }
	%match(DataId o) {
      dId(name) -> { return `name; }
      }
    %match(StreamId o) {
      sId(name) -> { return `name; }
      comp(d, t) -> { return "comp(" + pretty(`d) + "," + pretty(`t) +")"; }
      }
    %match(Pred o){
	  and(p, q) -> { return pretty(`p) + " and " + pretty(`q); }
	  implic(p, q) -> { return " ( " + pretty(`p) + " => " + pretty(`q) + " ) "; }
	  andL(p) -> { return pretty(`p); }
	  andL(p, l*) -> { return pretty(`p) + " and " + pretty(`andL(l*)); }
      eq(s1,s2) -> { return pretty(`s1) + " = " + pretty(`s2); }
      eqD(d1,d2) -> { return pretty(`d1) + " =d " + pretty(`d2); }
      eqT(t1,t2) -> { return pretty(`t1) + " =t " + pretty(`t2); }
      between(t1,t2) -> { return "between(" + pretty(`t1) + ", " + pretty(`t2) + ")"; }      
      exists(p, q) -> { return "E(" + pretty(`p) + ", " + pretty(`q) + ")"; }
      merged(s1, s2, s3) -> { return "merged(" + pretty(`s1) + ", " + pretty(`s2) + ", " + pretty(`s3) +  ")"; }
      neg(p) -> {return "~ " + pretty(`p);}
      D(sId) -> {return "D< " + pretty(`sId) + " >";}       
     }
    %match(Pre o) {
      pre(p) -> { return pretty(`p); }
    }
    %match(Post o) {
      post(q) -> { return pretty(`q); }
    }
    %match(CSpec o) {
     spec(p, q) -> { return pretty(`p) + " |- " + pretty(`q); }
     constraint(t, sa, sb) -> { return "constraint(" + `t + ", " + pretty(`sa) + ", " + pretty(`sb) + ")"; }
     }
    %match (Node o){
	 node(name, sid) -> { return "( " + `name + " , " + pretty(`sid) + " )"; }
    }
    %match(Ins o) {
     ins(n) -> {return pretty(`n); }	
     ins(n, ns*) -> {return pretty(`n) + ", " + pretty(`ins(ns*)); }      	
    }
    %match(Outs o) {
     outs(n) -> {return pretty(`n); }
     outs(n, ns*) -> {return pretty(`n) + ", " + pretty(`outs(ns*)); }      	
    }
    
    %match(Connector o) {
     channel(sync(), source(n1), sink(n2)) -> { return "sync(source(" + pretty(`n1) + "), sink(" + pretty(`n2) + ")";}
     channel(fifo(), source(n1), sink(n2)) -> { return "fifo(source(" + pretty(`n1) + "), sink(" + pretty(`n2) + ")";}	
     connector(R(i1, o1),spec) -> { return "R(" + pretty(`i1) + " : " + pretty(`o1) + ") , " + pretty(`spec); }
    }
    %match(ConnectorList o) {
     connectorList(c) -> { return pretty(`c); }
     connectorList(c,cl*) -> { return "[ " + pretty(`c) + ", " + pretty(`connectorList(cl*)) + " ]"; }
     connectorTree(c) -> { return pretty(`c); }
     connectorTree(c,cl*) -> { return "[ " + pretty(`c) + ", " + pretty(`connectorTree(cl*)) + " ]"; }
    }
    return o.toString();
  }


/*********************************************************/ 
/**                      STRATEGIES                     **/ 
/*********************************************************/

%strategy Fold() extends `Identity() {
	visit StreamId {
		comp(dId(concString('d',x*)), tId(concString('t',x*))) -> { return `sId(generate("s", x*)); }
	}
}

%strategy Unfold() extends `Identity() {
	visit StreamId {			
		sId(concString(_,x*)) -> { return `comp(dId(generate("d", x*)), tId(generate("t", x*))); }
	}
} 

// renames n1 with n2
%strategy Rename(n1:String,n2:String) extends Identity(){ 
  	visit StreamId {
  	  sId(n) -> { if(`n==n1) return `sId(n2); } 
  	  }
  	visit TimeId {
  	  tId(n) -> { 
  		  if(`n==n1) return `tId(n2); 
  		  if(`n.equals("between2("+n1+")")) return `tId("between2(" + n2 + ")"); 
  	  	}
  	  }
  	visit DataId{
  	  dId(n) -> { if(`n==n1) return `dId(n2); }
 	 } 
}

%strategy EvalConstraints() extends Identity(){ 
  	visit CSpec {
 		constraint(sync(), sa, sb) && comp(da, ta) << getUnfold(sa) && comp(db, tb) << getUnfold(sb) -> { 
 			return `spec(pre(D(comp(da, ta))), post(andL(D(comp(db, tb)), eqT(ta, tb), eqD(da, db)))); }
 		constraint(lossySync(), sa, sb) && comp(da, ta) << getUnfold(sa) && comp(db, tb) << getUnfold(sb) -> { 
 			return `spec(pre(D(comp(da, ta))), post(andL(D(comp(db, tb)), L(comp(da, ta), comp(db, tb))))); } 	    	   
 		constraint(fifo(), sa, sb) && comp(da, tId(taS)) << getUnfold(sa) && comp(db, tb) << getUnfold(sb) -> { 
 			return `spec(pre(D(comp(da, tId(taS)))), post(and(and(D(comp(db, tb)), eqD(da, db)), eqT(tb, tId("between2(" + taS + ")"))))); }
 		constraint(syncDrain(), sa, sb) && comp(da, ta) << getUnfold(sa) && comp(db, tb) << getUnfold(sb) -> { 
 			return `spec(pre(and(and(D(comp(da, ta)), D(comp(db, tb))), eqT(ta, tb))), post(True())); }
 	 } 
}

//this strategy applied to a specific channel (sync, fifo...) reduces it to the general format of a connector(R(), spec) 
%strategy Normalise() extends Identity(){ 
  	visit Connector {
  	  c@channel((sync|fifo|lossySync)(), source(n1), sink(n2)) -> { return `connector(R(ins(n1), outs(n2)), getSpecBC(c));}	
  	  c@channel(syncDrain(), source(n1), source(n2)) -> { return `connector(R(ins(n1, n2), outs()), getSpecBC(c));}
  	  c@channel(syncSpout(), sink(n1), sink(n2)) -> { return `connector(R(ins(), outs(n1, n2)), getSpecBC(c));}  	  
 	 } 
}

//the corresponding function
public static ConnectorList normalise(ConnectorList cl){
ConnectorList clN;
try{
	clN = `Normalise().visitLight(cl); return clN;
} catch (VisitFailure e) { System.out.println("normalise: strategy failed"); return null;}
}

%strategy And2AndL() extends Fail(){ 
  	visit Pred {  	  
  	  and(and(p, q), r) -> { 
  		  //System.out.println("And2AndL case 1"); 
  		  return `andL(p, q, r);} 
  	  and(r, and(p, q)) -> { 
  		  //System.out.println("And2AndL case 2"); 
  		  return `andL(p, q, r);}
  	  and(andL(l*), r) -> { 
  		  //System.out.println("And2AndL case 3"); 
  		  return `andL(l*, r);}    	  
  	  and(l, andL(r*)) -> { 
  		  //System.out.println("And2AndL case 4"); 
  		  return `andL(l, r*);}
  	  andL(r1*, and(p,q), r2*) -> { 
  		  //System.out.println("And2AndL case 5"); 
  		  return `andL(r1*, p, q, r2*);}
  	 and(p, q) -> {return `andL(p, q); }
 	 }
}

// i want to repeat it so it has to extend fail
%strategy GatherEquals() extends Fail(){ 
  	visit Pred {
  	  andL(p1*, eqT(tId(x), tId(y)), p2*, eqT(tId(y), tId(z)), p3*) -> { return `andL(p1*, eqL(x, y, z), p2*, p3*); }
  	  andL(p1*, eqT(tId(x), tId(y)), p2*, eqT(tId(z), tId(y)), p3*) -> { return `andL(p1*, eqL(x, y, z), p2*, p3*); }
  	  andL(p1*, eqT(tId(x), tId(y)), p2*, eqT(tId(x), tId(z)), p3*) -> { return `andL(p1*, eqL(x, y, z), p2*, p3*); }
  	  andL(p1*, eqT(tId(x), tId(y)), p2*, eqT(tId(z), tId(x)), p3*) -> { return `andL(p1*, eqL(x, y, z), p2*, p3*); } 
  	  andL(p1*, eqT(tId(x), tId(y)), p2*, eqL(y, z*), p3*) -> { return `andL(p1*, eqL(x, y, z*), p2*, p3*); }
  	  andL(p1*, eqT(tId(x), tId(y)), p2*, eqL(x, z*), p3*) -> { return `andL(p1*, eqL(x, y, z*), p2*, p3*); }
  	  andL(p1*, eqD(dId(x), dId(y)), p2*, eqD(dId(y), dId(z)), p3*) -> { return `andL(p1*, eqL(x, y, z), p2*, p3*); }
  	  andL(p1*, eqD(dId(x), dId(y)), p2*, eqD(dId(z), dId(y)), p3*) -> { return `andL(p1*, eqL(x, y, z), p2*, p3*); }
  	  andL(p1*, eqD(dId(x), dId(y)), p2*, eqD(dId(x), dId(z)), p3*) -> { return `andL(p1*, eqL(x, y, z), p2*, p3*); }
  	  andL(p1*, eqD(dId(x), dId(y)), p2*, eqD(dId(z), dId(x)), p3*) -> { return `andL(p1*, eqL(x, y, z), p2*, p3*); } 
  	  andL(p1*, eqD(dId(x), dId(y)), p2*, eqL(y, z*), p3*) -> { return `andL(p1*, eqL(x, y, z*), p2*, p3*); }
  	  andL(p1*, eqD(dId(x), dId(y)), p2*, eqL(x, z*), p3*) -> { return `andL(p1*, eqL(x, y, z*), p2*, p3*); }
 	 } 
}

%strategy DeleteDuplic() extends Fail() {
	visit Connector {
		connector(R(ins(l1*, n, l2*, n, l3*), o), spec) -> {return `connector(R(ins(l1*, n, l2*, l3*), o), spec);}
		connector(R(i, outs(l1*, n, l2*, n, l3*)), spec) -> {return `connector(R(i, outs(l1*, n, l2*, l3*)), spec);}
		//connector(R(i, o), spec()) -> {return `connector(R(ins(l1*, n, l2*, l3*), o), spec);}
		}
	visit Pred {
		 andL(p1*, p, p2*, p, p3*) -> { return `andL(p1*, p, p2*, p3*); }
		}  
}

// i want to repeat it so it has to extend fail
%strategy SimpImplication() extends Fail(){ 
  	visit Pred {
  		implic(_, andL()) -> { 
  			if(debugFlagStratSimpImpl) { 
  				System.out.println("SimpImplic p => True() is red to True() "); } 
  			return `True(); }
  		implic(p1, p2) && andL(p11*, D(s1), p12*) << getAndL(p1) && andL(p21*, D(s2), p22*) << getAndL(p2) 
  		&& sId(s) << getFold(s1) && sId(s) << getFold(s2) -> {
			if(debugFlagStratSimpImpl) {
				System.out.println("SimpImplication delete s1 = " + `s1); }
			return `implic(andL(p11*, p12*), andL(p21*, p22*)); }
  		implic(p1, p2) && andL(p11*, eqD(e1, e2), p12*) << getAndL(p1) && andL(p21*, eqD(e2, e1), p22*) << getAndL(p2) -> {
			if(debugFlagStratSimpImpl) {
				System.out.println("SimpImplication delete e1 = " + `e1); }
			return `implic(andL(p11*, p12*), andL(p21*, p22*)); }
  		implic(p1, p2) 
  		&& andL(p11*, e1@eqL(_*), p12*) << getEqL(getAndL(p1))
  		&& andL(p21*, e2@eqL(_*), p22*) << getEqL(getAndL(p2)) -> {
  			if (equalsS(`e1, `e2)) {
  				if(debugFlagStratSimpImpl) {
  					System.out.println("SimpImplication delete eqTL of = " + `e1); }
  				return `implic(andL(p11*, p12*), andL(p21*, p22*)); } 
			}
		implic(p1, p2) && andL(p11*, p, p12*) << getAndL(p1) && andL(p21*, p, p22*) << getAndL(p2) -> {
			if(debugFlagStratSimpImpl) { 
				System.out.println("SimpImplication delete p = " + `p + " in p1 = " + `p1 + " and in p2 = " + `p2); }
			return `implic(andL(p11*, p12*), andL(p21*, p22*)); }
		implic(p, p) -> {
			if(debugFlagStratSimpImpl) { 
				System.out.println("SimpImplication p => p is red to True and p = " + `p); } 
			return `True() ; }		
		implic(andL(p, q), p) -> {
			if(debugFlagStratSimpImpl) {  
				System.out.println("SimpImplication p and q => p is red to q = " + `q); } 
			return `q ; }   	 
 	 } 
}

// i want to repeat so extend fail
%strategy SimpResRef() extends Fail(){ 
  	visit Pred {
  	   // get rid of the True() part
  	   andL(True(), p) -> { return `p;}	
  	   andL(p, True()) -> { return `p;}
  	   
  	  // normalise (apply eqs and delete them)	
  	  implic(andL(p1*, eqD(dId(d1), dId(d2)), p2*), q) -> { 
  		  Pred newp = `TopDown(Sequence(Unfold(), Rename(d1, d2))).visitLight(`implic(andL(p1*, p2*), q)); 
  	  		return newp; }
  	  implic(andL(p1*, eqT(tId(t1), tId(t2)), p2*), q) -> {  
  		  Pred newp = `TopDown(Sequence(Unfold(), Rename(t1, t2))).visitLight(`implic(andL(p1*, p2*), q)); 
  	  		return newp; } 
  	   // get rid of D(s)
  	   implic(andL(p1*, D(_), p2*), q) -> { return `implic(andL(p1*, p2*), q) ; }	
  	   implic(p, andL(q1*, D(_), q2*)) -> { return `implic(p, andL(q1*, q2*)) ; }
  	   implic(andL(p), andL(q)) -> { return `implic(p, q) ; }
 	 } 
}

%strategy SimpPred() extends Identity() {
	visit Pred {
		and(D(sa), neg(D(sa))) -> 
			{ return `False(); } 
		eq(sa, sa) -> 
			{ return `True(); } 
		and(x, True()) -> 
			{ return `x; }
		neg(False()) -> 
			{ return `True(); }
	}
}

// i want to repeat it so it has to extend fail
%strategy SimplifySpec() extends Fail(){ 
  	visit Connector {
  		// delete source and sink with the same name 
  		// these are probably the result of seq between 2 connectors which have more than one pair of source and sink with the same name
  		connector(R(ins(i1*, node(n, _), i2*), outs(o1*, node(n, _), o2*)), spec) -> {  		   
  			  if(debugFlagStratSimp) { 
  				  System.out.println("SimplifySpec delete source and sink for same name = " + `n) ; }
  			  return `connector(R(ins(i1*, i2*), outs(o1*, o2*)), spec);  			
  	  }
  	  // delete 1 of 2 sources with the same name 
  	  // these are probably the result of rep between a connector and a syncdrain so replic is possible on both ends of the syncdrain
  		connector(R(ins(i1*, nv@node(n, _), i2*, node(n,_), i3*), o), spec) -> {  		   
  			  if(debugFlagStratSimp) { 
  				  System.out.println("SimplifySpec delete source and sink for same name = " + `n) ; }
  			  return `connector(R(ins(i1*, nv, i2*, i3*), o), spec);  			
  	  }   	   	  
  	  // delete 1 of two sinks with the same name 
  	  // these are probably the result of merge between a connector and a syncspout so merge is possible on both ends of the syncspout
  		connector(R(i, outs(o1*, nv@node(n, _), o2*, node(n, _), o3*)), spec) -> {  		   
  			  if(debugFlagStratSimp) { 
  				  System.out.println("SimplifySpec delete source and sink for same name = " + `n) ; }
  			  return `connector(R(i, outs(o1*, nv, o2*, o3*)), spec);  			
  	  }   	   	  
  	     	   	  
  	  // delete D(local streams) from post 
  	  c@connector(x, spec(prec, post(p))) && andL(p1*, D(s), p2*) << getAndL(p) 
  	  && sId(s1) << getFold(s) -> {
  		  if ( localName(`s1, `c) == true ) { 
  			  if(debugFlagStratSimp) { 
  				  System.out.println("SimplifySpec remove D(s1) from post = " + `s1) ; }
  			  return `connector(x, spec(prec, post(andL(p1*, p2*))));
  			  }
  	  }
  	  //delete D(local streams) from pre 
  	  c@connector(x, spec(pre(p), post)) && andL(p1*, D(s), p2*) << getAndL(p) 
  	  && sId(s1) << getFold(s) -> {
  		  if ( localName(`s1, `c) == true ) { 
  			  if(debugFlagStratSimp) { 
  				  System.out.println("SimplifySpec remove D(s1) from pre = " + `s1) ; }
  			  return `connector(x, spec(pre(andL(p1*, p2*)), post));
  			  }  		   
  	  }
  	  // simplifying post: delete duplicates from pre and post  	  
  	  connector(x, spec(pre(p), post)) && andL(p1*, pr, p2*, pr, p3*) << getAndL(p) -> {
  		  return `connector(x, spec(pre(andL(p1*, pr, p2*, p3*)), post)); 
  	  }
  	  
  	  connector(x, spec(prec, post(p))) && andL(p1*, pr, p2*, pr, p3*) << getAndL(p) -> {
  		  return `connector(x, spec(prec, post(andL(p1*, pr, p2*, p3*)))); 
  	  }

  	  /** the order of simplifications is important:
  	  ** if ta = td .. |= td = tb /\ td = tc then 
  	  ** it should be the case that first td is replaced by ta 
  	  ** and not that td in the 2nd eq is replaced by tb!!!  
  	  **/
  	  
  	  c@connector(x, spec(pre(p), post(q))) 
  	  && andL(_*, eqD(dId(d1), dId(d2)), _*) << getAndL(p) 
  	  && andL(q1*, eqD(dId(d3), dId(d4)), q2*) << getAndL(q) -> {
  		  if ( (localName(`d1, `c) == true) && (`d1.equals(`d3) || `d1.equals(`d4) ) ) { 
  			  Pred newq = `TopDown(Sequence(Unfold(), Rename(d1, d2))).visitLight(`andL(q1*, q2*));
  			  Pred newq2 = `BottomUp(Fold()).visitLight(newq);
  			  if(debugFlagStratSimp) { 
  				  System.out.println("SimplifySpec d1 = " + `d1  + " newq = " + newq + " newq2 = " + newq2); }
  			  return `connector(x, spec(pre(p), post(newq)));
  			  }
  		  if ( (localName(`d2, `c) == true) && (`d2.equals(`d3) || `d2.equals(`d4) ) ) { 
  			  Pred newq = `TopDown(Sequence(Unfold(), Rename(d2, d1))).visitLight(`andL(q1*, q2*));
  			  Pred newq2 = `BottomUp(Fold()).visitLight(newq);
  			  if(debugFlagStratSimp) { 
  			  		System.out.println("SimplifySpec d2 = " + `d2  + "\n working on p = " + pretty(`p) + "\n newq = " + pretty(newq) + "\n newq2 = " + pretty(newq2)); }
  			  return `connector(x, spec(pre(p), post(newq)));
  			  }
  	  }
  	  
  	  //the same for time...
  	  c@connector(x, spec(pre(p), post(q))) 
  	  && andL(_*, eqT(tId(t1), tId(t2)), _*) << getAndL(p) 
  	  && andL(q1*, e@eqT(tId(t3), tId(t4)), q2*) << getAndL(q) -> {
  		  if ( (localName(`t1, `c) == true) && (`t1.equals(`t3) || `t1.equals(`t4)) && (localName(`t2, `c) == false) ) { 
  			  Pred newq = `TopDown(Sequence(Unfold(), Rename(t1, t2))).visitLight(`andL(q1*, e, q2*));
  			  Pred newq2 = `BottomUp(Fold()).visitLight(newq);
  			  if(debugFlagStratSimp) { 
  				  System.out.println("SimplifySpec t1 = " + `t1  + " is replaced by t2 = " + `t2 + " newq = " + newq + " newq2 = " + newq2); }
  			  return `connector(x, spec(pre(p), post(newq)));
  			  }
  		  if ( (localName(`t2, `c) == true) && (`t2.equals(`t3) || `t2.equals(`t4)) && (localName(`t1, `c) == false) ) { 
  			  Pred newq = `TopDown(Sequence(Unfold(), Rename(t2, t1))).visitLight(`andL(q1*, e, q2*));
  			  Pred newq2 = `BottomUp(Fold()).visitLight(newq);
  			  if(debugFlagStratSimp) {  
  				  System.out.println("SimplifySpec t2 = " + `t2 + " is replaced by t1 = " + `t1 + "\n working on p = " + pretty(`p) + "\n newq = " + pretty(newq) + "\n newq2 = " + pretty(newq2)); }
  			  return `connector(x, spec(pre(p), post(newq)));
  			  }
  	  }
  	  // simplifying post: replace local data
  	  c@connector(x, spec(prec, post(p))) && andL(p1*, eqD(dId(d1), dId(d2)), p2*) << getAndL(p) -> {
  		  if ( (localName(`d1, `c) == true) && (localName(`d2, `c) == false)) { 
  			  Pred temp1 = `TopDown(Sequence(Unfold(), Rename(d1, d2))).visitLight(`andL(p1*, p2*));
  			  Pred temp2 = `BottomUp(Fold()).visitLight(temp1);
  			  if(debugFlagStratSimp) { 
  				  System.out.println("SimplifySpec d1 = " + `d1 + " is replaced by d2 = " + `d2 + " temp1 = " + temp1 + " temp2 = " + temp2); }
  			  return `connector(x, spec(prec, post(TopDown(Sequence(Unfold(), Rename(d1, d2))).visitLight(andL(p1*, p2*)))));
  			  }
  		  if ( (localName(`d2, `c) == true) && (localName(`d1, `c) == false)) { 
  			  Pred temp1 = `TopDown(Sequence(Unfold(), Rename(d2, d1))).visitLight(`andL(p1*, p2*));
  			  Pred temp2 = `BottomUp(Fold()).visitLight(temp1);
  			  if(debugFlagStratSimp) { 
  				  System.out.println("SimplifySpec d2 = " + `d2  + "\n working on p = "+ " is replaced by d1 = " + `d1 + pretty(`p) + "\n temp1 = " + pretty(temp1) + "\n temp2 = " + pretty(temp2)); }
  			  return `connector(x, spec(prec, post(TopDown(Sequence(Unfold(), Rename(d2, d1))).visitLight(andL(p1*, p2*)))));
  			  }
  	  }
  	  // replace local time??? (that is, if we use instead between(ta, tc) something like tc =t between(ta)
  	  c@connector(x, spec(prec, post(p))) && andL(p1*, eqT(tId(t1), tId(t2)), p2*) << getAndL(p) -> {
  		  if ( (localName(`t1, `c) == true) &&  (localName(`t2, `c) == false)) { 
  			  Pred temp1 = `TopDown(Sequence(Unfold(), Rename(t1, t2))).visitLight(`andL(p1*, p2*));
  			  Pred temp2 = `BottomUp(Fold()).visitLight(temp1);
  			  if(debugFlagStratSimp) { 
  				  System.out.println("SimplifySpec t1 = " + `t1  + " is replaced by t2 = " + `t2 + " temp1 = " + pretty(temp1) + " temp2 = " + pretty(temp2)); }
  			  return `connector(x, spec(prec, post(TopDown(Sequence(Unfold(), Rename(t1, t2))).visitLight(andL(p1*, p2*)))));
  			  }
  		  if ( (localName(`t2, `c) == true) && (localName(`t1, `c) == false)) { 
  			  Pred temp1 = `TopDown(Sequence(Unfold(), Rename(t2, t1))).visitLight(`andL(p1*, p2*));
  			  Pred temp2 = `BottomUp(Fold()).visitLight(temp1);
  			  if(debugFlagStratSimp) { 
  				  System.out.println("SimplifySpec t2 = " + `t2  + " temp1 = " + " is replaced by t1 = " + `t1 + pretty(temp1) + " temp2 = " + pretty(temp2)); }
  			  return `connector(x, spec(prec, post(TopDown(Sequence(Unfold(), Rename(t2, t1))).visitLight(andL(p1*, p2*)))));
  			  }
  	  }	  
  	 // delete hidden D(sa) from pre
  	 c@connector(x, spec(pre(p), post)) && andL(p1*, D(s), p2*) << getAndL(p)  
  	  && sId(s1) << getFold(s) -> {
  		  if ( localName(`s1, `c) == true) { 
  			  if(debugFlagStratSimp) { System.out.println("SimplifySpec delete hidden = " + `s1 + " p = " + pretty(`p)) ; }
  			  return `connector(x, spec(pre(andL(p1*, p2*)), post));
  			  }
  	  }
  	 // delete duplicates D(sa), D(da, ta) from pre
  	 connector(x, spec(pre(p), post)) && andL(p1*, D(s), p2*) << getAndL(p)  
  	  && sId(s1) << getFold(s) 
  	  && andL(_*, D(s2), _*) << andL(p1*, p2*) 
  	  && sId(s1) << getFold(s2) -> {  		   
  			  if(debugFlagStratSimp) { System.out.println("SimplifySpec delete duplicates D(s1) = " + `s1 + " p = " + pretty(`p)) ; }
  			  return `connector(x, spec(pre(andL(p1*, p2*)), post));  			
  	  }
  	  // delete True()
  	 connector(x, spec(pre(p), post)) && andL(p1*, True(), p2*) << getAndL(p) -> {  		   
  			  if(debugFlagStratSimp) { System.out.println("SimplifySpec delete True() from prec = ") ; }
  			  return `connector(x, spec(pre(andL(p1*, p2*)), post));  			
  	  }
  	 connector(x, spec(pre, post(q))) && andL(q1*, True(), q2*) << getAndL(q) -> {  		   
  			  if(debugFlagStratSimp) { System.out.println("SimplifySpec delete True() from post = ") ; }
  			  return `connector(x, spec(pre, post(andL(q1*, q2*))));  			
  	  }	 

  	 // simplify pre: delete hidden if they don't appear in post. use anti pattern!
  	 // replace data
  	 // i dont think that it can be the case that d1 = d2 is in pre and either d1 or d2 is not hidden... can it be?
  	 // because otherwise it should be sufficient to check only if localName(d1)... 
  	 c@connector(x, spec(pre(p), post(q))) 
  	 && andL(p1*, eqD(dId(d1), _), p2*) << getAndL(p) 
  	 && (!andL(_*, eqD(dId(d1), _), _*) << getAndL(q) || !andL(_*, eqD(_, dId(d1)), _*) << getAndL(q)) -> {
  		  if (localName(`d1, `c) == true) { 
  			  if(debugFlagStratSimp) { System.out.println("SimplifySpec delete from pre eq with d1 = " + `d1); }
  			  return `connector(x, spec(pre(andL(p1*, p2*)), post(q)));
  			  }
  	  }
  	  // replace local time
  	c@connector(x, spec(pre(p), post(q))) 
  	 && andL(p1*, eqT(tId(t1), _), p2*) << getAndL(p)   
  	 && (!andL(_*, eqT(tId(t1), _), _*) << getAndL(q) || !andL(_*, eqT(_, tId(t1)), _*) << getAndL(q)) -> {
  		  if (localName(`t1, `c) == true) { 
  			  if(debugFlagStratSimp) { System.out.println("SimplifySpec delete from pre eq with d1 = " + `t1); }
  			  return `connector(x, spec(pre(andL(p1*, p2*)), post(q)));
  			  }  		  
  	  }  	
 	 } 
}

// i want that connectorList(connectorList(c), x*) to be seen as connectorList(c, x*)			
%strategy FlattenCL() extends Identity(){ 
  	visit ConnectorList {  	     		
  	  /* connectorList(cl1*, connectorList(c), cl2*) && connectorList(_, _*) << connectorList(cl1*, cl2*) -> { 
  		  if(debugFlagStratFlatten) { System.out.println("FlattenCL: only one connector in the list : " + `c); } 
  		  return `connectorList(cl1*, c, cl2*); }  	    		   	 
  	 ct@connectorTree(cl1*, connectorTree(connectorList(c)), cl2*) && connectorTree(_, _*) << connectorTree(cl1*, cl2*) -> { 
  		  if(debugFlagStratFlatten) { System.out.println("FlattenCL: a connectorTree in the tree : " + `ct); } 
  		  return `connectorTree(cl1*, connectorList(c), cl2*); } */
  	  connectorTree(connectorList(cl*)) -> {
  		  if(debugFlagStratFlatten) { System.out.println("FlattenCL: tree to list"); } 
  		  return `connectorList(cl*); }
  	  connectorTree(connectorList(c1*), connectorList(c2*), cl*) && !connectorTree(_*, !connectorList(_), _*) << connectorTree(cl*) -> {
  		  if(debugFlagStratFlatten) { System.out.println("FlattenCL: gather"); } 
  		  return `connectorTree(connectorList(c1*, c2*), cl*); }  	  
 	 } 
}

/*******************************************************************************************/
/**                          STRATEGIES FOR CONNECTOR COMPOSITIONS                         */
/*******************************************************************************************/

%strategy Seq() extends Fail(){ 
  	visit ConnectorList {
  	  connectorList(l1*, c1@channel(t, n@(source|sink)(node(na, sId(sa))), sink(node(nb, sId(sb)))), c2, l2*)   	  
  	  && c22@connector(R(ins(i1*, node(nb, _), i2*), outs(o*)), spec) << getNormalised(c2) // && sId(sc) << getFold(s) 
  	  // check that na is not hidden, that is, if na is a source (resp. sink) then there's no sink (resp. source) on the left with the name na    	  
  	  && hidden(getNodeType(n), na, l1*) == false  -> { 
		  if(debugFlagStratSeq) { 
			  //System.out.println("Strategy Seq spec = " + `spec + " renaming " + `sc + " into " + `sa + " => " + `BottomUp(Rename(sc, sa)).visitLight(`spec));
			    System.out.println("Strategy Seq when sink belongs to a BC with the other end not hidden" + "-------------------- \n\n\n"); }
			  
		  //CSpec specL = `TopDown(Sequence(Rename(sb, sa),EvalConstraints())).visitLight(`constraint(t, sId(sa), sId(sb))); 
		  CSpec specL = `TopDown(EvalConstraints()).visitLight(`constraint(t, sId(sa), sId(sb)));
		  //CSpec specR = `BottomUp(Sequence(Try(EvalConstraints()), Rename(sc, sa))).visitLight(`spec);		  		  		  
		  CSpec specR = `BottomUp(Try(EvalConstraints())).visitLight(`spec);
		  Pred p1, p2, q1, q2;
		  p1 = getPre(specL);
		  q1 = getPost(specL);
		  p2 = getPre(specR);
		  q2 = getPost(specR);
		  // since we can rename, exists p /\ q is satisfied by sa!!     
		  //CSpec specRes = `spec(pre(and(p1, neg(and(q1, neg(p2))))), post(and(q1, q2)));
		  /* take care!!! you took the neg thing out...
		  ** it's ok...
		  ** assuming s and sId(sb) are the same, then p1/\q1;p2 is the same with p1 /\ neg(q1 /\ neg p2)
		  ** which is p1 /\ (neg q1 \/ p2) which is p1 /\ p2 
		  ** unless it can be that the postcond of a connector is false... can it ever be so??
		  */ 
		  CSpec specRes = `spec(pre(and(p1, p2)), post(and(q1, q2)));
		  CSpec specResSimp = `BottomUp(SimpPred()).visitLight(specRes);
		  if(debugFlagStratSeq) { 
			  System.out.println("Strategy Seq: \n specL = " + pretty(specL) + 
				  				"\n specR = " + pretty(specR) + 
				  				"\n specRes = " + pretty(specRes) + 
				  				"\n specResSimp = " + pretty(specResSimp) + "\n\n\n");		  
			
			  System.out.println("Strategy Seq of " + pretty(`c1) + " and " + pretty(`c22) + " = " +  
					  			pretty(`connectorList(l1*, connector(R(ins(node(na, sId(sa)), i1*, i2*), outs(o*)), specResSimp), l2*))
					  			+ "\n\n\n"); }
		 
		  if (getNodeType(`n) == "source") {
			  Connector cRes = `connector(R(ins(node(na, sId(sa)), i1*, i2*), outs(o*)), specResSimp);
			  Connector cRes2 = `Repeat(SimplifySpec()).visitLight(cRes);
			  if(debugFlagStratSeq) { System.out.println("Strategy Seq -> source cRes2 = " + pretty(cRes2)); }
			  return `connectorList(l1*, cRes2, l2*);
			  }
		  	else {
		  			Connector cRes = `connector(R(ins(i1*, i2*), outs(node(na, sId(sa)), o*)), specResSimp);
		  			Connector cRes2 = `Repeat(SimplifySpec()).visitLight(cRes);
		  			if(debugFlagStratSeq) { System.out.println("Strategy Seq -> sink cRes2 = " + pretty(cRes2)); }
		  			return `connectorList(l1*, cRes2, l2*);
		  		}		   	
			}

  	  connectorList(l1*, c2, c1@channel(t, source(node(na, sId(sa))), n@(source|sink)(node(nb, sId(sb)))), l2*)
  	  && c22@connector(R(ins(i*), outs(o1*, node(na, _), o2*)), spec) << getNormalised(c2) //&& sId(sc) << getFold(s)
  	  //check that nb is not hidden
  	  && hidden(getNodeType(n), nb, l2*) == false -> { 	     	  
		  if(debugFlagStratSeq) { System.out.println("Strategy Seq when source belongs to a BC with the other end not hidden" + "-------------------- \n\n\n"); }
		  CSpec specR = `TopDown(EvalConstraints()).visitLight(`constraint(t, sId(sa), sId(sb))); 
		  CSpec specL = `BottomUp(Try(EvalConstraints())).visitLight(`spec);		  
		  if(debugFlagStratSeq) { System.out.println("Strategy Seq specL = " + specL + " specR = " + specR + "\n\n\n"); }
		  Pred p1, p2, q1, q2;
		  p1 = getPre(specL);
		  q1 = getPost(specL);
		  p2 = getPre(specR);
		  q2 = getPost(specR);
		  /* take care!!! you took the neg thing out...
		  ** it's ok...
		  ** assuming s and sId(sb) are the same, then p1/\q1;p2 is the same with p1 /\ neg(q1 /\ neg p2)
		  ** which is p1 /\ (neg q1 \/ p2) which is p1 /\ p2 
		  ** unless it can be that the postcond of a connector is false... can it ever be so??
		  */ 
		  CSpec specRes = `spec(pre(and(p1, p2)), post(and(q1, q2)));
		  CSpec specResSimp = `BottomUp(SimpPred()).visitLight(specRes);
		  /* 
		   ** for debugging
		   */
		  if(debugFlagStratSeq) {
		  System.out.println("Strategy Seq: \n specL = " + pretty(specL) + 
				  							"\n specR = " + pretty(specR) + 
				  							"\n specRes = " + pretty(specRes) + 
				  							"\n specResSimp = " + pretty(specResSimp) + "\n\n\n");		  
  		   System.out.println("Strategy Seq of " + pretty(`c22) + " and " + pretty(`c1) + " = " +  
						pretty(`connectorList(l1*, connector(R(ins(node(nb, sId(sb)), i*), outs(o1*, o2*)), specResSimp), l2*))
						 + "\n\n\n"); }	
		   if (getNodeType(`n) == "source") {
			   		Connector cRes = `connector(R(ins(node(nb, sId(sb)), i*), outs(o1*, o2*)), specRes);
			   		Connector cRes2 = `Repeat(SimplifySpec()).visitLight(cRes);
		  			if(debugFlagStratSeq) { System.out.println("Strategy Seq <- source cRes2 = " + pretty(cRes2)); }
			   		return `connectorList(l1*, cRes2, l2*);
			   		}
		  	else {
		  			Connector cRes = `connector(R(ins(i*), outs(node(nb, sId(sb)), o1*, o2*)), specRes);
		  			Connector cRes2 = `Repeat(SimplifySpec()).visitLight(cRes);
		  			if(debugFlagStratSeq) { System.out.println("Strategy Seq <- sink cRes2 = " + pretty(cRes2)); }
		  			return `connectorList(l1*, cRes2 , l2*);
		  			}
			}

		// seq between source and sink of non-basic connectors 
		connectorList(l1*, c1, c2, l2*)
		  	&& c11@connector(R(ins(i*), outs(o1*, node(nb, _), o2*)), spec1) << getNormalised(c1)
			&& c22@connector(R(ins(i1*, node(nb, _), i2*), outs(o*)), spec2) << getNormalised(c2)  -> {
		  //System.out.println("Strategy Seq non-basic " + "-------------------- \n\n\n");
		  Pred p1, p2, q1, q2;
		  p1 = getPre(`spec1);
		  q1 = getPost(`spec1);
		  p2 = getPre(`spec2);
		  q2 = getPost(`spec2);
		  CSpec specRes = `spec(pre(and(p1, p2)), post(and(q1, q2)));
		  CSpec specResSimp = `BottomUp(SimpPred()).visitLight(specRes);
		  if(debugFlagStratSeq) {
			  System.out.println("Strategy Seq non-basic: " + 
				  							"\n specRes = " + pretty(specRes) + 
				  							"\n specResSimp = " + pretty(specResSimp) + "\n\n\n"); }
		 // Connector cRes = `Repeat(DeleteSourceSink()).visitLight(`connector(R(ins(i*, i1*, i2*), outs(o*, o1*, o2*)), specResSimp));
		  Connector cRes = `connector(R(ins(i*, i1*, i2*), outs(o*, o1*, o2*)), specResSimp);
		  Connector cRes1 = `BottomUp(Unfold()).visitLight(cRes);
		  Connector cRes2 = `Repeat(SimplifySpec()).visitLight(cRes1);	
		  /* 
		   ** for debugging
		   */
		  if(debugFlagStratSeq) {
		  System.out.println("Strategy Seq non-basic of " + pretty(`c11) + 
				  			"\n and \n" + pretty(`c22) +
				  			"\n is pretty(cRes) = \n" + pretty(cRes) +
				  			"\n and after simp becomes pretty(cRes2) = \n" + pretty(cRes2)  
				  			+ "\n\n\n"); }
		  	  return `connectorList(l1*, cRes2, l2*);					   	
			}		
 	 } 
} 

//make sure you always evaluate from right to left, so no l2*
%strategy Seq1() extends Fail(){ 
  	visit ConnectorList {
  	  connectorList(l1*, c1@channel(t, n@(source|sink)(node(na, sId(sa))), sink(node(nb, sId(sb)))), c2)   	  
  	  && c22@connector(R(ins(i1*, node(nb, _), i2*), outs(o*)), spec) << getNormalised(c2) // && sId(sc) << getFold(s) 
  	  // check that na is not hidden, that is, if na is a source (resp. sink) then there's no sink (resp. source) on the left with the name na    	  
  	  //&& hidden(getNodeType(n), na, l1*) == false  
	  -> { if(debugFlagStratSeq) { 
			  //System.out.println("Strategy Seq spec = " + `spec + " renaming " + `sc + " into " + `sa + " => " + `BottomUp(Rename(sc, sa)).visitLight(`spec));
			    System.out.println("Strategy Seq when sink belongs to a BC with the other end not hidden" + "-------------------- \n\n\n"); }
			  
		  //CSpec specL = `TopDown(Sequence(Rename(sb, sa),EvalConstraints())).visitLight(`constraint(t, sId(sa), sId(sb))); 
		  CSpec specL = `TopDown(EvalConstraints()).visitLight(`constraint(t, sId(sa), sId(sb)));
		  //CSpec specR = `BottomUp(Sequence(Try(EvalConstraints()), Rename(sc, sa))).visitLight(`spec);		  		  		  
		  CSpec specR = `BottomUp(Try(EvalConstraints())).visitLight(`spec);
		  Pred p1, p2, q1, q2;
		  p1 = getPre(specL);
		  q1 = getPost(specL);
		  p2 = getPre(specR);
		  q2 = getPost(specR);
		  // since we can rename, exists p /\ q is satisfied by sa!!     
		  //CSpec specRes = `spec(pre(and(p1, neg(and(q1, neg(p2))))), post(and(q1, q2)));
		  /* take care!!! you took the neg thing out...
		  ** it's ok...
		  ** assuming s and sId(sb) are the same, then p1/\q1;p2 is the same with p1 /\ neg(q1 /\ neg p2)
		  ** which is p1 /\ (neg q1 \/ p2) which is p1 /\ p2 
		  ** unless it can be that the postcond of a connector is false... can it ever be so??
		  */ 
		  CSpec specRes = `spec(pre(and(p1, p2)), post(and(q1, q2)));
		  CSpec specResSimp = `BottomUp(SimpPred()).visitLight(specRes);
		  if(debugFlagStratSeq) { 
			  System.out.println("Strategy Seq: \n specL = " + pretty(specL) + 
				  				"\n specR = " + pretty(specR) + 
				  				"\n specRes = " + pretty(specRes) + 
				  				"\n specResSimp = " + pretty(specResSimp) + "\n\n\n");		  
			
			  System.out.println("Strategy Seq of " + pretty(`c1) + " and " + pretty(`c22) + " = " +  
					  			pretty(`connectorList(l1*, connector(R(ins(node(na, sId(sa)), i1*, i2*), outs(o*)), specResSimp)))
					  			+ "\n\n\n"); }
		 
		  if (getNodeType(`n) == "source") {
			  Connector cRes = `connector(R(ins(node(na, sId(sa)), i1*, i2*), outs(o*)), specResSimp);
			  Connector cRes2 = `Repeat(SimplifySpec()).visitLight(cRes);
			  if(debugFlagStratSeq) { System.out.println("Strategy Seq -> source cRes2 = " + pretty(cRes2)); }
			  return `connectorList(l1*, cRes2);
			  }
		  	else {
		  			Connector cRes = `connector(R(ins(i1*, i2*), outs(node(na, sId(sa)), o*)), specResSimp);
		  			Connector cRes2 = `Repeat(SimplifySpec()).visitLight(cRes);
		  			if(debugFlagStratSeq) { System.out.println("Strategy Seq -> sink cRes2 = " + pretty(cRes2)); }
		  			return `connectorList(l1*, cRes2);
		  		}		   	
			}

  	  connectorList(l1*, c2, c1@channel(t, source(node(na, sId(sa))), n@(source|sink)(node(nb, sId(sb)))), l2*)
  	  && c22@connector(R(ins(i*), outs(o1*, node(na, _), o2*)), spec) << getNormalised(c2) //&& sId(sc) << getFold(s)
  	  //check that nb is not hidden
  	  && hidden(getNodeType(n), nb, l2*) == false 
	-> { 	     	  
		  if(debugFlagStratSeq) { System.out.println("Strategy Seq when source belongs to a BC with the other end not hidden" + "-------------------- \n\n\n"); }
		  CSpec specR = `TopDown(EvalConstraints()).visitLight(`constraint(t, sId(sa), sId(sb))); 
		  CSpec specL = `BottomUp(Try(EvalConstraints())).visitLight(`spec);		  
		  if(debugFlagStratSeq) { System.out.println("Strategy Seq specL = " + specL + " specR = " + specR + "\n\n\n"); }
		  Pred p1, p2, q1, q2;
		  p1 = getPre(specL);
		  q1 = getPost(specL);
		  p2 = getPre(specR);
		  q2 = getPost(specR);
		  /* take care!!! you took the neg thing out...
		  ** it's ok...
		  ** assuming s and sId(sb) are the same, then p1/\q1;p2 is the same with p1 /\ neg(q1 /\ neg p2)
		  ** which is p1 /\ (neg q1 \/ p2) which is p1 /\ p2 
		  ** unless it can be that the postcond of a connector is false... can it ever be so??
		  */ 
		  CSpec specRes = `spec(pre(and(p1, p2)), post(and(q1, q2)));
		  CSpec specResSimp = `BottomUp(SimpPred()).visitLight(specRes);
		  /* 
		   ** for debugging
		   */
		  if(debugFlagStratSeq) {
		  System.out.println("Strategy Seq: \n specL = " + pretty(specL) + 
				  							"\n specR = " + pretty(specR) + 
				  							"\n specRes = " + pretty(specRes) + 
				  							"\n specResSimp = " + pretty(specResSimp) + "\n\n\n");		  
  		   System.out.println("Strategy Seq of " + pretty(`c22) + " and " + pretty(`c1) + " = " +  
						pretty(`connectorList(l1*, connector(R(ins(node(nb, sId(sb)), i*), outs(o1*, o2*)), specResSimp), l2*))
						 + "\n\n\n"); }	
		   if (getNodeType(`n) == "source") {
			   		Connector cRes = `connector(R(ins(node(nb, sId(sb)), i*), outs(o1*, o2*)), specRes);
			   		Connector cRes2 = `Repeat(SimplifySpec()).visitLight(cRes);
		  			if(debugFlagStratSeq) { System.out.println("Strategy Seq <- source cRes2 = " + pretty(cRes2)); }
			   		return `connectorList(l1*, cRes2, l2*);
			   		}
		  	else {
		  			Connector cRes = `connector(R(ins(i*), outs(node(nb, sId(sb)), o1*, o2*)), specRes);
		  			Connector cRes2 = `Repeat(SimplifySpec()).visitLight(cRes);
		  			if(debugFlagStratSeq) { System.out.println("Strategy Seq <- sink cRes2 = " + pretty(cRes2)); }
		  			return `connectorList(l1*, cRes2 , l2*);
		  			}
			}

// seq between source and sink of non-basic connectors 
connectorList(l1*, c1, c2)
  	&& c11@connector(R(ins(i*), outs(o1*, node(nb, _), o2*)), spec1) << getNormalised(c1)
	&& c22@connector(R(ins(i1*, node(nb, _), i2*), outs(o*)), spec2) << getNormalised(c2)  -> {
		  //System.out.println("Strategy Seq non-basic " + "-------------------- \n\n\n");
		  Pred p1, p2, q1, q2;
		  p1 = getPre(`spec1);
		  q1 = getPost(`spec1);
		  p2 = getPre(`spec2);
		  q2 = getPost(`spec2);
		  CSpec specRes = `spec(pre(and(p1, p2)), post(and(q1, q2)));
		  CSpec specResSimp = `BottomUp(SimpPred()).visitLight(specRes);
		  if(debugFlagStratSeq) {
			  System.out.println("Strategy Seq non-basic: " + 
				  							"\n specRes = " + pretty(specRes) + 
				  							"\n specResSimp = " + pretty(specResSimp) + "\n\n\n"); }
		 // Connector cRes = `Repeat(DeleteSourceSink()).visitLight(`connector(R(ins(i*, i1*, i2*), outs(o*, o1*, o2*)), specResSimp));
		  Connector cRes = `connector(R(ins(i*, i1*, i2*), outs(o*, o1*, o2*)), specResSimp);
		  Connector cRes1 = `BottomUp(Unfold()).visitLight(cRes);
		  Connector cRes2 = `Repeat(SimplifySpec()).visitLight(cRes1);	
		  /* 
		   ** for debugging
		   */
		  if(debugFlagStratSeq) {
		  System.out.println("Strategy Seq non-basic of " + pretty(`c11) + 
				  			"\n and \n" + pretty(`c22) +
				  			"\n is pretty(cRes) = \n" + pretty(cRes) +
				  			"\n and after simp becomes pretty(cRes2) = \n" + pretty(cRes2)  
				  			+ "\n\n\n"); }
		  	  return `connectorList(l1*, cRes2);					   	
			}		
 	 } 
} 

%strategy Merge() extends Fail() {
  	visit ConnectorList {
  	  connectorList(l1*, c1, l2*, c2, l3*) 
  	  && c11@connector(R(ins(i1), outs(o11*, node(nb, sb1), o12*)), spec1) << getNormalised(c1)
  	  && c22@connector(R(ins(i2), outs(o21*, node(nb, sb2), o22*)), spec2) << getNormalised(c2) -> {
  		  if(debugFlagStratMerge) {
  			  System.out.println("Strategy Merge of c1 " + getNormalised(`c1) + " and c2 " + getNormalised(`c2) + "-------------------- \n\n\n"); }
  		  Pred p1, p2, q1, q2 , p3, p4, q3, q4, q11, q21, q12, q22, q13, q23;
  		  CSpec spec1 = `Try(TopDown(EvalConstraints())).visitLight(`spec1);
  		  CSpec spec2 = `Try(TopDown(EvalConstraints())).visitLight(`spec2);
		  p1 = getPre(spec1);
		  //what should we do with the sbformulas that contain sb1 or sb2??
		  q1 = getPost(spec1); 
		  p2 = getPre(spec2);
		  q2 = getPost(spec2);		  
		  StreamId newsb = `sId("s" + nb);
		  //StreamId beta1 = getStreamPair(`c11, `sb1);
		  //StreamId beta2 = getStreamPair(`c22, `sb2);
		  StreamId beta1, beta2;
		  // normally i should replace only if the names are different, i.e., if(sb1 == sb2), but for the moment i always replace. 
		  // do the check later for efficiency  
		  beta1 = `sId("s" + nb + "1"); beta2 = `sId("s" + nb + "2");  
		  if (beta1 != null && beta2 != null) {
			  q11 = `BottomUp(Rename(getTimeName(getUnfold(sb1)), "t" + nb + "1")).visitLight(q1);
			  if(debugFlagStratMerge) { 
				  System.out.println("merge q1 = " + q1 + " has time of sb1 = " + getTimeName(getUnfold(`sb1)) + " q11 = " + q11); }
			  q12 = `BottomUp(Rename(getDataName(getUnfold(sb1)), "d" + nb + "1")).visitLight(q11);
			  q21 = `BottomUp(Rename(getTimeName(getUnfold(sb2)), "t" + nb + "2")).visitLight(q2);
			  q22 = `BottomUp(Rename(getDataName(getUnfold(sb2)), "d" + nb + "2")).visitLight(q21);
			  q13 = `BottomUp(Rename(stream2String(sb1), "s" + nb + "1")).visitLight(q12);
			  q23 = `BottomUp(Rename(stream2String(sb2), "s" + nb + "2")).visitLight(q22);
			  q3 = `Repeat(And2AndL()).visitLight(`andL(D(newsb), D(beta1), D(beta2), q13, q23, merged(beta1, beta2, newsb)));
			  //System.out.println("q3 = " + q3);
			  q4 = `Repeat(DeleteDuplic()).visitLight(q3);		   
			  CSpec specRes = `spec(pre(and(p1, p2)), post(q4));
			  		   
			  Connector cRes = `connector(R(ins(i1, i2), outs(node(nb, newsb), o11*, o12*, o21*, o22*)), specRes);
			  
			  //Connector cRes2 = `Sequence(SimplifySpec(),SimplifySpec()).visitLight(cRes);
			  Connector cRes2 = `Repeat(SimplifySpec()).visitLight(cRes);
			  /* 
			   ** for debugging
		      */
		      if(debugFlagStratMerge) {
			  System.out.println("Merge test simplifySpec for cRes = " + cRes + " is \n " + cRes2 + "\n\n");
			  
			  System.out.println("Strategy Merge:\n " + pretty(`c11) + " \n with \n " + pretty(`c22) + " \n => \n " +  
						pretty(`connectorList(l1*, cRes2, l2*, l3*))  	
						+ "\n\n\n"); }
						
			  return `connectorList(l1*, cRes2, l2*, l3*); }
		  else {
			  System.out.println("Strategy Merge [error] beta1 or beta2 is null");
			  return null; }	
		   }
  	 } 
}

%strategy Replicate() extends Fail() {
  	visit ConnectorList {
  	  connectorList(l1*, c1, l2*, c2, l3*) 
  	  && c11@connector(R(ins(i11*, node(nb, sb1), i12*), outs(o1*)), spec1) << getNormalised(c1)
  	  && c22@connector(R(ins(i21*, node(nb, sb2), i22*), outs(o2*)), spec2) << getNormalised(c2) -> {
  		 // System.out.println("Strategy Replicate of c1 " + getNormalised(`c1) + " and c2 " + getNormalised(`c2) + "-------------------- \n\n\n");
  		  String s = "s" + `nb;
		  StreamId newsb = `sId(s);
  		  Pred p1, p2, q1, q2, p3, q3, p4;
  		  CSpec spec1 = `BottomUp(Sequence(Try(EvalConstraints()), Rename(stream2String(sb1), s))).visitLight(`spec1);
  		  CSpec spec2 = `BottomUp(Sequence(Try(EvalConstraints()), Rename(stream2String(sb2), s))).visitLight(`spec2);
		  p1 = getPre(spec1);
		  q1 = getPost(spec1); 
		  p2 = getPre(spec2);
		  q2 = getPost(spec2);		  
		  p3 = `Repeat(And2AndL()).visitLight(`andL(p2, p1));
		  p4 = `Repeat(DeleteDuplic()).visitLight(p3);
		  //System.out.println("Strategy Replicate: p3 = " + p3 + " p4 = " + p4); 
		  CSpec specRes = `spec(pre(p4), post(and(q1, q2)));
		  //CSpec specRes = `spec(pre(and(p2, p1)), post(and(q1, q2)));		 		  		  
		   Connector cRes = `connector(R(ins(node(nb, newsb), i11*, i12*, i21*, i22*), outs(o1*, o2*)), specRes);
		   Connector cRes2 = `Repeat(SimplifySpec()).visitLight(cRes);
		   /* 
		   ** for debugging
		   */
		   if(debugFlagStratRep) {
		   System.out.println("Strategy Replicate:\n " + pretty(`c11) + " \n and \n " + pretty(`c22) + " \n => \n " +
				  pretty(`connectorList(l1*, cRes2, l2*, l3*))
				  	+ "\n\n\n"); }
		   
		   return `connectorList(l1*, cRes2, l2*, l3*);
		   }
  	 } 
}

/****************************************************************************************/
/*                               FCTIONS USING STRATEGIES                               */   
/****************************************************************************************/

public static CSpec evalConstraints(CSpec spec){
	try{
		spec =  `Sequence(BottomUp(Fold()),EvalConstraints()).visitLight(spec);
		spec =  `EvalConstraints().visitLight(spec);
		//System.out.println("evalConstraints: evaluated = " + spec + " and getPre = " + getPre(spec) + "\n\n\n");
	} catch (VisitFailure e) { System.out.println("evalConstraints: strategy failed"); }
return spec;
}

//the corresponding functions adapted to work for 2 connectors as params
public static Connector merge(Connector c1, Connector c2){
Connector cRes;
try{
cRes = getConnector(`Merge().visitLight(`connectorList(c1, c2))); return cRes;
}catch(VisitFailure e) {System.out.println("merge: strategy failed. Return null!"); return null;}
}

//the recursive variant
public static ConnectorList mergeRec(ConnectorList cl){
ConnectorList cRes;
try{
cRes = `BottomUp(Repeat(Merge())).visitLight(cl); return cRes;
}catch(VisitFailure e) {System.out.println("mergeRec: strategy failed"); return null;}
}

public static Connector seq(Connector c1, Connector c2){
Connector cRes;
try{
cRes = getConnector(`Seq().visitLight(`connectorList(c1, c2))); return cRes;
}catch(VisitFailure e) {System.out.println("seq: strategy failed"); return null;}
}

//the recursive variant
public static ConnectorList seqRec(ConnectorList cl){
ConnectorList cRes;
try{
cRes = `BottomUp(Repeat(Seq())).visitLight(cl); return cRes;
}catch(VisitFailure e) {System.out.println("seqRec: strategy failed"); return null;}
}

public static Connector replicate(Connector c1, Connector c2){
Connector cRes;
try{
cRes = getConnector(`Replicate().visitLight(`connectorList(c1, c2))); return cRes;
}catch(VisitFailure e) {System.out.println("replicate: strategy failed"); return null;}
}

//the recursive variant
public static ConnectorList replicateRec(ConnectorList cl){
ConnectorList cRes;
try{
cRes = `BottomUp(Repeat(Replicate())).visitLight(cl); return cRes;
}catch(VisitFailure e) {System.out.println("replicateRec: strategy failed"); return null;}
}

//Predefined connectors
public static Connector getAlternator(ConnectorList la){
Connector alternator;
try{
	alternator = getConnector(`Repeat(Choice(Merge(), Replicate())).visitLight(la));
	if(alternator != null) { System.out.println("getAlternator: pretty(alternator) = \n " + pretty(alternator) + "\n\n\n"); return alternator;}		 
	else { System.out.println("getAlternator: alternator is null " + "\n\n\n"); return null;}
} catch (VisitFailure e) { System.out.println("getAlternator: strategy failed"); return null;}
}

public static Connector getExclusiveRouter(ConnectorList cl){
try {
	Connector excR = getConnector(`Outermost(Choice(Replicate(), Choice(Merge(), Choice(Seq(), FlattenCL())))).visitLight(cl));
	if(excR != null) { System.out.println("getExclusiveRouter: pretty(excR) = " + pretty(excR) + "\n\n\n"); return excR;}
	else { System.out.println("getExclusiveRouter: getConnector returned null!! Error." + "\n\n\n"); return null;}
} catch (VisitFailure e) { System.out.println("getExclusiveRouter: strategy failed"); return null;}
}

//try to get the connector after applying all compositions
//seq has the lowest priority
public static ConnectorList fixpoint(ConnectorList cl){
try{
	cl = `Repeat(Choice(Merge(), Replicate())).visitLight(cl);
	System.out.println("fixpoint: cl after merge+rep = " + cl); //pretty(cl));
	cl = `Repeat(Seq1()).visitLight(cl);
	//cl = `Seq1().visitLight(cl);
	System.out.println("fixpoint: cl after seq = " + pretty(cl));
} catch (VisitFailure e) { System.out.println("fixpoint: strategy failed"); }
return cl;
}

//end class
}
