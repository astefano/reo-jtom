package reospec;

import reospec.stream.types.*;

public class StreamFunctions{
%include{stream/Stream.tom}

public static DataSeq getData(Stream s) {
	%match(s) { stream(x,_) -> { return `x; } }
return null;
}

public static TimeSeq getTime(Stream s) {
	%match(s) { stream(_,y) -> { return `y; } }
return null;
}

public static void main(String[] args) {
	Stream s = `stream(data("s", "r"), time(1, 2));
	System.out.println("StreamTest getData = " + getData(s));	
}

}