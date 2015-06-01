import java.io.File;

public class Proba {
	public static void main(String[] args) throws Exception {
		Proba p = new Proba();
		p.start2();
		// p.start2();
	}

	/**
	 * Construct a DOT graph in memory, convert it to image and store the image
	 * in the file system.
	 */
	static void start() {
		GraphViz gv = new GraphViz();
		gv.addln(gv.start_graph());
		gv.addln("A -> B;");
		gv.addln("A -> C;");
		gv.addln("A -> D;");
		gv.addln(gv.end_graph());
		System.out.println(gv.getDotSource());

		// String type = "gif";
		// String type = "dot";
		// String type = "fig"; // open with xfig
		// String type = "pdf";
		// String type = "ps";
		// String type = "svg"; // open with inkscape
		String type = "png";
		// String type = "plain";
		// File out = new File("/tmp/out." + type); // Linux
		File out = new File("out." + type); // Mac
		// File out = new File("c:/eclipse.ws/graphviz-java-api/out." + type);
		// // Windows
		gv.writeGraphToFile(gv.getGraph(gv.getDotSource(), type), out);
	}

	/**
	 * Read the DOT source from a file, convert to image and store the image in
	 * the file system.
	 * 
	 * @throws Exception
	 */
	static void start2() throws Exception {
		// String dir = "/home/jabba/eclipse2/laszlo.sajat/graphviz-java-api";
		// // Linux
		// String input = dir + "/sample/simple.dot";
		// String input = "sample/simple.dot";
		String input = "solClean.txt";
		// String input = "c:/eclipse.ws/graphviz-java-api/sample/simple.dot";
		// // Windows

		GraphViz gv = new GraphViz();
		gv.readSource(input);
		System.out.println(gv.getDotSource());

		// String type = "gif";
		// String type = "dot";
		// String type = "fig"; // open with xfig
		// String type = "pdf";
		// String type = "ps";
		// String type = "svg"; // open with inkscape
		String type = "png";
		// String type = "plain";
		File out = new File("out1." + type); // Linux
		// File out = new File("c:/eclipse.ws/graphviz-java-api/tmp/simple." +
		// type); // Windows
		gv.writeGraphToFile(gv.getGraph(gv.getDotSource(), type), out);
//		String lastLine = ZParser.getLastLine();
		// if (lastLine.charAt(0) == "c".charAt(0)) {
		ZParser.setData();
		// if (true) {
		// Frame.setConfl();
		// Frame.showGraph();
		//
		// } else {
		// Frame.setNotConfl();
		// // Frame.setCP(lastLine.substring(1));
		// Frame.setCP("5");
		// Frame.showGraph();
		//
		// }

		// System.out.println("before last line: " +
		// ZParser.getBeforeLastLine());
		// System.out.println("last line: " + ZParser.getLastLine());

	}
}
