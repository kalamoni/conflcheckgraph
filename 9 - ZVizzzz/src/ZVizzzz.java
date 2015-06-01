import java.io.File;
import java.io.FileOutputStream;
import java.io.PrintStream;

import javax.swing.UIManager;

import jpl.*;

public class ZVizzzz {

	public static void main(String[] args) throws Exception {
		File file = new File("consoleOutput.txt"); // Your file
		FileOutputStream fos = new FileOutputStream(file);
		PrintStream ps = new PrintStream(fos);
		System.setOut(ps); // comment to set the output back to console
		System.setErr(ps); // comment to set the output back to console

		// ==========================================================================================

		// GUIFrame frame = new GUIFrame(
		// "Visual Confluence Checkers for CHR Solvers");
		
		Frame frame = new Frame();

		// ==========================================================================================
		// String path = frame.returnPath();
		// System.out.println(path);

		// conflcheck
		// test
		// Query q1 = new Query("consult",
		// new Term[] { new Atom("conflcheck.pl") });
		// System.out.println(q1.query());
		//
		// Query q2 = new Query("check_confluence",
		// new Term[] { new Atom("p4.pl") });
		// String x = q2.allSolutions().toString().toString();
		// String y = x;
		// System.out.println("before y");
		// System.out.println(y);
		// System.out.println("after y");
		// // System.out.println(q2.getSolution().toString());
		//
		// System.out.println(q2.toString());
		// Invoke a predicate
		// Query q2 = new Query("check_confluence", new Term )

		// ==========================================================================================

		// creating a query to consult the prolog program
		// if
		// (!Query.hasSolution("consult('/Users/kalamoni/Desktop/test.pl').")) {
	}

	public static void consult(String str) throws Exception {
		// File file = new File("consoooo.txt"); // Your file
		// FileOutputStream fos = new FileOutputStream(file);
		// PrintStream ps = new PrintStream(fos);
		// System.setOut(ps);
		// System.setErr(ps);

		if (!Query.hasSolution("consult('checktool/conflcheck.pl').")) {
			System.out.println("Consult failed");
		} else {
			Query q3 = new Query(new Compound("check_confluence",
					new Term[] { new Atom(str) }));
			// test3a("ria");
			// run("p4.pl");
			// System.out.println("before");
			System.out.println(q3.oneSolution().toString());
			// System.out.println(q3.allSolutions().toString() + " yoyo");
			// String sol = run(str);
			// System.out.println("yo1" + "yo2");

		}
		
//		ZParser.cleanFile();
		ZParser.createSol();
		
		
		
		// System.out.println(ZParser.getBeforeLastLine());
		// System.out.println(ZParser.getLastLine());
	}

	// static void run(String sent) throws Exception {
	// File file = new File("consoleOutput-final.txt"); // Your file
	// FileOutputStream fos = new FileOutputStream(file);
	// PrintStream ps = new PrintStream(fos);
	// System.setOut(ps); // comment to set the output back to concolse
	//
	// // a variable which will get the output.
	// // Variable X = new Variable("X");
	// // creating query object to make a query to prolog code.
	// // Query q3 = new Query("parent",new Term[] { X, new Atom(sent) });
	// // Query q3 = new Query("check_confluence", new Term[] { new Atom(sent)
	// // });
	// String q3 = new Query("check_confluence", new Term[] { new Atom(sent) })
	// .toString();
	// // System.out.println("Parent of " + sent + " is "
	// // + q3.oneSolution().get("X"));// get the value stored in X
	// // System.out.println(q3.oneSolution().toString());
	// // return q3.oneSolution().toString();
	// // q3.getSolution()
	// // q3.oneSolution
	// }

}
