import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.security.acl.LastOwnerException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Scanner;

//import java.util.regex.Pattern;

public class ZParser {
	// public ArrayList<Node[]> stats = new ArrayList<Node[]>();
	public Node[] yo = new Node[2];
	int x = yo.length;
	private static String lastLine;
	private static String beforeLastLine;
	private static String beforebeforeLastLine;

	public static String getLastLine() {
		return lastLine;
	}

	public void setLastLine(String lastLine) {
		ZParser.lastLine = lastLine;
	}

	public static String getBeforeLastLine() {
		return beforeLastLine;
	}

	public void setBeforeLastLine(String lastLine) {
		ZParser.beforeLastLine = lastLine;
	}

	public ZParser() {

	}

	public static void setData() throws Exception {
//		File file = new File("sol.txt");
		File file = new File("consOut.txt");
		Scanner input = new Scanner(file);
		String dataLine = "";
		dataLine = input.nextLine();
		String lastLine = "";

		while (input.hasNext()) {
			dataLine = input.nextLine();
			if (dataLine.length() > 0) {
				if (dataLine.charAt(0) == "=".charAt(0)) {
					dataLine = input.nextLine();
					if (dataLine.charAt(0) == "c".charAt(0)) {
						Frame.setConfl();
						Frame.showGraph();

					} else if (dataLine.charAt(0) == "n".charAt(0)) {
						Frame.setNotConfl();
						String noOfCP = dataLine.substring(1);
						Frame.setCP(noOfCP);
						Frame.showGraph();

					} else {
						Frame.setError("error have occured!");
					}

				}

			}
			lastLine = dataLine;

		}
		Frame.showGraph();
		Frame.refresh();
		System.out.println("last line in setData: " + lastLine);
	}
	
	
	public static void createSol() throws Exception {
		lastLine = "";
		beforeLastLine = "";
		beforebeforeLastLine = "";
		int counter = 1;
		String line = "";
//		File file = new File("sol.txt");
		File file = new File("consOut.txt");
		Scanner input = new Scanner(file);
		
		while (counter < 4) {
			line = input.nextLine();
			counter++;
		}
		
		while (input.hasNext()) {
			line = input.nextLine();
			String read;

			BufferedWriter out = new BufferedWriter(new FileWriter(
					"solClean.txt"));

			while (input.hasNext()) {

				read = line.replace("'", "");
				out.write(read);
				out.newLine();
				beforebeforeLastLine = beforeLastLine;
				beforeLastLine = lastLine;
				lastLine = line;
				line = input.nextLine();

			}
			out.close();
			// input.close();
		}
		System.out.println(beforeLastLine);
		Proba.start2();
//		ZParser.cleanFile();
		
	}
	
	

	public static void cleanFile() throws Exception {
		lastLine = "";
		beforeLastLine = "";
		beforebeforeLastLine = "";
		File file = new File("sol.txt");
//		File file = new File("consOut.txt");
		Scanner input = new Scanner(file);
		while (input.hasNext()) {
			String line = input.nextLine();
			String read;

			BufferedWriter out = new BufferedWriter(new FileWriter(
					"solClean.txt"));

			while (input.hasNext()) {

				read = line.replace("'", "");
				out.write(read);
				out.newLine();
				beforebeforeLastLine = beforeLastLine;
				beforeLastLine = lastLine;
				lastLine = line;
				line = input.nextLine();

			}
			out.close();
			// input.close();
		}
		System.out.println(beforeLastLine);
		Proba.start2();
	}

	// public static void replaceSelected(String replaceWith, String type) {
	// try {
	// // input the file content to the String "input"
	// BufferedReader file = new BufferedReader(new FileReader("notes.txt"));
	// String line;String input = "";
	//
	// while ((line = file.readLine()) != null) input += line + '\n';
	//
	// file.close();
	//
	// System.out.println(input); // check that it's inputted right
	//
	// // this if structure determines whether or not to replace "0" or "1"
	// if (Integer.parseInt(type) == 0) {
	// input = input.replace(replaceWith + "1", replaceWith + "0");
	// }
	// else if (Integer.parseInt(type) == 1) {
	// input = input.replace(replaceWith + "0", replaceWith + "1");
	// }
	//
	// // check if the new input is right
	// System.out.println("----------------------------------" + '\n' + input);
	//
	// // write the new String with the replaced line OVER the same file
	// FileOutputStream fileOut = new FileOutputStream("notes.txt");
	// fileOut.write(input.getBytes());
	// fileOut.close();
	//
	// } catch (Exception e) {
	// System.out.println("Problem reading file.");
	// }
	// }

	public static void main(String[] args) throws Exception {
		// Node[] yo = new Node[2];
		// int x = yo.length;
		// System.out.println(x);
		// ArrayList<Node[]> stats = new ArrayList<Node[]>();
		ArrayList<String> graph = new ArrayList<String>();
		// stats.add(new Node[2]);
		// int y = stats.get(0).toString();
		// System.out.println(stats.get(0).toString());

		HashMap<Integer, String> nodes = new HashMap<Integer, String>();
		File file = new File("g4.gv");
		Scanner input = new Scanner(file);
		String line = input.nextLine();
		line = input.nextLine();

		// line = input.nextLine();
		// System.out.println(input.toString());
		// System.out.println(nextLine);
		// input.findInLine("->");
		// if (input.hasNext("")) {
		// input.nextLine();
		// }
		while (input.hasNext()) {
			// String nextToken = input.next();
			// or to process line by line
			// line = input.nextLine();
			while (line.length() == 0) {
				line = input.nextLine();
			}
			// if (graph.contains(line)) {
			// // line = input.nextLine();
			// System.out.println("8888888888888888888");
			// } else {
			// graph.add(line);
			// }

			// while (line.length() == 0) {
			// line = input.nextLine();
			// }

			if (line.length() > 0) {
				System.out.println(line);
				// System.out.println(nextLine);
				// System.out.println("====================");
				if (line.charAt(0) == "\"".charAt(0)) {
					System.out.println("-----------------");
				}

				// String tempLine = line;
				// String[] parts = line.split(Pattern.quote("->"));
				String[] parts = line.split("->", 2);
				String part1 = parts[0];
				part1 = line.substring(0, part1.length() - 1);
				// String part2 = parts[1];
				System.out.println("part1: " + part1 + " of length "
						+ part1.length());
				String part2 = line.substring(part1.length() + 4,
						line.length() - 2);
				// part2.substring(4);

				// System.out.println("Part2: " + part2 + " of length "
				// + part2.length());

				if (part2.charAt(0) == "{".charAt(0)) {
					// System.out.println("heyyy yoozzz");
					part2 = part2.substring(2);
					// System.out.println(part2);
					// String[] partsAgain =
					// part2.split(Pattern.quote("\" \""));
					String[] partsAgain = part2.split("\" \"", 2);
					String subPart21 = partsAgain[0];
					System.out.println("1st of part 2: " + subPart21
							+ " of length " + subPart21.length());
					String subPart22 = partsAgain[1];
					System.out.println("2nd of part 2: " + subPart22
							+ " of length " + subPart22.length());

					String temp1 = part1 + " -> " + subPart21 + "\"";
					System.out.println(temp1 + " of length " + temp1.length());

					String temp2 = part1 + " -> " + "\"" + subPart22;

					System.out.println(temp2 + " of length " + temp2.length());
					//
					//
					// System.out.println("temp1 length: " + temp1.length());
					//
					// System.out.println("test full line2: " + part2 + " -> "
					// + "\"" + subPart22);
					if (!graph.contains(temp1)) {
						// line = input.nextLine();
						// System.out.println("8888888888888888888");
						// } else {
						graph.add(temp1);
					}
					if (!graph.contains(temp2)) {
						// line = input.nextLine();
						// System.out.println("8888888888888888888");
						// } else {
						graph.add(temp2);
					}

				} else {
					String temp3 = part1 + " -> " + part2;
					System.out.println(temp3 + " of length " + temp3.length());
					// System.out.println("part2: " + part2 + " of length "
					// + part2.length());
					// System.out.println("test mini line: " + part1 + " -> "
					// + part2);
					if (!graph.contains(temp3)) {
						// line = input.nextLine();
						// System.out.println("8888888888888888888");
						// } else {
						graph.add(temp3);
					}
				}
			}
			System.out.println("line: " + line);
			// String temp = input.nextLine();
			// System.out.println("temp: " + temp);

			if (line == input.nextLine()) {
				// System.out.println("this is duplicate!");
				// line = input.nextLine();
				line = input.nextLine();
				line = input.nextLine();
			} else {
				// System.out.println("this is NOT duplicate!"
				// + "length of temp: " + temp.length());
				line = input.nextLine();
			}

			while (line.length() == 0) {
				line = input.nextLine();
			}

		}

		input.close();
		int[] a = { 1, 2, 3, 4 };
		nodes.put(100, "yo1");

		nodes.put(100, "yo2");
		nodes.put(101, "red");
		nodes.put(102, "blue");
		nodes.put(100, "yo1");
		// nodes.put(nodes.get, value);
		for (Map.Entry m : nodes.entrySet()) {
			System.out.println(m.getKey() + " " + m.getValue());
		}
		System.out.println(nodes.containsKey(102));
		System.out.println(nodes.containsValue("blue"));
		System.out.println(nodes.get(101));
		System.out.println(nodes.size());
		System.out.println(nodes.values());

		System.out.println("size of graph ArrayList: " + graph.size());
		// System.out.println(graph.toString());
		Node[][] stats = makeStats(graph);
		statsLevels(stats);
		System.out.println("number of edges: " + stats.length);
		// stats[0][1].setName("[ b ]");
		// stats[8][1].setName("[ b ]");

		if (stats[2][1].getName() == stats[3][1].getName()) {
			System.out.println("the same" + stats[0][1].getName()
					+ stats[8][0].getName());
		} else {
			System.out.println("problema!!" + stats[0][1].getName()
					+ stats[8][0].getName());
		}

		System.out.println(stats[1][1].getName().charAt(3) == stats[8][0]
				.getName().charAt(3));

		// System.out.flush();
		// Runtime.getRuntime().exec("clear");
		System.out.println("testtssss");

	}

	public static Node[][] makeStats(ArrayList<String> graph) {
		Node[][] stats = new Node[graph.size()][2];
		System.out.println(stats[0].length);
		System.out.println(stats.length);
		for (int i = 0; i < graph.size(); i++) {

			System.out.println("=============");
			// String[] edge = graph.get(i).split(Pattern.quote(" -> "));
			String[] edge = graph.get(i).split(" -> ", 2);
			System.out.println(edge[0]);
			System.out.println(edge[1]);
			Node a = new Node(edge[0], 0);
			Node b = new Node(edge[1], 1);
			stats[i][0] = a;
			stats[i][1] = b;
			// stats[i][0].setName(edge[0]);
			// stats[i][0].setValue(1);
			// stats[i][1].setName(edge[1]);
			// stats[i][1].setValue(1);
			System.out.println("=============");
			// System.out.println(graph.get(i));
		}
		System.out.println("this is a test");
		// System.out.println(graph.toString());
		System.out.println("===================================");
		for (int i = 0; i < stats.length; i++) {
			System.out.print(stats[i][0].getName() + " "
					+ stats[i][0].getValue() + " " + stats[i][0].isNoChild()
					+ " " + stats[i][0].isSingleParent() + " --- ");
			System.out.println(stats[i][1].getName() + " "
					+ stats[i][1].getValue() + " " + stats[i][1].isNoChild()
					+ " " + stats[i][1].isSingleParent());
		}
		return stats;
	}

	public static void statsLevels(Node[][] graph) {
		for (int i = 0; i < graph.length; i++) {
			int counter = 0;
			String temp = "";
			for (int j = 0; j < graph.length; j++) {
				if (graph[i][1].getName() == graph[j][1].getName()) {
					System.out.println("this child " + graph[i][1].getName()
							+ " has parent");
					// graph[i][1].setSingleParent(false);
					counter++;
					temp = graph[i][1].getName();
				} else {
					// graph[i][1].setSingleParent(true);
				}

				if (graph[j][1].getName() == graph[i][0].getName()) {
					System.out.println("this child " + graph[i][1].getName()
							+ "is a parent");
				}

			}
			if (counter > 1) {
				graph[i][1].setSingleParent(false);
			}
			System.out.println(temp + " has " + counter + " parent(s)");
		}

	}

}
