import java.awt.Color;
import java.awt.Font;
import java.awt.Image;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import javax.imageio.ImageIO;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.UIManager;

public class Frame extends JFrame implements MouseListener {
	private static JFrame frame;
	private JLabel turn;
	private JLabel path;
	private JLabel confl1;
	private static JLabel confl2;
	private JLabel cp1;
	private JLabel cp2;
	private static JLabel cp3;
	private JButton consult;
	private JButton exit;
	private JButton browse;
	private static JLabel graph;

	public String returnPath() {
		return this.turn.getText();
	}

	public Frame() throws Exception {
		// UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
		// UIManager.setLookAndFeel(UIManager
		// .getCrossPlatformLookAndFeelClassName());

		frame = new JFrame("Visual Confluence Checkers for CHR Solvers");
		frame.setSize(900, 670);
		frame.setLocationRelativeTo(null);
		frame.setVisible(true);
		frame.setLayout(null);
		frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		frame.setBackground(Color.WHITE);
		frame.setResizable(false);
		// JPanel pStart = new JPanel();
		// pStart.setSize(700, 700);
		// frame.setVisible(false);
		// Font f18 = new Font("Helvetica Neue", Font.PLAIN, 18);
		Font f18b = new Font("Helvetica Neue", Font.BOLD, 18);
		Font f20b = new Font("Helvetica Neue", Font.BOLD, 20);
		Font f16 = new Font("Helvetica Neue", Font.PLAIN, 16);
		// Font f14 = new Font("Helvetica Neue", Font.PLAIN, 14);
		Font f14b = new Font("Helvetica Neue", Font.BOLD, 14);
		// Font f12 = new Font("Helvetica Neue", Font.PLAIN, 12);
		// Font f12b = new Font("Helvetica Neue", Font.BOLD, 12);
		// frame.setFont(f);

		ImageIcon icon = new ImageIcon("chr.png");
		JLabel thumb = new JLabel();
		thumb.setBounds(660, 470, 160, 160);
		thumb.setIcon(icon);
		frame.getContentPane().add(thumb);

		ImageIcon dotGraph = new ImageIcon("out1.png");
		graph = new JLabel();
		graph.setBounds(50, 115, 500, 500);
		graph.setIcon(dotGraph);
		graph.setBackground(Color.WHITE);
		graph.setOpaque(true);
		graph.setVisible(false);
		graph.setHorizontalAlignment(JLabel.CENTER);
		graph.setVerticalAlignment(JLabel.CENTER);
		frame.getContentPane().add(graph);
		// String h = Integer.toString(dotGraph.getIconHeight());
		// String w = Integer.toString(dotGraph.getIconWidth());

		path = new JLabel();
		path.setBounds(40, 30, 300, 40);
		path.setText("Path for CHR program:");
		// path.setForeground(Color.BLACK);
		path.setForeground(Color.BLACK);
		frame.getContentPane().add(path);
		path.setFont(f18b);

		turn = new JLabel();
		turn.setBounds(40, 60, 550, 40);
		turn.setText("No file selected.");
		turn.setForeground(Color.BLACK);
		frame.getContentPane().add(turn);
		turn.setFont(f16);
		// turn.setBackground(Color.black);
		// turn.setOpaque(true);

		confl1 = new JLabel();
		confl1.setBounds(650, 70, 300, 180);
		confl1.setText("This program is:");
		confl1.setForeground(Color.BLACK);
		frame.getContentPane().add(confl1);
		confl1.setFont(f14b);

		confl2 = new JLabel();
		confl2.setBounds(650, 90, 300, 180);
		confl2.setText("");
		confl2.setForeground(Color.BLACK);
		confl2.setFont(f20b);
		frame.getContentPane().add(confl2);

		cp1 = new JLabel();
		cp1.setBounds(650, 140, 300, 180);
		cp1.setText("Number of non-joinable");
		cp1.setForeground(Color.BLACK);
		cp1.setFont(f14b);
		frame.getContentPane().add(cp1);

		cp2 = new JLabel();
		cp2.setBounds(650, 160, 300, 180);
		cp2.setText("critical pairs:");
		cp2.setForeground(Color.BLACK);
		cp2.setFont(f14b);
		frame.getContentPane().add(cp2);

		cp3 = new JLabel();
		cp3.setBounds(650, 180, 300, 180);
		cp3.setText("");
		cp3.setForeground(Color.BLACK);
		cp3.setFont(f20b);
		frame.getContentPane().add(cp3);

		consult = new JButton("Consult Program");
		consult.setBounds(640, 80, 200, 50);
		this.consult.addMouseListener(this);
		consult.setToolTipText("Consult the program and draw graph.");
		consult.setFont(f14b);
		frame.getContentPane().add(consult);

		browse = new JButton("Browse");
		browse.setBounds(640, 350, 200, 50);
		this.browse.addMouseListener(this);
		browse.setToolTipText("Choose your program.");
		browse.setFont(f14b);
		frame.getContentPane().add(browse);

		exit = new JButton("Exit");
		exit.setBounds(640, 410, 200, 50);
		this.exit.addMouseListener(this);
		exit.setToolTipText("Close and exit the tool.");
		exit.setFont(f14b);
		frame.getContentPane().add(exit);

		frame.revalidate();
		frame.repaint();

	}

	public void actionPerformed(ActionEvent arg0) {

	}

	public void mouseClicked(MouseEvent e) {
		if (e.getSource() == browse) {
			JFileChooser fileChooser = new JFileChooser();
			fileChooser.setCurrentDirectory(new File(System
					.getProperty("user.home")));
			int result = fileChooser.showOpenDialog(exit);
			if (result == JFileChooser.APPROVE_OPTION) {
				File selectedFile = fileChooser.getSelectedFile();
				turn.setText(selectedFile.getAbsolutePath());
				// System.out.println("Selected file: "
				// + selectedFile.getAbsolutePath());
			}

			// pStart.setVisible(false);
			// pGame.setVisible(true);
		} else if (e.getSource() == this.exit) {
			System.exit(0);
		} else if (e.getSource() == this.consult) {
			String str = turn.getText();
			try {
				// hideGraph();
//				File file = new File("consOut.txt");
//				 File oldFile = new File("consOut.txt");
//				 oldFile.delete();
//				 File newFile = new File("consOut.txt");
//				 newFile.createNewFile();
				FileWriter fstreamWrite = new FileWriter("consOut.txt");
	            BufferedWriter out = new BufferedWriter(fstreamWrite);
	            out.write("");
	            out.close();
                
				ZVizzzz.consult(str);
				
				
				
				// ZParser.setData();
				// ZParser.cleanFile();
				// Proba.start2();
			} catch (Exception e1) {
				// TODO Auto-generated catch block
				e1.toString();
				e1.printStackTrace();
			}
		}

	}

	@Override
	public void mousePressed(MouseEvent e) {
		// TODO Auto-generated method stub

	}

	@Override
	public void mouseReleased(MouseEvent e) {
		// TODO Auto-generated method stub

	}

	@Override
	public void mouseEntered(MouseEvent e) {
		// TODO Auto-generated method stub

	}

	@Override
	public void mouseExited(MouseEvent e) {
		// TODO Auto-generated method stub

	}

	public static void setConfl() {
		confl2.setText("Confluent!");
		confl2.setForeground(new Color(0, 205, 0));
		cp3.setText("0");
		cp3.setForeground(new Color(0, 205, 0));
	}

	public static void setNotConfl() {
		confl2.setText("Not confluent!");
		confl2.setForeground(Color.red);
		cp3.setForeground(Color.red);
	}

	public static void setCP(String str) {
		cp3.setText(str);
	}

	public static void showGraph() {
		frame.remove(graph);
		frame.revalidate();
		frame.repaint();
		ImageIcon dotGraph = new ImageIcon("out1.png");
		dotGraph.getImage().flush();
		dotGraph = new ImageIcon("out1.png");
		graph.setIcon(dotGraph);
		frame.getContentPane().add(graph);
		// graph.setVisible(false);

		graph.setVisible(true);
		graph.updateUI();
		graph.revalidate();
		graph.repaint();
		frame.revalidate();
		frame.repaint();
	}

	public static void hideGraph() {
		ImageIcon dotGraph = new ImageIcon("out1.png");
		dotGraph.getImage().flush();
		graph.setIcon(dotGraph);
		graph.setVisible(false);
		frame.revalidate();
		frame.repaint();
	}

	public static void setError(String str) {
		confl2.setText(str);
		confl2.setForeground(Color.red);
		cp3.setText("");
		// hideGraph();
	}

	public static void refresh() {
		graph.revalidate();
		graph.repaint();
	}

}
