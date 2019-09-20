import javax.swing.*;
import javax.swing.filechooser.*;
import java.awt.event.*;
import java.awt.*;

public class FileDialogFrame {
	public static void main(String args[]) {
		// make frame
		JFrame frame = new JFrame("ubf file reader");

		// make menu
		JMenuBar menuBar = new JMenuBar();
		JMenu menu = new JMenu("File");
		menu.setMnemonic(KeyEvent.VK_F);
		
		JMenuItem openMenuItem = new JMenuItem("Open");
		openMenuItem.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent event) {
				// make file chooser and allow multiple selection
				JFileChooser fc = new JFileChooser("Open .ubf files");
				fc.setMultiSelectionEnabled(true);
				
				// make file extension filter
				FileNameExtensionFilter filter = new FileNameExtensionFilter("UBF FILES", "ubf", "ubf");
				fc.setFileFilter(filter);
				
				// open dialogue and inspect actions
				int returnVal = fc.showOpenDialog(null);
				
				// do something with the results
				if(returnVal == JFileChooser.APPROVE_OPTION) {
					System.out.println("file approved");
				} else {
					JOptionPane.showMessageDialog(null, "You have not selected files!", "Info", JOptionPane.INFORMATION_MESSAGE);
				}
				
			}
		});
		
		menu.add(openMenuItem);
		
		menuBar.add(menu);
		frame.setJMenuBar(menuBar);
		
		// show file
		frame.setSize(500,600);
		frame.setVisible(true);
	}
}