package com.company;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Scanner;

public class Main {
    public static void main(String[] args) {
        RedBlackTree redBlackTree = new RedBlackTree();
        String inputFile = "input.txt";
        String path = "src/data/" + inputFile;

        System.out.println("empty red black tree valid: " + redBlackTree.verifyRedBlackProperties());
        try {
            File file = new File(path);
            Scanner sc = new Scanner(file);
            while (sc.hasNextLine()) {
                String line = sc.nextLine();
                try {
                    Integer value = Integer.parseInt(line);
                    redBlackTree.insert(value);
                } catch (NumberFormatException e) {
                    System.err.println("Incorrect format of: " + line);
                }
            }
            sc.close();
        } catch (FileNotFoundException e) {
            System.err.println("No file called: " + inputFile);
        }
        System.out.println("Red black tree valid: " + redBlackTree.verifyRedBlackProperties());
        redBlackTree.inOrder();
        redBlackTree.preOrder();
        redBlackTree.postOrder();
        System.out.println("delete 8: " + redBlackTree.delete(8));
        System.out.println("delete 14: " + redBlackTree.delete(14));
        redBlackTree.inOrder();
        System.out.println("Red black tree valid: " + redBlackTree.verifyRedBlackProperties());
    }
}
