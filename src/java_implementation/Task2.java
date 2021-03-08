// Copyright 2020
// Author: Matei Simtinică

import java.io.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Task2
 * You have to implement 4 methods:
 * readProblemData         - read the problem input and store it however you see fit
 * formulateOracleQuestion - transform the current problem instance into a SAT instance and write the oracle input
 * decipherOracleAnswer    - transform the SAT answer back to the current problem's answer
 * writeAnswer             - write the current problem's answer
 */
public class Task2 extends Task {
    int nrFamilies; // number of the Mafia families (corresponding to "N")
    int nrRelations; // number of related families (corresponding to "M")
    int sizeExtendedFamily; // size of the searched extended family (corresponding to "K")
    // list of lists of all relations between the Mafia families
    List<List<Integer>> relations = new ArrayList<>();
    List<Integer> extendedFamily = new ArrayList<>(); // list of the extended family members
    boolean problemAnswer; // boolean answer of the problem

    @Override
    public void solve() throws IOException, InterruptedException {
        readProblemData();
        formulateOracleQuestion();
        askOracle();
        decipherOracleAnswer();
        writeAnswer();
    }

    /**
     * Reads the problem input from inFilename and stores the number of the Mafia families, the
     * number of relations, the size of the extended family and the relations between the
     * families in the attributes defined above.
     *
     * @throws IOException input/output exception to be thrown
     */
    @Override
    public void readProblemData() throws IOException {
        // defines the buffered reader for the input file
        FileReader inputFile = new FileReader(inFilename);
        BufferedReader inputReader = new BufferedReader(inputFile);

        // extracts the data from first input line and stores it in the corresponding attributes
        String firstLine = inputReader.readLine();
        String[] dataFirstLine = firstLine.split(" ");
        List<String> listFirstLine = Arrays.asList(dataFirstLine);
        nrFamilies = Integer.parseInt(listFirstLine.get(0));
        nrRelations = Integer.parseInt(listFirstLine.get(1));
        sizeExtendedFamily = Integer.parseInt(listFirstLine.get(2));

        // initializes "N + 1" lists of relations corresponding to each family number (the list
        // from index 0 remains unused)
        for (int i = 0; i <= nrFamilies; ++i) {
            List<Integer> newList = new ArrayList<>();
            relations.add(newList);
        }

        // extracts the data from the rest of the "M" lines of relations
        for (int i = 0; i < nrRelations; ++i) {
            String lineRelation = inputReader.readLine();
            String[] relation = lineRelation.split(" ");
            List<String> listRelation = Arrays.asList(relation);
            // extracts a pair of families which are in relation
            int family1 = Integer.parseInt(listRelation.get(0)); // corresponding to "u"
            int family2 = Integer.parseInt(listRelation.get(1)); // corresponding to "v"
            // creates a reciprocal connection between the two families by adding each family in
            // the other's corresponding list of relations
            (relations.get(family1)).add(family2);
            (relations.get(family2)).add(family1);
        }
    }

    /**
     * Reduces the current problem to SAT by writing it in oracleInFilename in a format
     * understood by the oracle.
     *
     * @throws IOException input/output exception to be thrown
     */
    @Override
    public void formulateOracleQuestion() throws IOException {
        // number of edges of the complementary graph of relations, calculated as the total
        // number of edges possible in an undirected graph with "N" nodes, from which the number
        // of relations is subtracted
        int nrNonEdges = nrFamilies * (nrFamilies - 1) / 2 - nrRelations;
        // number of total clauses used in the SAT transformation (corresponding to "F")
        int nrClauses =
                sizeExtendedFamily + sizeExtendedFamily * nrFamilies * (nrFamilies - 1) / 2
                        + nrFamilies * sizeExtendedFamily * (sizeExtendedFamily - 1) / 2
                        + nrNonEdges * sizeExtendedFamily * (sizeExtendedFamily - 1);
        // number of total variables used in the SAT transformation (corresponding to "V")
        int nrVariables = nrFamilies * sizeExtendedFamily;
        // defines the buffered writer for the input oracle file
        BufferedWriter writer = new BufferedWriter(new FileWriter(oracleInFilename));
        // writes first line of the oracle question
        writer.write("p cnf " + nrVariables + " " + nrClauses + "\n");

        // writes "K" clauses corresponding to the fact that each element from the clique (that
        // will represent the extended family of size "K") must be consisted of a family group
        for (int i = 0; i < sizeExtendedFamily; ++i) {
            for (int j = 1; j <= nrFamilies; ++j) {
                // creates the variables of each element of the clique connected to the family it
                // may be represented by and writes all corresponding variables in the file (each
                // clique node has an amount of variables equal to the number of families)
                int varClique = nrFamilies * i + j;
                writer.write(varClique + " ");
            }
            writer.write("0\n");
        }

        // writes "K * N * (N - 1) / 2" clauses corresponding to the fact that a node of a clique
        // can not be represented by more than a family
        for (int i = 0; i < sizeExtendedFamily; ++i) {
            for (int j = 1; j < nrFamilies; ++j) {
                // creates the variable of a clique node and a potential family it may have
                int varClique1 = nrFamilies * i + j;
                varClique1 = -varClique1;
                for (int k = j + 1; k <= nrFamilies; ++k) {
                    // creates the variable of a clique node and another potential family it may
                    // consist of
                    int varClique2 = nrFamilies * i + k;
                    varClique2 = -varClique2;
                    // writes down a negated relationship between the two variables, representing
                    // the fact that they can not coexist
                    writer.write(varClique1 + " " + varClique2 + " 0\n");
                }
            }
        }

        // writes "N * K * (K - 1) / 2" clauses corresponding to the fact that a family can not
        // represent more than a node in the clique
        for (int i = 1; i <= nrFamilies; ++i) {
            for (int j = 0; j < sizeExtendedFamily - 1; ++j) {
                // creates the variable of a family and a potential clique node it may represent
                int varCliqueFamily1 = nrFamilies * j + i;
                varCliqueFamily1 = -varCliqueFamily1;
                for (int k = j + 1; k < sizeExtendedFamily; ++k) {
                    // creates the variable of a family and another potential clique node it may
                    // represent
                    int varCliqueFamily2 = nrFamilies * k + i;
                    varCliqueFamily2 = -varCliqueFamily2;
                    // writes down a negated relationship between the two variables, representing
                    // the fact that they can not coexist
                    writer.write(varCliqueFamily1 + " " + varCliqueFamily2 + " 0\n");
                }
            }
        }

        // writes "nr non-edges * K * (K - 1)" clauses corresponding to the fact that for every two
        // families that do not form a relation, they can not both be present in the clique
        for (int i = 1; i <= nrFamilies; ++i) {
            for (int j = 1; j <= nrFamilies; ++j) {
                // gets the pairs of unconnected families
                if (i < j && !relations.get(i).contains(j)) {
                    // creates the variable of a family from an unconnected pair and a potential
                    // clique node it may represent
                    for (int k = 0; k < sizeExtendedFamily; ++k) {
                        int varFamily1 = nrFamilies * k + i;
                        varFamily1 = -varFamily1;
                        for (int l = 0; l < sizeExtendedFamily; ++l) {
                            if (l != k) {
                                // creates the variable of the other family from the unconnected
                                // pair and another potential clique node it may represent
                                int varFamily2 = nrFamilies * l + j;
                                varFamily2 = -varFamily2;
                                // writes down a negated relationship between the two variables,
                                // representing the fact that they can not coexist
                                writer.write(varFamily1 + " " + varFamily2 + " 0\n");
                            }
                        }
                    }
                }
            }
        }

        // closes the input oracle file
        writer.flush();
        writer.close();
    }

    /**
     * Extracts the answer of the problem from the one given by the oracle in oracleOutFilename by
     * converting the state of the variables to the problem's practical application.
     *
     * @throws IOException input/output exception to be thrown
     */
    @Override
    public void decipherOracleAnswer() throws IOException {
        // list of stated variables related to oracle's answer to the problem
        List<Integer> oracleAnswer = new ArrayList<>();
        // defines the buffered reader for the output oracle file
        FileReader inputFile = new FileReader(oracleOutFilename);
        BufferedReader inputReader = new BufferedReader(inputFile);

        // extracts the boolean answer of the problem
        String answerLogic = inputReader.readLine();
        problemAnswer = answerLogic.equals("True");

        // if the answer shows the problem is resolvable, extracts the state of the variables
        if (problemAnswer) {
            // number of variables extracted from the file (corresponding to "V")
            int nrVariables = Integer.parseInt(inputReader.readLine());
            String line = inputReader.readLine();
            String[] dataLine = line.split(" ");
            // list of string variables extracted from the file
            List<String> answerVariables = Arrays.asList(dataLine);
            for (int i = 0; i < nrVariables; ++i) {
                // adds the variables to the list of oracle answers
                oracleAnswer.add(Integer.parseInt(answerVariables.get(i)));
            }
        }

        // if the answer shows the problem is resolvable, converts the stated variables to the
        // problem's practical answer, consisting in populating the list of families part of the
        // extended connection of size "K"
        if (problemAnswer) {
            for (int i = 1; i <= nrFamilies; ++i) {
                // for each family, the variables related to every possible clique node
                // representation are created
                for (int j = 0; j < sizeExtendedFamily; ++j) {
                    int varFamily = nrFamilies * j + i;
                    // verifies whether the variable of the family and a respective clique node was
                    // assigned as True by the oracle
                    if (oracleAnswer.get(varFamily - 1) > 0) {
                        // adds the family to the list if the condition is verified
                        extendedFamily.add(i);
                    }
                }
            }
        }
    }

    /**
     * Writes the answer to the current problem to the outFilename based on the list of families
     * provided by the oracle.
     *
     * @throws IOException input/output exception to be thrown
     */
    @Override
    public void writeAnswer() throws IOException {
        // defines the buffered writer for the output file
        BufferedWriter writer = new BufferedWriter(new FileWriter(outFilename));

        // displays a message of the resolvable state of the problem along with the list of families
        // that create an extended relationship
        if (problemAnswer) {
            writer.write("True\n");
            for (int i = 0; i < sizeExtendedFamily; ++i) {
                writer.write(extendedFamily.get(i) + " ");
            }
        } else {
            writer.write("False\n");
        }

        // closes the output file
        writer.flush();
        writer.close();
    }
}
