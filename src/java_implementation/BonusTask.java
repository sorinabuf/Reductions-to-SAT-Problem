// Copyright 2020
// Author: Matei Simtinică

import java.io.*;
import java.util.*;

/**
 * Bonus Task
 * You have to implement 4 methods:
 * readProblemData         - read the problem input and store it however you see fit
 * formulateOracleQuestion - transform the current problem instance into a SAT instance and write the oracle input
 * decipherOracleAnswer    - transform the SAT answer back to the current problem's answer
 * writeAnswer             - write the current problem's answer
 */
public class BonusTask extends Task {
    int nrFamilies; // number of the Mafia families (corresponding to "N")
    int nrRelations; // number of related families (corresponding to "M")
    int sizeExtendedFamily; // size of the searched extended family (corresponding to "K")
    // list of lists of all relations between the Mafia families
    List<List<Integer>> relations = new ArrayList<>();
    // list of lists of all non-relations between the Mafia families
    List<List<Integer>> complementRelations = new ArrayList<>();
    // list of the extended family members of the complementary graph of relations
    List<Integer> extendedFamily = new ArrayList<>();

    @Override
    public void solve() throws IOException, InterruptedException {
        readProblemData();
        formulateOracleQuestion();
        askOracle();
        decipherOracleAnswer();
        writeAnswer();
    }

    /**
     * Method of optimization for setting K.
     */
    private void sizeOptimization() {
        // creates a list of all the families found in the mission
        List<Integer> families = new ArrayList<>();
        for (int family = 1; family <= nrFamilies; ++family) {
            families.add(family);
        }
        // sorts the list of families according to their numbers of complementary relations
        families.sort(Comparator.comparingInt(o -> complementRelations.get(o).size()));

        // used for calculating the maximum degree of a node in a clique based on the
        // complementary relations
        int degree = 0;

        for (int i = 0; i < nrFamilies; ++i) {
            int family = families.get(i);
            int j; // used for relations iteration
            // for each family, verifies whether its respective connected families have at least
            // the same amount of relations as the current family, otherwise the current node can
            // not be part of a clique
            for (j = 0; j < complementRelations.get(family).size(); ++j) {
                if (complementRelations.get(complementRelations.get(family).get(j)).size()
                        < complementRelations.get(family).size()) {
                    break;
                }
            }
            // if the condition is respected, updates the degree of a clique node
            if (j == complementRelations.get(family).size()) {
                degree = complementRelations.get(family).size();
            }
        }

        // updates the maximum size of an extended family if possible
        if (sizeExtendedFamily > degree + 1) {
            sizeExtendedFamily = degree + 1;
        }
    }

    /**
     * Reads the problem input from inFilename and stores the number of the Mafia families, the
     * number of relations and the relations between the families in the attributes defined above.
     * Also, creates the list of relations between the unconnected families.
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

        // number of connections of the complementary graph of relations, calculated as the total
        // number of edges possible in an undirected graph with "N" nodes, from which the number
        // of relations is subtracted
        int complementNrRelations = nrFamilies * (nrFamilies - 1) / 2 - nrRelations;
        // biggest possible size of an extended family calculated on the base of number of families
        sizeExtendedFamily = (int) Math.floor(Math.sqrt(2 * complementNrRelations + 0.25) + 0.5);

        // initializes "N + 1" lists of relations corresponding to each family number (the list
        // from index 0 remains unused); does the same thing for the complementary graph of
        // relations
        for (int i = 0; i <= nrFamilies; ++i) {
            List<Integer> newList = new ArrayList<>();
            relations.add(newList);
            List<Integer> newComplementList = new ArrayList<>();
            complementRelations.add(newComplementList);
        }

        // extracts the data from the rest of the "M" lines of relations and constructs the list
        // of relations for the connected families
        for (int i = 0; i < nrRelations; ++i) {
            String lineRelation = inputReader.readLine();
            String[] relation = lineRelation.split(" ");
            List<String> listRelation = Arrays.asList(relation);
            int family1 = Integer.parseInt(listRelation.get(0));
            int family2 = Integer.parseInt(listRelation.get(1));
            (relations.get(family1)).add(family2);
            (relations.get(family2)).add(family1);
        }

        //constructs the complementary adjacency lists of relations according to the unconnected
        // families
        for (int family1 = 1; family1 <= nrFamilies; ++family1) {
            for (int family2 = 1; family2 <= nrFamilies; ++family2) {
                if (!relations.get(family1).contains(family2)) {
                    (complementRelations.get(family1)).add(family2);
                }
            }
        }

        sizeOptimization(); // reduces K when possible
    }

    /**
     * Reduces the current complementary problem to SAT by writing it in oracleInFilename in a
     * format understood by the oracle.
     *
     * @throws IOException input/output exception to be thrown
     */
    @Override
    public void formulateOracleQuestion() throws IOException {
        // number of total clauses used in the SAT transformation (corresponding to "F")
        int nrClauses = sizeExtendedFamily + sizeExtendedFamily * nrFamilies * (nrFamilies - 1) / 2
                + nrFamilies * sizeExtendedFamily * (sizeExtendedFamily - 1) / 2
                + nrRelations * sizeExtendedFamily * (sizeExtendedFamily - 1);
        // number of total variables used in the SAT transformation (corresponding to "V")
        int nrVariables = nrFamilies * sizeExtendedFamily;
        // weight of a hard clause calculated as the sum of soft clauses + 1
        int top = (int) Math.pow(2, sizeExtendedFamily - 2);

        // defines the buffered writer for the input oracle file
        BufferedWriter writer = new BufferedWriter(new FileWriter(oracleInFilename));
        // writes first line of the oracle question
        writer.write("p wcnf " + nrVariables + " " + nrClauses + " " + top + "\n");

        // writes "K - 2" soft clauses and 2 hard clauses corresponding to the fact that each
        // element from the clique must be consisted of a family group (similar to task2)
        for (int i = 0; i < sizeExtendedFamily; ++i) {
            if (i == 0 || i == 1) {
                // first 2 hard clauses will have the top attribute at the beginning
                writer.write(top + " ");
            } else {
                // rest of the clauses will have an exponential weight at the beginning
                writer.write(Math.pow(2, i - 2) + " ");
            }
            for (int j = 1; j <= nrFamilies; ++j) {
                int varClique = nrFamilies * i + j;
                writer.write(varClique + " ");
            }
            writer.write("0\n");
        }

        // writes "K * N * (N - 1) / 2" hard clauses corresponding to the fact that a node of a
        // clique can not be represented by more than a family (similar to task2)
        for (int i = 0; i < sizeExtendedFamily; ++i) {
            for (int j = 1; j < nrFamilies; ++j) {
                int varClique1 = nrFamilies * i + j;
                varClique1 = -varClique1;
                for (int k = j + 1; k <= nrFamilies; ++k) {
                    int varClique2 = nrFamilies * i + k;
                    varClique2 = -varClique2;
                    // points out the hard close property by adding the top in front of the clause
                    writer.write(top + " " + varClique1 + " " + varClique2 + " 0\n");
                }
            }
        }

        // writes "N * K * (K - 1) / 2" hard clauses corresponding to the fact that a family can not
        // represent more than a node in the clique (similar to task2)
        for (int i = 1; i <= nrFamilies; ++i) {
            for (int j = 0; j < sizeExtendedFamily - 1; ++j) {
                int varCliqueFamily1 = nrFamilies * j + i;
                varCliqueFamily1 = -varCliqueFamily1;
                for (int k = j + 1; k < sizeExtendedFamily; ++k) {
                    int varCliqueFamily2 = nrFamilies * k + i;
                    varCliqueFamily2 = -varCliqueFamily2;
                    // points out the hard close property by adding the top in front of the clause
                    writer.write(top + " " + varCliqueFamily1 + " " + varCliqueFamily2 + " 0\n");
                }
            }
        }

        // writes "nrRelations * K * (K - 1)" hard clauses corresponding to the fact that for every
        // two families that form a relation, they can not both be present in the clique
        for (int i = 1; i <= nrFamilies; ++i) {
            for (int j = 1; j <= nrFamilies; ++j) {
                // gets the pairs of connected families
                if (i < j && relations.get(i).contains(j)) {
                    // creates the variable of a family from a connected pair and a potential
                    // clique node it may represent
                    for (int k = 0; k < sizeExtendedFamily; ++k) {
                        int varFamily1 = nrFamilies * k + i;
                        varFamily1 = -varFamily1;
                        for (int l = 0; l < sizeExtendedFamily; ++l) {
                            if (l != k) {
                                // creates the variable of the other family from the connected
                                // pair and another potential clique node it may represent
                                int varFamily2 = nrFamilies * l + j;
                                varFamily2 = -varFamily2;
                                // writes down a negated relationship between the two variables,
                                // representing the fact that they can not coexist, adding the
                                // top attribute in order to mark the hard clause property
                                writer.write(top + " " + varFamily1 + " " + varFamily2 + " 0\n");
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
     * Extracts the answer of the complementary problem from the one given by the oracle in
     * oracleOutFilename by converting the state of the variables to the problem's practical
     * application.
     *
     * @throws IOException input/output exception to be thrown
     */
    @Override
    public void decipherOracleAnswer() throws IOException {
        // list of stated variables related to oracle's answer to the complementary problem
        List<Integer> oracleAnswer = new ArrayList<>();
        // defines the buffered reader for the output oracle file
        FileReader inputFile = new FileReader(oracleOutFilename);
        BufferedReader inputReader = new BufferedReader(inputFile);

        String firstLine = inputReader.readLine();
        String[] dataFirstLine = firstLine.split(" ");
        List<String> first = Arrays.asList(dataFirstLine);
        // number of variables extracted from the file
        int nrVariables = Integer.parseInt(first.get(0));

        String line = inputReader.readLine();
        String[] dataLine = line.split(" ");
        // list of string variables extracted from the file
        List<String> answerVar = Arrays.asList(dataLine);
        for (int i = 0; i < nrVariables; ++i) {
            // adds the variables to the list of oracle answers
            oracleAnswer.add(Integer.parseInt(answerVar.get(i)));
        }

        // converts the stated variables to the complementary problem's practical answer, consisting
        // in populating the list of families part of the extended connection of size "K"
        for (int i = 0; i < sizeExtendedFamily; ++i) {
            for (int j = 1; j <= nrFamilies; ++j) {
                int varFamily = nrFamilies * i + j;
                if (oracleAnswer.get(varFamily - 1) > 0) {
                    extendedFamily.add(j);
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

        // displays the families needed to be arrested in order to disconnect the original graph
        // of relations which are represented by the complementary set of families which have not
        // been found in the answer of the oracle to the complementary problem
        for (int i = 1; i <= nrFamilies; ++i) {
            if (!extendedFamily.contains(i)) {
                writer.write(i + " ");
            }
        }

        // closes the output file
        writer.flush();
        writer.close();
    }
}
