// Copyright 2020
// Author: Matei Simtinică

import java.io.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Task1
 * You have to implement 4 methods:
 * readProblemData         - read the problem input and store it however you see fit
 * formulateOracleQuestion - transform the current problem instance into a SAT instance and write the oracle input
 * decipherOracleAnswer    - transform the SAT answer back to the current problem's answer
 * writeAnswer             - write the current problem's answer
 */
public class Task1 extends Task {
    int nrFamilies; // number of the Mafia families (corresponding to "N")
    int nrRelations; // number of related families (corresponding to "M")
    int nrSpies; // number of spies available for mission (corresponding to "K")
    List<Integer> relations = new ArrayList<>(); // list of all relations between the Mafia families
    List<Integer> assignedSpies = new ArrayList<>(); // list of the spies assigned to each family
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
     * number of relations, the number of spies and the relations between the families in the
     * attributes defined above.
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
        nrSpies = Integer.parseInt(listFirstLine.get(2));

        // extracts the data from the rest of the "M" lines of relations
        for (int i = 0; i < nrRelations; ++i) {
            String lineRelation = inputReader.readLine();
            String[] relation = lineRelation.split(" ");
            List<String> listRelation = Arrays.asList(relation);
            // extracts a pair of families which are in relation
            int family1 = Integer.parseInt(listRelation.get(0)); // corresponding to "u"
            int family2 = Integer.parseInt(listRelation.get(1)); // corresponding to "v"
            // adds the families in the list of relations
            relations.add(family1);
            relations.add(family2);
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
        // number of total clauses used in the SAT transformation (corresponding to "F")
        int nrClauses =
                nrRelations * nrSpies + nrFamilies + nrFamilies * nrSpies * (nrSpies - 1) / 2;
        // number of total variables used in the SAT transformation (corresponding to "V")
        int nrVariables = nrFamilies * nrSpies;
        // defines the buffered writer for the input oracle file
        BufferedWriter writer = new BufferedWriter(new FileWriter(oracleInFilename));
        // writes first line of the oracle question
        writer.write("p cnf " + nrVariables + " " + nrClauses + "\n");

        // writes "N" clauses corresponding to the fact that each family must have at least one spy
        for (int i = 1; i <= nrFamilies; ++i) {
            // creates the variables of each family connected to the spies it may have and writes
            // all corresponding variables in the file (each family has an amount of variables
            // equal to the number of spies)
            for (int j = 0; j < nrSpies; ++j) {
                int varFamily = nrFamilies * j + i;
                writer.write(varFamily + " ");
            }
            writer.write("0 \n");
        }

        // writes "M * K" clauses corresponding to the fact that two connected families can not
        // have the same spy
        for (int i = 0; i < nrRelations; ++i) {
            // extracts two connected families from the list of relations
            int family1 = relations.get(2 * i);
            int family2 = relations.get(2 * i + 1);
            for (int j = 0; j < nrSpies; ++j) {
                // creates the variables of the two families according to each spy they may have
                // in common and negates a possible similarity, writing down the clauses
                int varFamily1 = nrFamilies * j + family1;
                int varFamily2 = nrFamilies * j + family2;
                varFamily1 = -varFamily1;
                varFamily2 = -varFamily2;
                writer.write(varFamily1 + " " + varFamily2 + " " + 0 + "\n");
            }
        }

        // writes "N * K * (K - 1) / 2" clauses corresponding to the fact that a family can not
        // have more than one spy
        for (int i = 1; i <= nrFamilies; ++i) {
            for (int j = 0; j < nrSpies - 1; ++j) {
                // creates the variable of a family and a potential spy it may have
                int varFamilySpy1 = nrFamilies * j + i;
                varFamilySpy1 = -varFamilySpy1;
                for (int k = j + 1; k < nrSpies; ++k) {
                    // creates the variable of a family and another potential spy it may have
                    int varFamilySpy2 = nrFamilies * k + i;
                    varFamilySpy2 = -varFamilySpy2;
                    // writes down a negated relationship between the two variables, representing
                    // the fact that they can not coexist
                    writer.write(varFamilySpy1 + " " + varFamilySpy2 + " 0 \n");
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
        // problem's practical answer, consisting in populating the list of spies assigned to
        // each family
        if (problemAnswer) {
            for (int i = 1; i <= nrFamilies; ++i) {
                // for each family, the variables related to every possible infiltrated spy are
                // created
                for (int j = 0; j < nrSpies; ++j) {
                    int varFamily = nrFamilies * j + i;
                    // verifies whether the variable of the family and a respective spy was
                    // assigned as True by the oracle
                    if (oracleAnswer.get(varFamily - 1) > 0) {
                        // adds the spy to the list if the condition is verified
                        assignedSpies.add(j + 1);
                    }
                }
            }
        }
    }

    /**
     * Writes the answer to the current problem to the outFilename based on the list of spies
     * provided by the oracle.
     *
     * @throws IOException input/output exception to be thrown
     */
    @Override
    public void writeAnswer() throws IOException {
        // defines the buffered writer for the output file
        BufferedWriter writer = new BufferedWriter(new FileWriter(outFilename));

        // displays a message of the resolvable state of the problem along with the list of spies
        // assigned to each family in case of success
        if (problemAnswer) {
            writer.write("True\n");
            for (int i = 0; i < nrFamilies; ++i) {
                writer.write(assignedSpies.get(i) + " ");
            }
        } else {
            writer.write("False\n");
        }

        // closes the output file
        writer.flush();
        writer.close();
    }
}
