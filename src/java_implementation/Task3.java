// Copyright 2020
// Author: Matei Simtinică

import java.io.*;
import java.util.*;

/**
 * Task3
 * This being an optimization problem, the solve method's logic has to work differently.
 * You have to search for the minimum number of arrests by successively querying the oracle.
 * Hint: it might be easier to reduce the current task to a previously solved task
 */
public class Task3 extends Task {
    String task2InFilename;
    String task2OutFilename;

    int nrFamilies; // number of the Mafia families (corresponding to "N")
    int nrRelations; // number of related families (corresponding to "M")
    int sizeExtendedFamily; // size of the searched extended family (corresponding to "K")
    // list of lists of all relations between the Mafia families
    List<List<Integer>> relations = new ArrayList<>();
    // list of lists of all non-relations between the Mafia families
    List<List<Integer>> complementRelations = new ArrayList<>();
    // list of biggest extended family found through task2 call
    List<Integer> extendedFamily = new ArrayList<>();
    // list of minimum number of arrested families
    List<Integer> arrests = new ArrayList<>();

    /**
     * Successively queries the oracle using Task2 in order to find the maximal clique in the
     * complementary graph of Mafia families relations.
     *
     * @throws IOException          input/output exception to be thrown
     * @throws InterruptedException interruption exception to be thrown
     */
    @Override
    public void solve() throws IOException, InterruptedException {
        task2InFilename = inFilename + "_t2";
        task2OutFilename = outFilename + "_t2";
        Task2 task2Solver = new Task2();
        task2Solver.addFiles(task2InFilename, oracleInFilename, oracleOutFilename, task2OutFilename);
        readProblemData();

        // number of connections of the complementary graph of relations, calculated as the total
        // number of edges possible in an undirected graph with "N" nodes, from which the number
        // of relations is subtracted
        int complementNrRelations = nrFamilies * (nrFamilies - 1) / 2 - nrRelations;
        // biggest possible size of an extended family calculated on the base of number of families
        sizeExtendedFamily = (int) Math.floor(Math.sqrt(2 * complementNrRelations + 0.25) + 0.5);

        while (sizeExtendedFamily > 1) {
            reduceToTask2();
            task2Solver.solve(); // solves task2 with the given attributes
            extractAnswerFromTask2();
            // if the current problem has not been solved, continues querying the oracle by
            // downsizing the requested extended family
            if (!task2Solver.problemAnswer) {
                sizeExtendedFamily = sizeExtendedFamily - 1;
            } else {
                // when the maximal extended family of the complementary graph has been
                // discovered, the families needed to be arrested in order to disconnect the
                // original graph of relations are represented by the complementary set of
                // families which have not been found in the answer of task2
                for (int family = 1; family <= nrFamilies; ++family) {
                    if (!extendedFamily.contains(family)) {
                        arrests.add(family);
                    }
                }
                break;
            }
        }
        writeAnswer();
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

        // initializes "N + 1" lists of relations corresponding to each family number (the list
        // from index 0 remains unused); does the same thing for the complementary graph of
        // relations
        for (int i = 0; i <= nrFamilies; ++i) {
            List<Integer> newList = new ArrayList<>();
            relations.add(newList);
            List<Integer> newComplementList = new ArrayList<>();
            complementRelations.add(newComplementList);
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

        // constructs the lists of relations between unconnected families
        for (int family1 = 1; family1 <= nrFamilies; ++family1) {
            for (int family2 = 1; family2 <= nrFamilies; ++family2) {
                // verifies whether the two families are in relation and constructs the
                // complementary adjacency lists accordingly
                if (!relations.get(family1).contains(family2)) {
                    (complementRelations.get(family1)).add(family2);
                }
            }
        }
    }

    /**
     * Reduces the current problem to Task2 by creating the task2InFilename accordingly.
     *
     * @throws IOException input/output exception to be thrown
     */
    public void reduceToTask2() throws IOException {
        // defines the buffered writer for the input file of the task2
        BufferedWriter writer = new BufferedWriter(new FileWriter(task2InFilename));
        // number of connections of the complementary graph of relations, calculated as the total
        // number of edges possible in an undirected graph with "N" nodes, from which the number
        // of relations is subtracted
        int complementNrRelations = nrFamilies * (nrFamilies - 1) / 2 - nrRelations;
        // writes first line of the input file
        writer.write(nrFamilies + " " + complementNrRelations + " " + sizeExtendedFamily
                + "\n");

        // writes the next "complementNrRelations" lines representing the connections of the
        // complementary graph
        for (int family1 = 1; family1 <= nrFamilies; ++family1) {
            for (Integer family2 : complementRelations.get(family1)) {
                if (family2 > family1) {
                    writer.write(family1 + " " + family2 + "\n");
                }
            }
        }

        // closes the input file
        writer.flush();
        writer.close();
    }

    /**
     * Extracts the answer from task2OutFilename represented by the extended family found with
     * the questioned size.
     *
     * @throws IOException input/output exception to be thrown
     */
    public void extractAnswerFromTask2() throws IOException {
        // defines the buffered reader for the output file
        FileReader inputFile = new FileReader(task2OutFilename);
        BufferedReader inputReader = new BufferedReader(inputFile);

        // clears the attribute before populating it
        extendedFamily.clear();

        // extracts the boolean answer of the problem
        String answerLogic = inputReader.readLine();
        boolean problemAnswer = answerLogic.equals("True");

        // if the answer shows the problem is resolvable, extracts the extended family members
        if (problemAnswer) {
            String line = inputReader.readLine();
            String[] dataLine = line.split(" ");
            for (String family : dataLine) {
                extendedFamily.add(Integer.parseInt(family));
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

        // displays the list of arrested families
        for (Integer family : arrests) {
            writer.write(family + " ");
        }

        // closes the output file
        writer.flush();
        writer.close();
    }
}
