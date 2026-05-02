package de.featjar.analysis.sat4j.computation;

import ca.pfv.spmf.algorithms.frequentpatterns.apriori_fast.AlgoAprioriFAST;
import ca.pfv.spmf.algorithms.frequentpatterns.apriori_simple.AlgoApriori;
import ca.pfv.spmf.algorithms.frequentpatterns.eclat.AlgoEclat;
import ca.pfv.spmf.input.transaction_database_list_integers.TransactionDatabase;
import ca.pfv.spmf.patterns.itemset_array_integers_with_count.Itemset;
import ca.pfv.spmf.patterns.itemset_array_integers_with_count.Itemsets;
import ca.pfv.spmf.algorithms.frequentpatterns.fpgrowth.AlgoFPGrowth;
import de.featjar.analysis.IConfigurationTester;
import de.featjar.analysis.sat4j.solver.ISelectionStrategy;
import de.featjar.analysis.sat4j.solver.ModalImplicationGraph;
import de.featjar.base.FeatJAR;
import de.featjar.base.computation.Computations;
import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
import de.featjar.base.computation.Progress;
import de.featjar.base.data.IntegerList;
import de.featjar.base.data.Pair;
import de.featjar.base.data.Result;
import de.featjar.base.io.input.FileInputMapper;
import de.featjar.formula.VariableMap;
import de.featjar.formula.assignment.BooleanAssignment;
import de.featjar.formula.assignment.BooleanAssignmentList;
import de.featjar.formula.assignment.BooleanSolution;
import de.featjar.formula.assignment.conversion.ComputeBooleanClauseList;
import de.featjar.formula.combination.VariableCombinationSpecification;
import de.featjar.formula.computation.ComputeCNFFormula;
import de.featjar.formula.computation.ComputeNNFFormula;
import de.featjar.formula.io.xml.XMLFeatureModelFormulaParser;
import de.featjar.formula.structure.IFormula;

import java.io.*;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.concurrent.CompletableFuture;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static de.featjar.base.computation.Computations.await;

public class CSL extends ASAT4JAnalysis.Solution<BooleanAssignmentList> {

    public static final Dependency<Integer> T = Dependency.newDependency(Integer.class);
    public static final Dependency<ModalImplicationGraph> MIG =
            Dependency.newDependency(ModalImplicationGraph.class);

    public static final Dependency<BooleanAssignmentList> FAILING_CONFIGS =
            Dependency.newDependency(BooleanAssignmentList.class);
    public static final Dependency<BooleanAssignmentList> PASSING_CONFIGS =
            Dependency.newDependency(BooleanAssignmentList.class);
    public static final Dependency<Double> MINSUPP =  Dependency.newDependency(Double.class);
    public static final Dependency<Double> MINCONF =  Dependency.newDependency(Double.class);


    private static TestManager tester;
    private static RandomConfigurationUpdater updater;
    private static BooleanAssignmentList sample;
    private static BooleanAssignmentList featureModelClauses;
    private static BooleanAssignment coreFeatures;
    private static final String featureModelFile = "e-shop-model.xml";
    private static final String basePath =
            System.getProperty("user.home") + "/Documents/studium/Bachelorarbeit/".replace("/", File.separator);
    private static final String resourcesFolder = "resources_featjar/".replace("/", File.separator);
    private static int passing = 0, failing = 0;

    public CSL(IComputation<BooleanAssignmentList> booleanClauseList, Object... computations) {
        super(
                booleanClauseList,
                Computations.of(1),
                Computations.of(new BooleanAssignmentList((VariableMap) null)),
                new MIGBuilder(booleanClauseList),
                computations
        );

    }

    @Override
    public Result<BooleanAssignmentList> compute(List<Object> dependencyList, Progress progress) {
        BooleanAssignmentList passingConfigAssignmentList = PASSING_CONFIGS.get(dependencyList);
        BooleanAssignmentList failingConfigAssignmentList = FAILING_CONFIGS.get(dependencyList);



        return null;
    }

    public static void main(String[] args) throws Exception {
        FeatJAR.initialize();
        // Paths for configs, fm
        Path modelPath = Path.of(basePath, resourcesFolder, featureModelFile);
        featureModelClauses = parseModel(modelPath);

        // Third parameter must be true for AlgoAprioriFAST
        // This converts the mixture of positive and negative integers for feature representation to only positive
        // -> This mapping has to be converted back to featjar standard after running apriori
        boolean onlyPositiveInts = true;
        int configAmount = 80;
        sample = sampleRandomConfigs(featureModelClauses, configAmount);
        //sample = sampleTWise(featureModelClauses, 3, configAmount);
        updater = new RandomConfigurationUpdater(featureModelClauses, 2L);
        coreFeatures = Computations.of(featureModelClauses)
                .map(ComputeCoreSAT4J::new).
                get().orElseThrow().getFirst();

        // Simulate faulty interactions
        tester = new TestManager();
        //tester.addInteraction("Oats", "Apple");
        //tester.addInteraction("Strawberrys", "Apple");

        String interaction1 = "Purchase_value_scope269";
        tester.addInteraction(interaction1);

        //String interaction2 = "Shipping_address277";
        //tester.addInteractionByName(interaction2);

        String[] interaction3 = new String[]{"City149", "Thumbnail68"};
        tester.addInteraction(interaction3);

        String[] interaction4 = new String[]{"City149", "Welcome_message11"};
        tester.addInteraction(interaction4);

        // Test configs
        String configs = basePath + resourcesFolder;
        Path passingConfigsPath = Path.of(configs, "passingConfigs.txt");
        Path failingConfigsPath = Path.of(configs, "failingConfigs.txt");

        testSampledConfigs(passingConfigsPath, failingConfigsPath, onlyPositiveInts);

        System.out.println("Passing: " + passing);
        System.out.println("Failing: " + failing);
        System.out.println("Sample size: " + sample.size());
        System.out.println(tester.printInteractions());

        int maxInteractionSize = 2;
        long patternMinerTimestamp = System.currentTimeMillis();

        //CompletableFuture<Itemsets> passingFuture = runFpGrowth(true, 1, maxInteractionSize);
        //CompletableFuture<Itemsets> failingFuture = runFpGrowth(false, 1, maxInteractionSize);

        //CompletableFuture<Itemsets> passingFuture = runEclat(true, 1, maxInteractionSize);
        //CompletableFuture<Itemsets> failingFuture = runEclat(false, 1, maxInteractionSize);

        CompletableFuture<Itemsets> passingFuture = runAprioriFast(true, 1, maxInteractionSize);
        CompletableFuture<Itemsets> failingFuture = runAprioriFast(false, 1, maxInteractionSize);

        CompletableFuture.allOf(passingFuture, failingFuture).join();
        System.out.printf("Time for FP Growth execution: %d ms\n", System.currentTimeMillis() - patternMinerTimestamp);

        Itemsets frequentInteractionsInPassingConfigs = passingFuture.get();
        Itemsets frequentInteractionsInFailingConfigs = failingFuture.get();

        // Get frequent patterns
        List<Itemset> frequentPassingInteractionList = frequentInteractionsInPassingConfigs.getLevels().stream()
                .flatMap(Collection::stream)
                //.filter(i -> i.itemset.length <= maxInteractionSize)
                .collect(Collectors.toList());

        List<Itemset> frequentFailingInteractionList  =  frequentInteractionsInFailingConfigs .getLevels().stream()
                .flatMap(Collection::stream)
                //.filter(i -> i.itemset.length <= maxInteractionSize)
                .collect(Collectors.toList());



        // Convert Itemset lists to a HashMap BooleanAssigment -> Absolute support (Anzahl der Vorkommen)
        HashMap<BooleanAssignment, Integer> supportPerInteractionPassingConfigs =
                transformPatterns(frequentPassingInteractionList, onlyPositiveInts);
        HashMap<BooleanAssignment, Integer> supportPerInteractionFailingConfigs =
                transformPatterns(frequentFailingInteractionList, onlyPositiveInts);


        // Calculate growth rate per pattern
        HashMap<BooleanAssignment, Double> growthRatePerInteraction =
                computeGrowthRates(supportPerInteractionFailingConfigs, supportPerInteractionPassingConfigs, failing, passing);
        System.out.println("Interactions found: " + growthRatePerInteraction.size());

        // Filter infinite Growth rate patterns
        ArrayList<Pair<BooleanAssignment, Double>> infGrowthRateInteractions = filterInfiniteGrowthRates(growthRatePerInteraction);
        infGrowthRateInteractions.sort(Comparator.comparing(p -> p.getFirst().get()[0]));
        System.out.println("Infinite Growth Interactions: " + infGrowthRateInteractions.size());

        // Get minimal patterns to simplify finding interactions
        List<BooleanAssignment> minimalInteractions = getMinimalInteractions(infGrowthRateInteractions);
        System.out.println("Minimal Interactions: " + minimalInteractions.size());

        // Sample new config to further exclude more patterns
        List<BooleanAssignment> reducedInteractions = minimalInteractions;
        long reducerTimestamp = System.currentTimeMillis();
        //reducedInteractions =
        //        reduceDivideAndConquer(reducedInteractions, supportPerInteractionFailingConfigs, 3);
        System.out.printf("Took %d ms to reduce interactions with divide and conquer\n", System.currentTimeMillis() - reducerTimestamp);
        System.out.println("Reduced interactions after divide and conquer: " + reducedInteractions.size());

        reducerTimestamp = System.currentTimeMillis();
        reducedInteractions =
                reduceInteractionsInBatchesIterative(
                        reducedInteractions, supportPerInteractionFailingConfigs, 50, 4);
        System.out.printf("Took %d ms to reduce interactions in batches\n", System.currentTimeMillis() - reducerTimestamp);
        System.out.println("Reduced Interactions after iteratively batching: " + reducedInteractions.size());

        writeInteractionsToFile(reducedInteractions,"reducedPatterns.txt");
        printResults(reducedInteractions);

        FeatJAR.deinitialize();
        System.exit(0);
    }

    private static CompletableFuture<Itemsets> runAprioriFast(boolean passing, int occurrences, int maxInteractionSize){
        int configs = passing ? CSL.passing : CSL.failing;
        double minsup = (double) occurrences / configs;
        String fileName = passing ? "passingConfigs.txt" : "failingConfigs.txt";
        String path = basePath + resourcesFolder + fileName;

        AlgoAprioriFAST apriori = new AlgoAprioriFAST();
        apriori.setMaximumPatternLength(maxInteractionSize);
        return CompletableFuture.supplyAsync(() -> {
           try {
               return apriori.runAlgorithm(minsup, path, null, 30);
           } catch (IOException e) {
               throw new RuntimeException(e);
           } finally {
               System.out.println("Stats for itemsets with passing = " + passing);
               apriori.printStats();
           }
        });
    }

    private static CompletableFuture<Itemsets> runEclat(boolean passing, int occurrences, int maxInteractionSize){
        int configs = passing ? CSL.passing : CSL.failing;
        double minsup = (double) occurrences / configs;
        String fileName = passing ? "passingConfigs.txt" : "failingConfigs.txt";
        String path = basePath + resourcesFolder + fileName;

        TransactionDatabase database = new TransactionDatabase();
        try (BufferedReader reader = new BufferedReader(new FileReader(path))){
            String line;
            while ((line = reader.readLine()) != null){
                String[] numbers = line.split(" ");
                List<Integer> features =
                        Arrays.stream(numbers).map(Integer::parseInt).collect(Collectors.toList());
                database.addTransaction(features);
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

        AlgoEclat eclat = new AlgoEclat();
        eclat.setMaximumPatternLength(maxInteractionSize);
        return CompletableFuture.supplyAsync(() -> {
            try {
                return eclat.runAlgorithm(null, database, minsup, false);
            } catch (Exception e) {
                throw new RuntimeException(e);
            } finally {
                System.out.println("Stats for itemsets with passing = " + passing);
                eclat.printStats();
            }
        });
    }

    private static CompletableFuture<Itemsets> runFpGrowth(boolean passing, int occurrences, int maxInteractionSize){
        int configs = passing ? CSL.passing : CSL.failing;
        double minsup = (double) occurrences / configs;
        String fileName = passing ? "passingConfigs.txt" : "failingConfigs.txt";
        String path = basePath + resourcesFolder + fileName;

        AlgoFPGrowth fpGrowth = new AlgoFPGrowth();
        fpGrowth.setMinimumPatternLength(1);
        fpGrowth.setMaximumPatternLength(maxInteractionSize);

        return CompletableFuture.supplyAsync(() -> {
            try {
                return fpGrowth.runAlgorithm(path, null, minsup);
            } catch (Exception e) {
                throw new RuntimeException(e);
            } finally {
                System.out.println("Stats for itemsets with passing = " + passing);
                fpGrowth.printStats();
            }
        });

    }

    /**
     * Maps (complete) feature sets / configs from the representation of only positive integers to the FearJAR
     * representation with positive and negative integers for included and excluded features.
     * @param features
     * @param maxFeatureInt
     * @return
     */
    private static int[] mapFeaturesToNegativeInts(int[] features, int maxFeatureInt){
        return Arrays.stream(features).map(f -> {
            if (f > maxFeatureInt + 1){
                return -(Integer.MAX_VALUE - f);
            }
            return f;
        }).toArray();
    }

    /**
     * Maps (complete) feature sets / configs from the FeatJAR representation of positve and negative ints
     * for inlcuded and excluded features to only positive integers for compatibility purposes with SPMF algorithms.
     * @param features
     * @return
     */
    private static int[] mapFeaturesToPositiveInts(int[] features){
        return Arrays.stream(features).map(f -> {
            if (f < 0) {
                return Integer.MAX_VALUE - f;
            }
            return f;
        }).toArray();


    }

    private static List<BooleanAssignment> reduceInteractionsInBatchesIterative(
            List<BooleanAssignment> reducedInteractions,
            HashMap<BooleanAssignment, Integer> supportPerInteractionFailingConfigs,
            int exclusionLimit,
            int batchsize) {
        int iterations = 1;
        int oldsize = 0;
        do {
            oldsize = reducedInteractions.size();
            reducedInteractions =
                    reduceInteractionsInBatches(reducedInteractions, batchsize,
                            supportPerInteractionFailingConfigs, exclusionLimit);
            //System.out.printf("------------------- Iteration %d -------------------\n", iterations);
            //System.out.println("Reduced minimal Interactions: " + reducedInteractions.size());
            iterations++;
        } while (reducedInteractions.size() < oldsize);
        return reducedInteractions;
    }

    private static void writeInteractionsToFile(List<BooleanAssignment> reducedMinimalInteractions, String path) {
        String filePath = basePath + resourcesFolder + path;
        try (PrintWriter out = new PrintWriter(filePath)) {
            for (BooleanAssignment pattern : reducedMinimalInteractions) {
                out.println(pattern.print());
            }
            out.flush();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }
    }

    /**
     * Prints which simulated interaction is contained or not contained in the List.
     * @param reducedMinimalPatterns List of potential faulty interactions.
     */
    private static void printResults(List<BooleanAssignment> reducedMinimalPatterns) {
        boolean foundAllInteractions = true;
        for (int[] simulatedInteraction : tester.getInteractions()) {
            boolean foundThisInteraction = false;
            for (BooleanAssignment foundInteraction : reducedMinimalPatterns) {
                if (foundInteraction.containsAll(simulatedInteraction)) {
                    System.out.println("Interaction " + Arrays.toString(simulatedInteraction) + " in reduced minimal patterns.");
                    foundThisInteraction = true;
                    break;
                }
            }
            if (!foundThisInteraction) {
                System.out.println("Interaction " + Arrays.toString(simulatedInteraction) + " not found in reduced minimal patterns.");
                foundAllInteractions = false;
            }
        }
        if (foundAllInteractions) {
            System.out.println("--------- All interactions found! ---------");
        }
    }

    /**
     * Refines the set of potentially faulty interactions using a recursive "Divide and Conquer"
     * approach inspired by the Delta Debugging ($ddmin$) algorithm.
     * <p>
     * This method attempts to prune large subsets of candidates simultaneously. If a configuration
     * containing an entire block of interactions passes, all interactions in that block are
     * dismissed as false positives, achieving logarithmic reduction in the best case.
     * <p>
     * To maintain satisfiability within the feature model, this method employs a
     * <b>Relaxed Exclusion</b> strategy: it ranks all candidates by their failure frequency
     * and only negates the top-tier candidates (defined by {@code exclusionLimit}) during sampling.
     *
     * @param interactions   The initial list of suspected feature interactions to be reduced.
     * @param failSupportMap A map containing the absolute support of each interaction in
     * failing configurations, used for ranking.
     * @param exclusionLimit The maximum number of high-frequency patterns to exclude
     * in the SAT query to avoid architectural conflicts (UNSAT).
     * @return A minimized list of interactions that likely represent the actual root causes.
     */
    private static List<BooleanAssignment> reduceDivideAndConquer(
            List<BooleanAssignment> interactions,
            HashMap<BooleanAssignment, Integer> failSupportMap,
            int exclusionLimit) {

        // 1. Sortieren (Wichtig, damit echte Bugs oben stehen und Relaxed Exclusion funktioniert)
        List<BooleanAssignment> sortedInteractions = new ArrayList<>(interactions);
        sortedInteractions.sort((p1, p2) -> {
            int supp2 = failSupportMap.getOrDefault(p2, 0);
            int supp1 = failSupportMap.getOrDefault(p1, 0);
            return Integer.compare(supp2, supp1);
        });

        // 2. Globale Ausschlussliste für das "Relaxed Exclusion" berechnen
        int safeLimit = Math.min(exclusionLimit, sortedInteractions.size());
        List<BooleanAssignment> globalTopExcludes = sortedInteractions.subList(0, safeLimit);

        // 3. Rekursion starten
        return ddminRecursive(sortedInteractions, globalTopExcludes);
    }

    /**
     * Internal recursive worker for the Delta Debugging reduction.
     * <p>
     * The algorithm operates as follows:
     * <ol>
     * <li><b>Block Test:</b> It attempts to sample a configuration containing the entire
     * current block. If the test passes (PASS), the entire block is pruned.</li>
     * <li><b>Divide:</b> If the block test fails or results in UNSAT, the block is split
     * into two halves.</li>
     * <li><b>Conquer:</b> The method recurses on both halves to isolate individual
     * faulty patterns.</li>
     * </ol>
     *
     * @param currentBlock       The subset of interactions currently being analyzed.
     * @param globalTopExcludes  A pre-calculated list of high-priority patterns to be
     * negated in the SAT solver to isolate the current test.
     * @return The subset of {@code currentBlock} that could not be proven false.
     */
    private static List<BooleanAssignment> ddminRecursive(
            List<BooleanAssignment> currentBlock,
            List<BooleanAssignment> globalTopExcludes) {

        // --- BASIS-FÄLLE ---
        if (currentBlock.isEmpty()) {
            return new ArrayList<>();
        }

        // Wenn nur noch 1 Pattern übrig ist, teste es direkt (Abbruchbedingung)
        if (currentBlock.size() == 1) {
            BooleanAssignment singlePattern = currentBlock.get(0);
            List<int[]> include = Collections.singletonList(singlePattern.get());
            List<int[]> exclude = globalTopExcludes.stream()
                    .filter(p -> !p.equals(singlePattern))
                    .map(IntegerList::get).collect(Collectors.toList());

            Result<BooleanSolution> res = updater.complete(include, exclude, null);
            if (res.isPresent()) {
                boolean fails = tester.test(res.get()).orElseThrow() == 1;
                if (!fails) {
                    return new ArrayList<>(); // PASS -> False Positive!
                }
            }
            // FAIL oder UNSAT -> Wir können es nicht verwerfen. Es bleibt in der Liste.
            List<BooleanAssignment> kept = new ArrayList<>();
            kept.add(singlePattern);
            return kept;
        }

        // --- BLOCK-TEST ---
        // Teste den gesamten aktuellen Block (wie ein riesiger Batch)
        List<int[]> includeBlock = currentBlock.stream().map(IntegerList::get).collect(Collectors.toList());
        List<int[]> excludeBlock = globalTopExcludes.stream()
                .filter(p -> !currentBlock.contains(p))
                .map(IntegerList::get).collect(Collectors.toList());

        Result<BooleanSolution> blockRes = updater.complete(includeBlock, excludeBlock, null);

        if (blockRes.isPresent()) {
            boolean fails = tester.test(blockRes.get()).orElseThrow() == 1;
            if (!fails) {
                // JACKPOT! Der gesamte Block (egal ob 50 oder 2000 Patterns) ist fehlerfrei!
                // O(log n) Pruning!
                return new ArrayList<>();
            }
        }

        // --- DIVIDE (TEILEN) ---
        // Wenn der Block FAIL war (oder UNSAT), müssen wir ihn in zwei Hälften zerlegen.
        int mid = currentBlock.size() / 2;
        List<BooleanAssignment> leftHalf = new ArrayList<>();//currentBlock.subList(0, mid);
        List<BooleanAssignment> rightHalf = new ArrayList<>();//currentBlock.subList(mid, currentBlock.size());
        for (int i = 0; i < currentBlock.size() - 1; i+=2) {
            leftHalf.add(currentBlock.get(i));
            rightHalf.add(currentBlock.get(i+1));
        }
        if (currentBlock.size() % 2 == 0){
            leftHalf.add(currentBlock.getLast());
        }

        // --- CONQUER (HERRSCHEN) ---
        List<BooleanAssignment> remainingFromLeft = ddminRecursive(leftHalf, globalTopExcludes);
        List<BooleanAssignment> remainingFromRight = ddminRecursive(rightHalf, globalTopExcludes);

        // --- MERGE (ZUSAMMENFÜHREN) ---
        List<BooleanAssignment> combinedRootCauses = new ArrayList<>();
        combinedRootCauses.addAll(remainingFromLeft);
        combinedRootCauses.addAll(remainingFromRight);

        return combinedRootCauses;
    }

    /**
     * Reduces a list of potentially faulty feature interactions by systematically sampling
     * and testing new configurations (Delta Debugging approach).
     * <p>
     * To efficiently eliminate false positives, this method tests interactions in groups (batches).
     * If a generated test configuration for a batch passes successfully, all interactions contained
     * within that batch are proven to be fault-free and are subsequently removed from the candidate pool.
     * <p>
     * <b>Algorithmic Optimization (Relaxed Exclusion):</b><br>
     * The interactions are first sorted in descending order based on their failure frequency.
     * When sampling a new test configuration, the algorithm avoids explicitly excluding *all* other
     * patterns, as doing so almost always leads to unsolvable constraints (UNSAT) within the
     * underlying feature model. Instead, it applies a relaxed exclusion strategy that only negates
     * the strongest top-ranked candidates, bounded by the {@code exclusionLimit}.
     *
     * @param interactions   The initial list of minimal, potentially faulty interactions
     * (candidates) to be reduced.
     * @param batchsize      The maximum number of interactions to be tested simultaneously
     * within a single generated configuration. Must be strictly greater than 0.
     * @param failSupportMap A map assigning the absolute frequency (support) in failing
     * configurations to each interaction. Used to rank genuine bugs
     * higher for the relaxed exclusion strategy.
     * @param exclusionLimit The maximum number of top-ranked interactions to actively exclude
     * (negate) during sampling to prevent architectural conflicts (UNSAT)
     * in the SAT solver.
     * @return A reduced list of interactions from which proven fault-free candidates
     * (false positives) have been successfully filtered out.
     * @throws IllegalArgumentException if {@code batchsize} is less than 1.
     */

    // WICHTIG: Signatur anpassen! Du musst die failSupportMap aus der main() übergeben.
    private static List<BooleanAssignment> reduceInteractionsInBatches(
        List<BooleanAssignment> interactions,
        int batchsize,
        HashMap<BooleanAssignment, Integer> failSupportMap,
        int exclusionLimit) {

        if (batchsize < 1) throw new IllegalArgumentException("Batchsize has to be greater than 0.");

        // 1. Sortieren nach Häufigkeit (echte Bugs nach oben!)
        List<BooleanAssignment> sortedInteractions = new ArrayList<>(interactions);
        sortedInteractions.sort((p1, p2) -> {
            int supp2 = failSupportMap.getOrDefault(p2, 0);
            int supp1 = failSupportMap.getOrDefault(p1, 0);
            return Integer.compare(supp2, supp1);
        });

        List<BooleanAssignment> reducedInteractions = new ArrayList<>(sortedInteractions);

        // 2. Relaxed Exclusion: Wir schließen nur noch die Top 50 (oder z.B. 2% der Liste) aus.
        exclusionLimit = Math.min(exclusionLimit, sortedInteractions.size());
        List<BooleanAssignment> topCandidatesToExclude = sortedInteractions.subList(0, exclusionLimit);

        for (int i = 0; i < sortedInteractions.size(); i += batchsize) {
            int end = Math.min(i + batchsize, sortedInteractions.size());
            List<BooleanAssignment> currentBatch = sortedInteractions.subList(i, end);

            List<int[]> include = currentBatch.stream().map(IntegerList::get).collect(Collectors.toList());

            // 3. Batched Exclude: Schließe nur die Top-Kandidaten aus, die NICHT im aktuellen Batch sind
            List<int[]> exclude = topCandidatesToExclude.stream()
                    .filter(p -> !currentBatch.contains(p))
                    .map(IntegerList::get).collect(Collectors.toList());

            Result<BooleanSolution> batchConfigRes = updater.complete(include, exclude, null);

            if (batchConfigRes.isPresent()) {
                BooleanAssignment config = batchConfigRes.get();
                boolean fails = tester.test(config).orElseThrow() == 1;

                if (!fails) {
                    // Der ganze Batch ist sauber -> alle entfernen!
                    reducedInteractions.removeAll(currentBatch);
                    continue;
                }
            }

            // Fallback: Einzelne Prüfung, falls der Batch fehlschlägt oder UNSAT ist
            for (BooleanAssignment singlePattern : currentBatch) {
                List<int[]> singleInclude = new ArrayList<>(Collections.singleton(singlePattern.get()));

                // 4. Single Exclude: Auch hier nur die Top-Kandidaten ausschließen!
                List<int[]> singleExclude = topCandidatesToExclude.stream()
                        .filter(p -> !p.equals(singlePattern))
                        .map(IntegerList::get).collect(Collectors.toList());

                Result<BooleanSolution> singleConfigRes = updater.complete(singleInclude, singleExclude, null);

                if (singleConfigRes.isEmpty()){
                    // Wenn es selbst mit nur 50 Excludes UNSAT ist, ist das Pattern
                    // extrem hart gekoppelt. Wir behalten es vorerst.
                    continue;
                }

                BooleanAssignment singleConfig = singleConfigRes.get();
                boolean singleFails = tester.test(singleConfig).orElseThrow() == 1;
                if (!singleFails) {
                    reducedInteractions.remove(singlePattern);
                }
            }
        }
        return reducedInteractions;
}

    /**
     * This method reduces the minimal patterns by sampling new configs with exactly one minimal pattern included
     * and every other minimal pattern excluded to potentially exclude more non-faulty interactions.
     *
     * @param minimalPatterns
     * @return
     */
    private static List<BooleanAssignment> reduceInteractions(List<BooleanAssignment> minimalPatterns) {
        List<BooleanAssignment> reducedMinimalPatterns = new ArrayList<>(minimalPatterns);
        // sample configs, die gezielt nur ein pattern enthalten und teste, um evtl. mehr patters ausschließen zu können


        for (BooleanAssignment minimalPattern : minimalPatterns) {
            List<int[]> exclude = minimalPatterns.stream()
                    .map(IntegerList::get).collect(Collectors.toList());
            exclude.remove(minimalPattern.get());

            List<int[]> include = new ArrayList<>(Collections.singleton(minimalPattern.get()));
            Result<BooleanSolution> configRes = updater.complete(include, exclude, null);

            if (configRes.isEmpty()) continue;

            BooleanAssignment config = configRes.get();
            boolean fails = tester.test(config).orElseThrow() == 1;
            if (!fails) {
                reducedMinimalPatterns.remove(minimalPattern);
            }
        }
        return reducedMinimalPatterns;
    }

    private static void testSampledConfigs(Path passingConfigsPath, Path failingConfigsPath, boolean onlyPositiveInts) {
        try(
                BufferedWriter passingConfigs = Files.newBufferedWriter(passingConfigsPath, Charset.defaultCharset());
                BufferedWriter failingConfigs = Files.newBufferedWriter(failingConfigsPath, Charset.defaultCharset());
                ) {
            Set<Integer> core = Arrays.stream(coreFeatures.get())
                    .boxed()
                    .collect(Collectors.toSet());

            for (BooleanAssignment configuration : sample) {
                boolean fails = tester.test(configuration).orElseThrow() == 1;

                // Only write non-core features, because they cannot be found as an error
                int[] features = Arrays.stream(configuration.get())
                        .filter(feature -> feature != 0)
                        .filter(feature -> !core.contains(feature))
                        .toArray();
                // For algos like AlgoAprioriFAST
                if (onlyPositiveInts)
                    features = mapFeaturesToPositiveInts(features);

                String configStr = Arrays.stream(features)
                        .mapToObj(String::valueOf)
                        .reduce("", (acc, f) -> acc + f + " ");
                if (fails) {
                    failing++;
                    failingConfigs.write(configStr + "\n");
                } else {
                    passing++;
                    passingConfigs.write(configStr + "\n");
                }
            }
            passingConfigs.flush();
            failingConfigs.flush();
        } catch (IOException e) {
            System.out.println(e.getMessage());
            throw new RuntimeException(e);
        }
    }

    private static List<BooleanAssignment> getMinimalInteractions(List<Pair<BooleanAssignment, Double>> growthRatesPerPattern) {
        List<BooleanAssignment> minimalPatterns = new ArrayList<>();

        for (Pair<BooleanAssignment, Double> pair : growthRatesPerPattern) {
            BooleanAssignment pattern = pair.getFirst();

            boolean isSuperSet = false;
            for (BooleanAssignment minimalPattern : minimalPatterns) {
                if (superset(pattern.get(), minimalPattern.get())){
                    isSuperSet = true;
                    break;
                }
            }
            if (!isSuperSet) {
                minimalPatterns.add(pattern);
            }
        }
        return minimalPatterns;
    }

    private static boolean superset(int[] superSet, int[] subSet) {
        for (int item : subSet) {
            boolean contains = false;
            for (int subItem : superSet) {
                if (item == subItem) {
                    contains = true;
                    break;
                }
            }
            if (!contains) return false;
        }
        return true;
    }

    private static ArrayList<Pair<BooleanAssignment, Double>> filterInfiniteGrowthRates(HashMap<BooleanAssignment, Double> growthRatePerPatterns) {
        return growthRatePerPatterns.entrySet().stream()
                .filter(e -> e.getValue() == Double.POSITIVE_INFINITY)
                .map(e -> new Pair<>(e.getKey(), e.getValue()))
                .collect(Collectors.toCollection(ArrayList::new));
    }

    /**
     * Computes the growth rates of each pattern between the two classes
     * @param failSuppPerPattern
     * @param passSuppPerPattern
     * @param failingConfigAmount
     * @param passingConfigAmount
     * @return
     */
    private static HashMap<BooleanAssignment, Double> computeGrowthRates(
            HashMap<BooleanAssignment, Integer> failSuppPerPattern,
            HashMap<BooleanAssignment, Integer> passSuppPerPattern,
            double failingConfigAmount, double passingConfigAmount) {

        HashMap<BooleanAssignment, Double> growthRatePerPattern = new HashMap<>();
        for (Map.Entry<BooleanAssignment, Integer> entry : failSuppPerPattern.entrySet()) {
            BooleanAssignment pattern = entry.getKey();
            int support = entry.getValue();

            if (!passSuppPerPattern.containsKey(pattern)) {
                // Infinite growth rate because pattern only occurs in failing configs
                growthRatePerPattern.put(pattern, Double.POSITIVE_INFINITY);
            } else {
                double relativeSupportFail = (double) support / failingConfigAmount;
                double relativeSupportPass = (double) passSuppPerPattern.get(pattern) / passingConfigAmount;
                double growthRate = relativeSupportFail /  relativeSupportPass;
                growthRatePerPattern.put(pattern, growthRate);
            }
        }
        return growthRatePerPattern;
    }

    /**
     * Transforms patterns from a list of itemsets to a map mapping a boolean assignment to it's corresponding support value
     * @param patterns
     * @param fromOnlyPositive Has to be true, if the features were mapped to only positive ints prior
     * @return
     */
    private static HashMap<BooleanAssignment, Integer> transformPatterns(List<Itemset> patterns, boolean fromOnlyPositive) {
        HashMap<BooleanAssignment, Integer> suppPerPattern = new HashMap<>(patterns.size());
        if (fromOnlyPositive){
            int maxFeatureInt = sample.getVariableMap().size();
            for (Itemset itemset : patterns){
                suppPerPattern.put(new BooleanAssignment(mapFeaturesToNegativeInts(itemset.itemset, maxFeatureInt)), itemset.getAbsoluteSupport());
            }
            return suppPerPattern;
        }
        for (Itemset itemset : patterns) {
            suppPerPattern.put(new BooleanAssignment(itemset.itemset), itemset.getAbsoluteSupport());
        }
        return suppPerPattern;
    }
    private static BooleanAssignmentList sampleTWise(BooleanAssignmentList fmClauses, int T, int configLimit) {
        return Computations.of(fmClauses)
                .map(YASA::new) // Prüfe hier ggf. deinen genauen Import-Pfad für YASA
                .set(
                        YASA.COMBINATION_SET,
                        Computations.of(fmClauses)
                                .map(VariableCombinationSpecification.VariableCombinationSpecificationComputation::new)
                                .set(VariableCombinationSpecification.VariableCombinationSpecificationComputation.T, T)
                )
                .set(YASA.CONFIGURATION_LIMIT, configLimit)
                .computeResult()
                .orElseThrow();
        }

    private static BooleanAssignmentList sampleRandomConfigs(BooleanAssignmentList clauses, int configAmount) {
        return Computations.of(clauses)
                .map(ComputeSolutionsSAT4J::new)
                .set(ComputeSolutionsSAT4J.SELECTION_STRATEGY, ISelectionStrategy.NonParameterStrategy.FAST_RANDOM)
                .set(ComputeSolutionsSAT4J.LIMIT, configAmount)
                .set(ComputeSolutionsSAT4J.RANDOM_SEED, 1L)
                .compute();
    }

    private static BooleanAssignmentList parseModel(Path modelPath) throws IOException {
        XMLFeatureModelFormulaParser parser = new XMLFeatureModelFormulaParser();
        IFormula model = parser.parse(new FileInputMapper(modelPath, Charset.defaultCharset()))
                .orElseThrow();
        return Computations.async(model)
                .map(ComputeNNFFormula::new)
                .map(ComputeCNFFormula::new)
                .map(ComputeBooleanClauseList::new)
                .computeResult().orElseThrow();
    }

    private static final class TestManager implements IConfigurationTester {

        private final ArrayList<int[]> faultyInteractions;

        public TestManager() {
            this.faultyInteractions = new  ArrayList<>();
        }

        public boolean addInteraction(int... faultyInteraction) {
            if (updater == null) throw new IllegalStateException("Updater is null");

            List<int[]> include = new ArrayList<>(Collections.singleton(faultyInteraction));
            Result<BooleanSolution> solution = updater.complete(include, null, null);
            if (solution.isEmpty()){
                throw new RuntimeException("Interaction " +  Arrays.toString(faultyInteraction) + " is not satisfyable");
            }
            return faultyInteractions.add(faultyInteraction);
        }

        public boolean addInteraction(String... interaction){
            var variableMap = sample.getVariableMap();
            int[] faultyInteraction = new int[interaction.length];
            for (int i = 0; i < interaction.length; i++) {
                int feature = variableMap.get(interaction[i]).orElseThrow();
                faultyInteraction[i] = feature;
            }
            return addInteraction(faultyInteraction);
        }

        public List<int[]> getInteractions() {
            return faultyInteractions;
        }

        @Override
        public VariableMap getVariableMap() {
            return null;
        }

        @Override
        public void setVariableMap(VariableMap variableMap) {

        }

        /**
         *
         * @param configuration
         * @return 1 if config is failing
         */
        @Override
        public Result<Integer> test(BooleanAssignment configuration) {
            boolean testResult = faultyInteractions.stream().anyMatch(configuration::containsAll);
            return Result.of(testResult ? 1 : 0);
        }

        public String printInteractions(){
            StringBuilder sb = new StringBuilder();
            sb.append("Interactions: ");
            for (int[] faultyInteraction : faultyInteractions) {
                sb.append(Arrays.toString(faultyInteraction));
                if (faultyInteractions.indexOf(faultyInteraction) != faultyInteractions.size() - 1) {
                    sb.append(" or ");
                }
            }
            return sb.toString();
        }

        /**
         *
         * @param configuration
         * @return True is the given configuration is failing.
         */
        public boolean isFailing(BooleanAssignment configuration){
            return this.test(configuration).orElseThrow() == 1;
        }
    }
}
