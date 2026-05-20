package de.featjar.analysis.sat4j.computation;

import ca.pfv.spmf.algorithms.frequentpatterns.apriori_fast.AlgoAprioriFAST;
import ca.pfv.spmf.algorithms.frequentpatterns.apriori_fast.AlgoAprioriFASTClose;
import ca.pfv.spmf.algorithms.frequentpatterns.apriori_fast.AlgoAprioriFASTInverse;
import ca.pfv.spmf.patterns.itemset_array_integers_with_count.Itemset;
import ca.pfv.spmf.patterns.itemset_array_integers_with_count.Itemsets;
import ca.pfv.spmf.algorithms.frequentpatterns.fpgrowth.AlgoFPGrowth;
import de.featjar.analysis.sat4j.solver.ISelectionStrategy;
import de.featjar.analysis.sat4j.solver.ModalImplicationGraph;
import de.featjar.base.FeatJAR;
import de.featjar.base.computation.Computations;
import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.Progress;
import de.featjar.base.data.Pair;
import de.featjar.base.data.Result;
import de.featjar.base.io.input.FileInputMapper;
import de.featjar.formula.VariableMap;
import de.featjar.formula.assignment.BooleanAssignment;
import de.featjar.formula.assignment.BooleanAssignmentList;
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
import java.util.concurrent.ExecutionException;
import java.util.stream.Collectors;


public class CSL {

    public final Dependency<Integer> T = Dependency.newDependency(Integer.class);
    public final Dependency<ModalImplicationGraph> MIG =
            Dependency.newDependency(ModalImplicationGraph.class);

    public final Dependency<BooleanAssignmentList> FAILING_CONFIGS =
            Dependency.newDependency(BooleanAssignmentList.class);
    public final Dependency<BooleanAssignmentList> PASSING_CONFIGS =
            Dependency.newDependency(BooleanAssignmentList.class);
    public final Dependency<Double> MINSUPP =  Dependency.newDependency(Double.class);
    public final Dependency<Double> MINCONF =  Dependency.newDependency(Double.class);


    private ARMTester tester;
    private RandomConfigurationUpdater updater;
    private BooleanAssignmentList sample;
    private IFormula featureModelFormula;
    private BooleanAssignmentList featureModelCNF;
    private BooleanAssignment coreFeatures;
    private final String featureModelFile = "e-shop-model.xml";
    private final String basePath =
            System.getProperty("user.home") + "/Documents/studium/Bachelorarbeit/".replace("/", File.separator);
    private final String resourcesFolder = "resources_featjar/".replace("/", File.separator);
    private int passing = 0, failing = 0;
    private boolean onlyPositiveInts = false;

   
    
    public CSL(){

    }

    public Result<BooleanAssignmentList> compute(List<Object> dependencyList, Progress progress) {
        BooleanAssignmentList passingConfigAssignmentList = PASSING_CONFIGS.get(dependencyList);
        BooleanAssignmentList failingConfigAssignmentList = FAILING_CONFIGS.get(dependencyList);

        return null;
    }

    public static void main(String[] args) throws IOException, ExecutionException, InterruptedException {
        CSL csl = new CSL();
        csl.main();
    }
    
    public void main() throws ExecutionException, InterruptedException, IOException {
        setup();

        // Third parameter must be true for AlgoAprioriFAST
        // This converts the mixture of positive and negative integers for feature representation to only positive
        // -> This mapping has to be converted back to featjar standard after running apriori
        this.onlyPositiveInts = true;

        int configAmount = 100;
        this.sample = sampleRandomConfigs(this.featureModelCNF, configAmount);
        //sample = sampleTWise(featureModelCNF, 3, configAmount);
        this.updater = new RandomConfigurationUpdater(this.featureModelCNF, 2L);

        // Simulate faulty interactions
        this.tester = new ARMTester(123L, this.featureModelCNF, this.updater, this.coreFeatures, this.sample);
        this.tester.simulateInteractionWithRandomFeatures(ARMTester.InteractionType.AND, true);
        Pair<BooleanAssignmentList, BooleanAssignmentList> testedConfigs = testSample(onlyPositiveInts);
        BooleanAssignmentList passingConfigs = testedConfigs.getFirst();
        BooleanAssignmentList failingConfigs = testedConfigs.getSecond();

        /*
        CompletableFuture<Itemsets> oneWisePassingInteractionsFuture = runFpGrowth(true, 1, 1, 1);
        CompletableFuture<Itemsets> oneWiseFailingInteractionsFuture = runFpGrowth(false, 1, 1, 1);
        CompletableFuture.allOf(oneWisePassingInteractionsFuture, oneWiseFailingInteractionsFuture);

        Itemsets oneWisePassingInteractionsItemsets = oneWisePassingInteractionsFuture.get();
        Itemsets oneWiseFailingInteractionsItemsets = oneWiseFailingInteractionsFuture.get();
         */

        int minInteractionSize = 1;
        int maxInteractionSize = 2;
        long timestamp = System.currentTimeMillis();
        //CompletableFuture<Itemsets> passingFuture = runFpGrowth(true, 1, minInteractionSize, maxInteractionSize);
        //CompletableFuture<Itemsets> failingFuture = runFpGrowth(false, 1, minInteractionSize, maxInteractionSize);
        CompletableFuture<Itemsets> passingFuture = runAprioriFast(true, 1, maxInteractionSize);
        CompletableFuture<Itemsets> failingFuture = runAprioriFast(false, 1, maxInteractionSize);
        //CompletableFuture<Itemsets> passingFuture = runAprioriFastClose(true, 1, maxInteractionSize);
        //CompletableFuture<Itemsets> failingFuture = runAprioriFastClose(false, 1, maxInteractionSize);
        //CompletableFuture<Itemsets> passingFuture = runAprioriFastInverse(true, 1, this.passing, maxInteractionSize);
        //CompletableFuture<Itemsets> failingFuture = runAprioriFastInverse(false, 1, this.failing, maxInteractionSize);


        // Sobald ein Algorithmus fertig ist, wandelt er asynchron seine Itemsets in eine schnelle Map um.
        CompletableFuture<Map<InteractionKey, Integer>> passingMapFuture = passingFuture.thenApplyAsync(CSL::getInteractionMap);
        CompletableFuture<Map<InteractionKey, Integer>> failingMapFuture = failingFuture.thenApplyAsync(CSL::getInteractionMap);

        // Für alle interaktionen alle metriken auf ein mal berechnen
        ContrastMetricCalculator calc = new ContrastMetricCalculator(this.passing, this.failing);
        CompletableFuture<List<InteractionResult>> scoredInteractionsFuture =
                passingMapFuture.thenCombine(failingMapFuture,
                        (passMap, failMap) -> scoreInteractions(passMap, failMap, calc));

        List<InteractionResult> scoredInteractions = scoredInteractionsFuture.join();

        int k = 20;
        Comparator<InteractionResult> ochiaiComparator = (o1, o2) -> Float.compare(o1.ochiai, o2.ochiai);
        Comparator<InteractionResult> dStarComparator = (o1, o2) -> Float.compare(o1.dStar, o2.dStar);
        Comparator<InteractionResult> growthRateComparator = (o1, o2) -> Float.compare(o1.growthRate, o2.growthRate);
        recordTopKResults(scoredInteractions, "ochiai", k, ochiaiComparator);
        recordTopKResults(scoredInteractions, "d-star", k, dStarComparator);
        recordTopKResults(scoredInteractions, "growth-rate", k, growthRateComparator);

        System.out.printf("Time for pattern mining and interaction processing: %d ms", System.currentTimeMillis() - timestamp);
        FeatJAR.deinitialize();
        System.exit(0);
    }

    private List<InteractionResult> scoreInteractions(Map<InteractionKey, Integer> passMap, Map<InteractionKey, Integer> failMap,
                                                      ContrastMetricCalculator calc) {
        // Da wir alle einzigartigen Interaktionen brauchen, packen wir die Keys in ein Set
        Set<InteractionKey> allKeys = new HashSet<>(passMap.keySet());
        allKeys.addAll(failMap.keySet());

        List<InteractionResult> scoredResults = new ArrayList<>(allKeys.size());

        // Iteriere über alle gefundenen Muster und berechne die Scores
        for (InteractionKey key : allKeys) {
            // getOrDefault schützt uns davor, dass ein Muster nur in einer Map existiert
            int passes = passMap.getOrDefault(key, 0);
            int fails = failMap.getOrDefault(key, 0);

            float ochiai = calc.computeOchiai(passes, fails);
            float dStar = calc.computeDStar(passes, fails, 2.0);
            float growthRate = calc.computeGrowthRate(passes, fails);

            scoredResults.add(new InteractionResult(key, ochiai, dStar, growthRate, 0, 0, 0 ,0));
        }

        return scoredResults;
    }

    private static Map<InteractionKey, Integer> getInteractionMap(Itemsets itemsets) {
        int items = itemsets.getLevels().stream().map(List::size).reduce(0, Integer::sum);
        Map<InteractionKey, Integer> passMap = new HashMap<>((int) (items / 0.75));
        for (List<Itemset> level : itemsets.getLevels()) {
            for (Itemset itemset : level) {
                passMap.put(new InteractionKey(itemset.itemset), itemset.getAbsoluteSupport());
            }
        }
        return passMap;
    }

    private void setup() throws IOException {
        FeatJAR.initialize();
        // Paths for configs, fm
        Path modelPath = Path.of(this.basePath, this.resourcesFolder, this.featureModelFile);
        this.featureModelFormula = parseModel(modelPath);
        this.featureModelCNF = Computations.async(this.featureModelFormula)
                .map(ComputeNNFFormula::new)
                .map(ComputeCNFFormula::new)
                .map(ComputeBooleanClauseList::new)
                .computeResult().orElseThrow();

        this.coreFeatures = Computations.async(featureModelCNF)
                .map(ComputeCoreSAT4J::new)
                .computeResult().orElseThrow().getFirst();
    }

    /**
     * Tests the configs, sets core features to zero and writes them to files as a preparation for the ARM algorithm.
     * @param onlyPositiveInts
     * @return
     */
    private Pair<BooleanAssignmentList, BooleanAssignmentList> testSample(boolean onlyPositiveInts) {
        Set<Integer> coreFeaturesSet = Arrays.stream(this.coreFeatures.get())
                .boxed().collect(Collectors.toCollection(HashSet::new));
        // Test configs
        Pair<BooleanAssignmentList, BooleanAssignmentList> testedSample = this.tester.testSample(this.sample);
        BooleanAssignmentList passingConfigs = testedSample.getFirst();
        this.passing = passingConfigs.size();
        BooleanAssignmentList failingConfigs = testedSample.getSecond();
        this.failing = failingConfigs.size();

        String configs = basePath + resourcesFolder;
        Path passingConfigsPath = Path.of(configs, "passingConfigs.txt");
        passingConfigs = removeFromConfigs(passingConfigs, coreFeaturesSet);
        writeConfigsToFile(passingConfigs, passingConfigsPath, onlyPositiveInts);

        Path failingConfigsPath = Path.of(configs, "failingConfigs.txt");
        failingConfigs = removeFromConfigs(failingConfigs, coreFeaturesSet);
        writeConfigsToFile(failingConfigs, failingConfigsPath, onlyPositiveInts);

        System.out.println("Passing: " + passing);
        System.out.println("Failing: " + failing);
        System.out.println("Sample size: " + sample.size());
        tester.printInteractions();
        return new Pair<>(passingConfigs, failingConfigs);
    }

    /**
     * Removes the given feature ints from the configs.
     * @param configs
     * @param featuresToRemove
     * @return
     */
    public BooleanAssignmentList removeFromConfigs(BooleanAssignmentList configs, Set<Integer> featuresToRemove){
        for (BooleanAssignment config : configs){
            for (int i = 0; i < config.get().length; i++) {
                int feature = config.get(i);
                if (feature != 0 && featuresToRemove.contains(feature)){
                    config.get()[i] = 0;
                }
            }
        }
        return configs;
    }

    public void recordTopKResults(List<InteractionResult> scoredInteractions, String metricName, int k, Comparator<InteractionResult> comparator) {
        // Absteigend sortieren
        scoredInteractions.sort(comparator.reversed());

        int limit = Math.min(k, scoredInteractions.size());
        List<Pair<BooleanAssignment, Float>> topKForOutput = new ArrayList<>(limit);

        int maxFeatureInt = sample.getVariableMap().size();

        // NUR für diese Top K machen wir die teure Umrechnung!
        for (int i = 0; i < limit; i++) {
            InteractionResult result = scoredInteractions.get(i);

            // 1. Array umwandeln (wenn nötig)
            int[] negativeInts = onlyPositiveInts
                    ? mapFeaturesToNegativeInts(result.features.array, maxFeatureInt)
                    : result.features.array;

            // 2. BooleanAssignment erstellen
            BooleanAssignment assignment = new BooleanAssignment(negativeInts);

            // Wert für die aktuelle Metrik holen
            float metricValue;
            switch (metricName) {
                case "ochiai": {
                    metricValue = result.ochiai;
                    break;
                }
                case "d-Star": {
                    metricValue = result.dStar;
                    break;
                }
                default: {
                    metricValue = result.growthRate;
                    break;
                }
            };

            topKForOutput.add(new Pair<>(assignment, metricValue));
        }
        // Ab hier kannst du deine alten Methoden zum Drucken aufrufen
        writeScoredInteractionsToFile(topKForOutput, metricName + ".txt");
        List<BooleanAssignment> results = topKForOutput.stream().map(Pair::getFirst).collect(Collectors.toList());
        printResults(results, metricName, limit);
    }

    public CompletableFuture<Itemsets> runAprioriFastClose(boolean passing, int occurrences, int maxInteractionSize){
        AlgoAprioriFASTClose algo = new AlgoAprioriFASTClose();
        algo.setMaximumPatternLength(maxInteractionSize);

        return runMinerAsync(passing, occurrences,
                (inputPath, minsup) -> algo.runAlgorithm(minsup, inputPath, null, 30),
                algo::printStats
        );
    }

    public CompletableFuture<Itemsets> runAprioriFastInverse(boolean passing, int minOccurrences, int maxOccurrences, int maxInteractionSize){
        AlgoAprioriFASTInverse algo = new AlgoAprioriFASTInverse();
        algo.setMaximumPatternLength(maxInteractionSize);

        return runMinerAsync(passing, minOccurrences,
                ((inputPath, minsup) -> algo.runAlgorithm(minsup, minsup * (double) (maxOccurrences/minOccurrences), inputPath, null, 30)),
                algo::printStats
        );
    }

    public CompletableFuture<Itemsets> runAprioriFast(boolean passing, int occurrences, int maxInteractionSize){
        AlgoAprioriFAST algo = new AlgoAprioriFAST();
        algo.setMaximumPatternLength(maxInteractionSize);

        return runMinerAsync(passing, occurrences,
                ((inputPath, minsup) -> algo.runAlgorithm(minsup, inputPath, null, 30)),
                algo::printStats
        );
    }


    public CompletableFuture<Itemsets> runFpGrowth(boolean passing, int occurrences, int minInteractionSize, int maxInteractionSize){
        AlgoFPGrowth fpGrowth = new AlgoFPGrowth();
        fpGrowth.setMinimumPatternLength(minInteractionSize);
        fpGrowth.setMaximumPatternLength(maxInteractionSize);

        return runMinerAsync(passing, occurrences,
                (inputPath, minsup) -> fpGrowth.runAlgorithm(inputPath, null, minsup),
                fpGrowth::printStats
        );
    }

    /**
     * Maps (complete) feature sets / configs from the representation of only positive integers to the FearJAR
     * representation with positive and negative integers for included and excluded features.
     * @param features
     * @param maxFeatureInt
     * @return
     */
    private int[] mapFeaturesToNegativeInts(int[] features, int maxFeatureInt){
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
    private int[] mapFeaturesToPositiveInts(int[] features){
        return Arrays.stream(features).map(f -> {
            if (f < 0) {
                return Integer.MAX_VALUE + f;
            }
            return f;
        }).toArray();
    }


    private void writeScoredInteractionsToFile(Collection<Pair<BooleanAssignment, Float>> reducedMinimalInteractions, String path) {
        String filePath = basePath + resourcesFolder + path;
        VariableMap variableMap = sample.getVariableMap();
        try (PrintWriter out = new PrintWriter(filePath)) {
            for (Pair<BooleanAssignment, Float> interaction : reducedMinimalInteractions) {
                out.printf("%s: %f", interaction.getFirst().print(), interaction.getSecond());
                out.print("   ");
                for (int feature : interaction.getFirst().get()){
                    String sFeature = variableMap.get(Math.abs(feature)).orElseThrow();
                    if (feature < 0){
                        out.printf("not-%s ", sFeature);
                    } else {
                        out.printf("%s ", sFeature);
                    }
                }
                out.println();
            }
            out.flush();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }
    }

    private void writeInteractionsToFile(Collection<BooleanAssignment> interactions, String path) {
        String filePath = basePath + resourcesFolder + path;
        VariableMap variableMap = sample.getVariableMap();
        try (PrintWriter out = new PrintWriter(filePath)) {
            for (BooleanAssignment pattern : interactions) {
                out.print(pattern.print());
                out.print("   ");
                for (int feature : pattern.get()){
                    String sFeature = variableMap.get(Math.abs(feature)).orElseThrow();
                    if (feature < 0){
                        out.printf("not-%s ", sFeature);
                    } else {
                        out.printf("%s ", sFeature);
                    }
                }
                out.println();
            }
            out.flush();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }
    }

    /**
     * Prints which simulated interaction is contained or not contained in the List.
     * @param suspectInteractions List of potential faulty interactions.
     */
    public void printResults(Collection<BooleanAssignment> suspectInteractions, String metricName, int k) {
        System.out.printf("\n========= Results for %s with top-k = %d =========\n", metricName, k);
        boolean foundAllInteractions = true;
        for (int[] simulatedInteraction : tester.getInteractions()) {
            boolean foundThisInteraction = false;
            for (BooleanAssignment foundInteraction : suspectInteractions) {
                if (foundInteraction.get().length == simulatedInteraction.length &&
                        foundInteraction.containsAll(simulatedInteraction)) {
                    System.out.println("✅ Interaction " + Arrays.toString(simulatedInteraction) + " found in suspect list.");
                    foundThisInteraction = true;
                    break;
                }
            }
            if (!foundThisInteraction) {
                System.out.println("❌ Interaction " + Arrays.toString(simulatedInteraction) + " NOT found in suspect list.");
                foundAllInteractions = false;
            }
        }
        if (foundAllInteractions) {
            System.out.println("--------- All interactions found! ---------");
        }
    }


    public void writeConfigsToFile(BooleanAssignmentList configs, Path path, boolean onlyPositiveInts) {
        try(BufferedWriter writer = Files.newBufferedWriter(path, Charset.defaultCharset()))
        {
            for (BooleanAssignment configuration : configs) {
                // Only write non-zero features
                int[] features = Arrays.stream(configuration.get())
                        .filter(feature -> feature != 0)
                        .toArray();
                // For algos like AlgoAprioriFAST
                if (onlyPositiveInts)
                    features = mapFeaturesToPositiveInts(features);

                String configStr = Arrays.stream(features)
                        .mapToObj(String::valueOf)
                        .reduce("", (acc, f) -> acc + f + " ");
                writer.write(configStr + "\n");
            }
            writer.flush();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Transforms itemsets to a map mapping a boolean assignment to it's corresponding support value
     * @param itemsets
     * @param fromOnlyPositive Has to be true, if the features were mapped to only positive ints prior
     * @return
     */
    private Map<BooleanAssignment, Integer> transformPatterns(Itemsets itemsets, boolean fromOnlyPositive) {
        int totalElements = 0;
        for (List<Itemset> level : itemsets.getLevels()) {
            totalElements += level.size();
        }
        int mapCapacity = (int) Math.ceil(totalElements / 0.75);
        Map<BooleanAssignment, Integer> suppPerPattern = new HashMap<>(mapCapacity);

        int maxFeatureInt = sample.getVariableMap().size();
        for (List<Itemset> level : itemsets.getLevels()) {
            for (Itemset itemset : level) {
                int[] features = fromOnlyPositive
                        ? mapFeaturesToNegativeInts(itemset.itemset, maxFeatureInt)
                        : itemset.itemset;

                suppPerPattern.put(new BooleanAssignment(features), itemset.getAbsoluteSupport());
            }
        }
        return suppPerPattern;
    }

    public BooleanAssignmentList sampleTWise(BooleanAssignmentList fmClauses, int T, int configLimit) {
        return Computations.of(fmClauses)
                .map(YASA::new)
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

    public BooleanAssignmentList sampleRandomConfigs(BooleanAssignmentList clauses, int configAmount) {
        return Computations.of(clauses)
                .map(ComputeSolutionsSAT4J::new)
                .set(ComputeSolutionsSAT4J.SELECTION_STRATEGY, ISelectionStrategy.NonParameterStrategy.FAST_RANDOM)
                .set(ComputeSolutionsSAT4J.LIMIT, configAmount)
                .set(ComputeSolutionsSAT4J.RANDOM_SEED, 1L)
                .compute();
    }

    public IFormula parseModel(Path modelPath) throws IOException {
        XMLFeatureModelFormulaParser parser = new XMLFeatureModelFormulaParser();
        return parser.parse(new FileInputMapper(modelPath, Charset.defaultCharset())).orElseThrow();
    }

    @FunctionalInterface
    private interface IMinerAction {
        Itemsets run(String inputPath, double minsup) throws Exception;
    }

    private CompletableFuture<Itemsets> runMinerAsync(boolean passing, int occurrences,
                                                      IMinerAction minerAction,
                                                      Runnable statsPrinter) {
        int configs = passing ? this.passing : this.failing;
        double minsup = (double) occurrences / configs;
        String fileName = passing ? "passingConfigs.txt" : "failingConfigs.txt";
        String path = basePath + resourcesFolder + fileName;

        return CompletableFuture.supplyAsync(() -> {
            try {
                return minerAction.run(path, minsup);
            } catch (Exception e) {
                throw new RuntimeException(e);
            } finally {
                synchronized (System.out) {
                    System.out.println("Stats for itemsets with passing = " + passing);
                    if (statsPrinter != null) {
                        statsPrinter.run();
                    }
                }
            }
        });
    }

    private static final class InteractionKey {
        final int[] array;
        final int hash;

        InteractionKey(int[] array) {
            this.array = array;
            this.hash = Arrays.hashCode(array); // SPMF liefert sortierte Arrays, das klappt perfekt
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            return Arrays.equals(array, ((InteractionKey) o).array);
        }

        @Override
        public int hashCode() { return hash; }
    }

    // Eine primitive, veränderbare Container-Klasse (spart 2 Integer-Objekte)
    private static final class SupportCounts {
        int pass = 0;
        int fail = 0;

        public SupportCounts(int pass, int fail) {
            this.pass = pass;
            this.fail = fail;
        }
    }

    /**
     * Container for all Metrics of an Interaction
     */
    public final class InteractionResult {
        public final InteractionKey features;
        public final float ochiai;
        public final float dStar;
        public final float growthRate;
        public final float confidenceFailing;
        public final float confidencePassing;
        public final float liftFailing;
        public final float liftPassing;

        public InteractionResult(InteractionKey features,
                                 float ochiai,
                                 float growthRate,
                                 float dStar,
                                 float confidencePassing,
                                 float confidenceFailing,
                                 float liftPassing,
                                 float liftFailing) {
            this.features = features;
            this.ochiai = ochiai;
            this.growthRate = growthRate;
            this.dStar = dStar;
            this.confidenceFailing = confidenceFailing;
            this.confidencePassing = confidencePassing;
            this.liftFailing = liftFailing;
            this.liftPassing = liftPassing;
        }
    }

}