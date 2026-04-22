package de.featjar.analysis.sat4j.computation;

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
import de.featjar.formula.computation.ComputeCNFFormula;
import de.featjar.formula.computation.ComputeNNFFormula;
import de.featjar.formula.io.xml.XMLFeatureModelFormulaParser;
import de.featjar.formula.structure.IFormula;

import java.io.*;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;

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
    private static BooleanAssignmentList clauses;
    private static BooleanAssignment coreFeatures;
    private static final String featureModelFile = "e-shop-model.xml";
    private static final String basePath = "/Documents/studium/Bachelorarbeit/".replace("/", File.separator);
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
        Path modelPath = Path.of(System.getProperty("user.home"), basePath, resourcesFolder, featureModelFile);
        clauses = parseModel(modelPath);

        sample = sampleConfigs(clauses, 80);
        updater = new RandomConfigurationUpdater(sample, 2L);
        coreFeatures = Computations.of(clauses)
                .map(ComputeCoreSAT4J::new).
                get().orElseThrow().getFirst();

        // Simulate faulty interactions
        tester = new TestManager();
        String interaction1 = "Purchase_value_scope269";
        tester.addInteractionByName(interaction1);

        String interaction2 = "Shipping_address277";
        tester.addInteractionByName(interaction2);

        String[] interaction3 = new String[]{"City149", "Thumbnail68"};
        int city149, thumbnail68;
        city149 = sample.getVariableMap().get(interaction3[0]).get();
        thumbnail68 = sample.getVariableMap().get(interaction3[1]).get();
        int[] i3 = new int[]{city149, thumbnail68};
        tester.addInteractionByName(interaction3);

        // Test configs
        String configs = System.getProperty("user.home") + basePath + resourcesFolder;
        Path passingConfigsPath = Path.of(configs, "passingConfigs.txt");
        Path failingConfigsPath = Path.of(configs, "failingConfigs.txt");

        testSampledConfigs(passingConfigsPath, failingConfigsPath);

        System.out.println("Passing: " + passing);
        System.out.println("Failing: " + failing);
        System.out.println("Sample size: " + sample.size());
        System.out.println(tester.printInteractions());

        // Run FPGrowth
        AlgoFPGrowth fpGrowth = new AlgoFPGrowth();
        fpGrowth.setMinimumPatternLength(1);
        fpGrowth.setMaximumPatternLength(2);

        // Find frequent patterns in both classes
        Itemsets passingItemsets = fpGrowth.runAlgorithm(String.valueOf(passingConfigsPath), null, 1.0 / passing);
        Itemsets failingItemsets = fpGrowth.runAlgorithm(String.valueOf(failingConfigsPath), null, 2.0 / failing);

        // Get frequent patterns
        List<Itemset> passingPatterns = passingItemsets.getLevels().stream().flatMap(Collection::stream).collect(Collectors.toList());
        List<Itemset> failingPatterns =  failingItemsets.getLevels().stream().flatMap(Collection::stream).collect(Collectors.toList());

        // Convert Itemset lists to a HashMap BooleanAssigment -> Absolute support (Anzahl der Vorkommen)
        HashMap<BooleanAssignment, Integer> passSuppPerPattern = transformPatterns(passingPatterns);
        HashMap<BooleanAssignment, Integer> failSuppPerPattern = transformPatterns(failingPatterns);


        // Calculate growth rate per pattern
        HashMap<BooleanAssignment, Double> growthRatePerPatterns =
                computeGrowthRates(failSuppPerPattern, passSuppPerPattern, failing, passing);
        System.out.println("Patterns found: " + growthRatePerPatterns.size());

        // Filter infinite Growth rate patterns
        ArrayList<Pair<BooleanAssignment, Double>> infGrowthPatterns = filterInfiniteGrowthRates(growthRatePerPatterns);
        infGrowthPatterns.sort(Comparator.comparing(p -> p.getFirst().get().length));


        // Get minimal patterns to simplify finding interactions
        List<BooleanAssignment> minimalPatterns = getMinimalPatterns(infGrowthPatterns);
        System.out.println("Minimal patterns: " + minimalPatterns.size());

        // Sample new config to further exclude more patterns
        List<BooleanAssignment> reducedMinimalPatterns = reduceMinimalPatterns(minimalPatterns);
        System.out.println("Reduced minimal patterns: " + reducedMinimalPatterns.size());
        if (reducedMinimalPatterns.size() < 50) {
            reducedMinimalPatterns.forEach(System.out::println);
        }



        String filePath = System.getProperty("user.home") + basePath + resourcesFolder + "reducedPatterns.txt";
        int counter = 0;
        try (PrintWriter out = new PrintWriter(filePath)) {
            out.println(coreFeatures);
            for (BooleanAssignment pattern : reducedMinimalPatterns) {
                out.println(pattern.print());
                counter++;
            }
            out.flush();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }

        System.exit(0);

        // If interaction is not found in minimal patterns, do smth
        Set<int[]> foundInteractions = new HashSet<>(tester.getInteractions().size());
        for (BooleanAssignment foundInteraction : reducedMinimalPatterns){
            for (int[] simulatedInteraction : tester.getInteractions()){
                if (foundInteraction.containsAll(simulatedInteraction)) {
                    foundInteractions.add(simulatedInteraction);
                }
            }
        }
        boolean foundAllInteractions = true;
        for (var interaction : tester.getInteractions()){
            if (!foundInteractions.contains(interaction)) {
                System.out.println("Interaction " + Arrays.toString(interaction) + " not found in minimal patterns.");
                foundAllInteractions = false;
            }
        }
        if (foundAllInteractions) System.out.println("--------- All interactions found! ---------");

        FeatJAR.deinitialize();
    }

    /**
     * This method reduces the minimal patterns by sampling new configs with exactly one minimal pattern included
     * and every other minimal pattern excluded to potentially exclude more non-faulty interactions.
     * @param minimalPatterns
     * @return
     */
    private static List<BooleanAssignment> reduceMinimalPatterns(List<BooleanAssignment> minimalPatterns) {
        List<BooleanAssignment> reducedMinimalPatterns = new ArrayList<>(minimalPatterns);
        // sample configs, die gezielt nur ein pattern enthalten und teste, um evtl. mehr patters ausschließen zu können
        // TODO mehr als eine interaktion includen, um evtl mehr patterns rauszufiltern


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

    private static void testSampledConfigs(Path passingConfigsPath, Path failingConfigsPath) {
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
                StringBuilder sb = new StringBuilder();
                for (int feature : configuration.get()) {
                    if (!core.contains(Math.abs(feature))) {
                        sb.append(feature).append(" ");
                    }
                }
                String configStr = sb.toString();
                if (fails) {
                    failing++;
                    failingConfigs.write(configStr + "\n");
                    failingConfigs.flush();
                } else {
                    passing++;
                    passingConfigs.write(configStr + "\n");
                    passingConfigs.flush();
                }
            }
        } catch (IOException e) {
            System.out.println(e.getMessage());
            throw new RuntimeException(e);
        }
    }

    private static List<BooleanAssignment> getMinimalPatterns(List<Pair<BooleanAssignment, Double>> growthRatesPerPattern) {
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
     * @return
     */
    private static HashMap<BooleanAssignment, Integer> transformPatterns(List<Itemset> patterns) {
        HashMap<BooleanAssignment, Integer> suppPerPattern = new HashMap<>(patterns.size());
        for (Itemset itemset : patterns) {
            suppPerPattern.put(new BooleanAssignment(itemset.itemset), itemset.getAbsoluteSupport());
        }
        return suppPerPattern;
    }


    private static BooleanAssignmentList sampleConfigs(BooleanAssignmentList clauses, int configAmount) {
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

            List<int[]> include = new ArrayList<>(faultyInteractions);
            Result<BooleanSolution> solution = updater.complete(include, null, null);
            if (solution.isEmpty()){
                throw new RuntimeException("Interaction " +  Arrays.toString(faultyInteraction) + " is not satisfyable");
            }
            return faultyInteractions.add(faultyInteraction);
        }

        public boolean addInteractionByName(String... interaction){
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
    }
}
