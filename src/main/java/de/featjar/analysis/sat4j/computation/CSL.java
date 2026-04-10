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

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;

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
        String basePath = "/Documents/studium/Bachelorarbeit/".replace("/", File.separator);
        String resourcesFolder = "resources_featjar/".replace("/", File.separator);
        String configs = System.getProperty("user.home") + basePath + resourcesFolder;
        System.out.println(configs);
        Path passingConfigsPath = Path.of(configs, "passingConfigs.txt");
        Path failingConfigsPath = Path.of(configs, "failingConfigs.txt");
        Path modelPath = Path.of(System.getProperty("user.home"), basePath, resourcesFolder, "e-shop-model.xml");

        // File IO for SPMF lib
        BufferedWriter passingConfigs = Files.newBufferedWriter(passingConfigsPath, Charset.defaultCharset());
        BufferedWriter failingConfigs = Files.newBufferedWriter(failingConfigsPath, Charset.defaultCharset());

        // Parse feature model
        IComputation<BooleanAssignmentList> clauses = parseModel(modelPath);

        // Sample configs
        sample = sample(clauses, 50);

        // Simulate faulty interactions
        String interaction1 = "Purchase_value_scope269";
        String interaction2 = "Shipping_address277";
        String[] interaction3 = new String[]{"City149", "Thumbnail68"};
        tester = new TestManager();
        tester.addInteraction(interaction1);
        tester.addInteraction(interaction2);
        tester.addInteraction(interaction3);


        int passing = 0, failing = 0;

        // Separate passing and failing configs
        for (BooleanAssignment configuration : sample) {
            boolean fails = tester.test(configuration).orElseThrow() == 1;
            String configStr = configuration.print().replace(",", " ");
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
        passingConfigs.close();
        failingConfigs.close();

        System.out.println("Passing: " + passing);
        System.out.println("Failing: " + failing);
        System.out.println("Sample size: " + sample.size());
        System.out.println(tester.printInteractions());

        // Run FPGrowth
        AlgoFPGrowth fpGrowth = new AlgoFPGrowth();
        fpGrowth.setMinimumPatternLength(1);
        fpGrowth.setMaximumPatternLength(2);

        // Find frequent patterns in both classes
        Itemsets passingItemsets = fpGrowth.runAlgorithm(String.valueOf(passingConfigsPath), null, 0.3);
        Itemsets failingItemsets = fpGrowth.runAlgorithm(String.valueOf(failingConfigsPath), null, 0.3);
        // Get frequent patterns
        List<Itemset> passingPatterns = passingItemsets.getLevels().stream().flatMap(Collection::stream).collect(Collectors.toList());
        List<Itemset> failingPatterns =  failingItemsets.getLevels().stream().flatMap(Collection::stream).collect(Collectors.toList());
        // Convert Itemset lists to a HashMap BooleanAssigment -> Absolute support (Anzahl der Vorkommen)
        HashMap<BooleanAssignment, Integer> passSuppPerPattern = transformPatterns(passingPatterns);
        HashMap<BooleanAssignment, Integer> failSuppPerPattern = transformPatterns(failingPatterns);
        // Calculate growth rate per pattern
        HashMap<BooleanAssignment, Double> growthRatePerPatterns =
                computeGrowthRates(failSuppPerPattern, passSuppPerPattern, failing, passing);
        // Filter infinite Growth rate patterns
        ArrayList<Pair<BooleanAssignment, Double>> infGrowthPatterns = filterInfiniteGrowthRates(growthRatePerPatterns);
        infGrowthPatterns.sort(Comparator.comparing(p -> p.getFirst().get().length));
        // Get minimal patterns to simplify finding interactions
        List<BooleanAssignment> minimalPatterns = getMinimalPatterns(infGrowthPatterns);
        System.out.println("Minimal patterns: " + minimalPatterns.size());

        for (int[] interaction : tester.getInteractions()) {

        }

        List<BooleanAssignment> reducedMinimalPatterns = new ArrayList<>(minimalPatterns);

        // sample configs, die gezielt nur ein pattern enthalten und teste, um evtl. mehr patters ausschließen zu können
        updater = new RandomConfigurationUpdater(sample, 1L);
        for (BooleanAssignment minimalPattern : minimalPatterns) {
            List<int[]> exclude = minimalPatterns.stream()
                    .map(IntegerList::get).collect(Collectors.toList());
            exclude.remove(minimalPattern.get());

            List<int[]> include = new ArrayList<>(Collections.singleton(minimalPattern.get()));
            Result<BooleanSolution> configRes = updater.complete(include, exclude, null);

            if (configRes.isEmpty()){
                //System.out.println("No configuration found with included: ");
                //include.forEach(System.out::println);
                //System.out.println("Excluded: ");
                //exclude.forEach(System.out::println);
                continue;
            }
            BooleanAssignment config = configRes.get();
            boolean fails = tester.test(config).orElseThrow() == 1;
            if (!fails) {
                reducedMinimalPatterns.remove(minimalPattern);
            }
        }

        System.out.println("Reduced minimal patterns: " + reducedMinimalPatterns.size());
        reducedMinimalPatterns.forEach(System.out::println);

        boolean allInteractionsCorrectlyIdentified = true;
        for (BooleanAssignment minimalPattern : reducedMinimalPatterns) {
            boolean containsInteraction = false;
            for (int[] interaction : tester.getInteractions()){
                if (minimalPattern.containsAll(interaction)) {
                    containsInteraction = true;
                    break;
                }
            }
            if (!containsInteraction) {
                allInteractionsCorrectlyIdentified = false;
                break;
            }
        }
        if (allInteractionsCorrectlyIdentified) {
            System.out.println("----------All interactions correctly identified.----------");
        }
        FeatJAR.deinitialize();
    }

    private static List<BooleanAssignment> getMinimalPatterns(ArrayList<Pair<BooleanAssignment, Double>> infGrowthPatterns) {
        List<BooleanAssignment> minimalPatterns = new ArrayList<>();

        for (Pair<BooleanAssignment, Double> pair : infGrowthPatterns) {
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
            boolean allNegative = true;
            for (int i = 0; i < itemset.itemset.length; i++) {
                if (itemset.itemset[i] > 0) {
                    allNegative = false;
                    break;
                }
            }
            if (!allNegative) {
                suppPerPattern.put(new BooleanAssignment(itemset.itemset), itemset.getAbsoluteSupport());
            }
        }
        return suppPerPattern;
    }


    private static BooleanAssignmentList sample(IComputation<BooleanAssignmentList> clauses, int configAmount) {
        return clauses.map(ComputeSolutionsSAT4J::new)
                .set(ComputeSolutionsSAT4J.SELECTION_STRATEGY, ISelectionStrategy.NonParameterStrategy.FAST_RANDOM)
                .set(ComputeSolutionsSAT4J.LIMIT, configAmount)
                .set(ComputeSolutionsSAT4J.RANDOM_SEED, 1L)
                .compute();
    }

    private static IComputation<BooleanAssignmentList> parseModel(Path modelPath) throws IOException {
        XMLFeatureModelFormulaParser parser = new XMLFeatureModelFormulaParser();
        IFormula model = parser.parse(new FileInputMapper(modelPath, Charset.defaultCharset()))
                .orElseThrow();
        return Computations.async(model)
                .map(ComputeNNFFormula::new)
                .map(ComputeCNFFormula::new)
                .map(ComputeBooleanClauseList::new);
    }

    private static final class TestManager implements IConfigurationTester {

        private final ArrayList<int[]> faultyInteractions;

        public TestManager() {
            this.faultyInteractions = new  ArrayList<>();
        }

        public boolean addInteraction(int... faultyInteraction) {
            return faultyInteractions.add(faultyInteraction);
        }

        public boolean addInteraction(String... interaction){
            var variableMap = sample.getVariableMap();
            int[] faultyInteraction = new int[interaction.length];
            for (int i = 0; i < interaction.length; i++) {
                int feature = variableMap.get(interaction[i]).orElseThrow();
                faultyInteraction[i] = feature;
            }
            return this.addInteraction(faultyInteraction);
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
