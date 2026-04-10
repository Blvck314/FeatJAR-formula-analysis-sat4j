package de.featjar.analysis.sat4j.computation;

import ca.pfv.spmf.patterns.itemset_array_integers_with_count.Itemset;
import ca.pfv.spmf.patterns.itemset_array_integers_with_count.Itemsets;
import ca.pfv.spmf.algorithms.frequentpatterns.fpgrowth.AlgoFPGrowth;
import de.featjar.analysis.IConfigurationTester;
import de.featjar.analysis.sat4j.solver.ISelectionStrategy;
import de.featjar.analysis.sat4j.solver.ModalImplicationGraph;
import de.featjar.base.computation.Computations;
import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
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

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.time.temporal.TemporalUnit;
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
        // Paths for configs, fm
        Path configs = Path.of(System.getenv("HOME") + "/Documents/studium/Bachelorarbeit/");
        Path passingConfigFileName = Path.of("passingConfigs.txt");
        Path failingConfigFileName = Path.of("failingConfigs.txt");
        Path passingConfigsPath = Path.of(configs.toString(), passingConfigFileName.toString());
        Path failingConfigsPath = Path.of(configs.toString(), failingConfigFileName.toString());

        BufferedWriter passingConfigs = Files.newBufferedWriter(passingConfigsPath, Charset.defaultCharset());
        BufferedWriter failingConfigs = Files.newBufferedWriter(failingConfigsPath, Charset.defaultCharset());
        String pathFromHome = "/Documents/studium/Bachelorarbeit/model.xml".replace('/', File.separatorChar);
        Path modelPath = Path.of(System.getenv("HOME") + pathFromHome);

        // Parse feature model
        IComputation<BooleanAssignmentList> clauses = parseModel(modelPath);

        // Sample configs
        BooleanAssignmentList sample = sample(clauses, 100);

        // Simulate faulty interactions
        String interaction1 = "Purchase_value_scope269";
        String interaction2 = "Shipping_address277";
        int faultyInteractionInt1 = sample.getVariableMap().get(interaction1).get();
        int faultyInteractionInt2 = sample.getVariableMap().get(interaction2).get();
        int[] faultyInteraction1 = new int[]{faultyInteractionInt1};
        int[] faultyInteraction2 = new int[]{faultyInteractionInt2};
        TestManager tester = new TestManager();
        tester.addInteraction(faultyInteraction1);
        tester.addInteraction(faultyInteraction2);

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
            //System.out.println(configuration.print() + " " + fails);
        }
        passingConfigs.close();
        failingConfigs.close();

        System.out.println("Passing: " + passing);
        System.out.println("Failing: " + failing);
        System.out.println("Sample size: " + sample.size());
        System.out.println("Interactions: " + faultyInteractionInt1 + ", " + faultyInteractionInt2);

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
        // Convert Itemset lists to Map BooleanAssigment -> Absolute support
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

        // sample gezielt configs, die nach und nach idealerweise nur 1 minpattern enthalten, um sie zu reduzieren
        for (BooleanAssignment minimalPattern : minimalPatterns) {

        }
        //growthRatePerPatterns.entrySet().forEach(System.out::println);
        minimalPatterns.forEach(System.out::println);

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
        /*
        YASA sampler = new YASA(clauses);
        sampler.maxSampleSize = configAmount;
        return sampler.compute();

         */

        BooleanAssignmentList sample = clauses.map(ComputeSolutionsSAT4J::new)
                .set(ComputeSolutionsSAT4J.SELECTION_STRATEGY, ISelectionStrategy.NonParameterStrategy.FAST_RANDOM)
                .set(ComputeSolutionsSAT4J.LIMIT, configAmount)
                .compute();
        return sample;

        /*
        return clauses.map(YASA::new)
                .set(YASA.CONFIGURATION_LIMIT, configAmount)
                .set(YASA.SAT_TIMEOUT, Duration.ofSeconds(60))
                .set(YASA.BOOLEAN_CLAUSE_LIST, clauses)
                .computeResult()
                .orElseThrow();

         */
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

        public boolean addInteraction(int[] faultyInteraction) {
            return faultyInteractions.add(faultyInteraction);
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
    }
}
