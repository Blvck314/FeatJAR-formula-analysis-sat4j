package de.featjar;

import de.featjar.analysis.sat4j.computation.ARMTester;
import de.featjar.analysis.sat4j.computation.CSL;
import de.featjar.analysis.sat4j.computation.ComputeCoreSAT4J;
import de.featjar.analysis.sat4j.computation.ComputeSolutionsSAT4J;
import de.featjar.analysis.sat4j.computation.RandomConfigurationUpdater;
import de.featjar.analysis.sat4j.computation.YASA;
import de.featjar.analysis.sat4j.solver.ISelectionStrategy;
import de.featjar.base.FeatJAR;
import de.featjar.base.computation.Computations;
import de.featjar.base.io.IO;
import de.featjar.base.data.Pair;
import de.featjar.formula.assignment.BooleanAssignment;
import de.featjar.formula.assignment.BooleanAssignmentGroups;
import de.featjar.formula.assignment.BooleanAssignmentList;
import de.featjar.formula.assignment.conversion.ComputeBooleanClauseList;
import de.featjar.formula.combination.VariableCombinationSpecification;
import de.featjar.formula.computation.ComputeCNFFormula;
import de.featjar.formula.computation.ComputeNNFFormula;
import de.featjar.formula.io.FormulaFormats;
import de.featjar.formula.io.csv.BooleanAssignmentGroupsCSVFormat;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Random;


public class CSLTest {

    private static final long SEED = 1234L;
    private static final int RANDOM_SAMPLE_SIZE = 100;
    private static final int YASA_SAMPLE_SIZE = 200;
    private static final int YASA_T = 2;
    private static final int INTERACTION_SIZE = 2;
    private static final int CSL_MAX_T = 2;
    private static final int CSL_MINSUP = 1;
    private static final int CSL_MAXSUP = 10;
    private static final int MAX_SIMULATION_ATTEMPTS = 20;
    private static final int TOP_K = 20;
    private static final CSL.RankingMetric RANKING_METRIC = CSL.RankingMetric.PASSES_FAILS_SIZE;
    private static final CSL.Algorithm ALGORITHM = CSL.Algorithm.APRIORI_FAST;
    private static final double MIN_OCHIAI = 0.0;
    private static final double MIN_DSTAR = 0.0;
    private static final double MIN_GROWTH_RATE = 0.0;
    private static final double MIN_CONFIDENCE= 0.0;
    private static final double MIN_LIFT = 0.0;
    private static final String FEATURE_MODEL = "e-shop-model.xml";
    private static final boolean DO_PREFILTERING = true;
    private static final CSL.RankingMetric PREFILTER_METRIC = CSL.RankingMetric.PASSES_TO_FAILS_RATIO;
    private static final double PREFILTER_THRESHOLD = 0.5;


    public static void main(String[] args) throws IOException {
        Path resourcesPath = Path.of(System.getProperty("user.home"), "studium", "Bachelorarbeit",
                "resources_featjar");
        Path modelPath = args.length > 0 ? Path.of(args[0]) : resourcesPath.resolve(FEATURE_MODEL);
        Path outputPath = args.length > 1 ? Path.of(args[1]) : resourcesPath.resolve("csl-generated");
        Files.createDirectories(outputPath);

        FeatJAR.initialize();
        BooleanAssignmentList clauses = loadClauses(modelPath);

        runScenario("random", sampleRandomConfigs(clauses, RANDOM_SAMPLE_SIZE, SEED), clauses, outputPath);
        //runScenario("yasa", sampleTWise(clauses, YASA_T, YASA_SAMPLE_SIZE, SEED), clauses, coreFeatures, outputPath);
        FeatJAR.deinitialize();
    }

    private static BooleanAssignmentList loadClauses(Path modelPath) {
        return IO.load(modelPath, FormulaFormats.getInstance())
                .toComputation()
                .map(ComputeNNFFormula::new)
                .map(ComputeCNFFormula::new)
                .map(ComputeBooleanClauseList::new)
                .computeResult()
                .orElseThrow();
    }

    private static BooleanAssignment computeCoreFeatures(BooleanAssignmentList clauses) {
        BooleanAssignment coreFeatures = Computations.of(clauses)
                .map(ComputeCoreSAT4J::new)
                .computeResult()
                .orElseThrow()
                .getFirst();
        return coreFeatures != null ? coreFeatures : new BooleanAssignment();
    }

    private static BooleanAssignmentList sampleRandomConfigs(BooleanAssignmentList clauses, int sampleSize, long seed) {
        return Computations.of(clauses)
                .map(ComputeSolutionsSAT4J::new)
                .set(ComputeSolutionsSAT4J.SELECTION_STRATEGY, ISelectionStrategy.NonParameterStrategy.FAST_RANDOM)
                .set(ComputeSolutionsSAT4J.LIMIT, sampleSize)
                .set(ComputeSolutionsSAT4J.FORBID_DUPLICATES, true)
                .set(ComputeSolutionsSAT4J.RANDOM_SEED, seed)
                .computeResult()
                .orElseThrow();
    }

    private static BooleanAssignmentList sampleTWise(BooleanAssignmentList clauses, int t, int sampleSize, long seed) {
        return Computations.of(clauses)
                .map(YASA::new)
                .set(
                        YASA.COMBINATION_SET,
                        Computations.of(clauses)
                                .map(VariableCombinationSpecification.VariableCombinationSpecificationComputation::new)
                                .set(VariableCombinationSpecification.VariableCombinationSpecificationComputation.T, t))
                .set(YASA.CONFIGURATION_LIMIT, sampleSize)
                .set(YASA.ITERATIONS, 1)
                .set(YASA.INTERNAL_SOLUTION_LIMIT, 65_536)
                .set(YASA.INCREMENTAL_T, false)
                .set(YASA.RANDOM_SEED, seed)
                .computeResult()
                .orElseThrow();
    }

    private static void runScenario(
            String name,
            BooleanAssignmentList sample,
            BooleanAssignmentList featureModelClauses,
            Path outputPath)
            throws IOException {
        BooleanAssignment coreFeatures = computeCoreFeatures(featureModelClauses);
        RandomConfigurationUpdater updater = new RandomConfigurationUpdater(featureModelClauses, SEED);
        ARMTester tester = null;
        Pair<BooleanAssignmentList, BooleanAssignmentList> testedSample = null;
        for (int attempt = 0; attempt < MAX_SIMULATION_ATTEMPTS; attempt++) {
            long attemptSeed = SEED + attempt;
            tester = new ARMTester(attemptSeed, featureModelClauses, updater, coreFeatures, sample);
            boolean[] includedLiterals = randomSigns(INTERACTION_SIZE, attemptSeed);
            tester.simulateInteractionWithRandomFeatures(ARMTester.InteractionType.IMPLIES, includedLiterals);
            testedSample = tester.testSample(sample);
            if (!testedSample.getSecond().isEmpty()) {
                break;
            }
        }
        if (testedSample == null || testedSample.getSecond().isEmpty()) {
            throw new IllegalStateException("Could not simulate an interaction covered by the generated sample.");
        }
        BooleanAssignmentList passingConfigs = testedSample.getFirst();
        BooleanAssignmentList failingConfigs = testedSample.getSecond();

        Path samplePath = outputPath.resolve(name + "-sample.dimacs");
        Path passingPath = outputPath.resolve(name + "-passing.dimacs");
        Path failingPath = outputPath.resolve(name + "-failing.dimacs");
        writeConfigs(sample, samplePath);
        writeConfigs(passingConfigs, passingPath);
        writeConfigs(failingConfigs, failingPath);

        System.out.printf("%n=== %s sample ===%n", name);
        System.out.printf("sample size: %d, passing: %d, failing: %d%n",
                sample.size(), passingConfigs.size(), failingConfigs.size());
        System.out.printf("sample configs: %s%n", samplePath);
        System.out.printf("passing configs: %s%n", passingPath);
        System.out.printf("failing configs: %s%n", failingPath);
        tester.printInteractions();

        CSL.CSLResult result = Computations.of(featureModelClauses)
                .map(CSL::new)
                .set(CSL.PASSING_CONFIGS, passingConfigs)
                .set(CSL.FAILING_CONFIGS, failingConfigs)
                .set(CSL.CORE_FEATURES, coreFeatures)
                .set(CSL.MIN_T, 1)
                .set(CSL.MAX_T, CSL_MAX_T)
                .set(CSL.MINSUP, CSL_MINSUP)
                .set(CSL.MAXSUP, CSL_MAXSUP)
                .set(CSL.ALGORITHM, ALGORITHM)
                .set(CSL.MIN_OCHIAI, MIN_OCHIAI)
                .set(CSL.MIN_GROWTH_RATE, MIN_GROWTH_RATE)
                .set(CSL.MIN_DSTAR, MIN_DSTAR)
                .set(CSL.MIN_CONFIDENCE, MIN_CONFIDENCE)
                .set(CSL.MIN_LIFT, MIN_LIFT)
                .set(CSL.DO_PREFILTER, DO_PREFILTERING)
                .set(CSL.PREFILTER_METRIC, PREFILTER_METRIC)
                .set(CSL.PREFILTER_THRESHOLD, PREFILTER_THRESHOLD)
                .computeResult()
                .orElseThrow();

        System.out.printf("CSL result size: %d%n", result.getInteractions().size());
        System.out.println(result.serializeTopK(TOP_K, RANKING_METRIC));
        Path resultPath = outputPath.resolve(name + "-csl-result.tsv");
        System.out.printf("CSL result: %s%n", resultPath);
        try {
            result.writeAllBuffered(resultPath, RANKING_METRIC);
        } catch (IOException e) {
            System.err.println("Fehler beim Schreiben der TSV-Datei: " + e.getMessage());
            e.printStackTrace();
        }

    }

    private static boolean[] randomSigns(int interactionSize, long seed) {
        Random random = new Random(seed);
        boolean[] includedLiterals = new boolean[interactionSize];
        for (int i = 0; i < includedLiterals.length; i++) {
            includedLiterals[i] = random.nextBoolean();
        }
        System.out.printf("interaction signs: %s%n", Arrays.toString(includedLiterals));
        return includedLiterals;
    }

    private static void writeConfigs(BooleanAssignmentList configs, Path path) throws IOException {
        IO.save(new BooleanAssignmentGroups(configs), path, new BooleanAssignmentGroupsCSVFormat());
    }

    public record EvaluationConfig(
        long seed,
        int randomSampleSize,
        int yasaSampleSize,
        int yasaT,
        int interactionSize,
        int cslMaxT,
        int cslMinsup,
        int cslMaxsup,
        int maxSimulationAttempts,
        int topK,
        CSL.RankingMetric rankingMetric,
        CSL.Algorithm algorithm,
        double minOchiai,
        double minDstar,
        double minGrowthRate,
        double minConfidence,
        double minLift,
        String featureModel,
        boolean doPrefiltering,
        CSL.RankingMetric prefilterMetric,
        double prefilterThreshold
    ) {
        // Statische Factory-Methode, die deine Default-Konstanten nutzt
        public static EvaluationConfig createDefault() {
            return new EvaluationConfig(
                    123L, 100, 200, 2, 2, 2, 1, 10, 20, 20,
                    CSL.RankingMetric.OCHIAI, CSL.Algorithm.APRIORI_FAST,
                    0.0, 0.0, 0.0, 0.0, 0.0,
                    "e-shop-model.xml",
                    true, CSL.RankingMetric.OCHIAI, 0.5
            );
        }
    }
}
