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
import de.featjar.formula.io.dimacs.BooleanAssignmentGroupsDimacsListFormat;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

public class CSLTest {

    private static final long SEED = 123L;
    private static final int RANDOM_SAMPLE_SIZE = 100;
    private static final int YASA_SAMPLE_SIZE = 200;
    private static final int YASA_T = 2;
    private static final int INTERACTION_SIZE = 1;
    private static final int CSL_MAX_T = 3;
    private static final int CSL_MINSUP = 1;
    private static final int CSL_MAXSUP = 10;
    private static final int MAX_SIMULATION_ATTEMPTS = 20;
    private static final int TOP_K = 20;
    private static final CSL.RankingMetric RANKING_METRIC= CSL.RankingMetric.OCHIAI;
    private static final CSL.Algorithm ALGORITHM = CSL.Algorithm.APRIORI_FAST_INVERSE;
    private static final double MIN_OCHIAI = 0.0;
    private static final double MIN_DSTAR = 0.0;
    private static final double MIN_GROWTH_RATE = 0.0;
    private static final double MIN_CONFIDENCE= 0.0;
    private static final double MIN_LIFT = 0.0;
    private static final String FEATURE_MODEL = "e-shop-model.xml";

    public static void main(String[] args) throws IOException {
        Path resourcesPath = Path.of(System.getProperty("user.home"), "Documents", "studium", "Bachelorarbeit",
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
            tester.simulateInteractionWithRandomFeatures(ARMTester.InteractionType.AND, includedLiterals);
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
        IO.save(new BooleanAssignmentGroups(configs), path, new BooleanAssignmentGroupsDimacsListFormat());
    }

    public class EvaluationHarness {

        // 1. Define a robust configuration record for a single run
        public class EvaluationConfig {
            String modelName;
            BooleanAssignmentList clauses;
            BooleanAssignment coreFeatures;
            BooleanAssignmentList sample;
            // Injected Fault Parameters
            ARMTester.InteractionType faultType;
            int[] faultLiterals; // The actual injected interaction e.g., [1, -5]
            CSL.Algorithm algorithm;
            int maxT;
            int minsup;
            double minOchiai;
            CSL.RankingMetric targetMetric;

            public EvaluationConfig(String modelName, BooleanAssignmentList clauses, BooleanAssignment coreFeatures, BooleanAssignmentList sample, ARMTester.InteractionType faultType, int[] faultLiterals, CSL.Algorithm algorithm, int maxT, int minsup, double minOchiai, CSL.RankingMetric targetMetric) {
                this.modelName = modelName;
                this.clauses = clauses;
                this.coreFeatures = coreFeatures;
                this.sample = sample;
                this.faultType = faultType;
                this.faultLiterals = faultLiterals;
                this.algorithm = algorithm;
                this.maxT = maxT;
                this.minsup = minsup;
                this.minOchiai = minOchiai;
                this.targetMetric = targetMetric;
            }
        }

        // 2. Define a metric container to hold the results of a single run
        public class EvaluationResult {
            EvaluationConfig config;
            long executionTimeMs;
            int totalConfigs;
            int failingConfigs;
            int foundInteractionsCount;
            int rankOfInjectedFault;   // e.g., 1 if it's the top result, -1 if not found
            double scoreOfInjectedFault;
            boolean isSuccessful; // true if injected fault was found in top K

            public EvaluationResult(EvaluationConfig config, long executionTimeMs, int totalConfigs, int failingConfigs, int foundInteractionsCount, int rankOfInjectedFault, double scoreOfInjectedFault, boolean isSuccessful) {
                this.config = config;
                this.executionTimeMs = executionTimeMs;
                this.totalConfigs = totalConfigs;
                this.failingConfigs = failingConfigs;
                this.foundInteractionsCount = foundInteractionsCount;
                this.rankOfInjectedFault = rankOfInjectedFault;
                this.scoreOfInjectedFault = scoreOfInjectedFault;
                this.isSuccessful = isSuccessful;
            }
        }

        /**
         * Executes a single evaluation scenario based on the provided configuration.
         * This method contains no hardcoded values; everything is driven by 'config'.
         */
        public EvaluationResult evaluateScenario(EvaluationConfig config) {
            long startTime = System.currentTimeMillis();

            // 1. Setup the tester with the SPECIFIC fault from the config
            RandomConfigurationUpdater updater = new RandomConfigurationUpdater(config.clauses, 123L);
            ARMTester tester = new ARMTester(123L, config.clauses, updater, config.coreFeatures, config.sample);

            // Inject the exact fault we want to evaluate
            tester.simulateInteraction(config.faultType, config.faultLiterals);

            // 2. Split the sample
            var testedSample = tester.testSample(config.sample);
            BooleanAssignmentList passingConfigs = testedSample.getFirst();
            BooleanAssignmentList failingConfigs = testedSample.getSecond();

            // If the fault couldn't be simulated or didn't cause failures, abort early
            if (failingConfigs.isEmpty()) {
                return new EvaluationResult(config, System.currentTimeMillis() - startTime,
                        config.sample.size(), 0, 0, -1, 0.0, false);
            }

            // 3. Run CSL Analysis
            CSL.CSLResult cslResult = Computations.of(config.clauses)
                    .map(CSL::new)
                    .set(CSL.PASSING_CONFIGS, passingConfigs)
                    .set(CSL.FAILING_CONFIGS, failingConfigs)
                    .set(CSL.CORE_FEATURES, config.coreFeatures)
                    .set(CSL.MIN_T, 1)
                    .set(CSL.MAX_T, config.maxT)
                    .set(CSL.MINSUP, config.minsup)
                    .set(CSL.ALGORITHM, config.algorithm)
                    .set(CSL.MIN_OCHIAI, config.minOchiai)
                    // ... set other thresholds to 0.0 to prevent filtering out the target prematurely
                    .computeResult()
                    .orElseThrow();

            // 4. Analyze Results
            List<CSL.ScoredInteraction> sortedResults = cslResult.getTopInteractions(0, config.targetMetric);

            int faultRank = findRankOfInjectedFault(sortedResults, config.faultLiterals);
            double faultScore = getScoreOfFault(sortedResults, faultRank);

            long executionTime = System.currentTimeMillis() - startTime;

            // 5. Return structured data ready for CSV/TSV aggregation
            return new EvaluationResult(
                    config,
                    executionTime,
                    config.sample.size(),
                    failingConfigs.size(),
                    sortedResults.size(),
                    faultRank,
                    faultScore,
                    (faultRank > 0 && faultRank <= 10) // e.g. success = in top 10
            );
        }

        // --- Helper methods to analyze the output ---

        private int findRankOfInjectedFault(List<CSL.ScoredInteraction> results, int[] injectedFault) {
            // Here you implement the logic to check if the injected fault is present in the results.
            // Remember to compare the contents of the int arrays correctly!
            for (int i = 0; i < results.size(); i++) {
                int[] minedInteraction = results.get(i).getInteraction().get();
                if (isSameInteraction(minedInteraction, injectedFault)) {
                    return i + 1; // 1-based ranking
                }
            }
            return -1; // Not found
        }

        private double getScoreOfFault(List<CSL.ScoredInteraction> results, int rank) {
            if (rank == -1 || results.isEmpty()) return 0.0;
            return results.get(rank - 1).getOchiai(); // or whichever metric was requested
        }

        private boolean isSameInteraction(int[] a, int[] b) {
            // Write a helper to check if arrays contain the same literals (ignoring order if necessary)
            return false;
        }
    }
}
