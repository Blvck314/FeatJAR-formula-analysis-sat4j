package de.featjar.analysis.sat4j.computation;

import ca.pfv.spmf.algorithms.frequentpatterns.apriori_fast.AlgoAprioriFAST;
import ca.pfv.spmf.algorithms.frequentpatterns.apriori_fast.AlgoAprioriFASTClose;
import ca.pfv.spmf.algorithms.frequentpatterns.apriori_fast.AlgoAprioriFASTInverse;
import ca.pfv.spmf.algorithms.frequentpatterns.fpgrowth.AlgoFPGrowth;
import ca.pfv.spmf.patterns.itemset_array_integers_with_count.Itemset;
import ca.pfv.spmf.patterns.itemset_array_integers_with_count.Itemsets;
import de.featjar.base.computation.Computations;
import de.featjar.base.computation.Dependency;
import de.featjar.base.computation.IComputation;
import de.featjar.base.computation.Progress;
import de.featjar.base.data.Result;
import de.featjar.formula.VariableMap;
import de.featjar.formula.assignment.BooleanAssignment;
import de.featjar.formula.assignment.BooleanAssignmentList;
import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.stream.Collectors;

/**
 * Mines contrast-set-like feature interactions from passing and failing configurations.
 */
public class CSL extends ASAT4JAnalysis.Solution<BooleanAssignmentList> {

    public enum Algorithm {
        APRIORI_FAST,
        APRIORI_FAST_CLOSE,
        APRIORI_FAST_INVERSE,
        FP_GROWTH
    }

    public static final Dependency<BooleanAssignmentList> PASSING_CONFIGS =
            Dependency.newDependency(BooleanAssignmentList.class);
    public static final Dependency<BooleanAssignmentList> FAILING_CONFIGS =
            Dependency.newDependency(BooleanAssignmentList.class);
    public static final Dependency<BooleanAssignment> CORE_FEATURES = Dependency.newDependency(BooleanAssignment.class);
    public static final Dependency<Integer> MIN_T = Dependency.newDependency(Integer.class);
    public static final Dependency<Integer> MAX_T = Dependency.newDependency(Integer.class);
    public static final Dependency<Integer> MINSUP = Dependency.newDependency(Integer.class);
    public static final Dependency<Integer> MAXSUP = Dependency.newDependency(Integer.class);
    public static final Dependency<Algorithm> ALGORITHM = Dependency.newDependency(Algorithm.class);
    public static final Dependency<Double> MIN_OCHIAI = Dependency.newDependency(Double.class);
    public static final Dependency<Double> MIN_GROWTH_RATE = Dependency.newDependency(Double.class);
    public static final Dependency<Double> MIN_DSTAR = Dependency.newDependency(Double.class);
    public static final Dependency<Double> MIN_CONFIDENCE = Dependency.newDependency(Double.class);
    public static final Dependency<Double> MIN_LIFT = Dependency.newDependency(Double.class);

    public CSL(IComputation<BooleanAssignmentList> clauseList, Object... computations) {
        super(
                clauseList,
                Computations.of(new BooleanAssignmentList((VariableMap) null)),
                Computations.of(new BooleanAssignmentList((VariableMap) null)),
                new ComputeCoreSAT4J(clauseList)
                        .mapResult(CSL.class, "coreFeatures", core -> {
                            BooleanAssignment firstGroup = core.getFirst();
                            return firstGroup != null ? firstGroup : new BooleanAssignment();
                        }),
                Computations.of(1),
                Computations.of(3),
                Computations.of(1),
                Computations.of(Integer.MAX_VALUE),
                Computations.of(Algorithm.APRIORI_FAST),
                Computations.of(0.0),
                Computations.of(0.0),
                Computations.of(0.0),
                Computations.of(0.0),
                Computations.of(0.0),
                computations);
    }

    protected CSL(CSL other) {
        super(other);
    }

    @Override
    public Result<BooleanAssignmentList> compute(List<Object> dependencyList, Progress progress) {
        BooleanAssignmentList clauseList = BOOLEAN_CLAUSE_LIST.get(dependencyList);
        BooleanAssignmentList passingConfigs = PASSING_CONFIGS.get(dependencyList);
        BooleanAssignmentList failingConfigs = FAILING_CONFIGS.get(dependencyList);
        BooleanAssignment coreFeatures = CORE_FEATURES.get(dependencyList);
        int minT = MIN_T.get(dependencyList);
        int maxT = MAX_T.get(dependencyList);
        int minsup = MINSUP.get(dependencyList);
        int maxsup = MAXSUP.get(dependencyList);
        Algorithm algorithm = ALGORITHM.get(dependencyList);

        if (passingConfigs.getVariableMap() == null) {
            passingConfigs = new BooleanAssignmentList(clauseList.getVariableMap(), passingConfigs.getAll());
        }
        if (failingConfigs.getVariableMap() == null) {
            failingConfigs = new BooleanAssignmentList(clauseList.getVariableMap(), failingConfigs.getAll());
        }

        if (failingConfigs.isEmpty()) {
            return Result.empty(new IllegalArgumentException("No failing configurations specified."));
        }
        if (minT <= 0 || maxT < minT) {
            return Result.empty(new IllegalArgumentException("Invalid interaction size range."));
        }
        if (minsup <= 0) {
            return Result.empty(new IllegalArgumentException("Minimum support must be greater than zero."));
        }
        if (algorithm == Algorithm.APRIORI_FAST_INVERSE && maxsup < minsup) {
            return Result.empty(new IllegalArgumentException("Maximum support must be at least the minimum support."));
        }

        Set<Integer> coreFeatureSet =
                Arrays.stream(coreFeatures.get()).boxed().collect(Collectors.toCollection(LinkedHashSet::new));
        BooleanAssignmentList minedPassingConfigs = removeFromConfigs(passingConfigs, coreFeatureSet);
        BooleanAssignmentList minedFailingConfigs = removeFromConfigs(failingConfigs, coreFeatureSet);

        progress.setTotalSteps(3);
        progress.incrementCurrentStep();
        checkCancel();

        try {
            CompletableFuture<Map<BooleanAssignment, Integer>> passingFuture =
                    CompletableFuture.supplyAsync(() -> mine(minedPassingConfigs, minT, maxT, minsup, maxsup, algorithm));
            CompletableFuture<Map<BooleanAssignment, Integer>> failingFuture =
                    CompletableFuture.supplyAsync(() -> mine(minedFailingConfigs, minT, maxT, minsup, maxsup, algorithm));

            Map<BooleanAssignment, Integer> supportPerPassingInteraction = passingFuture.join();
            Map<BooleanAssignment, Integer> supportPerFailingInteraction = failingFuture.join();

            progress.incrementCurrentStep();
            checkCancel();

            LinkedHashSet<BooleanAssignment> interactions = new LinkedHashSet<>(supportPerFailingInteraction.keySet());
            interactions.removeAll(supportPerPassingInteraction.keySet());

            ContrastMetricCalculator metrics = new ContrastMetricCalculator(
                    passingConfigs.size(),
                    failingConfigs.size(),
                    supportPerPassingInteraction,
                    supportPerFailingInteraction);
            List<BooleanAssignment> result = interactions.stream()
                    .filter(interaction -> passesMetricThresholds(interaction, dependencyList, metrics))
                    .sorted(interactionComparator(metrics))
                    .collect(Collectors.toCollection(ArrayList::new));

            progress.incrementCurrentStep();
            return Result.of(new BooleanAssignmentList(clauseList.getVariableMap(), result));
        } catch (Exception e) {
            return Result.empty(e);
        }
    }

    private Map<BooleanAssignment, Integer> mine(
            BooleanAssignmentList configs, int minT, int maxT, int minsup, int maxsup, Algorithm algorithm) {
        if (configs.isEmpty()) {
            return new LinkedHashMap<>();
        }

        Path inputPath = null;
        try {
            inputPath = Files.createTempFile("featjar-csl-", ".transactions");
            writeConfigsToFile(configs, inputPath);
            Itemsets itemsets = runMiner(inputPath, configs.size(), minT, maxT, minsup, maxsup, algorithm);
            return transformPatterns(itemsets, configs.getVariableMap().size(), minT, maxT);
        } catch (Exception e) {
            throw new RuntimeException(e);
        } finally {
            if (inputPath != null) {
                try {
                    Files.deleteIfExists(inputPath);
                } catch (IOException ignored) {
                }
            }
        }
    }

    private Itemsets runMiner(Path inputPath, int configCount, int minT, int maxT, int minsup, int maxsup, Algorithm algorithm)
            throws Exception {
        double relativeMinSup = (double) minsup / configCount;
        String input = inputPath.toString();

        switch (algorithm) {
            case APRIORI_FAST:
                AlgoAprioriFAST aprioriFast = new AlgoAprioriFAST();
                aprioriFast.setMaximumPatternLength(maxT);
                return aprioriFast.runAlgorithm(relativeMinSup, input, null, 30);
            case APRIORI_FAST_CLOSE:
                AlgoAprioriFASTClose aprioriFastClose = new AlgoAprioriFASTClose();
                aprioriFastClose.setMaximumPatternLength(maxT);
                return aprioriFastClose.runAlgorithm(relativeMinSup, input, null, 30);
            case APRIORI_FAST_INVERSE:
                AlgoAprioriFASTInverse aprioriFastInverse = new AlgoAprioriFASTInverse();
                aprioriFastInverse.setMaximumPatternLength(maxT);
                double relativeMaxSup = (double) maxsup / configCount;
                return aprioriFastInverse.runAlgorithm(relativeMinSup, relativeMaxSup, input, null, 30);
            case FP_GROWTH:
                AlgoFPGrowth fpGrowth = new AlgoFPGrowth();
                fpGrowth.setMinimumPatternLength(minT);
                fpGrowth.setMaximumPatternLength(maxT);
                return fpGrowth.runAlgorithm(input, null, relativeMinSup);
            default:
                throw new IllegalArgumentException("Unsupported algorithm: " + algorithm);
        }
    }

    private BooleanAssignmentList removeFromConfigs(BooleanAssignmentList configs, Set<Integer> featuresToRemove) {
        return new BooleanAssignmentList(
                configs.getVariableMap(),
                configs.stream()
                        .map(config -> new BooleanAssignment(Arrays.stream(config.get())
                                .filter(feature -> feature != 0)
                                .filter(feature -> !featuresToRemove.contains(feature))
                                .toArray()))
                        .collect(Collectors.toList()));
    }

    private void writeConfigsToFile(BooleanAssignmentList configs, Path path) throws IOException {
        try (BufferedWriter writer = Files.newBufferedWriter(path, Charset.defaultCharset())) {
            for (BooleanAssignment configuration : configs) {
                int[] features = Arrays.stream(configuration.get())
                        .filter(feature -> feature != 0)
                        .map(this::mapFeatureToPositiveInt)
                        .distinct()
                        .sorted()
                        .toArray();
                String configString = Arrays.stream(features).mapToObj(String::valueOf).collect(Collectors.joining(" "));
                writer.write(configString);
                writer.newLine();
            }
        }
    }

    private int mapFeatureToPositiveInt(int feature) {
        return feature < 0 ? Integer.MAX_VALUE + feature : feature;
    }

    private int mapFeatureToFeatJARInt(int feature, int maxFeatureInt) {
        return feature > maxFeatureInt ? -(Integer.MAX_VALUE - feature) : feature;
    }

    private Map<BooleanAssignment, Integer> transformPatterns(Itemsets itemsets, int maxFeatureInt, int minT, int maxT) {
        Map<BooleanAssignment, Integer> supportPerPattern = new LinkedHashMap<>();
        for (List<Itemset> level : itemsets.getLevels()) {
            for (Itemset itemset : level) {
                int[] features = Arrays.stream(itemset.itemset)
                        .map(feature -> mapFeatureToFeatJARInt(feature, maxFeatureInt))
                        .sorted()
                        .toArray();
                if (features.length >= minT && features.length <= maxT) {
                    supportPerPattern.put(new BooleanAssignment(features), itemset.getAbsoluteSupport());
                }
            }
        }
        return supportPerPattern;
    }

    private boolean passesMetricThresholds(
            BooleanAssignment interaction, List<Object> dependencyList, ContrastMetricCalculator metrics) {
        return isAboveThreshold(metrics.computeOchiai(interaction), MIN_OCHIAI.get(dependencyList))
                && isAboveThreshold(metrics.computeGrowthRate(interaction), MIN_GROWTH_RATE.get(dependencyList))
                && isAboveThreshold(metrics.computeDStar(interaction, 2.0), MIN_DSTAR.get(dependencyList))
                && isAboveThreshold(metrics.computeConfidence(interaction), MIN_CONFIDENCE.get(dependencyList))
                && isAboveThreshold(metrics.computeLift(interaction), MIN_LIFT.get(dependencyList));
    }

    private boolean isAboveThreshold(double value, double threshold) {
        return threshold <= 0.0 || Double.isNaN(threshold) || (!Double.isNaN(value) && value >= threshold);
    }

    private Comparator<BooleanAssignment> interactionComparator(ContrastMetricCalculator metrics) {
        return (left, right) -> {
            int scoreComparison = Double.compare(
                    normalizedScore(metrics.computeOchiai(right)), normalizedScore(metrics.computeOchiai(left)));
            return scoreComparison != 0 ? scoreComparison : compareAssignments(left, right);
        };
    }

    private double normalizedScore(double score) {
        return Double.isNaN(score) ? Double.NEGATIVE_INFINITY : score;
    }

    private int compareAssignments(BooleanAssignment left, BooleanAssignment right) {
        int[] leftFeatures = left.get();
        int[] rightFeatures = right.get();
        for (int i = 0; i < Math.min(leftFeatures.length, rightFeatures.length); i++) {
            int comparison = Integer.compare(leftFeatures[i], rightFeatures[i]);
            if (comparison != 0) {
                return comparison;
            }
        }
        return Integer.compare(leftFeatures.length, rightFeatures.length);
    }

}
