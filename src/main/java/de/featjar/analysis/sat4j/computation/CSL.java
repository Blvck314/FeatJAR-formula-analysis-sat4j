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
import java.util.HashMap;
import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.stream.Collectors;

/**
 * Mines contrast-set-like feature interactions from passing and failing configurations.
 */
public class CSL extends ASAT4JAnalysis.Solution<CSL.CSLResult> {

    public enum Algorithm {
        APRIORI_FAST,
        APRIORI_FAST_CLOSE,
        APRIORI_FAST_INVERSE,
        FP_GROWTH
    }

    public enum RankingMetric {
        OCHIAI,
        GROWTH_RATE,
        DSTAR,
        CONFIDENCE,
        LIFT
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
    public Result<CSLResult> compute(List<Object> dependencyList, Progress progress) {
        BooleanAssignmentList clauseList = BOOLEAN_CLAUSE_LIST.get(dependencyList);
        BooleanAssignmentList passingConfigs = adaptVariableMap(PASSING_CONFIGS.get(dependencyList), clauseList);
        BooleanAssignmentList failingConfigs = adaptVariableMap(FAILING_CONFIGS.get(dependencyList), clauseList);
        BooleanAssignment coreFeatures = CORE_FEATURES.get(dependencyList);
        int minT = MIN_T.get(dependencyList);
        int maxT = MAX_T.get(dependencyList);
        int minsup = MINSUP.get(dependencyList);
        int maxsup = MAXSUP.get(dependencyList);
        Algorithm algorithm = ALGORITHM.get(dependencyList);

        Result<?> validationResult = validate(failingConfigs, minT, maxT, minsup, maxsup, algorithm);
        if (validationResult.isEmpty()) {
            return validationResult.nullify();
        }

        boolean[] coreFeatureMask = toCoreFeatureMask(coreFeatures, clauseList.getVariableMap().size());

        progress.setTotalSteps(4);
        progress.incrementCurrentStep();
        checkCancel();

        try {
            MiningInput passingInput = prepareMiningInput(passingConfigs, coreFeatureMask);
            MiningInput failingInput = prepareMiningInput(failingConfigs, coreFeatureMask);
            progress.incrementCurrentStep();
            checkCancel();

            CompletableFuture<Itemsets> passingFuture =
                    runMinerAsync(passingInput, minT, maxT, minsup, maxsup, algorithm);
            CompletableFuture<Itemsets> failingFuture =
                    runMinerAsync(failingInput, minT, maxT, minsup, maxsup, algorithm);

            CompletableFuture<HashMap<InteractionKey, SupportCounts>> failingMapFuture = failingFuture.thenApplyAsync(
                    failingItemsets -> getFailingInteractionSupports(failingItemsets, minT, maxT));

            ContrastMetricCalculator metrics = new ContrastMetricCalculator(passingConfigs.size(), failingConfigs.size());
            CompletableFuture<List<InteractionResult>> resultsFuture = failingMapFuture.thenCombineAsync(
                    passingFuture,
                    (supportTable, passingItemsets) -> scoreInteractions(
                            supportTable, passingItemsets, minT, maxT, dependencyList, metrics));

            List<InteractionResult> results = resultsFuture.join();
            progress.incrementCurrentStep();
            checkCancel();

            results.sort(interactionResultComparator());
            CSLResult result = toCSLResult(results, clauseList.getVariableMap());

            progress.incrementCurrentStep();
            return Result.of(result);
        } catch (Exception e) {
            return Result.empty(e);
        }
    }

    private BooleanAssignmentList adaptVariableMap(BooleanAssignmentList configs, BooleanAssignmentList clauseList) {
        if (configs.getVariableMap() == null) {
            return new BooleanAssignmentList(clauseList.getVariableMap(), configs.getAll());
        }
        return configs;
    }

    private Result<?> validate(
            BooleanAssignmentList failingConfigs, int minT, int maxT, int minsup, int maxsup, Algorithm algorithm) {
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
        return Result.of(Boolean.TRUE);
    }

    private boolean[] toCoreFeatureMask(BooleanAssignment coreFeatures, int variableCount) {
        boolean[] coreFeatureMask = new boolean[variableCount + 1];
        for (int feature : coreFeatures.get()) {
            int variable = Math.abs(feature);
            if (variable < coreFeatureMask.length) {
                coreFeatureMask[variable] = true;
            }
        }
        return coreFeatureMask;
    }

    private MiningInput prepareMiningInput(BooleanAssignmentList configs, boolean[] coreFeatureMask) throws IOException {
        Path inputPath = Files.createTempFile("featjar-csl-", ".transactions");
        writeConfigsToFile(configs, inputPath, coreFeatureMask);
        return new MiningInput(inputPath, configs.size());
    }

    private CompletableFuture<Itemsets> runMinerAsync(
            MiningInput input, int minT, int maxT, int minsup, int maxsup, Algorithm algorithm) {
        if (input.configCount == 0) {
            input.delete();
            return CompletableFuture.completedFuture(new Itemsets("empty"));
        }
        return CompletableFuture.supplyAsync(() -> {
            try {
                return runMiner(input.path, input.configCount, minT, maxT, minsup, maxsup, algorithm);
            } catch (Exception e) {
                throw new RuntimeException(e);
            } finally {
                input.delete();
            }
        });
    }

    private Itemsets runMiner(
            Path inputPath, int configCount, int minT, int maxT, int minsup, int maxsup, Algorithm algorithm)
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

    private void writeConfigsToFile(BooleanAssignmentList configs, Path path, boolean[] coreFeatureMask)
            throws IOException {
        try (BufferedWriter writer = Files.newBufferedWriter(path, Charset.defaultCharset())) {
            for (BooleanAssignment configuration : configs) {
                int[] features = Arrays.stream(configuration.get())
                        .filter(feature -> feature != 0)
                        .filter(feature -> !isCoreFeature(feature, coreFeatureMask))
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

    private boolean isCoreFeature(int feature, boolean[] coreFeatureMask) {
        int variable = Math.abs(feature);
        return variable < coreFeatureMask.length && coreFeatureMask[variable];
    }

    private int mapFeatureToPositiveInt(int feature) {
        return feature < 0 ? Integer.MAX_VALUE + feature : feature;
    }

    private int mapFeatureToFeatJARInt(int feature, int maxFeatureInt) {
        return feature > maxFeatureInt ? -(Integer.MAX_VALUE - feature) : feature;
    }

    private HashMap<InteractionKey, SupportCounts> getFailingInteractionSupports(
            Itemsets failingItemsets, int minT, int maxT) {
        int failItems = failingItemsets.getLevels().stream().map(List::size).reduce(0, Integer::sum);
        HashMap<InteractionKey, SupportCounts> supportTable = new HashMap<>((int) (failItems / 0.75f) + 1);

        for (List<Itemset> level : failingItemsets.getLevels()) {
            for (Itemset itemset : level) {
                if (isInteractionSize(itemset.itemset, minT, maxT)) {
                    supportTable.put(new InteractionKey(itemset.itemset), new SupportCounts(0, itemset.getAbsoluteSupport()));
                }
            }
        }
        return supportTable;
    }


    private List<InteractionResult> scoreInteractions(
            HashMap<InteractionKey, SupportCounts> supportTable,
            Itemsets passingItemsets,
            int minT,
            int maxT,
            List<Object> dependencyList,
            ContrastMetricCalculator metrics) {
        updatePassingSupports(supportTable, passingItemsets, minT, maxT);

        List<InteractionResult> results = new ArrayList<>(supportTable.size());
        for (java.util.Map.Entry<InteractionKey, SupportCounts> entry : supportTable.entrySet()) {
            SupportCounts counts = entry.getValue();
            InteractionResult result = new InteractionResult(
                    entry.getKey(),
                    counts.pass,
                    counts.fail,
                    metrics.computeOchiai(counts.pass, counts.fail),
                    metrics.computeGrowthRate(counts.pass, counts.fail),
                    metrics.computeDStar(counts.pass, counts.fail, 2.0),
                    metrics.computeConfidence(counts.pass, counts.fail),
                    metrics.computeLift(counts.pass, counts.fail));
            if (passesMetricThresholds(result, dependencyList)) {
                results.add(result);
            }
        }
        return results;
    }

    private void updatePassingSupports(
            HashMap<InteractionKey, SupportCounts> supportTable, Itemsets passingItemsets, int minT, int maxT) {
        for (List<Itemset> level : passingItemsets.getLevels()) {
            for (Itemset itemset : level) {
                SupportCounts counts = supportTable.get(new InteractionKey(itemset.itemset));
                if (counts != null) {
                    counts.pass = itemset.getAbsoluteSupport();
                }
            }
        }
    }

    private boolean isInteractionSize(int[] interaction, int minT, int maxT) {
        return interaction.length >= minT && interaction.length <= maxT;
    }

    private boolean passesMetricThresholds(InteractionResult result, List<Object> dependencyList) {
        return isAboveThreshold(result.ochiai, MIN_OCHIAI.get(dependencyList))
                && isAboveThreshold(result.growthRate, MIN_GROWTH_RATE.get(dependencyList))
                && isAboveThreshold(result.dStar, MIN_DSTAR.get(dependencyList))
                && isAboveThreshold(result.confidence, MIN_CONFIDENCE.get(dependencyList))
                && isAboveThreshold(result.lift, MIN_LIFT.get(dependencyList));
    }

    private boolean isAboveThreshold(double value, double threshold) {
        return threshold <= 0.0 || Double.isNaN(threshold) || (!Double.isNaN(value) && value >= threshold);
    }

    private Comparator<InteractionResult> interactionResultComparator() {
        return (left, right) -> {
            int scoreComparison = Double.compare(normalizedScore(right.ochiai), normalizedScore(left.ochiai));
            return scoreComparison != 0 ? scoreComparison : compareAssignments(left.features.array, right.features.array);
        };
    }

    private static double normalizedScore(double score) {
        return Double.isNaN(score) ? Double.NEGATIVE_INFINITY : score;
    }

    private static int compareAssignments(int[] left, int[] right) {
        for (int i = 0; i < Math.min(left.length, right.length); i++) {
            int comparison = Integer.compare(left[i], right[i]);
            if (comparison != 0) {
                return comparison;
            }
        }
        return Integer.compare(left.length, right.length);
    }

    private CSLResult toCSLResult(List<InteractionResult> results, VariableMap variableMap) {
        int maxFeatureInt = variableMap.size();
        List<ScoredInteraction> interactions = results.stream()
                .map(result -> new ScoredInteraction(
                        new BooleanAssignment(mapFeaturesToFeatJARInts(result.features.array, maxFeatureInt)),
                        result.pass,
                        result.fail,
                        result.ochiai,
                        result.growthRate,
                        result.dStar,
                        result.confidence,
                        result.lift))
                .collect(Collectors.toCollection(ArrayList::new));
        return new CSLResult(variableMap, interactions);
    }

    private int[] mapFeaturesToFeatJARInts(int[] features, int maxFeatureInt) {
        return Arrays.stream(features)
                .map(feature -> mapFeatureToFeatJARInt(feature, maxFeatureInt))
                .sorted()
                .toArray();
    }

    private static final class MiningInput {
        private final Path path;
        private final int configCount;

        private MiningInput(Path path, int configCount) {
            this.path = path;
            this.configCount = configCount;
        }

        private void delete() {
            try {
                Files.deleteIfExists(path);
            } catch (IOException ignored) {
            }
        }
    }

    private static final class InteractionKey {
        private final int[] array;
        private final int hash;

        private InteractionKey(int[] array) {
            this.array = array;
            this.hash = Arrays.hashCode(array);
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (other == null || getClass() != other.getClass()) return false;
            return Arrays.equals(array, ((InteractionKey) other).array);
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }

    private static final class SupportCounts {
        private int pass;
        private int fail;

        private SupportCounts(int pass, int fail) {
            this.pass = pass;
            this.fail = fail;
        }
    }

    private static final class InteractionResult {
        private final InteractionKey features;
        private final int pass;
        private final int fail;
        private final double ochiai;
        private final double growthRate;
        private final double dStar;
        private final double confidence;
        private final double lift;

        private InteractionResult(
                InteractionKey features,
                int pass,
                int fail,
                double ochiai,
                double growthRate,
                double dStar,
                double confidence,
                double lift) {
            this.features = features;
            this.pass = pass;
            this.fail = fail;
            this.ochiai = ochiai;
            this.growthRate = growthRate;
            this.dStar = dStar;
            this.confidence = confidence;
            this.lift = lift;
        }
    }

    public static final class CSLResult {
        private final VariableMap variableMap;
        private final List<ScoredInteraction> interactions;

        public CSLResult(VariableMap variableMap, List<ScoredInteraction> interactions) {
            this.variableMap = variableMap;
            this.interactions = List.copyOf(interactions);
        }

        public VariableMap getVariableMap() {
            return variableMap;
        }

        public List<ScoredInteraction> getInteractions() {
            return interactions;
        }

        public List<ScoredInteraction> getTopInteractions(int k, RankingMetric rankingMetric) {
            int limit = k <= 0 ? interactions.size() : Math.min(k, interactions.size());
            return interactions.stream()
                    .sorted(scoredInteractionComparator(rankingMetric))
                    .limit(limit)
                    .collect(Collectors.toList());
        }

        public String serializeAll(RankingMetric rankingMetric) {
            return serialize(interactions.stream()
                    .sorted(scoredInteractionComparator(rankingMetric))
                    .collect(Collectors.toList()));
        }

        public String serializeTopK(int k, RankingMetric rankingMetric) {
            return serialize(getTopInteractions(k, rankingMetric));
        }

        private String serialize(List<ScoredInteraction> interactions) {
            StringBuilder builder = new StringBuilder();

            builder.append("rank\tinteraction\tfeatures\tpass\tfail\tochiai\tgrowth_rate\tdstar\tconfidence\tlift\n");
            int rank = 1;
            for (ScoredInteraction interaction : interactions) {
                builder.append(rank++)
                        .append('\t')
                        .append(interaction.getInteraction().print())
                        .append('\t')
                        .append(formatFeatureNames(interaction.getInteraction()))
                        .append('\t')
                        .append(interaction.getPassingSupport())
                        .append('\t')
                        .append(interaction.getFailingSupport())
                        .append('\t')
                        .append(formatMetric(interaction.getOchiai()))
                        .append('\t')
                        .append(formatMetric(interaction.getGrowthRate()))
                        .append('\t')
                        .append(formatMetric(interaction.getDStar()))
                        .append('\t')
                        .append(formatMetric(interaction.getConfidence()))
                        .append('\t')
                        .append(formatMetric(interaction.getLift()))
                        .append('\n');
            }
            return builder.toString();
        }

        private String formatFeatureNames(BooleanAssignment interaction) {
            return Arrays.stream(interaction.get())
                    .mapToObj(feature -> {
                        String featureName = variableMap.get(Math.abs(feature)).orElse(String.valueOf(Math.abs(feature)));
                        return feature < 0 ? "not-" + featureName : featureName;
                    })
                    .collect(Collectors.joining(" "));
        }

        private String formatMetric(double value) {
            return Double.isInfinite(value)
                    ? String.valueOf(value)
                    : String.format(java.util.Locale.ROOT, "%.6f", value);
        }

        @Override
        public String toString() {
            return serializeAll(RankingMetric.OCHIAI);
        }
    }

    public static final class ScoredInteraction {
        private final BooleanAssignment interaction;
        private final int passingSupport;
        private final int failingSupport;
        private final double ochiai;
        private final double growthRate;
        private final double dStar;
        private final double confidence;
        private final double lift;

        public ScoredInteraction(
                BooleanAssignment interaction,
                int passingSupport,
                int failingSupport,
                double ochiai,
                double growthRate,
                double dStar,
                double confidence,
                double lift) {
            this.interaction = interaction;
            this.passingSupport = passingSupport;
            this.failingSupport = failingSupport;
            this.ochiai = ochiai;
            this.growthRate = growthRate;
            this.dStar = dStar;
            this.confidence = confidence;
            this.lift = lift;
        }

        public BooleanAssignment getInteraction() {
            return interaction;
        }

        public int getPassingSupport() {
            return passingSupport;
        }

        public int getFailingSupport() {
            return failingSupport;
        }

        public double getOchiai() {
            return ochiai;
        }

        public double getGrowthRate() {
            return growthRate;
        }

        public double getDStar() {
            return dStar;
        }

        public double getConfidence() {
            return confidence;
        }

        public double getLift() {
            return lift;
        }

        private double getMetric(RankingMetric rankingMetric) {
            switch (rankingMetric) {
                case GROWTH_RATE:
                    return growthRate;
                case DSTAR:
                    return dStar;
                case CONFIDENCE:
                    return confidence;
                case LIFT:
                    return lift;
                case OCHIAI:
                default:
                    return ochiai;
            }
        }
    }

    private static Comparator<ScoredInteraction> scoredInteractionComparator(RankingMetric rankingMetric) {
        return (left, right) -> {
            int scoreComparison = Double.compare(
                    normalizedScore(right.getMetric(rankingMetric)), normalizedScore(left.getMetric(rankingMetric)));
            return scoreComparison != 0
                    ? scoreComparison
                    : compareAssignments(left.getInteraction().get(), right.getInteraction().get());
        };
    }
}
