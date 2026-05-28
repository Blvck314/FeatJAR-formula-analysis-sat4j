package de.featjar.analysis.sat4j.cli;

import de.featjar.analysis.sat4j.computation.CSL;
import de.featjar.base.FeatJAR;
import de.featjar.base.cli.Option;
import de.featjar.base.cli.OptionList;
import de.featjar.base.computation.IComputation;
import de.featjar.base.data.Result;
import de.featjar.base.io.IO;
import de.featjar.base.io.IOMapperOptions;
import de.featjar.base.io.format.IFormat;
import de.featjar.base.log.Log;
import de.featjar.formula.assignment.BooleanAssignmentGroups;
import de.featjar.formula.assignment.BooleanAssignmentList;
import de.featjar.formula.io.BooleanAssignmentGroupsFormats;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.Optional;

public class CSLCommand extends ASAT4JAnalysisCommand<CSL.CSLResult> {

    public static final Option<Path> FAILING_CONFIGS_OPTION = Option.newOption("fc", Option.PathParser)
            .setDescription("Path to the file containing all failing configurations of the sample.")
            .setValidator(Option.PathValidator);

    public static final Option<Path> PASSING_CONFIGS_OPTION = Option.newOption("pc", Option.PathParser)
            .setDescription("Path to the file containing all passing configurations of the sample.")
            .setValidator(Option.PathValidator);

    public static final Option<Integer> MIN_T_OPTION = Option.newOption("min-t", Option.IntegerParser)
            .setDescription("Minimum interaction size.")
            .setValidator(t -> t > 0)
            .setDefaultValue(1);

    public static final Option<Integer> MAX_T_OPTION = Option.newOption("t", Option.IntegerParser)
            .setDescription("Maximum interaction size.")
            .setValidator(t -> t > 0)
            .setDefaultValue(3);

    public static final Option<CSL.Algorithm> ALGORITHM_OPTION = Option.newEnumOption("A", CSL.Algorithm.class)
            .setDescription("Pattern mining algorithm.")
            .setDefaultValue(CSL.Algorithm.APRIORI_FAST);

    public static final Option<Integer> MINSUP_OPTION = Option.newOption("ms", Option.IntegerParser)
            .setDescription("Minimal absolute support for each interaction.")
            .setValidator(support -> support > 0)
            .setDefaultValue(1);

    public static final Option<Integer> MAXSUP_OPTION = Option.newOption("mx", Option.IntegerParser)
            .setDescription("Maximal absolute support. Only used by APRIORI_FAST_INVERSE.")
            .setValidator(support -> support > 0)
            .setDefaultValue(Integer.MAX_VALUE);

    public static final Option<Double> MIN_OCHIAI_OPTION = Option.newOption("ochiai", Option.DoubleParser)
            .setDescription("Minimal Ochiai threshold.")
            .setDefaultValue(0.0);

    public static final Option<Double> MIN_GROWTH_RATE_OPTION = Option.newOption("gr", Option.DoubleParser)
            .setDescription("Minimal growth-rate threshold.")
            .setDefaultValue(0.0);

    public static final Option<Double> MIN_DSTAR_OPTION = Option.newOption("dstar", Option.DoubleParser)
            .setDescription("Minimal DStar threshold.")
            .setDefaultValue(0.0);

    public static final Option<Double> MIN_CONFIDENCE_OPTION = Option.newOption("conf", Option.DoubleParser)
            .setDescription("Minimal confidence threshold.")
            .setDefaultValue(0.0);

    public static final Option<Double> MIN_LIFT_OPTION = Option.newOption("lift", Option.DoubleParser)
            .setDescription("Minimal lift threshold.")
            .setDefaultValue(0.0);

    public static final Option<Boolean> PREFILTER_OPTION = Option.newFlag("prefilter")
            .setDescription("Prefilter one-wise feature patterns before mining larger interactions.");

    public static final Option<CSL.RankingMetric> PREFILTER_METRIC_OPTION =
            Option.newEnumOption("prefilter-metric", CSL.RankingMetric.class)
                    .setDescription("Metric used for one-wise feature prefiltering.")
                    .setDefaultValue(CSL.RankingMetric.OCHIAI);

    public static final Option<Double> PREFILTER_THRESHOLD_OPTION =
            Option.newOption("prefilter-threshold", Option.DoubleParser)
                    .setDescription("Minimal metric value for keeping a one-wise feature pattern.")
                    .setDefaultValue(0.0);

    public static final Option<Integer> TOP_K_OPTION = Option.newOption("k", Option.IntegerParser)
            .setDescription("Number of top-ranked interactions to print to stdout. Use 0 to print all.")
            .setValidator(k -> k >= 0)
            .setDefaultValue(10);

    public static final Option<CSL.RankingMetric> RANKING_METRIC_OPTION =
            Option.newEnumOption("rank-by", CSL.RankingMetric.class)
                    .setDescription("Metric used to rank printed and written interactions.")
                    .setDefaultValue(CSL.RankingMetric.OCHIAI);

    @Override
    public int run(OptionList optionParser) {
        boolean parallel = !optionParser.get(NON_PARALLEL);
        Duration timeout = optionParser.get(TIMEOUT_OPTION);
        Path outputPath = optionParser.getResult(OUTPUT_OPTION).orElse(null);

        IComputation<CSL.CSLResult> computation;
        try {
            computation = newComputation(optionParser);
        } catch (Exception e) {
            FeatJAR.log().error(e);
            FeatJAR.log().plainMessage(OptionList.printHelp(this));
            return FeatJAR.ERROR_COMPUTING_RESULT;
        }

        Result<CSL.CSLResult> result;
        if (!timeout.isZero()) {
            result = computation.computeResult(true, true, timeout);
        } else if (parallel) {
            result = computation.computeFutureResult(true, true).get();
        } else {
            result = computation.computeResult(true, true);
        }

        if (result.isEmpty()) {
            FeatJAR.log().problems(result.getProblems());
            FeatJAR.log().error("Could not compute result.");
            return FeatJAR.ERROR_TIMEOUT;
        }

        CSL.RankingMetric rankingMetric = optionParser.get(RANKING_METRIC_OPTION);
        FeatJAR.log().plainMessage(result.get().serializeTopK(optionParser.get(TOP_K_OPTION), rankingMetric));

        if (outputPath != null) {
            if (Files.isDirectory(outputPath)) {
                FeatJAR.log().error(new IOException(outputPath + " is a directory"));
                return FeatJAR.ERROR_WRITING_RESULT;
            }
            try {
                writeToOutput(result.get(), getOuputFormat(optionParser), optionParser);
            } catch (IOException e) {
                FeatJAR.log().error(e);
                return FeatJAR.ERROR_WRITING_RESULT;
            }
        }
        return 0;
    }

    @Override
    protected IComputation<CSL.CSLResult> newAnalysis(
            OptionList optionParser, IComputation<BooleanAssignmentList> formula) {
        IComputation<CSL.CSLResult> analysis = formula.map(CSL::new)
                .set(CSL.RANDOM_SEED, optionParser.get(RANDOM_SEED_OPTION))
                .set(CSL.SAT_TIMEOUT, optionParser.get(SAT_TIMEOUT_OPTION))
                .set(CSL.MIN_T, optionParser.get(MIN_T_OPTION))
                .set(CSL.MAX_T, optionParser.get(MAX_T_OPTION))
                .set(CSL.MINSUP, optionParser.get(MINSUP_OPTION))
                .set(CSL.MAXSUP, optionParser.get(MAXSUP_OPTION))
                .set(CSL.ALGORITHM, optionParser.get(ALGORITHM_OPTION))
                .set(CSL.MIN_OCHIAI, optionParser.get(MIN_OCHIAI_OPTION))
                .set(CSL.MIN_GROWTH_RATE, optionParser.get(MIN_GROWTH_RATE_OPTION))
                .set(CSL.MIN_DSTAR, optionParser.get(MIN_DSTAR_OPTION))
                .set(CSL.MIN_CONFIDENCE, optionParser.get(MIN_CONFIDENCE_OPTION))
                .set(CSL.MIN_LIFT, optionParser.get(MIN_LIFT_OPTION))
                .set(CSL.DO_PREFILTER, optionParser.get(PREFILTER_OPTION))
                .set(CSL.PREFILTER_METRIC, optionParser.get(PREFILTER_METRIC_OPTION))
                .set(CSL.PREFILTER_THRESHOLD, optionParser.get(PREFILTER_THRESHOLD_OPTION));

        loadConfigs(optionParser.getResult(FAILING_CONFIGS_OPTION))
                .ifPresent(configs -> analysis.set(CSL.FAILING_CONFIGS, configs));
        loadConfigs(optionParser.getResult(PASSING_CONFIGS_OPTION))
                .ifPresent(configs -> analysis.set(CSL.PASSING_CONFIGS, configs));

        return analysis;
    }

    private Optional<BooleanAssignmentList> loadConfigs(Result<Path> path) {
        if (path.isEmpty()) {
            return Optional.empty();
        }
        BooleanAssignmentGroups configs =
                IO.load(path.get(), BooleanAssignmentGroupsFormats.getInstance()).orElseLog(Log.Verbosity.WARNING);
        return configs != null ? Optional.of(configs.getFirstGroup()) : Optional.empty();
    }

    @Override
    protected IFormat<CSL.CSLResult> getOuputFormat(OptionList optionParser) {
        return new CSLResultFormat(optionParser.get(RANKING_METRIC_OPTION));
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of("Identifies potential faulty complex feature interactions with contrast-set mining.");
    }

    @Override
    public Optional<String> getShortName() {
        return Optional.of("csl");
    }

    private static final class CSLResultFormat implements IFormat<CSL.CSLResult> {
        private final CSL.RankingMetric rankingMetric;

        private CSLResultFormat(CSL.RankingMetric rankingMetric) {
            this.rankingMetric = rankingMetric;
        }

        @Override
        public Result<String> serialize(CSL.CSLResult result) {
            return Result.of(result.serializeAll(rankingMetric));
        }

        @Override
        public String getFileExtension() {
            return "tsv";
        }

        @Override
        public String getName() {
            return "CSL TSV";
        }

        @Override
        public boolean supportsWrite() {
            return true;
        }
    }
}
