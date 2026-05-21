package de.featjar.analysis.sat4j.cli;

import de.featjar.analysis.sat4j.computation.CSL;
import de.featjar.base.cli.Option;
import de.featjar.base.cli.OptionList;
import de.featjar.base.computation.IComputation;
import de.featjar.base.data.Result;
import de.featjar.base.io.IO;
import de.featjar.base.io.format.IFormat;
import de.featjar.base.log.Log;
import de.featjar.formula.assignment.BooleanAssignmentGroups;
import de.featjar.formula.assignment.BooleanAssignmentList;
import de.featjar.formula.io.BooleanAssignmentGroupsFormats;
import de.featjar.formula.io.dimacs.BooleanAssignmentListDimacsFormat;
import java.nio.file.Path;
import java.util.Optional;

public class CSLCommand extends ASAT4JAnalysisCommand<BooleanAssignmentList> {

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


    @Override
    protected IComputation<BooleanAssignmentList> newAnalysis(
            OptionList optionParser, IComputation<BooleanAssignmentList> formula) {
        IComputation<BooleanAssignmentList> analysis = formula.map(CSL::new)
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
                .set(CSL.MIN_LIFT, optionParser.get(MIN_LIFT_OPTION));

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
    protected IFormat<BooleanAssignmentList> getOuputFormat(OptionList optionParser) {
        return new BooleanAssignmentListDimacsFormat();
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of("Identifies potential faulty complex feature interactions with contrast-set mining.");
    }

    @Override
    public Optional<String> getShortName() {
        return Optional.of("csl");
    }
}
