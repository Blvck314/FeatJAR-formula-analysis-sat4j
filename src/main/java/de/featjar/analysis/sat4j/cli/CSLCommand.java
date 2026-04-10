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

    public static final Option<Path> FAILING_CONFIGS_OPTION = Option.newOption("f", Option.PathParser)
            .setDescription("Set of failing initial configurations.")
            .setDefaultValue(null)
            .setValidator(Option.PathValidator);

    public static final Option<Path> PASSING_CONFIGS_OPTION = Option.newOption("p", Option.PathParser)
            .setDescription("Set of passing initial configurations.")
            .setDefaultValue(null)
            .setValidator(Option.PathValidator);

    public static final Option<Double> MINSUPP_OPTION = Option.newOption("s", Option.DoubleParser)
            .setDescription("Minimal support threshold for each pattern.")
            .setDefaultValue(0.01);

    public static final Option<Double> MINCONF_OPTION = Option.newOption("c", Option.DoubleParser)
            .setDescription("Minimal confidence threshold for each pattern.")
            .setDefaultValue(0.01);

    public static final Option<Integer> T_OPTION = Option.newOption("t", Option.IntegerParser)
            .setDescription("Maximum interaction size t.")
            .setDefaultValue(2);



    @Override
    protected IComputation<BooleanAssignmentList> newAnalysis(
            OptionList optionParser, IComputation<BooleanAssignmentList> formula) {
        IComputation<BooleanAssignmentList> analysis = formula.map(CSL::new)
                .set(CSL.RANDOM_SEED, optionParser.get(RANDOM_SEED_OPTION))
                .set(CSL.MINSUPP, optionParser.get(MINSUPP_OPTION))
                .set(CSL.MINCONF, optionParser.get(MINCONF_OPTION))
                .set(CSL.T,  optionParser.get(T_OPTION));

    Result<Path> failingConfigsPath = optionParser.getResult(FAILING_CONFIGS_OPTION);
    Result<Path> passingConfigsPath = optionParser.getResult(PASSING_CONFIGS_OPTION);
    if (failingConfigsPath.isPresent() && passingConfigsPath.isPresent()) {
        BooleanAssignmentGroups failingConfigs = IO.load(
                    failingConfigsPath.get(), BooleanAssignmentGroupsFormats.getInstance())
                .orElseLog(Log.Verbosity.WARNING);
        BooleanAssignmentGroups passingConfigs = IO.load(
                        passingConfigsPath.get(), BooleanAssignmentGroupsFormats.getInstance())
                .orElseLog(Log.Verbosity.WARNING);

        if (failingConfigs != null && passingConfigs != null) {
            analysis.set(CSL.FAILING_CONFIGS, failingConfigs.getFirstGroup());
            analysis.set(CSL.PASSING_CONFIGS, passingConfigs.getFirstGroup());
        }
    }
        return analysis.mapResult(CSL.class, "list", BooleanAssignmentList::new);
    }

    @Override
    protected IFormat<BooleanAssignmentList> getOuputFormat(OptionList optionParser) {
        return new BooleanAssignmentListDimacsFormat();
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of("Identifies a list of potential faulty complex feature interactions.");
    }

    @Override
    public Optional<String> getShortName() {
        return Optional.of("CSL");
    }
}
