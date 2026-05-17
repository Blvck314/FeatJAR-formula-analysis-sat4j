package de.featjar.analysis.sat4j.computation;

import de.featjar.base.data.Pair;
import de.featjar.formula.assignment.BooleanAssignment;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

public class ContrastMetricCalculator {
    private final int passingConfigs, failingConfigs;
    private final Map<BooleanAssignment, Integer> supportPerPassingInteraction;
    private final Map<BooleanAssignment, Integer> supportPerFailingInteraction;

    public ContrastMetricCalculator(int passingConfigs, int failingConfigs,
                                    Map<BooleanAssignment, Integer> supportPerPassingInteraction,
                                    Map<BooleanAssignment, Integer> supportPerFailingInteraction) {
        this.passingConfigs = passingConfigs;
        this.failingConfigs = failingConfigs;
        this.supportPerPassingInteraction = supportPerPassingInteraction;
        this.supportPerFailingInteraction = supportPerFailingInteraction;
    }

    public Double computeOchiai(BooleanAssignment interaction) {
        int fails = this.supportPerFailingInteraction.getOrDefault(interaction, 0);
        int passes = this.supportPerPassingInteraction.getOrDefault(interaction, 0);
        if (failingConfigs == 0) return 0.0;
        return fails / Math.sqrt(failingConfigs * (fails + passes));
    }

    public Double computeDStar(BooleanAssignment interaction, double e) {
        int fails = this.supportPerFailingInteraction.getOrDefault(interaction, 0);
        int passes = this.supportPerPassingInteraction.getOrDefault(interaction, 0);
        return Math.pow(fails, e) / (passes + (failingConfigs - fails));
    }

    public Double computeGrowthRate(BooleanAssignment interaction){
        int passes = this.supportPerPassingInteraction.getOrDefault(interaction, 0);
        if (passes == 0) return Double.POSITIVE_INFINITY;
        int fails = this.supportPerFailingInteraction.getOrDefault(interaction, 0);

        double relativeSupportFail = (double) fails / this.failingConfigs;
        double relativeSupportPass = (double) passes / this.passingConfigs;
        double growthRate = relativeSupportFail /  relativeSupportPass;
        return growthRate;
    }

    public List<Pair<BooleanAssignment, Double>> mapInteractions(
            Collection<BooleanAssignment> interactions,
            Function<BooleanAssignment, Double> metric) {
        return interactions.stream()
                .map(interaction -> new Pair<>(interaction, metric.apply(interaction)))
                .collect(Collectors.toList());
    }
}

