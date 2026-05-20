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

    public ContrastMetricCalculator(int passingConfigs, int failingConfigs) {
        this.passingConfigs = passingConfigs;
        this.failingConfigs = failingConfigs;
    }

    public float computeOchiai(int passes, int fails) {
        if (failingConfigs == 0) return 0;
        return (float) (fails / Math.sqrt(failingConfigs * (fails + passes)));
    }

    public float computeDStar(int passes, int fails, double e) {
        return (float) (Math.pow(fails, e) / (passes + (failingConfigs - fails)));
    }

    public float computeGrowthRate(int passes, int fails){
        if (passes == 0) return Float.POSITIVE_INFINITY;
        float relativeSupportFail = (float) fails / this.failingConfigs;
        float relativeSupportPass = (float) passes / this.passingConfigs;
        float growthRate = relativeSupportFail /  relativeSupportPass;
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

