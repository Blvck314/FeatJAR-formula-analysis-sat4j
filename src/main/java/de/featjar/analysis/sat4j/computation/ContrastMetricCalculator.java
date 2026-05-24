package de.featjar.analysis.sat4j.computation;

public class ContrastMetricCalculator {
    private final int passingConfigs, failingConfigs;

    public ContrastMetricCalculator(int passingConfigs, int failingConfigs) {
        this.passingConfigs = passingConfigs;
        this.failingConfigs = failingConfigs;
    }

    public double computeOchiai(int passes, int fails) {
        if (failingConfigs == 0) return 0.0;
        return fails / Math.sqrt(failingConfigs * (fails + passes));
    }

    public double computeDStar(int passes, int fails, double e) {
        return Math.pow(fails, e) / (passes + (failingConfigs - fails));
    }

    public double computeGrowthRate(int passes, int fails) {
        if (passes == 0) return Double.POSITIVE_INFINITY;

        double relativeSupportFail = (double) fails / this.failingConfigs;
        double relativeSupportPass = (double) passes / this.passingConfigs;
        return relativeSupportFail / relativeSupportPass;
    }

    public double computeConfidence(int passes, int fails) {
        int totalSupport = fails + passes;
        return totalSupport == 0 ? 0.0 : (double) fails / totalSupport;
    }

    public double computeLift(int passes, int fails) {
        int totalConfigs = passingConfigs + failingConfigs;
        if (totalConfigs == 0 || failingConfigs == 0) return 0.0;
        double baseFailureRate = (double) failingConfigs / totalConfigs;
        return computeConfidence(passes, fails) / baseFailureRate;
    }
}
