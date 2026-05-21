package de.featjar.analysis.sat4j.computation;

import de.featjar.analysis.IConfigurationTester;
import de.featjar.base.data.Pair;
import de.featjar.base.data.Result;
import de.featjar.formula.VariableMap;
import de.featjar.formula.assignment.BooleanAssignment;
import de.featjar.formula.assignment.BooleanAssignmentList;
import de.featjar.formula.assignment.BooleanSolution;

import java.util.*;
import java.util.stream.Collectors;

public class ARMTester implements IConfigurationTester {

    public enum InteractionType {
        AND, OR, XOR, IMPLIES, EQUIV
    }

    private final List<int[]> faultyInteractions;
    private final BooleanAssignmentList featureModelCNF;
    private final Random random;
    private final List<Integer> eligibleFeatures;
    private final RandomConfigurationUpdater updater;
    private final BooleanAssignmentList sample;

    public ARMTester(long seed, BooleanAssignmentList featureModelCNF, RandomConfigurationUpdater updater, BooleanAssignment coreFeatures,
                     BooleanAssignmentList sample) {
        this.faultyInteractions = new ArrayList<>();
        this.featureModelCNF = featureModelCNF;
        this.random = new Random(seed);
        this.updater = updater;
        this.eligibleFeatures = featureModelCNF.getVariableMap().getIndices().stream()
                .filter(feature -> !coreFeatures.contains(Math.abs(feature)))
                .collect(Collectors.toList());
        this.sample = sample;
    }

    /**
     * Tests the configs in the sample.
     * @param sample
     * @return A pair of BooleanAssignmentLists. The first element are the passing configs and the second one the failing configs.
     */
    public Pair<BooleanAssignmentList, BooleanAssignmentList> testSample(BooleanAssignmentList sample){
        BooleanAssignmentList passing = new BooleanAssignmentList(sample.getVariableMap());
        BooleanAssignmentList failing = new BooleanAssignmentList(sample.getVariableMap());

        for (BooleanAssignment config : sample){
            if (isFailing(config))
                failing.add(config);
            else
                passing.add(config);
        }
        return new Pair<>(passing, failing);
    }

    public void simulateInteractionWithRandomFeatures(InteractionType type, boolean... includes){
        int t = includes.length;
        if (t > this.eligibleFeatures.size()) throw new IllegalArgumentException("Zu große interaktion: " + t);

        int[] features = new int[t];
        int counter = 0;
        int maxAttempts = 1000;
        do {
            Collections.shuffle(eligibleFeatures, this.random);
            for (int i = 0; i < t; i++) {
                int feature = eligibleFeatures.get(i);
                features[i] = includes[i] ? feature : -feature;
            }
            counter++;
        } while (!simulateInteraction(type, features) && counter < maxAttempts);
    }

    /**
     * Simuliert eine Fehlerinteraktion.
     * @param type     Der logische Typ (AND, XOR, etc.)
     * @param features
     * @return true, wenn erfolgreich eine valide Kombination gefunden wurde.
     */
    public boolean simulateInteraction(InteractionType type, int ... features) {
        int t = features.length;
        if (eligibleFeatures.size() < t) {
            throw new IllegalArgumentException("Nicht genügend freie Features für Interaktionsgröße " + t);
        }

        List<int[]> dnf = buildDNF(type, features);

        if (isSatisfiable(dnf)) {
            return addAllInteractions(dnf);
        }
        throw new RuntimeException("Konnte keine erfüllbare " + type + "-Interaktion mit " + Arrays.toString(features) + " generieren.");
    }

    /**
     * Baut die Disjunktive Normalform für beliebige Vorzeichen-Arrays.
     */
    private List<int[]> buildDNF(ARMTester.InteractionType type, int[] lit) {
        List<int[]> dnf = new ArrayList<>();
        System.out.printf("Building %s-Interaction for %s.\n", type.toString(), Arrays.toString(lit));
        switch (type) {
            case AND: {
                dnf.add(lit.clone());
                break;
            }
            case OR: {
                for (int l : lit) dnf.add(new int[]{l});
                dnf.add(lit.clone());
                break;
            }
            case XOR: {
                if (lit.length != 2) throw new IllegalArgumentException("XOR momentan nur für t=2");
                // (L1 AND NOT L2) OR (NOT L1 AND L2)
                dnf.add(new int[]{lit[0], -lit[1]});
                dnf.add(new int[]{-lit[0], lit[1]});
                break;
            }
            case IMPLIES: {
                if (lit.length != 2) throw new IllegalArgumentException("IMPLIES momentan nur für t=2");
                // L1 => L2 = (NOT L1) OR L2
                dnf.add(new int[]{-lit[0]});
                dnf.add(new int[]{lit[1]});
                break;
            }
            case EQUIV: {
                if (lit.length != 2) throw new IllegalArgumentException("EQUIV momentan nur für t=2");
                // (L1 AND L2) OR (NOT L1 AND NOT L2)
                dnf.add(new int[]{lit[0], lit[1]});
                dnf.add(new int[]{-lit[0], -lit[1]});
                break;
            }
        }
        return dnf;
    }

    private boolean isSatisfiable(List<int[]> dnf) {
        for (int[] clause : dnf) {
            List<int[]> includeList = new ArrayList<>(Collections.singletonList(clause));
            Result<BooleanSolution> result = this.updater.complete(includeList, null, null);
            if (result.isEmpty()) return false;
        }
        return true;
    }

    public boolean contains(BooleanAssignment interaction){
        for (int[] interactionArr : this.faultyInteractions){
            if (interaction.containsAll(interactionArr))
                return true;
        }
        return false;
    }

    public boolean addAllInteractions(Collection<int[]> interactions){
        for (int[] interactionArr : interactions){
            Arrays.sort(interactionArr);
            if (!addInteraction(interactionArr)) return false;
        }
        return true;
    }

    public boolean addInteraction(int... faultyInteraction) {
        if (updater == null) throw new IllegalStateException("Updater is null");

        int[] sortedInteraction = Arrays.stream(faultyInteraction).sorted().toArray();
        for (int[] existing : faultyInteractions) {
            if (Arrays.equals(existing, sortedInteraction)) {
                return false;
            }
        }

        if (isSatisfiable(new ArrayList<>(Collections.singleton(faultyInteraction)))){
            return faultyInteractions.add(sortedInteraction);
        }
        return false;
    }

    public boolean addInteraction(String... interaction){
        var variableMap = sample.getVariableMap();
        int[] faultyInteraction = new int[interaction.length];
        for (int i = 0; i < interaction.length; i++) {
            int feature = variableMap.get(interaction[i]).orElseThrow();
            faultyInteraction[i] = feature;
        }
        return addInteraction(faultyInteraction);
    }

    public List<int[]> getInteractions() {
        return faultyInteractions;
    }

    @Override
    public VariableMap getVariableMap() {
        return null;
    }

    @Override
    public void setVariableMap(VariableMap variableMap) {

    }

    /**
     *
     * @param configuration
     * @return 1 if config is failing
     */
    @Override
    public Result<Integer> test(BooleanAssignment configuration) {
        boolean testResult = faultyInteractions.stream().anyMatch(configuration::containsAll);
        return Result.of(testResult ? 1 : 0);
    }

    public void printInteractions(){
        StringBuilder sb = new StringBuilder();
        sb.append("Interactions: ");
        for (Iterator<int[]> it = faultyInteractions.iterator(); it.hasNext();) {
            sb.append(Arrays.toString(it.next()));

            if (it.hasNext())
                sb.append(" or ");
        }
        System.out.println(sb);
    }

    /**
     *
     * @param configuration
     * @return True is the given configuration is failing.
     */
    public boolean isFailing(BooleanAssignment configuration){
        return this.test(configuration).orElseThrow() == 1;
    }
}
