package de.featjar.analysis.sat4j.computation;

import de.bwaldvogel.liblinear.*;
import java.util.*;

public class GeneticAlgo {

    // Simuliert eine von featjar getestete Konfiguration
    public static class TestedConfig {
        public int[] activeFeatures; // In featjar als ints repräsentiert
        public boolean isFail;

        public TestedConfig(int[] activeFeatures, boolean isFail) {
            this.activeFeatures = activeFeatures;
            this.isFail = isFail;
        }
    }

    // Speichert das Mapping von Interaktionen (FeatureA, FeatureB) zu einer neuen LibLinear ID
    private Map<String, Integer> interactionToIdMap = new HashMap<>();
    private Map<Integer, String> idToNameMap = new HashMap<>();
    private int nextAvailableId = 10000; // Startwert für 2-wise IDs, um Konflikte mit 1-wise zu vermeiden

    /**
     * Hauptmethode zur Analyse der Konfigurationen.
     */
    public void analyzeConfigurations(List<TestedConfig> configs, int maxSingleFeatureId) {
        System.out.println("--- Starte Fehler-Lokalisierung (Lasso Regression) ---");

        Problem problem = new Problem();
        problem.l = configs.size(); // Anzahl der Beobachtungen
        problem.x = new Feature[problem.l][]; // Input-Matrix (Sparse)
        problem.y = new double[problem.l];    // Output-Labels (0.0 = Pass, 1.0 = Fail)

        for (int i = 0; i < configs.size(); i++) {
            TestedConfig config = configs.get(i);

            // 1. Label setzen
            problem.y[i] = config.isFail ? 1.0 : -1.0;

            // 2. Features und Interaktionen extrahieren
            List<Feature> rowFeatures = new ArrayList<>();
            Arrays.sort(config.activeFeatures); // Sicherstellen, dass die Basis-Features sortiert sind

            for (int f = 0; f < config.activeFeatures.length; f++) {
                int featA = config.activeFeatures[f];

                // 1-wise Feature hinzufügen
                rowFeatures.add(new FeatureNode(featA, 1.0));
                idToNameMap.put(featA, "Feature_" + featA); // Für den lesbaren Output später

                // 2-wise Interaktionen generieren (A * B)
                for (int j = f + 1; j < config.activeFeatures.length; j++) {
                    int featB = config.activeFeatures[j];
                    int interactionId = getOrCreateInteractionId(featA, featB);
                    rowFeatures.add(new FeatureNode(interactionId, 1.0));
                }
            }

            // WICHTIG: LibLinear verlangt, dass die Indizes in jedem Array strikt aufsteigend sortiert sind!
            rowFeatures.sort(Comparator.comparingInt(Feature::getIndex));
            problem.x[i] = rowFeatures.toArray(new Feature[0]);
        }

        // Maximale ID setzen (1-wise Features + generierte 2-wise Interaktionen)
        problem.n = nextAvailableId;

        // 3. Solver konfigurieren
        // L1R_LR = L1-Regularized Logistic Regression (Das "Lasso", welches Sparse-Lösungen erzwingt)
        // C = 1.0 (Kostenparameter, kann für mehr "Strenge" verringert werden, z.B. 0.5)
        // eps = 0.01 (Toleranz für das Abbruchkriterium)
        Parameter parameter = new Parameter(SolverType.L1R_LR, 10.0, 0.01);

        // 4. Modell trainieren
        Model model = Linear.train(problem, parameter);

        // 5. Ergebnisse auswerten
        printTopSuspects(model);
    }

    /**
     * Mappt ein Feature-Paar auf eine eindeutige ID für das ML-Modell.
     */
    private int getOrCreateInteractionId(int f1, int f2) {
        // Formatiere Schlüssel immer als "kleinereID_größereID"
        String key = (f1 < f2) ? (f1 + "_" + f2) : (f2 + "_" + f1);

        if (!interactionToIdMap.containsKey(key)) {
            int newId = nextAvailableId++;
            interactionToIdMap.put(key, newId);
            idToNameMap.put(newId, "Interaktion (" + f1 + " & " + f2 + ")");
        }
        return interactionToIdMap.get(key);
    }

    /**
     * Extrahiert die Gewichte und gibt die wahrscheinlichsten Fehlerursachen aus.
     */
    private void printTopSuspects(Model model) {
        double[] weights = model.getFeatureWeights();
        int[] labels = model.getLabels();

        System.out.println("\n--- DEBUG INFO UNTER DER HAUBE ---");
        System.out.println("LibLinear hat diese Klassen gefunden: " + Arrays.toString(labels));

        // Wir prüfen, auf welches Label LibLinear die positiven Gewichte ausgerichtet hat
        double targetDirection = (labels[0] == 1) ? 1.0 : -1.0;
        System.out.println("Multiplikator für 'Fail'-Richtung: " + targetDirection);
        System.out.println("------------------------------------");

        List<Map.Entry<String, Double>> suspects = new ArrayList<>();

        for (int i = 0; i < weights.length; i++) {
            // Zeige ALLES an, was nicht exakt 0.0 ist (LibLinear hat 4 Stück gefunden!)
            if (weights[i] != 0.0) {
                int actualFeatureId = i + 1;
                String name = idToNameMap.getOrDefault(actualFeatureId, "Unknown_" + actualFeatureId);

                // Hier drehen wir das Gewicht in die richtige Richtung
                double actualWeight = weights[i] * targetDirection;

                System.out.printf("[DEBUG] Roh-Gewicht: %8.4f | In Fail-Richtung: %8.4f -> %s\n",
                        weights[i], actualWeight, name);

                // Schwächerer Threshold für winzige Datensätze
                if (actualWeight > 0.0001) {
                    suspects.add(new AbstractMap.SimpleEntry<>(name, actualWeight));
                }
            }
        }

        suspects.sort((e1, e2) -> Double.compare(e2.getValue(), e1.getValue()));

        System.out.println("\n--- Diagnose-Ergebnis (Wahrscheinliche Fehlerquellen) ---");
        if (suspects.isEmpty()) {
            System.out.println("Das Modell konnte keine klaren Fehlerursachen isolieren.");
        } else {
            for (Map.Entry<String, Double> suspect : suspects) {
                System.out.printf("Gewicht %.4f -> %s\n", suspect.getValue(), suspect.getKey());
            }
        }
    }

    // --- MAIN METHODE ZUM TESTEN (Unser A OR B Szenario) ---
    public static void main(String[] args) {
        GeneticAlgo locator = new GeneticAlgo();

        // Feature Definitionen: 1=Root(M), 2=A, 3=B, 4=C
        // Wir simulieren den Fehler: (Feature 2)
        List<TestedConfig> configs = new ArrayList<>();

        configs.add(new TestedConfig(new int[]{4}, false));          // T2: Nicht A -> pass
        configs.add(new TestedConfig(new int[]{2}, true));           // T3: A aktiv -> fail
        configs.add(new TestedConfig(new int[]{3}, false));          // T4: Nicht A -> pass
        configs.add(new TestedConfig(new int[]{3, 4}, false));       // T7: Nicht A -> pass

        // 4 ist unsere maximale 1-wise Feature ID
        locator.analyzeConfigurations(configs, 4);
    }
}