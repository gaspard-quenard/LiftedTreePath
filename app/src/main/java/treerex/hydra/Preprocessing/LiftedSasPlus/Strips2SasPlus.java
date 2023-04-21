package treerex.hydra.Preprocessing.LiftedSasPlus;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Collection;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;

//Strips2SasPlus exists for 2 reasons
//1. The fluent2Clique map
//2. To be able to create a clique for each fluent (i.e. no SAS+)
public class Strips2SasPlus {
    static public List<List<Integer>> cliques = new ArrayList<>(); // all mutex sets
    static public HashMap<Integer, Integer> fluent2Clique = new HashMap<Integer, Integer>(); // key: fluentId; value:
                                                                                             // cliqueId
    // fluent2Clique allows us to quickly find to which clique some fluent belongs
    // to

    // for every fluent creates its own clique. I.e. No SAS+
    public static void cliquePerFact(Problem problem) {
        cliques.clear();
        for (int i = 0; i < problem.getFluents().size(); i++) {
            List<Integer> chosenSetFiltered = new ArrayList<>();
            chosenSetFiltered.add(i);
            fluent2Clique.put(i, i); // the mapping indicating to which clique a specific fluent belongs
            cliques.add(chosenSetFiltered);
        }

    }

    public static void resetCliques() {
        cliques.clear();
        fluent2Clique = new HashMap<Integer, Integer>();
    }

    public static List<List<Integer>> collectionToList(List<Collection<Integer>> unconvCliques, Problem problem) {
        List<List<Integer>> out = new ArrayList<>();

        for (Collection<Integer> col : unconvCliques) {
            List<Integer> newList = new ArrayList<>(col);
            out.add(newList);
            for (int fluent : newList) {
                fluent2Clique.put(fluent, out.size() - 1);
            }

        }

        // if fluent is not in a mutex group, create a mutex group
        // with single item
        for (int fluentId = 0; fluentId < problem.getFluents().size(); fluentId++) {
            if (Strips2SasPlus.fluent2Clique.get(fluentId) == null) {
                Strips2SasPlus.fluent2Clique.put(fluentId, out.size());
                List<Integer> tmp = new ArrayList<Integer>();
                tmp.add(fluentId);
                out.add(tmp);
            }
        }
        return out;
    }

}
