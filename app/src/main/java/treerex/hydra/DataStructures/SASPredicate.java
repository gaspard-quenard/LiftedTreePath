package treerex.hydra.DataStructures;

import java.util.ArrayList;

public class SASPredicate {

    // Thd id of the predicate
    int id;

    int lastDefined;

    String predicateName;

    String fullName;

    ArrayList<String> params;

    // A predicate can belong to multiples clique
    ArrayList<Clique> cliques;

    // The value of predicate into each of the cliques
    ArrayList<Integer> valueInCliques;

    public SASPredicate(int id, String predicateName, String fullName, ArrayList<String> paramsPredicates) {
        this.id = id;
        this.lastDefined = 0;
        this.predicateName = predicateName;
        this.fullName = fullName;
        this.cliques = new ArrayList<>();
        this.valueInCliques = new ArrayList<>();
        this.params = new ArrayList<>();
        this.params.addAll(paramsPredicates);
    }

    public void addClique(Clique clique, int value) {
        this.cliques.add(clique);
        this.valueInCliques.add(value);
    } 
    
    public int getLastTimePredicateWasDefined() {
        return this.lastDefined;
    }

    public void setLastTimePredicateWasDefined(int lastDefined) {
        this.lastDefined = lastDefined;
    }

    public ArrayList<Clique> getCliques() {
        return this.cliques;
    }

    public ArrayList<Integer> getValuesPredInClique() {
        return this.valueInCliques;
    }

    public String getPredicateName() {
        return this.predicateName;
    }

    public String getFullName() {
        return this.fullName;
    }

    public ArrayList<String> getParams() {
        return this.params;
    }
}