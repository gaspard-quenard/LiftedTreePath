package treerex.hydra.DataStructures;

import java.util.HashSet;

import org.apache.commons.lang3.tuple.Pair;

public class ScopesEqual {

    private Pair<ScopeVariable, ScopeVariable> scopeEquals;
    private String name;

    public ScopesEqual(ScopeVariable scopeVar1, ScopeVariable scopeVar2) {
        scopeEquals = unorderedKeyPair(scopeVar1, scopeVar2);
        this.name = this.scopeEquals.getLeft().getUniqueName() + "__eq__" + this.scopeEquals.getRight().getUniqueName();
    }

    public boolean contains(ScopeVariable scopeVariable1, ScopeVariable scopeVariable2) {
        Pair<ScopeVariable, ScopeVariable> key = unorderedKeyPair(scopeVariable1, scopeVariable2);
        return scopeEquals.equals(key);
    }

    private Pair<ScopeVariable, ScopeVariable> unorderedKeyPair(ScopeVariable key1, ScopeVariable key2) {
        if (key1.hashCode() < key2.hashCode()) {
            return Pair.of(key1, key2);
        } else {
            return Pair.of(key2, key1);
        }
    }

    public String getName() {
        return name;
    }

    public String generateSMTRule() {
        StringBuilder sb = new StringBuilder();
        
        // First, compute the intersection of the two sets
        HashSet<String> intersection = new HashSet<String>(this.scopeEquals.getLeft().getPossibleValueVariable());
        intersection.retainAll(this.scopeEquals.getRight().getPossibleValueVariable());

        // Next compute the difference of the two sets (all values that is in at most one of the sets)
        // HashSet<String> difference = new HashSet<String>(this.scopeEquals.getLeft().getPossibleValueVariable());
        // difference.addAll(this.scopeEquals.getRight().getPossibleValueVariable());
        // difference.removeAll(intersection);

        // With that, we can generate the SMT rule
        sb.append("(assert (= " + this.getName() + " (or ");
        for (String value : intersection) {
            sb.append("(and " + this.scopeEquals.getLeft().getUniqueName() + "__" + value + " " + this.scopeEquals.getRight().getUniqueName() + "__" + value + ") ");
        }
        if (intersection.size() == 0) {
            sb.append("false ");
        }
        sb.append(")))\n");

        return sb.toString();
    }
 
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof ScopesEqual)) {
            return false;
        }
        ScopesEqual other = (ScopesEqual) obj;
        return this.scopeEquals.equals(other.scopeEquals);
    }

    @Override
    public int hashCode() {
        return this.scopeEquals.hashCode();
    }
}
