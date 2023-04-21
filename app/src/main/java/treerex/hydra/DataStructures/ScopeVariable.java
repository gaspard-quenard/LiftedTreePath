package treerex.hydra.DataStructures;

import java.util.HashSet;
import java.util.Iterator;


public class ScopeVariable {

    static int numScopeVariable;

    private int uniqueId;
    private String typeVariable;
    private HashSet<String> possibleValueVariable;

    public ScopeVariable() {
        this.typeVariable = null;
        this.possibleValueVariable = new HashSet<String>();

        this.uniqueId = ScopeVariable.numScopeVariable;
        ScopeVariable.numScopeVariable++;
    }

    public void addTypeVariable(String typeVariable) {
        this.typeVariable = typeVariable;
    }

    public void addValueToScope(String value) {
        this.possibleValueVariable.add(value);
    }

    public HashSet<String> getPossibleValueVariable() {
        return this.possibleValueVariable;
    }

    public String getType() {
        return this.typeVariable;
    }

    public boolean isConstant() {
        return this.possibleValueVariable.size() == 1;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append(this.getUniqueName() + ": ");
        sb.append("<" + this.typeVariable + "> ");
        if (!this.isConstant()) {
            sb.append(" { ");
            for (String value : this.possibleValueVariable) {
                sb.append(value + " ");
            }
            sb.append("}");
        }
        return sb.toString();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (!ScopeVariable.class.isAssignableFrom(obj.getClass())) {
            return false;
        }
        final ScopeVariable other = (ScopeVariable) obj;
        if (this.uniqueId != other.uniqueId) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        return this.uniqueId;
    }

    public String getUniqueName() {
        if (this.isConstant()) {
            Iterator<String> it = this.possibleValueVariable.iterator();
            return it.next();
        } else {
            return "SCOPE_" + uniqueId;
        }

    }
}