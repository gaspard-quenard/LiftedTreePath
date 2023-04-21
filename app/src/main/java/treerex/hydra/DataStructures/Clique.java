package treerex.hydra.DataStructures;

import java.util.ArrayList;

import treerex.hydra.Preprocessing.LiftedSasPlus.Candidate;

public class Clique {
    int idMutexGround;
    int nbBits;
    Candidate LFG;
    ArrayList<String> params;
    public int numberValues;
    public int id;
    int lastDefined = 0;
    static int idCounter = 0;

    public Clique(int idMutexGround, Candidate LFG, ArrayList<String> params) {
        this.idMutexGround = idMutexGround;
        this.LFG = LFG;
        this.params = params;
        this.numberValues = 1; // By default, the number of values is 1
        this.nbBits = 1;
        this.id = idCounter;
        Clique.idCounter++;
    }

    public void setNumberValues(int numberValues) {
        this.numberValues = numberValues;
        this.nbBits = (int) Math.ceil((Math.log(numberValues) / Math.log(2)));
    }

    public ArrayList<String> getParams() {
        return this.params;
    }

    public Candidate getParentLFG() {
        return this.LFG;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("Clique " + this.id + " Mutex group: " + LFG.toString() + " params: ");
        for (String param : this.params) {
            sb.append(param);
        }
        return sb.toString();
    }

    public int getNbBits() {
        return nbBits;
    }

    public int getLastTimeCliqueWasDefined() {
        return this.lastDefined;
    }

    public void setLastTimeCliqueWasDefined(int lastDefined) {
        this.lastDefined = lastDefined;
    }
}
