package treerex.hydra.DataStructures;

public class OutputStatistics {
    private int solveTimeInMs;
    private int walltimeInMs;
    private boolean timeout;
    private boolean unsolvable;
    private boolean crashed;

    public OutputStatistics(int solvetimeInMs, int walltimeInMs, boolean timeout, boolean unsolvable) {
        this.solveTimeInMs = solvetimeInMs;
        this.walltimeInMs = walltimeInMs;
        this.timeout = timeout;
        this.unsolvable = unsolvable;
        this.crashed = false;
    }

    public OutputStatistics() {
        this.crashed = true;
    }

    public boolean crashed() {
        return crashed;
    }

    public boolean unsolvable() {
        return unsolvable;
    }

    public boolean timeout() {
        return timeout;
    }

    public int getSolvetime() {
        return solveTimeInMs;
    }

    public int getWalltime() {
        return walltimeInMs;
    }
}
