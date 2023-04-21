package treerex.hydra.SolverConfig;

public class LiftedTreePathConfig {
    // Debug mode
    public static boolean DEBUG = false;

    public static boolean simplifyEffsActionsWithSASPlus = false;
    // Use SAS+ encoding
    public static boolean useSASPlusEncoding = false;
    // Use macro actions
    public static boolean useMacroAction = false;

    public LiftedTreePathConfig(boolean debug, boolean simplifyEffsActionsWithSASPlus, boolean useSASPlusEncoding, boolean useMacroAction) {
        LiftedTreePathConfig.DEBUG = debug;
        LiftedTreePathConfig.simplifyEffsActionsWithSASPlus = simplifyEffsActionsWithSASPlus;
        LiftedTreePathConfig.useSASPlusEncoding = useSASPlusEncoding;
        LiftedTreePathConfig.useMacroAction = useMacroAction;
    }
}
