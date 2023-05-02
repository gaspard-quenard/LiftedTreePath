package treerex.hydra.SolverConfig;

public class LiftedTreePathConfig {
    // Debug mode
    public static boolean DEBUG = false;

    public static boolean simplifyEffsActionsWithSASPlus = false;
    // Use SAS+ encoding
    public static boolean useSASPlusEncoding = false;
    // Use macro actions
    public static boolean useMacroAction = false;

    // If multiple actions have the same preconditions, use a (or actions) => precondition instead of action1 => precondition, action2 => precondition...
    public static boolean accumulatePrecondtions = false;

    // Compute for each path, the set of predicate which can be true at this path
    // And use it to restrict the range of the scope variables
    public static boolean restrictRangeScopeVars = false;

    // Use an optimized version of the at most one constraint
    public static boolean optimizedAtMostOne = false;

    // Share the same scope for action which cannot be executed concurrently instead of creating a new scope every time a method or action needs it
    public static boolean reuseScopeVariable = false;

    // Use the Z3 API instead of the SMTLIB2 format
    public static boolean useZ3Api = false;

    public LiftedTreePathConfig(boolean debug, boolean simplifyEffsActionsWithSASPlus, boolean useSASPlusEncoding, boolean useMacroAction) {
        LiftedTreePathConfig.DEBUG = debug;
        LiftedTreePathConfig.simplifyEffsActionsWithSASPlus = simplifyEffsActionsWithSASPlus;
        LiftedTreePathConfig.useSASPlusEncoding = useSASPlusEncoding;
        LiftedTreePathConfig.useMacroAction = useMacroAction;


        LiftedTreePathConfig.restrictRangeScopeVars = false;
        LiftedTreePathConfig.reuseScopeVariable = true;

        LiftedTreePathConfig.accumulatePrecondtions = false;

        LiftedTreePathConfig.optimizedAtMostOne = false;

        // LiftedTreePathConfig.useZ3Api = true;
    }
}
