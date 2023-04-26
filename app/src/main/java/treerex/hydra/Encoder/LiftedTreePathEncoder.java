package treerex.hydra.Encoder;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Stack;
import java.util.Vector;

import fr.uga.pddl4j.parser.Connector;
import fr.uga.pddl4j.parser.Expression;
import fr.uga.pddl4j.parser.NamedTypedList;
import fr.uga.pddl4j.parser.ParsedAction;
import fr.uga.pddl4j.parser.ParsedMethod;
import fr.uga.pddl4j.parser.Symbol;
import fr.uga.pddl4j.parser.TypedSymbol;
import fr.uga.pddl4j.plan.Hierarchy;
import fr.uga.pddl4j.plan.Plan;
import fr.uga.pddl4j.plan.SequentialPlan;
import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.problem.operator.TaskNetwork;
import treerex.hydra.DataStructures.CertifiedPredicate;
import treerex.hydra.DataStructures.Clique;
import treerex.hydra.DataStructures.LiftedFlow;
import treerex.hydra.DataStructures.PrimitiveTree;
import treerex.hydra.DataStructures.SASPredicate;
import treerex.hydra.DataStructures.ScopeVariable;
import treerex.hydra.HelperFunctions.UtilFunctions;
import treerex.hydra.Preprocessing.UtilsStructureProblem;
import treerex.hydra.Preprocessing.LiftedSasPlus.AtomCandidate;
import treerex.hydra.Preprocessing.LiftedSasPlus.AtomVariable;
import treerex.hydra.Preprocessing.LiftedSasPlus.Candidate;
import treerex.hydra.Preprocessing.LiftedSasPlus.SASplusLiftedFamGroup;
import treerex.hydra.SolverConfig.LiftedTreePathConfig;
import org.apache.commons.lang3.tuple.Pair;

enum LIFTED_FAM_GROUP_UNIFIER {
    SUCCESS,
    FAILED,
    SUCCESS_WITH_CONSTRAINS
}

public class LiftedTreePathEncoder {

    private final Problem problem;

    boolean DEBUG_DO_NOT_MERGE_ACTION = true;

    private final LiftedTreePathConfig config;

    StringBuilder allClauses;
    Vector<String> allBoolVariables;
    Vector<String> allIntVariables;

    ArrayList<LiftedFlow> initialPaths;
    ArrayList<LiftedFlow> paths;

    // A dictionary which map the name of a type to all the parent of this type
    private Map<String, HashSet<String>> dictTypeToParentTypes;
    // A dictionary which map the name of a type to all the children of this type
    private Map<String, HashSet<String>> dictTypeToChildTypes;

    HashSet<String> staticPredicates;

    HashSet<String> predicatesToDefine;

    Map<String, Vector<String>> dictTypeToObjects;
    Map<String, Integer> liftedMethodToNumberSubtasks;
 
    Map<String, ParsedMethod> methodNameToObj;
    Map<String, ParsedAction> actionNameToObj;

    Map<String, ScopeVariable> dictConstantToScopeVariable;

    Map<String, Integer> objNameToUniqueId;

    ArrayList<ArrayList<Integer>> cliques;

    HashMap<Integer, ArrayList<String>> dictIdxToFrameAxioms;

    ArrayList<String> rule13PerTimeStep;
    ArrayList<String> frameAxiomsAndEffsPerTimeStep;

    HashSet<String> fluentsTrueInit;
    HashSet<String> fluentsFalseInit;

    HashSet<Integer> fluentsIdTrueInit;
    HashSet<Integer> fluentsIdFalseInit;

    HashSet<Integer> fluentsIdTrueGoal;
    HashSet<Integer> fluentsIdFalseGoal;

    HashSet<String> cliqueBitsToDefine;
    HashSet<String> groundFactsToDefine;
    HashSet<String> pseudoFactsToDefine;

    HashSet<ScopeVariable> scopeVarsToDefine;

    private int layer = 0;

    String filenameSMT = "LiftedTreePathFrameAxioms.SMT";
    private String path_exec_VAL = "validator/pandaPIparser";
    String domainPath;
    String problemPath;

    // A dictionary which map the name of an object to the type of the object
    private Map<String, String> dictObjNameToType;

    Map<String, HashSet<String>> dictPredNameToLiftedActionWithPredAsPosEff;
    Map<String, HashSet<String>> dictPredNameToLiftedActionWithPredAsNegEff;

    Map<String, Map<String, ArrayList<Integer>>> dictIdxArgPredToIdxArgActionAssociatedPosEff;
    Map<String, Map<String, ArrayList<Integer>>> dictIdxArgPredToIdxArgActionAssociatedNegEff;

    PrimitiveTree primitiveTree;

    ArrayList<Candidate> liftedFamGroups;

    public void showAllPaths() {

        // Show a single path
        for (LiftedFlow f : this.initialPaths) {
            String prettyDisplayLiftedFlow = f.prettyDisplay(problem);
            System.out.println(prettyDisplayLiftedFlow);
        }
    }

    public LiftedTreePathEncoder(Problem problem, String domainPath, String problemPath) throws IOException {

        this.domainPath = domainPath;
        this.problemPath = problemPath;

        this.config = new LiftedTreePathConfig(true, false, false, false);

        rule13PerTimeStep = new ArrayList<String>();
        frameAxiomsAndEffsPerTimeStep = new ArrayList<String>();

        this.dictIdxToFrameAxioms = new HashMap<Integer, ArrayList<String>>();

        this.predicatesToDefine = new HashSet<String>();

        cliqueBitsToDefine = new HashSet<String>();
        groundFactsToDefine = new HashSet<String>();
        pseudoFactsToDefine = new HashSet<String>();

        this.problem = problem;
        this.allBoolVariables = new Vector<String>();
        this.allIntVariables = new Vector<String>();
        this.allClauses = new StringBuilder();
        this.primitiveTree = new PrimitiveTree();

        this.initialPaths = new ArrayList<LiftedFlow>();
        this.paths = new ArrayList<LiftedFlow>();

        this.scopeVarsToDefine = new HashSet<ScopeVariable>();
        // Ok, let's begin !
        int previousTaksId = -1;


        // Ordered all the subtaks of each task (to have a deterministic order which allow reproducibility)
        TaskNetwork initHTN = problem.getInitialTaskNetwork();
        List<Integer> unorderedTasks = initHTN.getTasks();
        // NOTE: I assume that .getTasks() returns an unordered list of child tasks
        // therefore, we must order the subtasks with regards to the ordering
        // constraints (if any)
        // If there is no order to subtasks, we apply a random (deterministic) order
        List<Integer> orderedTasks = UtilFunctions.totallyOrderedList(unorderedTasks,
                problem.getInitialTaskNetwork().getOrderingConstraints());

        problem.getInitialTaskNetwork().setTasks(orderedTasks);


        // Do the same for the methods
        for (Method method : problem.getMethods()) {
            List<Integer> unorderedSubtasks = method.getSubTasks();
            List<Integer> orderedSubtasks = UtilFunctions.totallyOrderedList(unorderedSubtasks,
                    method.getOrderingConstraints());
            method.setSubTasks(orderedSubtasks);
        }



        // TODO should remove this ??
        preprocessing();

        if (LiftedTreePathConfig.useSASPlusEncoding) {

            // Get SAS+ cliques (in the lifted form)
            SASplusLiftedFamGroup.determinateLiftedFamGroups(problem);
            // Change the lifted fam groups to an array to have a specifial index for each
            // lifted fam group
            this.liftedFamGroups = new ArrayList<Candidate>(SASplusLiftedFamGroup.candidatesProved);

            System.out.println("Lifted fam groups:");
            for (Candidate c : this.liftedFamGroups) {
                System.out.println(c.getUniqueStringRepresentation());
            }
        }


        UtilsStructureProblem.initialize(problem, this.liftedFamGroups, this.cliques);

        if (LiftedTreePathConfig.simplifyEffsActionsWithSASPlus) {
            // Remove all the negative effects of an action if there is a positive effect in the same LFG than the negative effect
            int a = 0;

            // Iterate over all the actions of the problem
            for (ParsedAction parsedAction : problem.getParsedProblem().getActions()) {


                Expression<String> effsActions = parsedAction.getEffects();

                // Iterate over all the negative effects of the parsed action
                int numberEffActions = parsedAction.getEffects().getChildren().size();
                if (numberEffActions == 0 && parsedAction.getEffects().getSymbol() != null) {
                    numberEffActions = 1;
                }

                for (int negEffId = 0; negEffId < numberEffActions; negEffId++) {

                    Expression<String> negEff;
                    if (numberEffActions > 1) {
                        negEff = effsActions.getChildren().get(negEffId);
                    } else {
                        negEff = effsActions;
                    }

                    // If this is not a negative effect, continue
                    if (!negEff.getConnector().equals(Connector.NOT)) {
                        continue;
                    }

                    negEff = negEff.getChildren().get(0);

                    // Get the predicate name of the negative effect
                    String nameNegPredicate = negEff.getSymbol().getValue();

                    // Get the type of each paramater of the predicate
                    ArrayList<String> typesParametersNegPred = new ArrayList<String>();
                    // Get the name of each parameter of the predicate
                    ArrayList<String> namesParametersNegPred = new ArrayList<String>();

                    for (Symbol<String> arg : negEff.getArguments()) {
                        namesParametersNegPred.add(arg.getValue());
                        try {
                            int idxArg = Integer.parseInt(arg.getValue().substring(2));
                            String typeArg = parsedAction.getParameters().get(idxArg).getTypes().get(0).getValue();
                            typesParametersNegPred.add(typeArg);
                        } catch (Exception e) {
                            // It must be a constant, find the constant associated with it
                            // TODO should iterate over all constants of the parsed problem and find the one with the same name
                            System.out.println("TODO");
                            System.exit(0);
                        }
                    }

                    // Now, we need to find all the lifted fam groups which can contains this predicate
                    HashSet<Candidate> liftedFamGroupsWhichCanContainsThisPredicate = new HashSet<Candidate>();
                    for (Candidate candidate : this.liftedFamGroups) {
                        if (!candidate.hasPredicateInMutexGroup(nameNegPredicate)) {
                            continue;
                        }

                        AtomCandidate atomCandidate;
                        for (AtomCandidate aC : candidate.mutexGroup) {
                            if (aC.predSymbolName.equals(nameNegPredicate)) {

                                boolean allParametersAreCompatible = true;

                                // Check if all the parameters of the predicate are can be included into the atomCandidate
                                for (int i = 0; i < aC.paramsId.size(); i++) {
                                    String typeParamAtomCandidate = candidate.variables.get(aC.paramsId.get(i)).typeName;

                                    // Check if this type is equal to the type of the parameter of the predicate or if it is a parent of the type of the parameter of the predicate
                                    if (!typeParamAtomCandidate.equals(typesParametersNegPred.get(i)) && this.dictTypeToChildTypes.get(typeParamAtomCandidate).contains(typesParametersNegPred.get(i))) {
                                        allParametersAreCompatible = false;
                                        break;
                                    }
                                }
                                    
                                if (!allParametersAreCompatible) {
                                    continue;
                                }

                                // Set the value of the lifted fam group (for all fixed variables)
                                for (int i = 0; i < aC.paramsId.size(); i++) {
                                    AtomVariable var = candidate.variables.get(aC.paramsId.get(i));
                                    if (!var.isCountedVar) {
                                        var.value = namesParametersNegPred.get(i);
                                    }   
                                }

                                liftedFamGroupsWhichCanContainsThisPredicate.add(candidate);
                                break;
                            }
                        }
                    }

                    // Now, we need to iterate over all positive effects of the action and check if the positive effect is in the same lifted fam group than the negative effect
                    // If that's the case, we can remove the negative effect
                    for (int posEffId = 0; posEffId < numberEffActions; posEffId++) {

                        Expression<String> posEff;
                        if (numberEffActions > 1) {
                            posEff = effsActions.getChildren().get(posEffId);
                        } else {
                            posEff = effsActions;
                        }
    
                        // If is not a negative effect, continue
                        if (posEff.getConnector().equals(Connector.NOT)) {
                            continue;
                        }

                        // Get the predicate name of the positive effect
                        String namePosPredicate = posEff.getSymbol().getValue();

                        // Get the type of each paramater of the predicate
                        ArrayList<String> typesParametersPosPred = new ArrayList<String>();
                        // Get the name of each parameter of the predicate
                        ArrayList<String> namesParametersPosPred = new ArrayList<String>();

                        for (Symbol<String> arg : posEff.getArguments()) {
                            namesParametersPosPred.add(arg.getValue());
                            try {
                                int idxArg = Integer.parseInt(arg.getValue().substring(2));
                                String typeArg = parsedAction.getParameters().get(idxArg).getTypes().get(0).getValue();
                                typesParametersPosPred.add(typeArg);
                            } catch (Exception e) {
                                // It must be a constant, find the constant associated with it
                                // TODO should iterate over all constants of the parsed problem and find the one with the same name
                                System.out.println("TODO");
                                System.exit(0);
                            }
                        }

                        // Ok, now we have evrything we need to check if the positive effect is in the same lifted fam group than the negative effect
                        boolean isPosEffectInSameLiftedFamGroupThanNegEffect = false;
                        for (Candidate candidate : liftedFamGroupsWhichCanContainsThisPredicate) {
                            if (!candidate.hasPredicateInMutexGroup(namePosPredicate)) {
                                continue;
                            }

                            AtomCandidate atomCandidate;
                            for (AtomCandidate aC : candidate.mutexGroup) {
                                if (aC.predSymbolName.equals(namePosPredicate)) {

                                    boolean allParametersAreCompatible = true;

                                    // Check if all the parameters of the predicate are can be included into the atomCandidate
                                    for (int i = 0; i < aC.paramsId.size(); i++) {
                                        String typeParamAtomCandidate = candidate.variables.get(aC.paramsId.get(i)).typeName;

                                        // Check if this type is equal to the type of the parameter of the predicate or if it is a parent of the type of the parameter of the predicate
                                        if (!typeParamAtomCandidate.equals(typesParametersPosPred.get(i)) && this.dictTypeToChildTypes.get(typeParamAtomCandidate).contains(typesParametersPosPred.get(i))) {
                                            allParametersAreCompatible = false;
                                            break;
                                        }

                                        // If this is a fixed variable, check if the value of the variable is the same as the value of the parameter
                                        AtomVariable var = candidate.variables.get(aC.paramsId.get(i));
                                        if (!var.isCountedVar && !var.value.equals(namesParametersPosPred.get(i))) {
                                            allParametersAreCompatible = false;
                                            break;
                                        }
                                    }
                                        
                                    if (!allParametersAreCompatible) {
                                        continue;
                                    }

                                    // All the parameters are compatible, we can remove the negative effect
                                    isPosEffectInSameLiftedFamGroupThanNegEffect = true;
                                    break;
                                }
                            }

                            if (isPosEffectInSameLiftedFamGroupThanNegEffect) {
                                break;
                            }
                        }

                        if (isPosEffectInSameLiftedFamGroupThanNegEffect) {
                            // Remove the negative effect
                            if (numberEffActions > 1) {
                                effsActions.getChildren().remove(negEffId);
                                numberEffActions--;
                                negEffId--;
                                if (numberEffActions == 1) {
                                    // We need to remove the 'and' symbol
                                    effsActions = effsActions.getChildren().get(0);
                                    parsedAction.setEffects(effsActions);
                                    int d = 0;
                                }
                            } else {
                                effsActions = null;
                                numberEffActions = 0;
                            }
                            // The negative effect has already been removed, we do not care, if it is in the same lifted fam group than another positive effect
                            break;
                        }
                    }
                }
            }
        }

        if (LiftedTreePathConfig.useSASPlusEncoding) {
            // Convert the List<CollectionqInteger> to an ArrayList<ArrayList<Integer>>
            this.cliques = new ArrayList<ArrayList<Integer>>();
            for (Collection<Integer> clique : SASplusLiftedFamGroup.cliques) {
                ArrayList<Integer> cliqueAsArrayList = new ArrayList<Integer>(clique);
                this.cliques.add(cliqueAsArrayList);
            }
        }


        

        
        // Determinate the initial state
        this.fluentsTrueInit = new HashSet<String>();
        this.fluentsFalseInit = new HashSet<String>();

        this.fluentsIdTrueInit = new HashSet<Integer>();
        this.fluentsIdFalseInit = new HashSet<Integer>();

        // We need to iterate over all possible predicates
        UtilsStructureProblem.findAllPredicateTrueAndFalseForInitialState(problem, this.fluentsTrueInit, this.fluentsFalseInit);
        UtilsStructureProblem.findAllPredicateIdTrueAndFalseForInitialState(problem, this.fluentsIdTrueInit, this.fluentsIdFalseInit);

        // Determinate the goal state
        this.fluentsIdTrueGoal = new HashSet<Integer>();
        this.fluentsIdFalseGoal = new HashSet<Integer>();

        UtilsStructureProblem.findAllPredicateIdTrueAndFalseForGoalState(problem, this.fluentsIdTrueGoal, this.fluentsIdFalseGoal);


        for (int i = 0; i < this.problem.getInitialTaskNetwork().getTasks().size(); i++) {

            int idxTaskNetwork = this.problem.getInitialTaskNetwork().getTasks().get(i);
            // int idxTaskNetwork = orderedTasks.get(i);

            // Get all the methods which can resolve this task and the scope of the variable
            // of each of the method which can resolve this task

            Map<String, ArrayList<ScopeVariable>> methodNameToScope = new HashMap<String, ArrayList<ScopeVariable>>();
            for (int idxMethod : this.problem.getTaskResolvers().get(idxTaskNetwork)) {
                Method m = this.problem.getMethods().get(idxMethod);
                if (!methodNameToScope.containsKey(m.getName())) {
                    // Initialize the score of this method
                    ArrayList<ScopeVariable> scopeMethod = new ArrayList<>();
                    for (int k = 0; k < m.getParameters().length; k++) {
                        ScopeVariable s = new ScopeVariable();
                        this.scopeVarsToDefine.add(s);
                        scopeMethod.add(s);
                    }
                    methodNameToScope.put(m.getName(), scopeMethod);
                }
                // Add all the arguments in the scope of the method
                ArrayList<ScopeVariable> scopeMethod = methodNameToScope.get(m.getName());
                for (int argi = 0; argi < m.getParameters().length; argi++) {
                    String objName = problem.getConstantSymbols().get(m.getInstantiations()[argi]);
                    String objType = this.dictObjNameToType.get(objName);
                    scopeMethod.get(argi).addValueToScope(objName);
                    // Add the type as well
                    scopeMethod.get(argi).addTypeVariable(objType);
                }
            }

            // Now we can add all of our methods with the appropriate scope
            // Create a flow for each different method that can be taken
            for (String methodName : methodNameToScope.keySet()) {
                LiftedFlow f = new LiftedFlow(methodName, null, idxTaskNetwork, methodNameToScope.get(methodName),
                        methodNameToObj, false, this.liftedFamGroups);
                this.paths.add(f);

                if (i == 0) {
                    this.initialPaths.add(f);
                }

                // Indicate to all the flows from the previous task network that they we must
                // follow them
                for (LiftedFlow previousLiftedFlow : this.paths) {
                    if (previousLiftedFlow.getParentId() == previousTaksId) {
                        previousLiftedFlow.addNextLiftedFlow(f);

                        f.addPreviousesLiftedFlow(previousLiftedFlow);
                    }
                }
            }
            previousTaksId = idxTaskNetwork;
        }

        showAllPaths();

        // Now, we have all our initial paths
        int layerMax = 10;
        while (layer <= layerMax) {

            System.out.println("==================");
            System.out.println("FOR LAYER: " + layer);
            System.out.println("==================");

            // Check if there exist a path where there are only primitivate action
            // If there is, encode all paths with primitive actions to SAT (and encode
            // all the paths possible as well to better guide the SAT research)

            // System.out.println("Get all primitive paths");
            // getAllPrimitivePaths();

            System.out.println("Create primitive tree");
            // createPrimitiveTree();
            // createPrimitiveTreeQuick();
            createPrimitiveTreeQuick2();

            // List of ID to check:
            

            // SOME DEBUG
            // if (layer == 7) {
            //     // List<Integer> id = Arrays.asList(363, 480, 1397, 265, 657, 2795, 268, 53, 377, 409, 994, 1837, 475, 1280, 3420, 478, 34, 89, 444, 600, 27, 115, 458, 926, 2885, 30, 5);
            //     List<String> id = Arrays.asList(
            //         "FLOW_A_m_construct_factory-m_get_resource-m_construct_factory-m_get_resource-m_factory_already_constructed-BLANK", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_construct_factory-m_get_resource-m_produce_resource-produce-without-demands", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_construct_factory-m_get_resource-m_deliver_resource-m_already_there-BLANK", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_construct_factory-m_get_resource-m_deliver_resource-pickup", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_construct_factory-m_get_resource-m_deliver_resource-m_goto-move", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_construct_factory-m_get_resource-m_deliver_resource-m_goto-m_already_there-BLANK", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_construct_factory-m_get_resource-m_deliver_resource-drop", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_construct_factory-construct", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_get_and_produce_resource-m_get_resource-m_factory_already_constructed-BLANK", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_get_and_produce_resource-m_get_resource-m_produce_resource-produce-without-demands", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_get_and_produce_resource-m_get_resource-m_deliver_resource-m_goto-move", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_get_and_produce_resource-m_get_resource-m_deliver_resource-m_goto-m_already_there-BLANK", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_get_and_produce_resource-m_get_resource-m_deliver_resource-pickup", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_get_and_produce_resource-m_get_resource-m_deliver_resource-m_goto-move", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_get_and_produce_resource-m_get_resource-m_deliver_resource-m_goto-m_already_there-BLANK", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_get_and_produce_resource-m_get_resource-m_deliver_resource-drop", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_get_and_produce_resource-produce", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_deliver_resource-m_goto-move", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_deliver_resource-m_goto-m_goto-move", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_deliver_resource-m_goto-m_goto-m_already_there-BLANK", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_deliver_resource-pickup", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_deliver_resource-m_goto-move", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_deliver_resource-m_goto-m_goto-move", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_deliver_resource-m_goto-m_goto-m_goto-move", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_deliver_resource-m_goto-m_goto-m_goto-m_already_there-BLANK", 
            //         "FLOW_A_m_construct_factory-m_get_resource-m_deliver_resource-drop", 
            //         "FLOW_A_m_construct_factory-construct"
            //     );
                

            //     // First, check that one of the initial path correspond to the first id
            //     LiftedFlow f = null;
            //     for (LiftedFlow f2 : this.initialPaths) {
            //         if (f2.getUniqueName().split("%")[0].equals(id.get(0))) {
            //             f = f2;
            //             if (!this.primitiveTree.getNodes().contains(f)) {
            //                 System.out.println("ERROR: the first id is not in the primitive tree");
            //                 System.exit(0);
            //             }
            //             break;
            //         }
            //     }

            //     if (f == null) {
            //         System.out.println("ERROR: the first id is not in the initial paths");
            //         System.exit(0);
            //     }

            //     if (f.isMethodLiftedFlow())  {
            //         System.out.println("ERROR: the first id is a method");
            //         System.exit(0);
            //     }

            //     // Now, check that one of the nextFlows of the first id is the second id and it is not a method, and so on until the end of the list
            //     for (int i = 1; i < id.size(); i++) {
            //         System.out.println(f.getUniqueName());
            //         boolean found = false;
            //         for (LiftedFlow f2 : f.getNextsLiftedFlow()) {
            //             if (f2.getUniqueName().split("%")[0].equals(id.get(i))) {
            //                 f = f2;
            //                 found = true;
            //                 if (!this.primitiveTree.getNodes().contains(f)) {
            //                     System.out.println("ERROR: the id is not in the primitive tree");
            //                     System.exit(0);
            //                 }
            //                 break;
            //             }
            //         }
            //         if (!found) {
            //             System.out.println("ERROR: the id " + id.get(i) + " is not in the next flows of " + f.getUniqueName());
            //             System.exit(0);
            //         }
            //         if (f.isMethodLiftedFlow())  {
            //             System.out.println("ERROR: the id " + id.get(i) + " is a method");
            //             System.exit(0);
            //         }
            //         // System.out.println(i + " / " + id.size() + "-> OK");
            //     }

            //     int a = 0;
            // }




            // To debug, write into a file all the paths (which can then be visualized with graphviz)
            // debugWriteAllPathsInFile(layer);

            boolean primitivePathExist = (this.primitiveTree.getNodes().size() > 0);

            if (primitivePathExist) {

                // Find all the certified predicate (predicate which we do know the value if we
                // are in a current node)
                System.out.println("Compute certified predicates primitive tree");
                computeCertifiedPredicatesPrimitiveTree();

                System.out.println("Encode SMT\n");
                // Encode for SAT
                // CleanAndOptimizePritmitivePaths();
                try {
                    encodeSAT();
                } catch (IOException e) {
                    // Handle the exception
                    e.printStackTrace();
                }

                System.out.println("Launch solver on file");

                // Run the SMT solver on the file
                String responseSMT = executeSMTSolverOnFile();

                if (fileIsSatisfiable(responseSMT)) {
                    System.out.println("SAT solution found !");

                    System.out.println("Extract the hierarchy of the plan...\n");
                    SequentialPlan plan = extractPlanAndHierarchyFromSolver(responseSMT);

                    // Verify if the plan is valid
                    System.out.println("Check if plan is valid...");
                    boolean planIsValid;
                    try {
                        planIsValid = validatePlan(problem, plan);
                    } catch (IOException e) {
                        System.out.println("Failed to check if plan is valid !\n");
                        planIsValid = false;
                    }

                    if (planIsValid) {
                        System.out.println("Plan is valid !\n");
                    } else {
                        System.out.println("Plan is NOT valid !\n");
                    }

                    System.out.println("Finishing executing at layer: " + this.layer);

                    return;
                }
            }


            this.layer++;

            if (this.layer > layerMax) {
                layer--;
                break;
            }

            // Refine each method in all the flows
            System.out.println("Number flows before refining: " + this.paths.size());
            refineAllLiftedFlows();
            System.out.println("Number flows after refining: " + this.paths.size());

            // Remove all paths which are impossible
            // (e.g: Initial path with an action flow impossible)
            // or an flow which cannot be possible if a previous action flow is executed
            // cleanAllLiftedFlows();

            
        }

        System.out.println("Finishing executing at layer: " + this.layer);
    }

    private void refineAllLiftedFlows() {

        ArrayList<LiftedFlow> newPaths = new ArrayList<LiftedFlow>();
        ArrayList<LiftedFlow> newInitialPaths = new ArrayList<LiftedFlow>();

        Map<LiftedFlow, ArrayList<LiftedFlow>> dictMethodFlowToAllFirstChildrenFlows = new HashMap<LiftedFlow, ArrayList<LiftedFlow>>();

        // Iterate over all flows
        for (LiftedFlow flowParent : this.paths) {

            // We do not refine the action flow (it is already refined to maximum)
            if (!flowParent.isMethodLiftedFlow()) {
                newPaths.add(flowParent);
                if (flowParent.getPreviousesLiftedFlow().size() == 0) {
                    newInitialPaths.add(flowParent);
                }
                continue;
            }

            // Iterate over all children of the method of this flow
            String methodNameFlow = flowParent.getMethodName();

            System.out.println("Refine flow : " + flowParent);

            ParsedMethod liftedMethod = this.methodNameToObj.get(methodNameFlow);

            // We have a special case if this method has no children. We create an action
            // with no preconditions and no effects

            if (liftedMethod.getSubTasks().getChildren().size() == 0) {

                // Create the blank action
                LiftedFlow newFlowBlankAction = new LiftedFlow(true, flowParent, methodNameToObj, true, this.liftedFamGroups);
                for (LiftedFlow previousFlow : flowParent.getPreviousesLiftedFlow()) {
                    newFlowBlankAction.addPreviousesLiftedFlow(previousFlow);
                }
                for (LiftedFlow nextFlow : flowParent.getNextsLiftedFlow()) {
                    newFlowBlankAction.addNextLiftedFlow(nextFlow);
                }

                if (flowParent.getPreviousesLiftedFlow().size() == 0) {
                    newInitialPaths.add(newFlowBlankAction);
                }

                ArrayList<LiftedFlow> h = new ArrayList<>();
                h.add(newFlowBlankAction);

                dictMethodFlowToAllFirstChildrenFlows.put(flowParent, h);

                newPaths.add(newFlowBlankAction);

                System.out.println(newFlowBlankAction);
                System.out.println("===============");
                continue;
            }

            ArrayList<String> consecutiveActionsOfLiftedFlow = new ArrayList<String>();
            ArrayList<ArrayList<ScopeVariable>> consecutiveActionsOfLiftedFlowScope = new ArrayList<ArrayList<ScopeVariable>>();
            boolean lastSubTaskIsAction = false;
            ArrayList<LiftedFlow> previousLiftedFlows = new ArrayList<LiftedFlow>();
            ArrayList<LiftedFlow> newLiftedFlows = new ArrayList<LiftedFlow>();
            boolean firstNewLiftedFlow = true;
            boolean subTaskIsPrimitive = false;

            boolean actionIsFirstChildOfMethod = false;

            // Iterate over all subtasks of this method
            for (int idxSubtask = 0; idxSubtask < liftedMethod.getSubTasks().getChildren().size(); idxSubtask++) {

                Expression<String> subtask = liftedMethod.getSubTasks().getChildren().get(idxSubtask);
                // Check if the subtasks is an action (primitive task or another task)

                String subtaskName = subtask.getSymbol().getValue();

                subTaskIsPrimitive = this.actionNameToObj.keySet().contains(subtaskName);

                if (subTaskIsPrimitive) {
                    // This is an action. Get the action object associated with this
                    // Initialize the action with the correct scope
                    lastSubTaskIsAction = true;

                    if (idxSubtask == 0) {
                        actionIsFirstChildOfMethod = true;
                    }

                    // Find the scope of the action (two cases here:
                    // - first: it heritate its scope from a parent method (then we use the same
                    // scope as the parent method))
                    // - two: it is a constant variable (then we create a new scope with only the
                    // constant variable)
                    ArrayList<ScopeVariable> scopeAction = new ArrayList<>();
                    for (int argi = 0; argi < subtask.getArguments().size(); argi++) {
                        String nameArg = subtask.getArguments().get(argi).getValue();
                        try {
                            int idxArgOfMethod = Integer.parseInt(nameArg.substring(2));
                            scopeAction.add(flowParent.getScopeVariables().get(idxArgOfMethod));
                        } catch (Exception e) {
                            // Maybe it is a constant variable
                            // TODO create a scope variable for each constant to avoir duplicatas
                            // FOR NOW DO NOT DO IT
                            if (!this.dictConstantToScopeVariable.keySet().contains(nameArg)) {
                                System.out.println("STRANGE THINGS HERE...");
                                System.exit(1);
                            } else {
                                scopeAction.add(this.dictConstantToScopeVariable.get(nameArg));
                            }
                        }
                    }

                    consecutiveActionsOfLiftedFlow.add(subtaskName);
                    consecutiveActionsOfLiftedFlowScope.add(scopeAction);

                    if (!this.DEBUG_DO_NOT_MERGE_ACTION) {
                        if (idxSubtask != liftedMethod.getSubTasks().getChildren().size() - 1) {
                            continue;
                        }
                    }

                }

                if (lastSubTaskIsAction) {
                    // Create a new flow with all these actions in it
                    LiftedFlow flowAction = new LiftedFlow(consecutiveActionsOfLiftedFlow, flowParent,
                            consecutiveActionsOfLiftedFlowScope, actionNameToObj, methodNameToObj,
                            actionIsFirstChildOfMethod, this.liftedFamGroups);
                    consecutiveActionsOfLiftedFlow = new ArrayList<String>();
                    consecutiveActionsOfLiftedFlowScope = new ArrayList<ArrayList<ScopeVariable>>();
                    lastSubTaskIsAction = false;
                    newLiftedFlows.add(flowAction);
                    actionIsFirstChildOfMethod = false;
                }

                if (!subTaskIsPrimitive) {
                    // First, we need to know the scope of each argument of this subtask
                    ArrayList<ScopeVariable> scopeSubtask = new ArrayList<ScopeVariable>();
                    for (int argi = 0; argi < subtask.getArguments().size(); argi++) {
                        String nameArg = subtask.getArguments().get(argi).getValue();
                        try {
                            int idxArgOfMethod = Integer.parseInt(nameArg.substring(2));
                            scopeSubtask.add(flowParent.getScopeVariables().get(idxArgOfMethod));
                        } catch (Exception e) {
                            // Maybe it is a constant variable
                            // scopeSubtask.add(nameArg);
                            System.out.println("WE WILL SEE THAT LATER...");
                            System.exit(1);
                        }
                    }

                    // Now, we need to find all the methods which can solve this subtask
                    for (ParsedMethod subMethod : problem.getParsedProblem().getMethods()) {

                        String subMethodName = subMethod.getName().getValue();
                        ArrayList<ScopeVariable> scopeSubMethod = new ArrayList<ScopeVariable>();

                        // If this method cannot resolve this subtask, continue
                        if (!subMethod.getTask().getSymbol().getValue().equals(subtaskName)) {
                            continue;
                        }

                        // Here it where it is delicate, when this method use a parameter of the task
                        // parent, use the scope of the task
                        // parent. Else, initialize a new scope with all possible value in it (maybe it
                        // is not optimal, I don't know there)

                        // First, we need to know with which argument the parent method called the task

                        // Iterate over all argument of the subMethod
                        for (TypedSymbol<String> subMethodArg : subMethod.getParameters()) {
                            // Find if this is also a parameter of the parent task
                            String nameParameter = subMethodArg.getValue();
                            int idxArgOfMethod = Integer.parseInt(nameParameter.substring(2));

                            // Check if it is a parameter of the parent task
                            boolean isParameterOfParentTask = false;
                            for (int i_parentTaskParam = 0; i_parentTaskParam < subMethod.getTask().getArguments()
                                    .size(); i_parentTaskParam++) {
                                if (subMethod.getTask().getArguments().get(i_parentTaskParam).getValue()
                                        .equals(nameParameter)) {
                                    // Use the scope of the parent task
                                    scopeSubMethod.add(scopeSubtask.get(i_parentTaskParam));
                                    isParameterOfParentTask = true;
                                    break;
                                }
                            }

                            // Or if it is a new parameter introduced by the method
                            if (!isParameterOfParentTask) {
                                ScopeVariable scopeArg = new ScopeVariable();
                                this.scopeVarsToDefine.add(scopeArg);
                                // Get the type of the argument
                                String typeArg = subMethodArg.getTypes().get(0).getValue();
                                scopeArg.addTypeVariable(typeArg);
                                // Initialize the scope argument with all value of this type
                                for (String obj : dictTypeToObjects.get(typeArg)) {
                                    scopeArg.addValueToScope(obj);
                                }
                                for (String typeChild : dictTypeToChildTypes.get(typeArg)) {
                                    for (String obj : dictTypeToObjects.get(typeChild)) {
                                        scopeArg.addValueToScope(obj);
                                    }
                                }
                                scopeSubMethod.add(scopeArg);
                            }
                        }

                        boolean isFirstChildOfMethod = (idxSubtask == 0);

                        LiftedFlow flowMethod = new LiftedFlow(subMethodName, flowParent, 0, scopeSubMethod,
                                methodNameToObj, isFirstChildOfMethod, this.liftedFamGroups);
                        newLiftedFlows.add(flowMethod);
                    }
                }

                if (firstNewLiftedFlow) {
                    // HashSet<LiftedFlow> allChild
                    dictMethodFlowToAllFirstChildrenFlows.put(flowParent, newLiftedFlows);
                    // for (LiftedFlow newLiftedFlow : newLiftedFlows) {
                    // for (LiftedFlow previousLiftedFlowParentMethod :
                    // flowParent.getPreviousesLiftedFlow()) {
                    // newLiftedFlow.addNextLiftedFlow(previousLiftedFlowParentMethod);
                    // }
                    // }
                    firstNewLiftedFlow = false;
                }

                if (idxSubtask == liftedMethod.getSubTasks().getChildren().size() - 1) {
                    for (LiftedFlow newLiftedFlow : newLiftedFlows) {
                        for (LiftedFlow nextLiftedFlowParentMethod : flowParent.getNextsLiftedFlow()) {
                            newLiftedFlow.addNextLiftedFlow(nextLiftedFlowParentMethod);
                        }
                    }
                }

                // This flow method should follow the previous flow method
                for (LiftedFlow previousLiftedFlow : previousLiftedFlows) {
                    for (LiftedFlow nextLiftedFlow : newLiftedFlows) {
                        previousLiftedFlow.addNextLiftedFlow(nextLiftedFlow);
                        nextLiftedFlow.addPreviousesLiftedFlow(previousLiftedFlow);
                    }
                }

                // Add all newLiftedFlows to the path
                newPaths.addAll(newLiftedFlows);

                if (flowParent.getPreviousesLiftedFlow().size() == 0 && idxSubtask == 0) {
                    newInitialPaths.addAll(newLiftedFlows);
                }

                System.out.println("Subtask: " + idxSubtask + " ");
                for (LiftedFlow newLiftedFlow : newLiftedFlows) {
                    System.out.println(newLiftedFlow);
                }
                System.out.println("===============");

                previousLiftedFlows = newLiftedFlows;
                newLiftedFlows = new ArrayList<LiftedFlow>();
            }

            int a = 0;
        }

        // Not optimal at all, but since we are lifted, we do not care ?
        for (LiftedFlow newLiftedFlow : newPaths) {
            for (LiftedFlow oldParentFlow : dictMethodFlowToAllFirstChildrenFlows.keySet()) {
                if (newLiftedFlow.getPreviousesLiftedFlow().contains(oldParentFlow)) {
                    newLiftedFlow.getPreviousesLiftedFlow().remove(oldParentFlow);
                }
                if (newLiftedFlow.getNextsLiftedFlow().contains(oldParentFlow)) {
                    newLiftedFlow.getNextsLiftedFlow().remove(oldParentFlow);
                    newLiftedFlow.getNextsLiftedFlow().addAll(dictMethodFlowToAllFirstChildrenFlows.get(oldParentFlow));
                    for (LiftedFlow firstChildrenNextFlow : dictMethodFlowToAllFirstChildrenFlows.get(oldParentFlow)) {
                        firstChildrenNextFlow.getPreviousesLiftedFlow().add(newLiftedFlow);
                    }
                }
            }
        }

        // TODO it seems that I have a bug where the previous flow are not always
        // recorded. I do
        // an ugly fix here, but I have to correct this...
        for (LiftedFlow newLiftedFlow : newPaths) {
            for (LiftedFlow nextFlow : newLiftedFlow.getNextsLiftedFlow()) {
                nextFlow.getPreviousesLiftedFlow().add(newLiftedFlow);
            }
        }

        this.paths = newPaths;
        this.initialPaths = newInitialPaths;

        // SOME DEBUG INFORMATION
        for (LiftedFlow flow : this.paths) {
            System.out.println(flow.getUniqueName());
            System.out.print("  Previous flows: ");
            for (LiftedFlow previousFlow : flow.getPreviousesLiftedFlow()) {
                System.out.print(previousFlow.getUniqueName() + " ");
            }
            System.out.print("\n  Next flows: ");
            for (LiftedFlow nextFlow : flow.getNextsLiftedFlow()) {
                System.out.print(nextFlow.getUniqueName() + " ");
            }
            System.out.println("\n");
            int a = 0;
        }
        int b= 0;
    }

    /**
     * Returns true if the given response of the SMT solver indicates that the SMT
     * file is satisfiable, false otherwise.
     *
     * @param response the response of the SMT solver
     * @return true if the SMT file is satisfiable, false otherwise
     */
    private Boolean fileIsSatisfiable(String responseSolverSMT) {
        return !responseSolverSMT.contains("unsat");
    }

    /**
     * Executes the SMT solver on the SMT file and returns the response as a string.
     *
     * @return the response of the SMT solver as a string
     */
    String executeSMTSolverOnFile() {
        String outputSMTSolver = "";
        // Path executablePath = Paths.get("app", "solverBinary", "cvc5").toAbsolutePath();
        // String executableSolverSMT = executablePath.toString();
        String executableSolverSMT = "/home/gaspard/LIG/Code/lifted_tree_path/app/solverBinary/cvc5";
        String command = executableSolverSMT + " " + this.filenameSMT + " --lang smt";
        // String command = "z3 " + this.filenameSMT;
        try {
            Process p = Runtime.getRuntime().exec(command);
            BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()));
            String newLine = "";

            while ((newLine = reader.readLine()) != null) {
                outputSMTSolver += newLine + "\n";
            }
            p.waitFor();
        } catch (IOException | InterruptedException e1) {
            e1.printStackTrace();
        }
        return outputSMTSolver;
    }

    SequentialPlan extractPlanAndHierarchyFromSolver(String outputSMTSolver) {

        int a = 0;

        String[] outputLines = outputSMTSolver.split("\n");

        List<String> actionsInPlan = Arrays.asList(outputLines);
        List<String> scopeVarActions = Arrays.asList(outputLines);

        // First, extract all the actions which are true
        actionsInPlan = Arrays.asList(actionsInPlan.stream().filter(s -> (s.contains("FLOW_") && s.contains(" true)")))
                .toArray(String[]::new));
        // scopeVarActions = Arrays
                // .asList(scopeVarActions.stream().filter(s -> s.contains("SCOPE_")).toArray(String[]::new));

        scopeVarActions = Arrays
                .asList(scopeVarActions.stream().filter(s -> s.contains("true")).filter(s -> s.split(" ")[1].startsWith("SCOPE_")).toArray(String[]::new));

        // Get the objects associated with each action
        List<LiftedFlow> actionsObjInPlan = new ArrayList<LiftedFlow>();

        for (String actionInPlan : actionsInPlan) {
            for (LiftedFlow actionObj : this.primitiveTree.getNodes()) {
                String actionName = actionObj.getUniqueName();

                if (actionInPlan.contains(actionName)) {
                    actionsObjInPlan.add(actionObj);
                }
            }
        }

        SequentialPlan p = new SequentialPlan();
        Hierarchy hierarchy = new Hierarchy();

        // Add the roots tasks to the hierarchy
        int numberRootTasks = problem.getInitialTaskNetwork().getTasks().size();
        for (int rootTaskIdx = 0; rootTaskIdx < numberRootTasks; rootTaskIdx++) {
            hierarchy.getRootTasks().add(rootTaskIdx);
            hierarchy.getDecomposition().put(rootTaskIdx, new ArrayList<>());
        }

        System.out.println("==============");
        for (LiftedFlow actionObjInPlan : actionsObjInPlan) {
            System.out.println(actionObjInPlan.getUniqueName());
        }
        System.out.println("==============");
        // take the first action executed
        for (LiftedFlow actionObjInPlan : actionsObjInPlan) {

            int sizeRootFromAction = 0;
            // Get the parent of the action
            LiftedFlow node = actionObjInPlan;
            while (node.getParentFlow() != null) {
                sizeRootFromAction++;
                node = node.getParentFlow();
            }

            int parentMethodId = -1;

            for (int i = sizeRootFromAction; i >= 0; i--) {

                // Get the method of this layer
                node = actionObjInPlan;
                for (int j = 0; j < i; j++) {
                    node = node.getParentFlow();
                }

                if (i == 0 && node.getUniqueName().contains("FLOW_BLANK")) {
                    continue;
                }

                ArrayList<String> argsMethod = new ArrayList<>();

                ArrayList<ScopeVariable> scopesVariableMethod = new ArrayList<>();

                // If this is an action
                if (i == 0) {

                    ArrayList<ArrayList<ScopeVariable>> scopesVariableAction = node.getScopeVariablesActionsFlow();

                    ArrayList<ArrayList<String>> argsAction = new ArrayList<ArrayList<String>>();

                    // Find the value of each scope variable of each action

                    for (int actionIdx = 0; actionIdx < scopesVariableAction.size(); actionIdx++) {

                        argsAction.add(new ArrayList<>());

                        ArrayList<ScopeVariable> scopeVariableAction = scopesVariableAction.get(actionIdx);

                        for (ScopeVariable scopeVariable : scopeVariableAction) {

                            if (scopeVariable.getPossibleValueVariable().size() == 1) {
                                argsAction.get(actionIdx)
                                        .add(scopeVariable.getPossibleValueVariable().iterator().next());
                                continue;
                            }
                            String nameScopeVariable = scopeVariable.getUniqueName();
                            // Get the value from the SMT file
                            for (String scopeVar : scopeVarActions) {
                                // String scopeVarExactName = scopeVar.split(" ")[1];
                                String scopeVarExactName = scopeVar.split(" ")[1].split("__")[0];
                                if (scopeVarExactName.equals(nameScopeVariable)) {
                                    // Extract the value
                                    // String[] split = scopeVar.split(" ");
                                    // String value = split[split.length - 1].substring(0,
                                    //         split[split.length - 1].length() - 1);

                                    // String objAssociated = null;
                                    // Integer valueInt = Integer.parseInt(value);
                                    // for (String objName : this.objNameToUniqueId.keySet()) {
                                    //     if (this.objNameToUniqueId.get(objName) == valueInt) {
                                    //         objAssociated = objName;
                                    //         break;
                                    //     }
                                    // }
                                    String objAssociated = scopeVar.split(" ")[1].split("__")[1];
                                    argsAction.get(actionIdx).add(objAssociated);
                                    break;
                                }
                            }
                        }
                    }

                    for (int actionIdx = 0; actionIdx < node.getMacroAction().size(); actionIdx++) {

                        String nameAction = node.getMacroAction().get(actionIdx);
                        boolean actionIsFound = false;
                        for (Action groundAction : problem.getActions()) {

                            if (!groundAction.getName().equals(nameAction)) {
                                continue;
                            }

                            // System.out.println(argMethod);
                            // System.out.println(prettyDisplayMethod(groundMethod, problem));

                            boolean isCorrectAction = true;
                            for (int argi = 0; argi < groundAction.getInstantiations().length; argi++) {
                                if (!problem.getConstantSymbols().get(groundAction.getInstantiations()[argi])
                                        .equals(argsAction.get(actionIdx).get(argi))) {
                                    isCorrectAction = false;
                                    break;
                                }
                            }

                            if (isCorrectAction) {

                                // Add it into our hierarchy if it not already there
                                // int actionId = this.problem.getActions().indexOf(groundAction);
                                int actionId = node.uniqueId + actionIdx;
                                hierarchy.getPrimtiveTasks().put(actionId, groundAction);

                                // Add this method as the child of the parent method
                                if (parentMethodId != -1) {
                                    hierarchy.getDecomposition().get(parentMethodId).add(actionId);
                                }

                                actionIsFound = true;
                                break;
                            }
                        }
                        if (!actionIsFound) {
                            System.out.println("WHAT !!");
                        }
                    }

                }
                // If this is a method
                else {
                    scopesVariableMethod = node.getScopeVariables();

                    // Find all value of the scope of this method/action
                    for (ScopeVariable scopeVariable : scopesVariableMethod) {

                        if (scopeVariable.getPossibleValueVariable().size() == 1) {
                            argsMethod.add(scopeVariable.getPossibleValueVariable().iterator().next());
                            continue;
                        }
                        String nameScopeVariable = scopeVariable.getUniqueName();
                        // Get the value from the SMT file
                        for (String scopeVar : scopeVarActions) {
                            // String scopeVarExactName = scopeVar.split(" ")[1];
                            // if (scopeVarExactName.equals(nameScopeVariable)) {
                            //     // Extract the value
                            //     String[] split = scopeVar.split(" ");
                            //     String value = split[split.length - 1].substring(0,
                            //             split[split.length - 1].length() - 1);

                            //     String objAssociated = null;
                            //     Integer valueInt = Integer.parseInt(value);
                            //     for (String objName : this.objNameToUniqueId.keySet()) {
                            //         if (this.objNameToUniqueId.get(objName) == valueInt) {
                            //             objAssociated = objName;
                            //             break;
                            //         }
                            //     }
                            //     argsMethod.add(objAssociated);
                            //     int b = 0;
                            // }
                            String scopeVarExactName = scopeVar.split(" ")[1].split("__")[0];
                            if (scopeVarExactName.equals(nameScopeVariable)) {
                                String objAssociated = scopeVar.split(" ")[1].split("__")[1];
                                argsMethod.add(objAssociated);
                                break;
                            }
                        }
                    }

                    // Find the ground method associated with this method and argument
                    String nameMethod = node.getMethodName();

                    for (Method groundMethod : problem.getMethods()) {

                        if (!groundMethod.getName().equals(nameMethod)) {
                            continue;
                        }

                        // System.out.println(argMethod);
                        // System.out.println(prettyDisplayMethod(groundMethod, problem));

                        boolean isCorrectMethod = true;
                        for (int argi = 0; argi < groundMethod.getInstantiations().length; argi++) {
                            if (!problem.getConstantSymbols().get(groundMethod.getInstantiations()[argi])
                                    .equals(argsMethod.get(argi))) {
                                isCorrectMethod = false;
                                break;
                            }
                        }

                        if (isCorrectMethod) {

                            // Add it into our hierarchy if it not already there
                            // int methodId = this.problem.getMethods().indexOf(groundMethod);
                            int methodId = node.uniqueId;
                            if (!hierarchy.getCounpoudTasks().keySet().contains(methodId)) {
                                hierarchy.getCounpoudTasks().put(methodId, groundMethod);
                                hierarchy.getDecomposition().put(methodId, new ArrayList<>());
                            }

                            // Add this method as the child of the parent method
                            if (parentMethodId != -1
                                    && !hierarchy.getDecomposition().get(parentMethodId).contains(methodId)) {
                                hierarchy.getDecomposition().get(parentMethodId).add(methodId);
                            }

                            parentMethodId = methodId;
                            break;
                        }
                    }
                }
                a = 0;
            }
        }

        // Create the sequential plan
        int timeStep = 0;
        for (Action action : hierarchy.getPrimtiveTasks().values()) {
            p.add(timeStep, action);
            timeStep++;
        }

        System.out.println(problem.toString(hierarchy));
        p.setHierarchy(hierarchy);

        return p;
    }

    /**
     * Validates a given plan by writing the plan's hierarchy to a file and
     * executing a command to verify the plan.
     * If the plan is valid, the function returns true. If the plan is invalid or if
     * there is an error in executing
     * the command, the function returns false.
     *
     * @param problem the problem for which the plan is being validated
     * @param plan    the plan to validate
     * @return true if the plan is valid, false otherwise
     * @throws IOException if there is an error in writing to the file or executing
     *                     the command
     */
    public boolean validatePlan(Problem problem, Plan plan) throws IOException {
        // Create a temporary file to store the hierarchy of the plan
        File planFile = File.createTempFile("tmp_plan", ".txt");

        // Write the hierarchy of the plan to the file
        try (BufferedWriter writer = new BufferedWriter(new FileWriter(planFile))) {
            writer.write(problem.toString(plan.getHierarchy()));
        }

        // Construct the command to verify the plan
        String command = String.format("./%s --verify %s %s %s -l", this.path_exec_VAL, this.domainPath,
                this.problemPath, planFile.getAbsolutePath()); // -l to be case insensitive

        System.out.println(command);

        // Execute the command and store the output
        String output = executeCommand(command);

        // Split the output into separate lines
        String[] lines = output.split("\n");

        // Get the last line of the output
        String lastLine = lines[lines.length - 1];

        // Check if the last line contains the string "Plan verification result"
        if (!lastLine.contains("Plan verification result")) {
            // If the last line does not contain the string "Plan verification result", log
            // an error and return false
            System.out.println("Cannot verify the plan given. Output returned by executable: \n" + output);
            return false;
        }
        // If the last line contains the string "Plan verification result", return true
        // if the last line also contains the string "true"
        return lastLine.contains("true");
    }

    /**
     * Executes a command and returns the output as a string.
     *
     * @param command the command to execute
     * @return the output of the command as a string
     * @throws IOException if there is an error in executing the command
     */
    private String executeCommand(String command) throws IOException {
        StringBuilder output = new StringBuilder();
        Process p = Runtime.getRuntime().exec(command);
        try (BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()))) {
            String line;
            while ((line = reader.readLine()) != null) {
                output.append(line).append("\n");
            }
        }
        return output.toString();
    }

    /**
     * Return a string containing a method in easily readable format
     * 
     * @param a       The method to display in easily readable format
     * @param problem The problem to solve
     * @return A String representing the action in easily readable format
     */
    public String prettyDisplayMethod(Method m, Problem problem) {
        StringBuilder methodToDisplay = new StringBuilder();

        // Add the fluent name (e.g "at" for the fluent at ?r - robot ?l - location)
        methodToDisplay.append("METHOD_" + m.getName());

        // Then, for each argument of this fluent, add the argument into the string
        for (int methodArg : m.getInstantiations()) {
            methodToDisplay.append("_" + problem.getConstantSymbols().get(methodArg));
        }

        return methodToDisplay.toString();
    }

    private void encodeSAT() throws IOException {

        // So what do we have to encode

        StringBuilder allClauses = new StringBuilder();
        allClauses.append("(set-logic QF_UFLIA)\n");
        allClauses.append("(set-option :produce-models true)\n");

        // Encode all objects
        // allClauses.append("; Declare all of our objects and assign value to them\n");
        // allClauses.append(encodeDeclarationAllObjectsSAT());

        // Then declare all of the initial predicates
        // allClauses.append("; Declare all of our predciates initial values\n");
        // allClauses.append(encodeDeclarationAllPredicateSAT());
        allClauses.append("; Declare all the ground predicates\n");
        allClauses.append(encodeDeclarationAllPredicateSAT2());

        if (LiftedTreePathConfig.useSASPlusEncoding) {
            allClauses.append("; Declare all of our cliques bits\n");
            allClauses.append(encodeDeclarationAllCliqueBitsSAT());
        }

        // Then declare all of our flow actions
        allClauses.append("; declare all macro actions\n");
        allClauses.append(encodeDeclarationAllMacroActionsSAT());

        // Then declare the all the variables scope (only the scope that can be taken by
        // the flows that will be encoded)
        allClauses.append("; declare all of our macro actions variable scope\n");
        allClauses.append(encodeDeclarationScopeVariablesSAT());

        // Then declare all of the possible flows path
        allClauses.append("; Declare all the macro actions paths\n");
        allClauses.append(declareAllMacroActionsPaths());

        // Declare all the substitution of a pseudo fact to a ground fact
        allClauses.append("; Declare all the substitution of a pseudo fact to a ground fact\n");
        allClauses.append(declareAllSubstitutionOfPseudoFactToGroundFact());

        // Then set the value for the initial predicates
        allClauses.append("; Initial values predicates: \n");
        allClauses.append(encodeSetInitialValueAllPredicateSAT());

        // Add all the constrains on the scopes
        // allClauses.append("; Constrains on scopes\n");
        // allClauses.append(declaratationAllConstrainsOnScope());

        // Then, for each flows, indicate where it can take its precondition (either a
        // previous flow can satisfied it or it can take it from the initial predicate)

        int currentTimeStep = 0;

        allClauses.append("; For time step " + currentTimeStep + "\n");
        for (LiftedFlow node : this.primitiveTree.getNodes()) {
            
            if (node.getMaxStepFromRootNode() > currentTimeStep) {
                allClauses.append("; For time step " + (currentTimeStep + 1) + "\n");

                // Define the rule13 for this time step
                // allClauses.append("; Rule 13\n");
                // allClauses.append(this.rule13PerTimeStep.get(currentTimeStep));

                // Define the frame axioms for this time step
                allClauses.append("; Frame axioms\n");
                allClauses.append(this.frameAxiomsAndEffsPerTimeStep.get(currentTimeStep));

                currentTimeStep = node.getMaxStepFromRootNode();
            }

            // Define the precondition of the node
            allClauses.append("; Precondition of " + node.getUniqueName() + "\n");
            allClauses.append(node.preconditionsSMT);

            // Define the effects of the node
            allClauses.append("; Effects of " + node.getUniqueName() + "\n");
            allClauses.append(node.effectsSMT);
        }

        // Declare the goal state (if there is one)
        if (this.fluentsIdTrueGoal.size() > 0 || this.fluentsIdFalseGoal.size() > 0) {
            allClauses.append("; Declare the goal state\n");
            allClauses.append(encodeDeclarationGoalStateSAT());
        }

        allClauses.append("(check-sat)\n");
        allClauses.append("(get-model)\n");
        allClauses.append("(exit)\n");
        // Should be about it.

        BufferedWriter writer = new BufferedWriter(new FileWriter(this.filenameSMT));
        writer.write(allClauses.toString());
        writer.flush();
        writer.close();

        int a = 0;
    }

    private String encodeSetInitialValueAllPredicateSAT() {
        StringBuilder initialPredicates = new StringBuilder();

        if (LiftedTreePathConfig.useSASPlusEncoding) {

            for (Integer fluentIdTrueInit : this.fluentsIdTrueInit) {

                // Check if this fluent is into one or multiple clique
                SASPredicate predicate = UtilsStructureProblem.predicatesSAS[fluentIdTrueInit];
                if (predicate == null) {
                    System.out.println("PROBLEM HERE !");
                    System.exit(1);
                }
                initialPredicates.append("; define " + predicate.getFullName() + "\n");

                if (predicate.getCliques().size() == 0) {
                    // We will treat this predicate as a normal predicate
                    String predicateFullNameAndTImeStep = predicate.getFullName() + "__0";
                    if (!this.groundFactsToDefine.contains(predicateFullNameAndTImeStep)) {
                        initialPredicates.append("(declare-const " + predicate.getFullName() + "__0 Bool)\n");
                    }
                    initialPredicates.append("(assert (= " + predicate.getFullName() + "__0 true))\n");
                }

                // Iterate over all the clique that this predicate is into
                for (int cliqueIdx = 0; cliqueIdx < predicate.getCliques().size(); cliqueIdx++) {

                    // Get the clique
                    Clique clique = predicate.getCliques().get(cliqueIdx);

                    // Get the clique ID
                    int cliqueId = clique.id;

                    // Check that this clique is defined somewhere. If it not the case, there is no need to encode the initial value of the clique
                    String bit0Clique = "Clique_" + cliqueId + "_bit0__0";

                    if (!this.cliqueBitsToDefine.contains(bit0Clique)) {
                        continue;
                    }

                    // Get the number of variables in this clique
                    int nbVariablesInClique = clique.numberValues;

                    // Get the value of the predicate in this clique
                    int valueInClique = predicate.getValuesPredInClique().get(cliqueIdx);

                    // With the number of variable into the clique and the specific value of the predicate in this clique, 
                    // We can get the binary representation of the value of the predicate in this clique
                    String binaryValue = UtilsStructureProblem.getBinaryValueInSMTFormat(cliqueId, valueInClique, nbVariablesInClique, 0);
                    initialPredicates.append(binaryValue);
                }
            }
            for (Integer fluentIdFalseInit : this.fluentsIdFalseInit) {
                // Check if this fluent is into one or multiple clique
                SASPredicate predicate = UtilsStructureProblem.predicatesSAS[fluentIdFalseInit];
                if (predicate == null) {
                    System.out.println("PROBLEM HERE !");
                    System.exit(1);
                }
                if (predicate.getCliques().size() == 0) {
                    // We will treat this predicate as a normal predicate
                    String predicateFullNameAndTImeStep = predicate.getFullName() + "__0";
                    if (!this.groundFactsToDefine.contains(predicateFullNameAndTImeStep)) {
                        initialPredicates.append("(declare-const " + predicate.getFullName() + "__0 Bool)\n");
                    }
                    initialPredicates.append("(assert (= " + predicate.getFullName() + "__0 false))\n");
                }
            }   
        } else {
            for (String groundFluent : this.fluentsTrueInit) {
                initialPredicates.append("(assert (= " + groundFluent + " true))\n");
            }
            for (String groundFluent : this.fluentsFalseInit) {
                initialPredicates.append("(assert (= " + groundFluent + " false))\n");
            }
        }
        return initialPredicates.toString();
    }

    private String encodeDeclarationGoalStateSAT() {
        StringBuilder goalPredicates = new StringBuilder();

        // Iterate over all the positive goal predicates
        for (Integer posPredicateId : this.fluentsIdTrueGoal) {

            SASPredicate predicate = UtilsStructureProblem.predicatesSAS[posPredicateId];

            // Get the last time that this predicate has been defined
            int lastTimeStep = predicate.getLastTimePredicateWasDefined();

            // Write the predicate
            goalPredicates.append("(assert (= " + predicate.getFullName() + "__" + lastTimeStep + " true))\n");
        }

        // Iterate over all the negative goal predicates
        for (Integer negPredicateId : this.fluentsIdFalseGoal) {

            SASPredicate predicate = UtilsStructureProblem.predicatesSAS[negPredicateId];

            // Get the last time that this predicate has been defined
            int lastTimeStep = predicate.getLastTimePredicateWasDefined();

            // Write the predicate
            goalPredicates.append("(assert (= " + predicate.getFullName() + "__" + lastTimeStep + " false))\n");
        }

        return goalPredicates.toString();
    }

    private String declareAllSubstitutionOfPseudoFactToGroundFact() {
        StringBuilder substitutionPseudoFactToGroundFact = new StringBuilder();

        // Iterate over all the pseudo facts
        // TODO finish here
        for (String consersionPseudoFactToGroundFact : this.rule13PerTimeStep) {
            substitutionPseudoFactToGroundFact.append(consersionPseudoFactToGroundFact);
        }

        return substitutionPseudoFactToGroundFact.toString();
    }

    private String encodeDeclarationAllObjectsSAT() {
        StringBuilder declarationObjects = new StringBuilder();

        for (String typeName : this.dictTypeToObjects.keySet()) {
            Vector<String> allObjsOfType = this.dictTypeToObjects.get(typeName);
            for (int i = 0; i < allObjsOfType.size(); i++) {
                declarationObjects.append("(declare-const " + allObjsOfType.get(i) + " Int)\n");
            }
            // Just use a second loop because it is more estetic on the SMT file generated
            // with this way
            for (int i = 0; i < allObjsOfType.size(); i++) {
                declarationObjects.append("(assert (= " + allObjsOfType.get(i) + " "
                        + this.objNameToUniqueId.get(allObjsOfType.get(i)) + "))\n");
            }
        }
        return declarationObjects.toString();
    }


    private String encodeDeclarationAllPredicateSAT2() {
        StringBuilder declarationPredicates = new StringBuilder();

        // for (HashSet<String> groundPredicatesPerTimeStep : this.groundPredicatesToDefinePerTimeStep) {
        //     for (String groundPredicate : groundPredicatesPerTimeStep) {
        //         declarationPredicates.append("(declare-const " + groundPredicate + " Bool)\n");
        //     } 
        // }
        for (String groundPredicate : this.groundFactsToDefine) {
            declarationPredicates.append("(declare-const " + groundPredicate + " Bool)\n");
        }

        // Declare has well all the pseudo predicates
        declarationPredicates.append("; Declare all the pseudo predicates\n");
        // for (int timeStep = 0; timeStep < this.pseudoFactsToDefinePerTimeStep.size(); timeStep++) {
        //     for (CertifiedPredicate pseudoFact : this.pseudoFactsToDefinePerTimeStep.get(timeStep)) {
        //         declarationPredicates.append("(declare-const " + pseudoFact.toSmt(timeStep) + " Bool)\n");
        //     }
        // }

        if (LiftedTreePathConfig.DEBUG) {
            // Sort our pseudo facts by time step to be more readable (pseudo fact is in form name__timeStep)
            HashSet<String> allPseudoFacts = this.pseudoFactsToDefine;
            ArrayList<String> allPseudoFactsSorted = new ArrayList<>();
            allPseudoFactsSorted.addAll(allPseudoFacts);
            // Sort by time step

            Collections.sort(allPseudoFactsSorted, new Comparator<String>() {
                @Override
                public int compare(String o1, String o2) {
                    String[] o1Split = o1.split("__");
                    String[] o2Split = o2.split("__");
                    int o1TimeStep = Integer.parseInt(o1Split[o1Split.length - 1]);
                    int o2TimeStep = Integer.parseInt(o2Split[o2Split.length - 1]);
                    return o1TimeStep - o2TimeStep;
                }
            });
            
            for (String pseudoFact : allPseudoFactsSorted) {
                declarationPredicates.append("(declare-const " + pseudoFact + " Bool)\n");
            }
        } else {
            for (String pseudoFact : this.pseudoFactsToDefine) {
                declarationPredicates.append("(declare-const " + pseudoFact + " Bool)\n");
            }
        }

        return declarationPredicates.toString();
    }

    private String encodeDeclarationAllCliqueBitsSAT() {
        StringBuilder declarationCliqueBits = new StringBuilder();

        for (String cliqueBit : this.cliqueBitsToDefine) {
            declarationCliqueBits.append("(declare-const " + cliqueBit + " Bool)\n");
        }

        return declarationCliqueBits.toString();
    }

    private String encodeDeclarationAllPredicateSAT() {
        StringBuilder declarationPredicates = new StringBuilder();

        Map<String, Vector<ArrayList<String>>> dictPredicateNameToArgForTrueValue = new HashMap();

        Map<String, Integer> dictPredicateNameToNumArgs = new HashMap<>();

        // Put all the predicate
        for (NamedTypedList pred : problem.getParsedProblem().getPredicates()) {
            String predicateName = pred.getName().getValue();
            int numArgs = pred.getArguments().size();
            dictPredicateNameToArgForTrueValue.put(predicateName, new Vector<ArrayList<String>>());
            dictPredicateNameToNumArgs.put(predicateName, numArgs);
        }

        for (int i = 0; i < this.problem.getFluents().size(); i++) {
            if (this.problem.getInitialState().getPositiveFluents().get(i)) {
                Fluent f = this.problem.getFluents().get(i);
                String predicateName = problem.getPredicateSymbols().get(f.getSymbol());

                // if (!dictPredicateNameToArgForTrueValue.keySet().contains(predicateName)) {
                // dictPredicateNameToArgForTrueValue.put(predicateName, new
                // Vector<ArrayList<String>>());
                // }

                ArrayList<String> args = new ArrayList<String>();
                for (int argi = 0; argi < f.getArguments().length; argi++) {
                    args.add(problem.getConstantSymbols().get(f.getArguments()[argi]));
                }
                dictPredicateNameToArgForTrueValue.get(predicateName).add(args);
            }
        }

        // Now, we can declare all of our predicate
        for (String predicateName : dictPredicateNameToArgForTrueValue.keySet()) {

            Vector<ArrayList<String>> args = dictPredicateNameToArgForTrueValue.get(predicateName);
            int numArgsPredicate = dictPredicateNameToNumArgs.get(predicateName);

            // int numArgsPredicate = 0;
            // if (args.size() > 0) {
            // numArgsPredicate = args.get(0).size();
            // }
            declarationPredicates.append("(define-fun " + predicateName + "__0 ( ");
            for (int i = 0; i < numArgsPredicate; i++) {
                declarationPredicates.append("(x!" + i + " Int) ");
            }
            declarationPredicates.append(") Bool\n");
            declarationPredicates.append("(ite (or\n");
            if (args.size() == 0) {
                declarationPredicates.append("false\n");
            } else {
                for (ArrayList<String> larg : args) {
                    declarationPredicates.append("  (and ");
                    for (int i = 0; i < numArgsPredicate; i++) {
                        declarationPredicates.append("(= x!" + i + " " + larg.get(i) + ") ");
                    }
                    declarationPredicates.append(")\n");
                }
            }

            declarationPredicates.append(") true false\n");
            declarationPredicates.append("))\n");
        }

        // Declare as well all the predicate that are not in the initial state
        for (String predicateToDefine : this.predicatesToDefine) {
            declarationPredicates.append(predicateToDefine);
        }

        return declarationPredicates.toString();
    }

  

    private String encodeDeclarationAllMacroActionsSAT() {
        StringBuilder declarationMacroActions = new StringBuilder();

        // Stack<Integer> topologicalSortTree = this.primitiveTree.getTopologicalSort();

        // Consume all the node of the topological sort tree
        for (LiftedFlow node : this.primitiveTree.getNodesInTopologicalOrder()) {

            declarationMacroActions.append("; " + node + "\n");

            declarationMacroActions.append("(declare-const " +
                    node.getUniqueName() + " Bool)\n");

        }

        return declarationMacroActions.toString();
    }

    private String declareAllMacroActionsPaths() {

        StringBuilder allMacroActionsPath = new StringBuilder();

        // I've come up with an algo for that, but I do not know if it is the most
        // optimal
        // Iterate over our primitive tree in a topological way

        // Map<Integer, String> flowToFormula = new HashMap<Integer, String>();
        String[] flowToFormula = new String[this.primitiveTree.getNodes().size()];
        HashSet<String> fullFormula = new HashSet<String>();
        ArrayList<ArrayList<LiftedFlow>> allConcurrentsActions = new ArrayList<>();
        int[] dictNodeToIdxConcurrentActions = new int[this.primitiveTree.getNodes().size()];
        for (int i = 0; i < this.primitiveTree.getNodes().size(); i++) {
            dictNodeToIdxConcurrentActions[i] = -1;
        }

        // Consume all the node of the topological sort tree
        for (LiftedFlow node : this.primitiveTree.getNodesInTopologicalOrder()) {

            Integer idxNode = this.primitiveTree.getNodes().indexOf(node);


            // Add all concurrent actions in the at most list
            if (this.primitiveTree.getChildrenNodesIdx().get(idxNode).size() > 1) {
                // Check if those children are already in a HashSet
                int idxMutexAction = -1;
                for (Integer idxChild : this.primitiveTree.getChildrenNodesIdx().get(idxNode)) {
                    if (dictNodeToIdxConcurrentActions[idxChild] != -1) {
                        idxMutexAction = dictNodeToIdxConcurrentActions[idxChild];
                        break;
                    }
                }
                if (idxMutexAction == -1) {
                    allConcurrentsActions.add(new ArrayList<>());
                    idxMutexAction = allConcurrentsActions.size() - 1;
                }
                for (Integer idxChild : this.primitiveTree.getChildrenNodesIdx().get(idxNode)) {
                    if (!allConcurrentsActions.get(idxMutexAction).contains(this.primitiveTree.getNodes().get(idxChild))) {
                        allConcurrentsActions.get(idxMutexAction).add(this.primitiveTree.getNodes().get(idxChild));
                        dictNodeToIdxConcurrentActions[idxChild] = idxMutexAction;
                    }
                }
            }
            if (this.primitiveTree.getParentsNodesIdx().get(idxNode).size() > 1) {
                // Check if those children are already in a HashSet
                int idxMutexAction = -1;
                for (Integer idxParent : this.primitiveTree.getParentsNodesIdx().get(idxNode)) {
                    if (dictNodeToIdxConcurrentActions[idxParent] != -1) {
                        idxMutexAction = dictNodeToIdxConcurrentActions[idxParent];
                        break;
                    }
                }
                if (idxMutexAction == -1) {
                    allConcurrentsActions.add(new ArrayList<>());
                    idxMutexAction = allConcurrentsActions.size() - 1;
                }
                for (Integer idxParent : this.primitiveTree.getParentsNodesIdx().get(idxNode)) {
                    if (!allConcurrentsActions.get(idxMutexAction).contains(this.primitiveTree.getNodes().get(idxParent))) {
                        allConcurrentsActions.get(idxMutexAction).add(this.primitiveTree.getNodes().get(idxParent));
                        dictNodeToIdxConcurrentActions[idxParent] = idxMutexAction;
                    }

                }
            }
        }

        // allMacroActionsPath.append("(assert (or\n");
        // for (String path : fullFormula) {
        // allMacroActionsPath.append(path + " \n");
        // }
        // allMacroActionsPath.append("))\n");

        // One of the root action should be true
        allMacroActionsPath.append("; one of the root action should be true\n");
        allMacroActionsPath.append("(assert (or ");
        for (Integer rootNode : this.primitiveTree.getRootNodesIdx()) {
            allMacroActionsPath.append(this.primitiveTree.getNodes().get(rootNode).getUniqueName() + " ");
        }
        allMacroActionsPath.append("))\n");

        allMacroActionsPath.append("; action true => one of its child action is true\n");
        // Consume all the node of the topological sort tree
        for (LiftedFlow node : this.primitiveTree.getNodesInTopologicalOrder()) {
            Integer idxNode = this.primitiveTree.getNodes().indexOf(node);
            HashSet<Integer> childrenNode = this.primitiveTree.getChildrenNodesIdx().get(idxNode);

            if (childrenNode.size() == 0) {
                continue;
            }

            else if (childrenNode.size() == 1) {
                LiftedFlow childNode = this.primitiveTree.getNodes().get(childrenNode.iterator().next());
                allMacroActionsPath
                        .append("(assert (=> " + node.getUniqueName() + " " + childNode.getUniqueName() + "))\n");
            }

            else {
                allMacroActionsPath.append("(assert (=> " + node.getUniqueName() + " (or ");
                for (Integer idxChild : this.primitiveTree.getChildrenNodesIdx().get(idxNode)) {
                    allMacroActionsPath.append(this.primitiveTree.getNodes().get(idxChild).getUniqueName() + " ");
                }
                allMacroActionsPath.append(")))\n");
            }
        }

        // Add as well the at most one action for all concurrents actions
        allMacroActionsPath.append("; at most one action\n");
        HashSet<String> pairAlreadySeen = new HashSet<String>();
        // Consume all the node of the topological sort tree
        for (LiftedFlow node : this.primitiveTree.getNodesInTopologicalOrder()) {
            Integer idxNode = this.primitiveTree.getNodes().indexOf(node);

            if (this.primitiveTree.getParentsNodesIdx().get(idxNode).size() > 1) {

                List<Integer> concurrentIdxActionList = new ArrayList<>(
                        this.primitiveTree.getParentsNodesIdx().get(idxNode));
                // All thoses actions should be mutex
                for (int i = 0; i < concurrentIdxActionList.size(); i++) {
                    for (int j = i + 1; j < concurrentIdxActionList.size(); j++) {
                        int idxParentNode1 = concurrentIdxActionList.get(i);
                        int idxParentNode2 = concurrentIdxActionList.get(j);
                        int min = Math.min(idxParentNode1, idxParentNode2);
                        int max = Math.max(idxParentNode1, idxParentNode2);
                        String key = min + "_" + max;
                        if (!pairAlreadySeen.contains(key)) {
                            allMacroActionsPath
                                    .append("(assert (or (not " + this.primitiveTree.getNodes().get(min).getUniqueName()
                                            + ") (not " + this.primitiveTree.getNodes().get(max).getUniqueName() + ")))\n");
                            pairAlreadySeen.add(key);
                        }
                    }
                }

            }

            if (this.primitiveTree.getChildrenNodesIdx().get(idxNode).size() > 1) {

                List<Integer> concurrentIdxActionList = new ArrayList<>(
                        this.primitiveTree.getChildrenNodesIdx().get(idxNode));
                // All thoses actions should be mutex
                for (int i = 0; i < concurrentIdxActionList.size(); i++) {
                    for (int j = i + 1; j < concurrentIdxActionList.size(); j++) {
                        int idxChildNode1 = concurrentIdxActionList.get(i);
                        int idxChildNode2 = concurrentIdxActionList.get(j);
                        int min = Math.min(idxChildNode1, idxChildNode2);
                        int max = Math.max(idxChildNode1, idxChildNode2);
                        String key = min + "_" + max;
                        if (!pairAlreadySeen.contains(key)) {
                            allMacroActionsPath
                                    .append("(assert (or (not " + this.primitiveTree.getNodes().get(min).getUniqueName()
                                            + ") (not " + this.primitiveTree.getNodes().get(max).getUniqueName() + ")))\n");
                            pairAlreadySeen.add(key);
                        }
                    }
                }

            }

        }
        return allMacroActionsPath.toString();
    }

    private String encodeDeclarationScopeVariablesSAT() {
        StringBuilder declarationScopeVariables = new StringBuilder();

        HashSet<ScopeVariable> scopeAlreadyDeclared = new HashSet<ScopeVariable>();

        // for (LiftedFlow flow : this.primitiveTree.getNodes()) {
        //     if (flow.getUniqueName().equals("FLOW_A_m14_everyone_go_hiking-m6_prepare_trip-m9_bring_tent-nop%15")) {
        //         int debug = 0;
        //     }
        //     for (ArrayList<ScopeVariable> arrayScope : flow.getScopeVariablesActionsFlow()) {
        //         for (ScopeVariable scopeVariable : arrayScope) {
        //             if (!scopeAlreadyDeclared.contains(scopeVariable) && !scopeVariable.isConstant()) {

        //                 for (String value : scopeVariable.getPossibleValueVariable()) {
        //                     declarationScopeVariables.append("(declare-const " + scopeVariable.getUniqueName() + "__" + value + " Bool)\n");
        //                 }
        //                 // Indicate as well all the different value that this scope variable can take

        //                 declarationScopeVariables.append("(assert (or ");
        //                 for (String value : scopeVariable.getPossibleValueVariable()) {
        //                     // declarationScopeVariables
        //                     //         .append("(= " + scopeVariable.getUniqueName() + " " + value + ") ");
        //                     declarationScopeVariables
        //                             .append(scopeVariable.getUniqueName() + "__" + value + " ");
        //                 }
        //                 declarationScopeVariables.append("))\n");

        //                 // Indicate as well that the scope variable can take at most one value
        //                 // HashSet<String> valuesToIterate = scopeVariable.getPossibleValueVariable();
        //                 ArrayList<String> valuesOfScope = new ArrayList<String>(scopeVariable.getPossibleValueVariable());
        //                 for (int i = 0; i < valuesOfScope.size(); i++) {
        //                     for (int j = i + 1; j < valuesOfScope.size(); j++) {
        //                         declarationScopeVariables.append("(assert (or (not " + scopeVariable.getUniqueName()
        //                                 + "__" + valuesOfScope.get(i) + ") (not " + scopeVariable.getUniqueName() + "__"
        //                                 + valuesOfScope.get(j) + ")))\n");
        //                     }
        //                 }

        //                 scopeAlreadyDeclared.add(scopeVariable);
        //             }
        //         }
        //     }
        // }

        for (ScopeVariable scopeVariable : this.scopeVarsToDefine) {
            if (!scopeVariable.isConstant()) {

                for (String value : scopeVariable.getPossibleValueVariable()) {
                    declarationScopeVariables.append("(declare-const " + scopeVariable.getUniqueName() + "__" + value + " Bool)\n");
                }
                // Indicate as well all the different value that this scope variable can take

                declarationScopeVariables.append("(assert (or ");
                for (String value : scopeVariable.getPossibleValueVariable()) {
                    // declarationScopeVariables
                    //         .append("(= " + scopeVariable.getUniqueName() + " " + value + ") ");
                    declarationScopeVariables
                            .append(scopeVariable.getUniqueName() + "__" + value + " ");
                }
                declarationScopeVariables.append("))\n");

                // Indicate as well that the scope variable can take at most one value
                // HashSet<String> valuesToIterate = scopeVariable.getPossibleValueVariable();
                ArrayList<String> valuesOfScope = new ArrayList<String>(scopeVariable.getPossibleValueVariable());
                for (int i = 0; i < valuesOfScope.size(); i++) {
                    for (int j = i + 1; j < valuesOfScope.size(); j++) {
                        declarationScopeVariables.append("(assert (or (not " + scopeVariable.getUniqueName()
                                + "__" + valuesOfScope.get(i) + ") (not " + scopeVariable.getUniqueName() + "__"
                                + valuesOfScope.get(j) + ")))\n");
                    }
                }

                scopeAlreadyDeclared.add(scopeVariable);
            }
        }
        return declarationScopeVariables.toString();
    }

    

    /**
     * Recursive way to create the primitive tree. 
     */
    private void createPrimitiveTreeQuick2() {

        // For now clean everything at the beginning
        // There is surey a smarter way to do this
        this.primitiveTree.clear();
        for (LiftedFlow f : this.paths) {
            f.setIsPrimitiveFlow(false);
            f.hasAlreadyBeenComputedForPrimitiveTree = false;
            f.setNumberChildrenPrimitiveFlow(0);
        }

        for (LiftedFlow initPaths : this.initialPaths) {
            if (!initPaths.isMethodLiftedFlow()) {
                recursiveComputePrimitiveTree(initPaths);
            }
        }

        // Create our tree now, and indicate for each node how far it is from the root (take the longest path from the root)
        // Which indicate the time step when we can execute this node
        this.primitiveTree.clear();

        HashSet<String> flowAlreadySeen = new HashSet<String>();
        HashSet<LiftedFlow> flowToVisit = new HashSet<LiftedFlow>();


        int stepFromRoot = 0;

        for (LiftedFlow initialFlow : this.initialPaths) {
            if (initialFlow.isPrimitiveFlow()) {
                initialFlow.setMaxStepFromRootNode(stepFromRoot);
                this.primitiveTree.addRootNode(initialFlow);
                // Add all its children to the pool if they are primitive flow
                for (LiftedFlow nextFlow : initialFlow.getNextsLiftedFlow()) {
                    if (nextFlow.isPrimitiveFlow()) {
                        flowToVisit.add(nextFlow);
                    }
                }

                // Indicate that we have seen this flow
                flowAlreadySeen.add(initialFlow.getUniqueName());
            }
        }

        stepFromRoot++;

        while (flowToVisit.size() > 0) {
            HashSet<LiftedFlow> flowToVisitNext = new HashSet<LiftedFlow>();
            for (LiftedFlow flow : flowToVisit) {
                // If all the parents haven't been seen, we can pass this flow (we will see it later)
                boolean allParentsSeen = true;
                for (LiftedFlow parent : flow.getPreviousesLiftedFlow()) {
                    if (parent.isPrimitiveFlow() && !flowAlreadySeen.contains(parent.getUniqueName())) {
                        allParentsSeen = false;
                        break;
                    }
                }

                if (!allParentsSeen) {
                    continue;
                }

                // Set the max step from root
                flow.setMaxStepFromRootNode(stepFromRoot);

                // Add all its children to the pool if they are primitive flow
                for (LiftedFlow nextFlow : flow.getNextsLiftedFlow()) {
                    if (nextFlow.isPrimitiveFlow()) {
                        flowToVisitNext.add(nextFlow);
                    }
                }

                // And add it to the tree
                for (LiftedFlow parentNode : flow.getPreviousesLiftedFlow()) {
                    if (parentNode.isPrimitiveFlow()) {
                        this.primitiveTree.addNodeAndParentIfNotExist(flow, parentNode);
                    }
                }

                // Add it to the list of seen flows
                flowAlreadySeen.add(flow.getUniqueName());
            }
            flowToVisit = flowToVisitNext;
            stepFromRoot++;
        }

        // Finally sort the node in our primitive tree in topological order
        this.primitiveTree.sortNodesInTopologicalSort();

        int a = 0;



        // for (LiftedFlow node : this.paths) {
        //     if (node.isPrimitiveFlow) {

        //         // this.primitiveTree.addNodeIfNotExist(node);
        //         boolean isRootNode = true;
        //         for (LiftedFlow parentNode : node.getPreviousesLiftedFlow()) {
        //             if (parentNode.isPrimitiveFlow) {
        //                 isRootNode = false;
        //                 // this.primitiveTree.addParentToNode(node, parentsNode);
        //                 this.primitiveTree.addNodeAndParentIfNotExist(node, parentNode);
        //             }
        //         }
        //         if (isRootNode) {
        //             this.primitiveTree.addRootNode(node);
        //         }
        //     }
        // }
    }

    private boolean recursiveComputePrimitiveTree(LiftedFlow currentNode) {

        // Iterate over all children of the current node and call the recursive compute primitive tree on it
        // If at least one of the children is a primitive flow, then the current node is a primitive flow as well
        // So its attribute isPrimitiveFlow is set to true and we return true

        // If this node is a method node, then it is not a primitive flow, and we do not need to iterate over its children
        if (currentNode.isMethodLiftedFlow()) {
            currentNode.setIsPrimitiveFlow(false);
            currentNode.hasAlreadyBeenComputedForPrimitiveTree = true;
            return false;
        }

        // If this node is an action and has no children, then it is a primitive flow (because the recursive call on this node will only be called 
        // if there is always at least one parent that is an action)
        if (currentNode.getNextsLiftedFlow().size() == 0) {
            currentNode.setIsPrimitiveFlow(true);
            currentNode.hasAlreadyBeenComputedForPrimitiveTree = true;
            return true;
        }



        // If this node is an action node, then we have to iterate over all its children
        // If at least one of the children is a primitive flow, then the current node is a primitive flow as well
        // So its attribute isPrimitiveFlow is set to true and we return true
        // (If a children has already been computed, then we do not have to compute it again)

        boolean currentNodeIsPrimitiveFlow = false;
        for (LiftedFlow childNode : currentNode.getNextsLiftedFlow()) {
            if (childNode.hasAlreadyBeenComputedForPrimitiveTree) {
                if (childNode.isPrimitiveFlow()) {
                    currentNodeIsPrimitiveFlow = true;
                }
            } else {
                if (recursiveComputePrimitiveTree(childNode)) {
                    currentNodeIsPrimitiveFlow = true;
                }
            }
        }

        currentNode.setIsPrimitiveFlow(currentNodeIsPrimitiveFlow);
        currentNode.hasAlreadyBeenComputedForPrimitiveTree = true;
        return currentNodeIsPrimitiveFlow;
    }

    /**
     * Indicate for each LiftedFlow of the primitive tree, the set of the
     * predicates that it know the value as well as the set of the predicates
     * that are true depending of the parent used (for the input (before the action
     * is called), and for the output (afer the action is called))
     */
    private void computeCertifiedPredicatesPrimitiveTree() {

        System.out.println("Compute input and output certified predicates...\n");

        // Indicate all the roots nodes
        for (Integer idxRootNode : this.primitiveTree.getRootNodesIdx()) {
            LiftedFlow node = this.primitiveTree.getNodes().get(idxRootNode);
            node.getRootsNodesWhichCanLedToThisFlow().add(node);
        }


        int currentStepToProcess = 0;

        
        if (LiftedTreePathConfig.useSASPlusEncoding) {
            // Reset the time step of all the cliques
            for (HashSet<Clique> subClique: UtilsStructureProblem.getSubCliques()) {
                for (Clique clique : subClique) {
                    clique.setLastTimeCliqueWasDefined(0);
                }
            }
        }

        // Reset as well the time step of each predicate
        for (SASPredicate pred : UtilsStructureProblem.predicatesSAS) {
            pred.setLastTimePredicateWasDefined(0);
        }


        // Some cleaning
        UtilsStructureProblem.resetLastTimePredicateDefined();

        // Add the predicates of the initial state into the list of the predicates to define (for the time step 0)
        HashSet<String> groundPredicateAtInitState = new HashSet<String>();
        groundPredicateAtInitState.addAll(this.fluentsTrueInit);
        groundPredicateAtInitState.addAll(this.fluentsFalseInit);

        int stepFromRoot = 0;

        this.cliqueBitsToDefine.clear();
        this.pseudoFactsToDefine.clear();
        this.groundFactsToDefine.clear();

        // Indicate that we must declare all those ground fluents
        if (!LiftedTreePathConfig.useSASPlusEncoding) {
            this.groundFactsToDefine.addAll(this.fluentsTrueInit);
            this.groundFactsToDefine.addAll(this.fluentsFalseInit);
        }

        HashSet<String> pseudoFactsAlreadyDefined = new HashSet<String>();

        HashSet<CertifiedPredicate> pseudoFactTimeStep = new HashSet<CertifiedPredicate>();
        HashSet<String> groundPredTimeStep = new HashSet<String>();

        groundPredTimeStep.addAll(groundPredicateAtInitState);

        HashSet<CertifiedPredicate> precondPredToGround = new HashSet<CertifiedPredicate>();
        HashSet<CertifiedPredicate> effectPredToGround = new HashSet<CertifiedPredicate>();
        HashSet<String> varsToDefine = new HashSet<String>();

        this.rule13PerTimeStep.clear();
        this.frameAxiomsAndEffsPerTimeStep.clear();

        // For each time step, we have to define the frame axioms and effects
        HashMap<Integer, HashMap<LiftedFlow, HashSet<CertifiedPredicate>>> allPosPredicateWhichCanBeChangedByActionOfThisTimeStep = new HashMap<Integer, HashMap<LiftedFlow, HashSet<CertifiedPredicate>>>();
        HashMap<Integer, HashMap<LiftedFlow, HashSet<CertifiedPredicate>>> allNegPredicateWhichCanBeChangedByActionOfThisTimeStep = new HashMap<Integer, HashMap<LiftedFlow, HashSet<CertifiedPredicate>>>();

        // Consume all the node of the topological sort tree
        for (LiftedFlow nodeToProcess : this.primitiveTree.getNodesInTopologicalOrder()) {

            // Get the time step of the node
            int stepNodeToIterate = nodeToProcess.getMaxStepFromRootNode();

            // If it is greated that the step from Root, we can execute the frame axioms and clear them afterward
            if (stepNodeToIterate > stepFromRoot) {
                System.out.println("Execute frame axioms and effects for time step: " + stepFromRoot);
                

                pseudoFactTimeStep = new HashSet<CertifiedPredicate>();
                groundPredTimeStep = new HashSet<String>();

                // TODO rule 13 here (conversion from pseudo fact to predicate)
                String rule13_precond = UtilsStructureProblem.generateRuleConversionPseudoFactToGroundFact(precondPredToGround, cliqueBitsToDefine, groundFactsToDefine, stepFromRoot, true);
                String rule13_effects = UtilsStructureProblem.generateRuleConversionPseudoFactToGroundFact(effectPredToGround, cliqueBitsToDefine, groundFactsToDefine, stepFromRoot + 1, false);

                this.rule13PerTimeStep.add(rule13_precond);
                this.rule13PerTimeStep.add(rule13_effects);

                System.out.println(rule13_precond);
                System.out.println(rule13_effects);

                // StringBuilder allEffsAndFrameAxioms = new StringBuilder();
                // for (EffActionsAndFrameAxioms effActionsAndFrameAxioms : predicateToFrameAxiomsAndEffectsNotYetDefined) {
                //     String frameAxiomsAndEffects = effActionsAndFrameAxioms.toSmt(stepFromRoot + 1, pseudoFactTimeStep, groundPredTimeStep);
                //     allEffsAndFrameAxioms.append(frameAxiomsAndEffects);
                //     System.out.println(frameAxiomsAndEffects);
                // }
                // this.frameAxiomsAndEffsPerTimeStep.add(allEffsAndFrameAxioms.toString());

                // Do the frame axioms with all the predicates which may have changed in this time step
                String allEffsAndFrameAxioms;
                
                if (LiftedTreePathConfig.useSASPlusEncoding) {
                    allEffsAndFrameAxioms = UtilsStructureProblem.generateFrameAxiomsForPredicatesWithSASPlus(allPosPredicateWhichCanBeChangedByActionOfThisTimeStep, stepFromRoot + 1, pseudoFactTimeStep, groundPredTimeStep, this.cliqueBitsToDefine);
                    String test = UtilsStructureProblem.generateFrameAxiomsForPredicatesWithSASPlus(allNegPredicateWhichCanBeChangedByActionOfThisTimeStep, stepFromRoot + 1, pseudoFactTimeStep, groundPredTimeStep, this.cliqueBitsToDefine);
                    allEffsAndFrameAxioms += test;
                    int c = 0;
                } else {
                    allEffsAndFrameAxioms = UtilsStructureProblem.generateFrameAxiomsForPredicatesWithoutSASPlus(allPosPredicateWhichCanBeChangedByActionOfThisTimeStep, allNegPredicateWhichCanBeChangedByActionOfThisTimeStep, stepFromRoot + 1, pseudoFactTimeStep, this.groundFactsToDefine);
                } 

                this.frameAxiomsAndEffsPerTimeStep.add(allEffsAndFrameAxioms);

                // Clear the list of the frame axioms and effects to define
                precondPredToGround.clear();
                effectPredToGround.clear();

                // precondPredToGround.addAll(pseudoFactTimeStep);

                allPosPredicateWhichCanBeChangedByActionOfThisTimeStep.clear();
                allNegPredicateWhichCanBeChangedByActionOfThisTimeStep.clear();


                // Increment the step from root
                stepFromRoot = stepNodeToIterate;


            }


            System.out.println("==========");
            System.out.println("Current Node: " + nodeToProcess.getUniqueName() + " (" + nodeToProcess.getMaxStepFromRootNode() + ")");

            nodeToProcess.cleanInputAndOutputCertifiedPredicate();
            nodeToProcess.cleanPreconditionAndEffectsSMT();

            if (nodeToProcess.getUniqueName().equals("FLOW_visit_47") || nodeToProcess.getUniqueName().equals("FLOW_visit_14")) {
                int a = 0;
            }

            HashSet<LiftedFlow> parentsNode = this.primitiveTree.getParents(nodeToProcess);

            nodeToProcess.computePreconditionsAndDefaultOutputCertifiedPredicates2WithoutLFG(this.staticPredicates, this.liftedFamGroups, this.dictConstantToScopeVariable);

            nodeToProcess.getAllRootsNodeThatCanLedToThisFlowFromParents(parentsNode);


            // if (LiftedTreePathConfig.useSASPlusEncoding) {
                // nodeToProcess.determinateHowToResolvePreconditionsWithLFG2(precondPredToGround, varsToDefine, pseudoFactTimeStep, groundPredTimeStep);
            // } else {
                nodeToProcess.determinateHowToResolvePreconditionsWithoutLFG2(precondPredToGround, varsToDefine, this.pseudoFactsToDefine, this.groundFactsToDefine, pseudoFactsAlreadyDefined);
            // }
            
            // nodeToProcess.determinateHowToResolveEffectsWithoutLFG2(effectPredToGround, varsToDefine, predicateToFrameAxiomsAndEffectsNotYetDefined);
            nodeToProcess.determinateHowToResolveEffectsWithoutLFG3(effectPredToGround, varsToDefine, this.pseudoFactsToDefine, this.groundFactsToDefine, allPosPredicateWhichCanBeChangedByActionOfThisTimeStep, allNegPredicateWhichCanBeChangedByActionOfThisTimeStep, pseudoFactsAlreadyDefined);

            System.out.println("Preconditions:\n" + nodeToProcess.preconditionsSMT);
            System.out.println("Effects:\n" + nodeToProcess.effectsSMT);

            int a = 0;
        }

        String rule13_precond = UtilsStructureProblem.generateRuleConversionPseudoFactToGroundFact(precondPredToGround, cliqueBitsToDefine, groundFactsToDefine, stepFromRoot, true);
        this.rule13PerTimeStep.add(rule13_precond);

        if (this.fluentsIdTrueGoal.size() > 0 || this.fluentsIdFalseGoal.size() > 0) {
            // We have to compute the frame axioms for the last step only if we have fluents in the goal (else, we do not care the values of the predicate at the end)
            String rule13_effects = UtilsStructureProblem.generateRuleConversionPseudoFactToGroundFact(effectPredToGround, cliqueBitsToDefine, groundFactsToDefine, stepFromRoot + 1, false);

                this.rule13PerTimeStep.add(rule13_precond);
                this.rule13PerTimeStep.add(rule13_effects);

                System.out.println(rule13_precond);
                System.out.println(rule13_effects);

                // StringBuilder allEffsAndFrameAxioms = new StringBuilder();
                // for (EffActionsAndFrameAxioms effActionsAndFrameAxioms : predicateToFrameAxiomsAndEffectsNotYetDefined) {
                //     String frameAxiomsAndEffects = effActionsAndFrameAxioms.toSmt(stepFromRoot + 1, pseudoFactTimeStep, groundPredTimeStep);
                //     allEffsAndFrameAxioms.append(frameAxiomsAndEffects);
                //     System.out.println(frameAxiomsAndEffects);
                // }
                // this.frameAxiomsAndEffsPerTimeStep.add(allEffsAndFrameAxioms.toString());

                // Do the frame axioms with all the predicates which may have changed in this time step
                String allEffsAndFrameAxioms;
                
                if (LiftedTreePathConfig.useSASPlusEncoding) {
                    allEffsAndFrameAxioms = UtilsStructureProblem.generateFrameAxiomsForPredicatesWithSASPlus(allPosPredicateWhichCanBeChangedByActionOfThisTimeStep, stepFromRoot + 1, pseudoFactTimeStep, groundPredTimeStep, this.cliqueBitsToDefine);
                    String test = UtilsStructureProblem.generateFrameAxiomsForPredicatesWithSASPlus(allNegPredicateWhichCanBeChangedByActionOfThisTimeStep, stepFromRoot + 1, pseudoFactTimeStep, groundPredTimeStep, this.cliqueBitsToDefine);
                    allEffsAndFrameAxioms += test;
                    int c = 0;
                } else {
                    allEffsAndFrameAxioms = UtilsStructureProblem.generateFrameAxiomsForPredicatesWithoutSASPlus(allPosPredicateWhichCanBeChangedByActionOfThisTimeStep, allNegPredicateWhichCanBeChangedByActionOfThisTimeStep, stepFromRoot + 1, pseudoFactTimeStep, this.groundFactsToDefine);
                } 

                this.frameAxiomsAndEffsPerTimeStep.add(allEffsAndFrameAxioms);

        }
        // String rule13_effects = UtilsStructureProblem.generateRuleConversionPseudoFactToGroundFact(effectPredToGround, stepFromRoot + 1, false);

        
        // this.rule13PerTimeStep.add(rule13_effects);

        int b = 0;
    }

    private void preprocessing() {
        // Find each object and give a value for each object of each type
        this.dictTypeToObjects = new HashMap<String, Vector<String>>();
        for (String typeName : this.problem.getTypes()) {
            this.dictTypeToObjects.put(typeName, new Vector<String>());
        }
        // Now iterate over each object to get the type
        for (TypedSymbol<String> obj : this.problem.getParsedProblem().getConstants()) {
            String nameObj = obj.getValue();
            String typeObj = obj.getTypes().get(0).getValue();
            System.out.println(nameObj + " " + typeObj);
            this.dictTypeToObjects.get(typeObj).add(nameObj);
        }

        preprocessingComputeAllParentsAndChildrenEachTypes(problem);

        this.objNameToUniqueId = objNameToUniqueId();

        // For each method, map its name to the object parsed method associated
        // + For each method, compute the number of children that this method can take
        this.methodNameToObj = new HashMap<String, ParsedMethod>();
        this.liftedMethodToNumberSubtasks = new HashMap<String, Integer>();
        for (ParsedMethod methodObj : this.problem.getParsedProblem().getMethods()) {
            String nameMethod = methodObj.getName().getValue();
            this.methodNameToObj.put(nameMethod, methodObj);

            // Ugly way to get the number of subtasks of a lifted method, but it is done
            // only once, so who care
            for (Method m : problem.getMethods()) {
                if (m.getName().equals(nameMethod)) {
                    this.liftedMethodToNumberSubtasks.put(nameMethod, m.getSubTasks().size());
                    break;
                }
            }
        }

        this.actionNameToObj = new HashMap<String, ParsedAction>();
        for (ParsedAction actionObj : this.problem.getParsedProblem().getActions()) {
            String nameAction = actionObj.getName().getValue();
            this.actionNameToObj.put(nameAction, actionObj);
        }
        // Add as well a blank action (which can be usefull for method with no subtasks)
        // this.actionNameToObj.put("BLANK_ACTION", new ParsedAction(new
        // Symbol<String>(SymbolType.ACTION, ), new ArrayList<TypedSymbol<String>>(),
        // new Expression<String>(), new Expression<String>()));

        // Get all the static predicates
        this.staticPredicates = preprocessingComputeStaticPredicates(problem);

        // Create a map from the name of an object to its type
        this.dictObjNameToType = preprocessingComputeDictObjectNameToType(problem);

        // Create a special scope variable for each object if the object is alone (constant)
        this.dictConstantToScopeVariable = new HashMap<String, ScopeVariable>();
        for (String objName : this.dictObjNameToType.keySet()) {
            ScopeVariable sv = new ScopeVariable();
            this.scopeVarsToDefine.add(sv);
            sv.addTypeVariable(this.dictObjNameToType.get(objName));
            sv.addValueToScope(objName);
            this.dictConstantToScopeVariable.put(objName, sv);
        }


    }

    private HashSet<String> preprocessingComputeStaticPredicates(Problem problem) {

        HashSet<String> staticPredicates = new HashSet<String>();
        // Iterate over all predicates name
        for (String predicateName : problem.getPredicateSymbols()) {
            if (predicatIsStatic(predicateName, problem)) {
                staticPredicates.add(predicateName);
            }
        }
        return staticPredicates;
    }

    public Map<String, String> preprocessingComputeDictObjectNameToType(Problem problem) {

        Map<String, String> dictObjNameToType = new HashMap<>();
        for (TypedSymbol<String> obj : problem.getParsedProblem().getConstants()) {
            dictObjNameToType.put(obj.getValue(), obj.getTypes().get(0).getValue());
        }
        return dictObjNameToType;
    }

    private static boolean predicatIsStatic(String predicateToCheck, Problem problem) {

        // Iterate over all action of our problem (in a lifted way)
        for (ParsedAction action : problem.getParsedProblem().getActions()) {

            // If the action only have one effect, check if this effect affect the predicate
            if (action.getEffects().getSymbol() != null && action.getEffects().getSymbol().equals(predicateToCheck)) {
                return false;
            }

            // Else Iterate over all effects of this action
            for (int effId = 0; effId < action.getEffects().getChildren().size(); effId++) {

                String predicateModifiedByAction = null;

                // Get the name of the predicate that will be modified by this effect
                if (action.getEffects().getChildren().get(effId).getConnector().getImage()
                        .equals("not")) {

                    predicateModifiedByAction = action.getEffects().getChildren().get(effId).getChildren().get(0)
                            .getSymbol().getValue();
                } else {
                    predicateModifiedByAction = action.getEffects().getChildren().get(effId).getSymbol().getValue();
                }

                if (predicateModifiedByAction.equals(predicateToCheck)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Compute all the parents name type and children name type of each type. Fill
     * the two map dictTypeToParentTypes and dictTypeToChildTypes
     * 
     * @param problem
     */
    private void preprocessingComputeAllParentsAndChildrenEachTypes(Problem problem) {

        // Initialize our 2 maps + create A map from the name of the type to the object
        Map<String, TypedSymbol<String>> dictTypeNameToObj = new HashMap<>();
        this.dictTypeToParentTypes = new HashMap<>();
        this.dictTypeToChildTypes = new HashMap<>();

        for (TypedSymbol<String> typeObj : problem.getParsedProblem().getTypes()) {
            String typeName = typeObj.getValue();
            this.dictTypeToParentTypes.put(typeName, new HashSet<String>());
            this.dictTypeToChildTypes.put(typeName, new HashSet<String>());
            dictTypeNameToObj.put(typeName, typeObj);
        }

        // Now iterate over each object to set their parent. And once we have
        // them, reiterate to find all the children
        // Not optimal, but we do not care, as there are never too much different
        // objects

        for (TypedSymbol<String> type : problem.getParsedProblem().getTypes()) {
            recursiveFindAllParentOfType(this.dictTypeToParentTypes.get(type.getValue()), type, dictTypeNameToObj);
        }

        // Now, that we have all the parents of each type, we can compute the children
        for (String typeParent : this.dictTypeToParentTypes.keySet()) {
            for (String typeChild : this.dictTypeToParentTypes.keySet()) {
                if (this.dictTypeToParentTypes.get(typeChild).contains(typeParent)) {
                    this.dictTypeToChildTypes.get(typeParent).add(typeChild);
                }
            }
        }
    }

    private void recursiveFindAllParentOfType(HashSet<String> parents, TypedSymbol<String> type,
            Map<String, TypedSymbol<String>> dictTypeNameToObj) {

        // If this type has no parent, do nothing
        if (type.getTypes().size() == 0) {
            return;
        }

        for (Symbol<String> nameTypeParent : type.getTypes()) {

            // Add the parent to the list
            parents.add(nameTypeParent.getValue());

            // Find the parent of this parent
            recursiveFindAllParentOfType(parents, dictTypeNameToObj.get(nameTypeParent.getValue()), dictTypeNameToObj);
        }
    }

    private Map<String, Integer> objNameToUniqueId() {

        Map<String, Integer> mapObjNameToUniqueId = new HashMap<String, Integer>();

        int valueObj = 0;
        for (String typeName : this.dictTypeToObjects.keySet()) {
            Vector<String> allObjsOfType = this.dictTypeToObjects.get(typeName);
            for (int i = 0; i < allObjsOfType.size(); i++) {
                mapObjNameToUniqueId.put(allObjsOfType.get(i), valueObj);
                valueObj++;
            }
        }
        return mapObjNameToUniqueId;
    }

    /**
     * Return a string containing a fluent in easily readable format
     * 
     * @param f       The fluent to display in easily readable format
     * @param problem The problem to solve
     * @return A String representing the fluent in easily readable format
     */
    private String prettyDisplayFluent(Fluent f, Problem problem) {
        StringBuilder fluentToDisplay = new StringBuilder();

        // Add the fluent name (e.g "at" for the fluent at ?r - robot ?l - location)
        fluentToDisplay.append("FLUENT_" + problem.getPredicateSymbols().get(f.getSymbol()));

        // Then, for each argument of this fluent, add the argument into the string
        for (int fluentArg : f.getArguments()) {
            fluentToDisplay.append("_" + problem.getConstantSymbols().get(fluentArg));
        }

        return fluentToDisplay.toString();
    }

    /**
     * Indicate for each flow its previous and next flow. Write into a file named :
     * "previousAndNextFlows_<layer>.txt"
     * @param layer The current layer
     * @throws IOException If the file can not be created
     */
    private void debugWriteAllPathsInFile(int layer) throws IOException {

        // Create the file
        String fileName = "DAG_layer" + layer + ".txt";

        StringBuilder nameAllFlows = new StringBuilder();
        StringBuilder content = new StringBuilder();

        // Iterate over all the flows in the layer
        // for (LiftedFlow node : this.primitiveTree.getNodes()) {
            for (LiftedFlow node : this.paths) {
            // Get the name of the flow
            String nameFlow = node.getUniqueName();

            int isPrimitive = 0;
            if (this.primitiveTree.getNodes().contains(node)) {
                isPrimitive = 1;
            }

            int isAction = 1;
            if (node.isMethodLiftedFlow()) {
                isAction = 0;
            }

            nameAllFlows.append(nameFlow + " " + isAction + " " + isPrimitive + "\n");

            // Get the name of the previous flows
            // String previousFlows = "";
            // for (LiftedFlow previousFlow : node.getPreviousesLiftedFlow()) {
                // previousFlows += previousFlow.getUniqueName() + " ";
            // }

            // Get the name of the next flows
            // String nextFlows = "";
            // for (LiftedFlow nextFlow : this.primitiveTree.getChildren(node)) {
            //     nextFlows += nextFlow.getUniqueName() + " ";
            // }
            String nextFlows = "";
            for (LiftedFlow nextFlow : node.getNextsLiftedFlow()) {
                nextFlows += nextFlow.getUniqueName() + " ";
            }

            // Write into the file
            content.append(nameFlow + " " + nextFlows + "\n");
        }

        StringBuilder fullContent = new StringBuilder();
        fullContent.append(nameAllFlows.toString() + "\n" + content.toString());


        // Write into the file
        BufferedWriter writer = new BufferedWriter(new FileWriter(fileName));
        writer.write(fullContent.toString());
        writer.flush();
        writer.close();
    }
}