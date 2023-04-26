package treerex.hydra.DataStructures;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Vector;

import fr.uga.pddl4j.parser.Expression;
import fr.uga.pddl4j.parser.ParsedAction;
import fr.uga.pddl4j.parser.ParsedMethod;
import fr.uga.pddl4j.parser.Symbol;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import treerex.hydra.Preprocessing.UtilsStructureProblem;
import treerex.hydra.Preprocessing.LiftedSasPlus.AtomCandidate;
import treerex.hydra.Preprocessing.LiftedSasPlus.AtomVariable;
import treerex.hydra.Preprocessing.LiftedSasPlus.Candidate;
import treerex.hydra.SolverConfig.LiftedTreePathConfig;
import org.apache.commons.lang3.tuple.Pair;

public class LiftedFlow {

    static int numberLiftedFlow = 0;

    public int uniqueId;

    private int stepFromRoot;

    private Method method = null;
    private String methodName = null;
    private ArrayList<String> macroAction = null;

    boolean isBlankAction = false;

    LiftedFlow parentFlow = null;
    private Integer parentId; // ID of task for method, ID of method for action
    HashSet<LiftedFlow> nextsFlow;
    HashSet<LiftedFlow> previousesFlow;

    HashSet<CertifiedPredicate> preconditionsHerited;

    Expression<String> preconditions;
    Expression<String> effects;
    ArrayList<Expression<String>> preconditions2;
    ArrayList<Expression<String>> effects2;

    private ArrayList<ScopeVariable> scopeMethod;
    private ArrayList<ArrayList<ScopeVariable>> scopeMacroAction;

    HashSet<CertifiedPredicate> inputCertifiedPredicates;
    HashSet<CertifiedPredicate> outputCertifiedPredicates;
    HashSet<CertifiedPredicate> preconditionPredicates;
    HashSet<CertifiedPredicate> effectPredicates;


    HashSet<LiftedFlow> rootsNodesWhichCanLedToThisFlow;

    public String preconditionsSMT;
    public String effectsSMT;

    boolean isPrimitiveFlow;
    public boolean hasAlreadyBeenComputedForPrimitiveTree = false;
    int numberChildrenPrimitiveFlow;

    public LiftedFlow(String methodName, LiftedFlow parentFlow, Integer parentTaskId,
            ArrayList<ScopeVariable> methodScope, Map<String, ParsedMethod> methodNameToObject,
            boolean isFirstChildOfMethod, ArrayList<Candidate> liftedFamGroups) {
        this.methodName = methodName;
        this.parentFlow = parentFlow;
        this.parentId = parentTaskId;
        this.scopeMethod = methodScope;
        isPrimitiveFlow = false;
        this.numberChildrenPrimitiveFlow = 0;

        this.nextsFlow = new HashSet<LiftedFlow>();
        this.previousesFlow = new HashSet<LiftedFlow>();

        this.rootsNodesWhichCanLedToThisFlow = new HashSet<LiftedFlow>();

        this.preconditionsHerited = new HashSet<CertifiedPredicate>();
        // If we are the first child of a method, we must inherit its preconditions
        if (isFirstChildOfMethod) {
            inheritPreconditionsFromParent(parentFlow, methodNameToObject);
            // inheritPreconditionsFromParentLFG(parentFlow, methodNameToObject, liftedFamGroups);
        }

        this.uniqueId = LiftedFlow.numberLiftedFlow;
        LiftedFlow.numberLiftedFlow++;
    }

    public LiftedFlow(ArrayList<String> macroAction, LiftedFlow parentFlow,
            ArrayList<ArrayList<ScopeVariable>> scopeMacroAction, Map<String, ParsedAction> actionNameToObject,
            Map<String, ParsedMethod> methodNameToObject, boolean isFirstChildOfMethod, ArrayList<Candidate> liftedFamGroups) {
        this.macroAction = macroAction;
        this.parentFlow = parentFlow;
        this.scopeMacroAction = scopeMacroAction;
        this.isPrimitiveFlow = false;
        this.numberChildrenPrimitiveFlow = 0;

        // TODO, we should compute the precondition and effects of the macro action here
        // (or take them from a table since there will always be the same macro action)
        // For now, consider that there is only one action, and takes its preconditions
        // and effects
        ParsedAction liftedAction = actionNameToObject.get(macroAction.get(0));
        this.preconditions = liftedAction.getPreconditions();
        this.effects = liftedAction.getEffects();

        this.preconditions2 = new ArrayList<>();
        this.effects2 = new ArrayList<>();
        for (String actionName : macroAction) {
            ParsedAction liftedAction2 = actionNameToObject.get(actionName);
            this.preconditions2.add(liftedAction2.getPreconditions());
            this.effects2.add(liftedAction2.getEffects());
        }

        this.preconditionsHerited = new HashSet<CertifiedPredicate>();
        // If we are the first child of a method, we must inherit its preconditions
        if (isFirstChildOfMethod) {
            inheritPreconditionsFromParent(parentFlow, methodNameToObject);
            // inheritPreconditionsFromParentLFG(parentFlow, methodNameToObject, liftedFamGroups);
        }

        this.rootsNodesWhichCanLedToThisFlow = new HashSet<LiftedFlow>();

        this.nextsFlow = new HashSet<LiftedFlow>();
        this.previousesFlow = new HashSet<LiftedFlow>();

        this.inputCertifiedPredicates = new HashSet<CertifiedPredicate>();
        this.outputCertifiedPredicates = new HashSet<CertifiedPredicate>();
        this.preconditionPredicates = new HashSet<CertifiedPredicate>();
        this.effectPredicates = new HashSet<CertifiedPredicate>();

        this.uniqueId = LiftedFlow.numberLiftedFlow;
        LiftedFlow.numberLiftedFlow += macroAction.size(); // To have each subaction have a unique ID
    }

    // Use to create blank action
    public LiftedFlow(boolean isBlankAction, LiftedFlow parentFlow, Map<String, ParsedMethod> methodNameToObject,
            boolean isFirstChildOfMethod, ArrayList<Candidate> liftedFamGroups) {
        this.macroAction = new ArrayList<String>();
        this.macroAction.add("BLANK");
        this.parentFlow = parentFlow;
        this.scopeMacroAction = new ArrayList<>();
        this.scopeMacroAction.add(new ArrayList<>());
        // Since we are a blank action, we inherit the scope of the parent
        this.scopeMacroAction.get(0).addAll(parentFlow.scopeMethod);
        this.isPrimitiveFlow = false;
        this.numberChildrenPrimitiveFlow = 0;

        this.preconditions2 = new ArrayList<>();
        this.effects2 = new ArrayList<>();

        this.preconditionsHerited = new HashSet<CertifiedPredicate>();
        // If we are the first child of a method, we must inherit its preconditions
        if (isFirstChildOfMethod) {
            inheritPreconditionsFromParent(parentFlow, methodNameToObject);
        }

        this.rootsNodesWhichCanLedToThisFlow = new HashSet<LiftedFlow>();

        this.nextsFlow = new HashSet<LiftedFlow>();
        this.previousesFlow = new HashSet<LiftedFlow>();

        this.inputCertifiedPredicates = new HashSet<CertifiedPredicate>();
        this.outputCertifiedPredicates = new HashSet<CertifiedPredicate>();
        this.preconditionPredicates = new HashSet<CertifiedPredicate>();
        this.effectPredicates = new HashSet<CertifiedPredicate>();

        this.isBlankAction = true;
        this.uniqueId = LiftedFlow.numberLiftedFlow;
        LiftedFlow.numberLiftedFlow++;

    }

    public void setParentId(int parentId) {
        this.parentId = parentId;
    }

    public ArrayList<String> getMacroAction() {
        return this.macroAction;
    }

    public boolean isPrimitiveFlow() {
        return this.isPrimitiveFlow;
    }

    public void setIsPrimitiveFlow(boolean isPrimitiveFlow) {
        this.isPrimitiveFlow = isPrimitiveFlow;
    }

    public int getNumberChildrenPrimitiveFlow() {
        return this.numberChildrenPrimitiveFlow;
    }

    public void setNumberChildrenPrimitiveFlow(int numberChildrenPrimitiveFlow) {
        this.numberChildrenPrimitiveFlow = numberChildrenPrimitiveFlow;
    }

    public HashSet<LiftedFlow> getRootsNodesWhichCanLedToThisFlow() {
        return this.rootsNodesWhichCanLedToThisFlow;
    }

    

    public ArrayList<ScopeVariable> getScopeVariables() {
        return this.scopeMethod;
    }

    public ArrayList<ArrayList<ScopeVariable>> getScopeVariablesActionsFlow() {
        return this.scopeMacroAction;
    }

    public void setMethod(Method m) {
        this.method = m;
    }

    public void setMacroAction(ArrayList<String> macroAction) {
        this.macroAction = macroAction;
    }

    public void addNextLiftedFlow(LiftedFlow f) {
        this.nextsFlow.add(f);
    }

    public void addPreviousesLiftedFlow(LiftedFlow f) {
        this.previousesFlow.add(f);
    }

    public HashSet<LiftedFlow> getNextsLiftedFlow() {
        return this.nextsFlow;
    }

    public HashSet<LiftedFlow> getPreviousesLiftedFlow() {
        return this.previousesFlow;
    }

    public Integer getParentId() {
        return this.parentId;
    }

    public boolean isMethodLiftedFlow() {
        return this.methodName != null;
    }

    public Method getMethod() {
        return this.method;
    }

    public String getMethodName() {
        return this.methodName;
    }

    public void inheritPreconditionsFromParent(LiftedFlow parentFlow, Map<String, ParsedMethod> methodNameToObject) {

        // First, see if the parent method has already heritate precondition from its
        // parent node
        this.preconditionsHerited.addAll(parentFlow.preconditionsHerited);

        // By inherithing these predicates, we become de facto the certifier of these
        // predicates
        for (CertifiedPredicate pred : this.preconditionsHerited) {
            pred.certifiers.clear();
            pred.certifiers.add(this);
        }

        // Now add the precondition of the parent method in it
        ParsedMethod parentMethod = methodNameToObject.get(parentFlow.getMethodName());

        Expression<String> preconditionsMethod = parentMethod.getPreconditions();

        int numberPreMethod = preconditionsMethod.getChildren().size();
        if (numberPreMethod == 0 && preconditionsMethod.getSymbol() != null) {
            numberPreMethod = 1;
        }

        for (int preId = 0; preId < numberPreMethod; preId++) {

            Expression<String> pre;

            if (numberPreMethod > 1) {
                pre = preconditionsMethod.getChildren().get(preId);
            } else {
                pre = preconditionsMethod;
            }

            if (pre.getConnector().getImage().equals("true")) {
                continue;
            }

            boolean predicateIsPositive = true;

            // Negative predicate
            if (pre.getConnector().getImage().equals("not")) {
                predicateIsPositive = false;
                pre = pre.getChildren().get(0);
            }

            String namePredicate = pre.getSymbol().getValue();
            ArrayList<ScopeVariable> scopePred = new ArrayList<ScopeVariable>();

            for (Symbol<String> arg : pre.getArguments()) {
                int idxArg = Integer.parseInt(arg.getValue().substring(2));
                scopePred.add(parentFlow.scopeMethod.get(idxArg));
            }

            CertifiedPredicate certPredicate = new CertifiedPredicate(namePredicate, predicateIsPositive,
                    scopePred, this);

            this.preconditionsHerited.add(certPredicate);
        }
    }

    public LiftedFlow getParentFlow() {
        return this.parentFlow;
    }

   
    private ArrayList<ArrayList<CertifiedPredicate>> getCertifiedPredicateFromExpression(
            ArrayList<Expression<String>> preconditionOrEffectMacroAction, Map<String, ScopeVariable> dictConstantToScopeVariable) {

        ArrayList<ArrayList<CertifiedPredicate>> preOrEffMacroAction = new ArrayList<ArrayList<CertifiedPredicate>>();

        for (int actionIdx = 0; actionIdx < this.macroAction.size(); actionIdx++) {

            ArrayList<CertifiedPredicate> preOrEffAction = new ArrayList<CertifiedPredicate>();

            Expression<String> expresiionPreOfEffAction = preconditionOrEffectMacroAction.get(actionIdx);

            int numberPreActions = expresiionPreOfEffAction.getChildren().size();
            if (numberPreActions == 0 && expresiionPreOfEffAction.getSymbol() != null) {
                numberPreActions = 1;
            }

            for (int preId = 0; preId < numberPreActions; preId++) {

                Expression<String> pre;

                if (numberPreActions > 1) {
                    pre = expresiionPreOfEffAction.getChildren().get(preId);
                } else {
                    pre = expresiionPreOfEffAction;
                }

                if (pre.getConnector().getImage().equals("true")) {
                    continue;
                }

                boolean predicateIsPositive = true;

                // Negative predicate
                if (pre.getConnector().getImage().equals("not")) {
                    predicateIsPositive = false;
                    pre = pre.getChildren().get(0);
                }

                if (pre.getSymbol() == null) {
                    System.out.println("Error in the scope of the predicate " + pre.getConnector().getImage());
                    System.exit(0);
                }

                String namePredicate = pre.getSymbol().getValue();
                ArrayList<ScopeVariable> scopePred = new ArrayList<ScopeVariable>();

                for (Symbol<String> arg : pre.getArguments()) {
                    try {
                        int idxArg = Integer.parseInt(arg.getValue().substring(2));
                        scopePred.add(this.scopeMacroAction.get(actionIdx).get(idxArg));
                    } catch (Exception e) {
                        // It must be a constant, find the constant associated with it
                        if (!dictConstantToScopeVariable.containsKey(arg.getValue())) {
                            System.out.println("Error in the scope of the predicate " + namePredicate);
                            e.printStackTrace();
                            System.exit(0);
                        }
                        else {
                            scopePred.add(dictConstantToScopeVariable.get(arg.getValue()));
                        }
                    }
                }

                CertifiedPredicate certPredicate = new CertifiedPredicate(namePredicate, predicateIsPositive,
                        scopePred, this);

                preOrEffAction.add(certPredicate);
            }

            preOrEffMacroAction.add(preOrEffAction);
        }

        return preOrEffMacroAction;
    }



 

    public void computePreconditionsAndDefaultOutputCertifiedPredicates2WithoutLFG(HashSet<String> staticPredicate,
        ArrayList<Candidate> liftedFamGroups, Map<String, ScopeVariable> dictConstantToScopeVariable) {

        ArrayList<ArrayList<CertifiedPredicate>> preconditionsAllActions;
        ArrayList<ArrayList<CertifiedPredicate>> effectsAllActions;

        if (!this.isBlankAction) {
            // First, get the preconditions by default of the macro action
            preconditionsAllActions = getCertifiedPredicateFromExpression(this.preconditions2, dictConstantToScopeVariable);

            // Get as well the effect of the macro action
            effectsAllActions = getCertifiedPredicateFromExpression(this.effects2, dictConstantToScopeVariable);
        } else {
            preconditionsAllActions = new ArrayList<ArrayList<CertifiedPredicate>>();
            preconditionsAllActions.add(new ArrayList<CertifiedPredicate>());

            effectsAllActions = new ArrayList<ArrayList<CertifiedPredicate>>();
            effectsAllActions.add(new ArrayList<CertifiedPredicate>());
        }

        // Add all the precondition of the parent method into the precondition of the
        // first action of the macro action if the action does not already satisfied it
        for (CertifiedPredicate preconditionsHerited : this.preconditionsHerited) {
            boolean canAddPreconditionHerited = true;
            for (CertifiedPredicate preconditionFirstAction : preconditionsAllActions.get(0)) {
                if (preconditionFirstAction.isEqualsTo(preconditionsHerited)) {
                    canAddPreconditionHerited = false;
                    break;
                }
            }
            if (canAddPreconditionHerited) {
                preconditionsAllActions.get(0).add(preconditionsHerited);
            }
        }

        // Ok, now is the difficult part
        // from the precondition and effects of all the actions of the method
        // we want to generate a unique new action with its own preconditions and
        // effects

        ArrayList<CertifiedPredicate> preconditionsMacroAction = new ArrayList<CertifiedPredicate>();
        HashSet<CertifiedPredicate> currentStateOfTheWorld = new HashSet<CertifiedPredicate>();

        HashSet<CertifiedPredicate> predicatesToRemove = new HashSet<CertifiedPredicate>();
        HashSet<CertifiedPredicate> predicatesToAdd = new HashSet<CertifiedPredicate>();
        Vector<Pair<ScopeVariable, ScopeVariable>> constrainsToBeInSameLiftedFamGroup = new Vector<Pair<ScopeVariable, ScopeVariable>>();


        for (int i = 0; i < this.macroAction.size(); i++) {

            // First, iterate over all the precondition of the current action
            if (i == 0) {
                // For the first action, we can directly add all the precondition into the precondition of the macro action
                // and into the state of the world
                for (CertifiedPredicate precondition : preconditionsAllActions.get(i)) {
                    preconditionsMacroAction.add(precondition);
                    currentStateOfTheWorld.add(precondition);
                }
            }
            else {
                // Iterate over all preconditions of the current action
                for (CertifiedPredicate precondition : preconditionsAllActions.get(i)) {
                    
                    // If the precondition is already into the state of the world, there is no need to add it into the precondition of the macro action
                    boolean preconditionAlreadyInStateOfTheWorld = false;
                    for (CertifiedPredicate predCurrentStateOfTheWorld : currentStateOfTheWorld) {
                        if (predCurrentStateOfTheWorld.isEqualsTo(precondition)) {
                            preconditionAlreadyInStateOfTheWorld = true;
                            break;
                        }
                    }

                    if (preconditionAlreadyInStateOfTheWorld) {
                        continue;
                    }

                    // Else we need to try to unify the precondition with each predicate of the state of the world
                    boolean canUnify = false;
                    for (CertifiedPredicate predCurrentStateOfTheWorld : currentStateOfTheWorld) {

                        // If this is the same predicate  with the same values, from a predicate of the state of the world
                        // There is no need to add it as a precondition of the macro action
                        if (predCurrentStateOfTheWorld.isEqualsTo(precondition)) {
                            canUnify = false;
                            break;
                        }
                        else if (predCurrentStateOfTheWorld.predicateName.equals(precondition.predicateName)) {
                            // We must indicate that the parameters of the predicate must be different
                            System.out.println("MUST IMPLEMENT HERE !");
                            System.exit(1);
                        }   
                    }
                    if (!canUnify) {
                        // We cannot unify the precondition with any predicate of the state of the world
                        // We add it into the precondition of the macro action
                        preconditionsMacroAction.add(precondition);
                        predicatesToAdd.add(precondition);
                    }
                    int b = 0;
                }
                currentStateOfTheWorld.addAll(predicatesToAdd);
                predicatesToAdd.clear();
            }

            predicatesToAdd.clear();
            predicatesToRemove.clear();

            // Then iterate over all the effects of the current action
            // First, iterate over all the negative effects
            for (CertifiedPredicate negEffect : effectsAllActions.get(i)) {
                if (negEffect.isPositive) {
                    continue;
                }

                // Try to unify the effect with each predicate of the state of the world
                for (CertifiedPredicate predCurrentStateOfTheWorld : currentStateOfTheWorld) {

                    // If this is the opposite predicate  with the same predicate, from a predicate of the state of the world, 
                    // we can remove it from the state of the world
                    if (predCurrentStateOfTheWorld.isOppositeTo(negEffect)) {
                        predicatesToRemove.add(predCurrentStateOfTheWorld);
                        // continue;
                    }

                    // Now, we can add this predicate into the state of the world
                    predicatesToAdd.add(negEffect);
                   
                }
                currentStateOfTheWorld.addAll(predicatesToAdd);
                currentStateOfTheWorld.removeAll(predicatesToRemove);
            }

            predicatesToAdd.clear();
            predicatesToRemove.clear();





            // Now, we add the positive effect into the state of the world
            for (CertifiedPredicate posEffect : effectsAllActions.get(i)) {
                if (!posEffect.isPositive) {
                    continue;
                }

                if (currentStateOfTheWorld.size() == 0) {
                    predicatesToAdd.add(posEffect);
                    continue;
                }

                // Try to unify the effect with each predicate of the state of the world
                for (CertifiedPredicate predCurrentStateOfTheWorld : currentStateOfTheWorld) {

                    // If this is the opposite predicate  with the same predicate, from a predicate of the state of the world, 
                    // we can remove it from the state of the world
                    if (predCurrentStateOfTheWorld.isOppositeTo(posEffect)) {
                        predicatesToRemove.add(predCurrentStateOfTheWorld);
                        continue;
                    }

                    // Now, we can add this predicate into the state of the world
                    predicatesToAdd.add(posEffect);
                
                } 
            }  
            
            currentStateOfTheWorld.addAll(predicatesToAdd);
            currentStateOfTheWorld.removeAll(predicatesToRemove);

            predicatesToAdd.clear();
            predicatesToRemove.clear();
        }

        this.preconditionPredicates.clear();
        this.effectPredicates.clear();
        this.outputCertifiedPredicates.clear();

        this.preconditionPredicates.addAll(preconditionsMacroAction);
        // Add all the state of the world into the effect of the macro action
        this.outputCertifiedPredicates.addAll(currentStateOfTheWorld);
        // Add all the effects as well (which correspond to all the predicate of the output certifier predicate which are not in the precondition)

        for (CertifiedPredicate outputCertifiedPredicate : this.outputCertifiedPredicates) {
            boolean isAlreadyInPrecondition = false;
            for (CertifiedPredicate precondition : this.preconditionPredicates) {
                if (precondition.isEqualsTo(outputCertifiedPredicate)) {
                    isAlreadyInPrecondition = true;
                    break;
                }
            }
            if (!isAlreadyInPrecondition) {
                this.effectPredicates.add(outputCertifiedPredicate);
            }
        }

        int a = 0;
    }

    // Will be useful to know if we must check the initial predicate to satisfy a
    // precondition
    public void getAllRootsNodeThatCanLedToThisFlowFromParents(HashSet<LiftedFlow> allParentsNode) {
        for (LiftedFlow parentNode : allParentsNode) {
            this.rootsNodesWhichCanLedToThisFlow.addAll(parentNode.rootsNodesWhichCanLedToThisFlow);
        }
    }

    public void computeInputCertifiedPredicatesFromParents(HashSet<LiftedFlow> allParentsNode) {

        int numParents = allParentsNode.size();

        boolean isLastParentNode = false;
        int idxParent = 0;

        HashSet<CertifiedPredicate> allHeritateCertPredToAdd = new HashSet<CertifiedPredicate>();

        for (LiftedFlow parentNode : allParentsNode) {

            HashSet<CertifiedPredicate> certPredsToAdd = new HashSet<CertifiedPredicate>();

            idxParent++;
            if (idxParent == allParentsNode.size()) {
                isLastParentNode = true;
            }

            // Add the certified predicate only if we do not contain it ourself
            // and if we do not contains the opposite of this predicate ourself
            for (CertifiedPredicate certPredParent : parentNode.outputCertifiedPredicates) {

                // Check if we do contains this certified predicate
                boolean alreadyContainsCertifiedPred = false;
                for (CertifiedPredicate ownCertifiedPredicate : this.inputCertifiedPredicates) {
                    if (ownCertifiedPredicate.isEqualsTo(certPredParent)) {
                        alreadyContainsCertifiedPred = true;
                        break;
                    }
                }

                // TODO what to do if the certified predicate is opposite to
                // out own input certified predicate (i.e, this path is impossible ?)

                if (alreadyContainsCertifiedPred) {
                    continue;
                }

                // Now we can add the certified predicate into our heritate certified predicate
                // If we already have a identical certified predicate that we have heritate from
                // another
                // parent, update it to tell that we can add this certified predicate from this
                // parent as well
                boolean predicateIsAlreadyHeritate = false;
                for (CertifiedPredicate heritateCertifiedPred : allHeritateCertPredToAdd) {
                    if (heritateCertifiedPred.isEqualsTo(certPredParent)) {
                        heritateCertifiedPred.certifiers.add(parentNode);

                        // Little optimization here, if all of our parent can certified a predicate, we
                        // remove it
                        // from the heritate certified predicates and put it into our own certified
                        // predicates
                        // (because any path from the inital action to this node will mandatory
                        // certified this predicate)
                        if (isLastParentNode && heritateCertifiedPred.certifiers.size() == allParentsNode.size()
                                && heritateCertifiedPred.certifiers.equals(allParentsNode)) {
                            heritateCertifiedPred.certifiers.clear();
                            heritateCertifiedPred.certifiers.add(this);
                        }

                        predicateIsAlreadyHeritate = true;
                        break;
                    }
                }

                if (!predicateIsAlreadyHeritate) {
                    // Create our new certified predicate
                    CertifiedPredicate heritateCertifiedPred;
                    // If we only have one parent and it is him who
                    // certify a predicate, we can certified it ourself:
                    // add this certified predicate as our own certified predicate (TODO not so
                    // simple here...)
                    if (numParents == 1 && certPredParent.certifiers.contains(parentNode)) {
                        heritateCertifiedPred = new CertifiedPredicate(certPredParent.predicateName,
                                certPredParent.isPositive, certPredParent.scope, this);

                        heritateCertifiedPred.setConstrainsScope(certPredParent.outputConstrainsScope);
                        certPredsToAdd.add(heritateCertifiedPred);
                    } else {
                        heritateCertifiedPred = new CertifiedPredicate(certPredParent.predicateName,
                                certPredParent.isPositive, certPredParent.scope, certPredParent.certifiers);
                        heritateCertifiedPred.setConstrainsScope(certPredParent.outputConstrainsScope);
                        certPredsToAdd.add(heritateCertifiedPred);
                    }
                }
            }
            allHeritateCertPredToAdd.addAll(certPredsToAdd);
        }
        this.inputCertifiedPredicates.addAll(allHeritateCertPredToAdd);
    }


    public void determinateHowToResolvePreconditionsWithoutLFG2(HashSet<CertifiedPredicate> pseudoFactsToGround, HashSet<String> varsToDefine, HashSet<String> pseudoFactsToDefine, HashSet<String> groundFactsToDefine, HashSet<String> pseudoFactsAlreadyDefined) {


        StringBuilder preconditionsSMT_sb = new StringBuilder();
        StringBuilder preconditionSMTStaticPredicates_sb = new StringBuilder();

        if (this.preconditionPredicates.size() == 0) {
            return;
        }

        preconditionsSMT_sb.append("(assert (=> " + this.getUniqueName() + " (and ");

        boolean atLeastOnePreconditionNotStatic = false;

        for (CertifiedPredicate precondition : this.preconditionPredicates) {

            System.out.println("Node: " + this.getUniqueName() + " Precondition: " + precondition);

            if (precondition.predicateName.equals("=")) {

                atLeastOnePreconditionNotStatic = true;

                if (!precondition.isPositive) {
                    preconditionsSMT_sb.append("(not (or ");
                }

                boolean atLeastOneEquality = false;

                // Iterate over the objects possible for the first argument
                for (String obj : precondition.scope.get(0).getPossibleValueVariable()) {
                    // Check if the object is in the possible value for the second argument
                    if (precondition.scope.get(1).getPossibleValueVariable().contains(obj)) {
                        atLeastOneEquality = true;
                        if (precondition.scope.get(0).isConstant()) {
                            preconditionsSMT_sb.append(precondition.scope.get(1).getUniqueName() + "__" + obj + " ");
                        }
                        else if (precondition.scope.get(1).isConstant()) {
                            preconditionsSMT_sb.append(precondition.scope.get(0).getUniqueName() + "__" + obj + " ");
                        } else {
                            preconditionsSMT_sb.append("(and " + precondition.scope.get(0).getUniqueName() + "__" + obj + " " + precondition.scope.get(1).getUniqueName() + "__" + obj + ") ");
                        }
                    }
                }

                if (!atLeastOneEquality) {
                    preconditionsSMT_sb.append("false ");
                }

                if (!precondition.isPositive) {
                    preconditionsSMT_sb.append(")) ");
                }

                continue;
            }
            // Add the precondtion into the list of predicates to ground if it not already here and if it is not static and if it is not trivially true
            if (UtilsStructureProblem.staticPredicates.contains(precondition.predicateName)) {

                // If it is a static predicate, we do not need to ground it, and the rule is a little different (see rule 22/23 of the lilotane paper)
                // In resume, we enforce that some valid substitions set must hold
                HashSet<ArrayList<String>> validSubstitutions = UtilsStructureProblem.getAllObjectsForStaticPredicate(precondition.predicateName);
                boolean atLeastOneValidSubstitutionIsPossible = false;
                StringBuilder preconditionSMTStaticPredicate_sb = new StringBuilder();
                preconditionSMTStaticPredicate_sb.append("; Static Precondition: " + precondition + "\n");

                if (validSubstitutions.size() == 0) {
                    // By definition, if there is no valid substitution, the precondition is always false
                    // so this path is impossible
                    preconditionsSMT_sb.append("(not " + this.getUniqueName() + ") ");
                    continue;
                }

                if (precondition.isPositive) {
                    preconditionSMTStaticPredicate_sb.append("(assert (=> " + this.getUniqueName() + " (or ");
                    for (ArrayList<String> validSubstitution : validSubstitutions) {
                        
                        boolean substitutionIsValid = true;
                        // First check that this substitution is valid
                        for (int paramIdx = 0; paramIdx < precondition.scope.size(); paramIdx++) {
                            // Check that the intersection of the objects of the scope variable and the objects of the valid substitution is not empty
                            if (!precondition.scope.get(paramIdx).getPossibleValueVariable().contains(validSubstitution.get(paramIdx))) {
                                // It means that the substitution is not valid
                                substitutionIsValid = false;
                                break;
                            }
                        }
                        if (!substitutionIsValid) {
                            continue;
                        }

                        // If we are here, it means that the substitution is valid
                        atLeastOneValidSubstitutionIsPossible = true;
                        // Enforce the rule that the substitution must hold
                        preconditionSMTStaticPredicate_sb.append("(and ");
                        boolean allParametersAreConstants = true;
                        for (int paramIdx = 0; paramIdx < precondition.scope.size(); paramIdx++) {
                            if (precondition.scope.get(paramIdx).isConstant()) {
                                continue;
                            }
                            allParametersAreConstants = false;
                            preconditionSMTStaticPredicate_sb.append(precondition.scope.get(paramIdx).getUniqueName() + "__" + validSubstitution.get(paramIdx) + " ");
                        }
                        if (allParametersAreConstants) {
                            preconditionSMTStaticPredicate_sb.append("true");
                        }
                        preconditionSMTStaticPredicate_sb.append(") ");
                    }

                    if (!atLeastOneValidSubstitutionIsPossible) {
                        preconditionSMTStaticPredicate_sb.append("false");
                    }
                    preconditionSMTStaticPredicate_sb.append(")))\n");
                } else {
                    preconditionSMTStaticPredicate_sb.append("(assert (=> " + this.getUniqueName() + " (and ");
                    for (ArrayList<String> validSubstitution : validSubstitutions) {
                        
                        boolean substitutionIsValid = true;
                        // First check that this substitution is valid
                        for (int paramIdx = 0; paramIdx < precondition.scope.size(); paramIdx++) {
                            // Check that the intersection of the objects of the scope variable and the objects of the valid substitution is not empty
                            if (!precondition.scope.get(paramIdx).getPossibleValueVariable().contains(validSubstitution.get(paramIdx))) {
                                // It means that the substitution is not valid
                                substitutionIsValid = false;
                                break;
                            }
                        }
                        if (!substitutionIsValid) {
                            continue;
                        }

                        // If we are here, it means that the substitution is valid
                        atLeastOneValidSubstitutionIsPossible = true;
                        // Enforce the rule that the substitution must hold
                        preconditionSMTStaticPredicate_sb.append("(not (and ");
                        boolean allParametersAreConstants = true;
                        for (int paramIdx = 0; paramIdx < precondition.scope.size(); paramIdx++) {
                            if (precondition.scope.get(paramIdx).isConstant()) {
                                continue;
                            }
                            allParametersAreConstants = false;
                            preconditionSMTStaticPredicate_sb.append(precondition.scope.get(paramIdx).getUniqueName() + "__" + validSubstitution.get(paramIdx) + " ");
                        }
                        if (allParametersAreConstants) {
                            preconditionSMTStaticPredicate_sb.append("true");
                        }
                        preconditionSMTStaticPredicate_sb.append(")) ");
                    }

                    if (!atLeastOneValidSubstitutionIsPossible) {
                        preconditionSMTStaticPredicate_sb.append("true");
                    }
                    preconditionSMTStaticPredicate_sb.append(")))\n"); 
                }
                preconditionSMTStaticPredicates_sb.append(preconditionSMTStaticPredicate_sb.toString());
            }
            else {

                atLeastOnePreconditionNotStatic = true;

                // Get the timestep
                int timeStep = this.stepFromRoot;
                if (precondition.isGroundFact()) {
                    if (!LiftedTreePathConfig.useSASPlusEncoding) {
                        // Get the last time that this ground fact was defined
                        ArrayList<String> groundParams = new ArrayList<String>();
                        for (ScopeVariable scopeVar : precondition.scope) {
                            groundParams.add(scopeVar.getPossibleValueVariable().iterator().next());
                        }
                        timeStep = UtilsStructureProblem.getLastTimePredicateDefined(precondition.predicateName, groundParams);
                    }
                }

                // Add this pseudo fact to the list of pseudo facts to define (only if it is not already in it)
                String namePseudoFactWithTimeStep = precondition.toSmt(timeStep);

                if (!pseudoFactsAlreadyDefined.contains(namePseudoFactWithTimeStep)) {
                    pseudoFactsAlreadyDefined.add(namePseudoFactWithTimeStep);
                    // No need to add it if it is a ground fact and we do not use SASPlus encoding, since there is nothing to ground in this case
                    if (!precondition.isGroundFact() || LiftedTreePathConfig.useSASPlusEncoding) {
                        pseudoFactsToGround.add(precondition);
                        pseudoFactsToDefine.add(namePseudoFactWithTimeStep);
                    } else {
                        groundFactsToDefine.add(namePseudoFactWithTimeStep);
                    }
                }
                





                // if (LiftedTreePathConfig.useSASPlusEncoding && precondition.isGroundFact()) {
                //    Directly replace the ground fact by its 
                // }

                varsToDefine.add(namePseudoFactWithTimeStep);
                if (!precondition.isPositive) {
                    preconditionsSMT_sb.append("(not " + namePseudoFactWithTimeStep + ") ");
                } else {
                    preconditionsSMT_sb.append(namePseudoFactWithTimeStep + " ");
                }
            }

            int a = 0;
        }

        if (!atLeastOnePreconditionNotStatic) {
            preconditionsSMT_sb.append("true");
        }

        preconditionsSMT_sb.append(")))\n");

        this.preconditionsSMT = preconditionsSMT_sb.toString();
        if (preconditionSMTStaticPredicates_sb.length() > 0) {
            this.preconditionsSMT += preconditionSMTStaticPredicates_sb.toString();
        }
        int a = 0;
    }


    public void determinateHowToResolvePreconditionsWithLFG2(HashSet<CertifiedPredicate> pseudoFactsToGround, HashSet<String> varsToDefine, HashSet<CertifiedPredicate> pseudoFactsToDefine, HashSet<String> groundFactsToDefine) {


        StringBuilder preconditionsSMT_sb = new StringBuilder();
        StringBuilder preconditionSMTStaticPredicates_sb = new StringBuilder();

        if (this.preconditionPredicates.size() == 0) {
            return;
        }

        preconditionsSMT_sb.append("(assert (=> " + this.getUniqueName() + " (and ");

        for (CertifiedPredicate precondition : this.preconditionPredicates) {

            System.out.println("Node: " + this.getUniqueName() + " Precondition: " + precondition);

            if (precondition.predicateName.equals("=")) {

                if (!precondition.isPositive) {
                    preconditionsSMT_sb.append("(not (or ");
                }

                // Iterate over the objects possible for the first argument
                for (String obj : precondition.scope.get(0).getPossibleValueVariable()) {
                    // Check if the object is in the possible value for the second argument
                    if (precondition.scope.get(1).getPossibleValueVariable().contains(obj)) {
                        preconditionsSMT_sb.append("(= " + precondition.scope.get(0).getUniqueName() + "__" + obj + " " + precondition.scope.get(1).getUniqueName() + "__" + obj + ") ");
                    }
                }

                if (!precondition.isPositive) {
                    preconditionsSMT_sb.append(")) ");
                }

                continue;
            }
            // Add the precondtion into the list of predicates to ground if it not already here and if it is not static and if it is not trivially true
            if (UtilsStructureProblem.staticPredicates.contains(precondition.predicateName)) {

                // If it is a static predicate, we do not need to ground it, and the rule is a little different (see rule 22/23 of the lilotane paper)
                // In resume, we enforce that some valid substitions set must hold
                HashSet<ArrayList<String>> validSubstitutions = UtilsStructureProblem.getAllObjectsForStaticPredicate(precondition.predicateName);
                boolean atLeastOneValidSubstitutionIsPossible = false;
                StringBuilder preconditionSMTStaticPredicate_sb = new StringBuilder();
                preconditionSMTStaticPredicate_sb.append("; Static Precondition: " + precondition + "\n");

                if (precondition.isPositive) {
                    preconditionSMTStaticPredicate_sb.append("(assert (=> " + this.getUniqueName() + " (or ");
                    for (ArrayList<String> validSubstitution : validSubstitutions) {
                        
                        boolean substitutionIsValid = true;
                        // First check that this substitution is valid
                        for (int paramIdx = 0; paramIdx < precondition.scope.size(); paramIdx++) {
                            // Check that the intersection of the objects of the scope variable and the objects of the valid substitution is not empty
                            if (!precondition.scope.get(paramIdx).getPossibleValueVariable().contains(validSubstitution.get(paramIdx))) {
                                // It means that the substitution is not valid
                                substitutionIsValid = false;
                                break;
                            }
                        }
                        if (!substitutionIsValid) {
                            continue;
                        }

                        // If we are here, it means that the substitution is valid
                        atLeastOneValidSubstitutionIsPossible = true;
                        // Enforce the rule that the substitution must hold
                        preconditionSMTStaticPredicate_sb.append("(and ");
                        boolean allParametersAreConstants = true;
                        for (int paramIdx = 0; paramIdx < precondition.scope.size(); paramIdx++) {
                            if (precondition.scope.get(paramIdx).isConstant()) {
                                continue;
                            }
                            allParametersAreConstants = false;
                            preconditionSMTStaticPredicate_sb.append(precondition.scope.get(paramIdx).getUniqueName() + "__" + validSubstitution.get(paramIdx) + " ");
                        }
                        if (allParametersAreConstants) {
                            preconditionSMTStaticPredicate_sb.append("true");
                        }
                        preconditionSMTStaticPredicate_sb.append(") ");
                    }
                    preconditionSMTStaticPredicate_sb.append(")))\n");
                } else {
                    preconditionSMTStaticPredicate_sb.append("(assert (=> " + this.getUniqueName() + " (and ");
                    for (ArrayList<String> validSubstitution : validSubstitutions) {
                        
                        boolean substitutionIsValid = true;
                        // First check that this substitution is valid
                        for (int paramIdx = 0; paramIdx < precondition.scope.size(); paramIdx++) {
                            // Check that the intersection of the objects of the scope variable and the objects of the valid substitution is not empty
                            if (!precondition.scope.get(paramIdx).getPossibleValueVariable().contains(validSubstitution.get(paramIdx))) {
                                // It means that the substitution is not valid
                                substitutionIsValid = false;
                                break;
                            }
                        }
                        if (!substitutionIsValid) {
                            continue;
                        }

                        // If we are here, it means that the substitution is valid
                        atLeastOneValidSubstitutionIsPossible = true;
                        // Enforce the rule that the substitution must hold
                        preconditionSMTStaticPredicate_sb.append("(not (and ");
                        boolean allParametersAreConstants = true;
                        for (int paramIdx = 0; paramIdx < precondition.scope.size(); paramIdx++) {
                            if (precondition.scope.get(paramIdx).isConstant()) {
                                continue;
                            }
                            allParametersAreConstants = false;
                            preconditionSMTStaticPredicate_sb.append(precondition.scope.get(paramIdx).getUniqueName() + "__" + validSubstitution.get(paramIdx) + " ");
                        }
                        if (allParametersAreConstants) {
                            preconditionSMTStaticPredicate_sb.append("true");
                        }
                        preconditionSMTStaticPredicate_sb.append(")) ");
                    }

                    if (!atLeastOneValidSubstitutionIsPossible) {
                        preconditionSMTStaticPredicate_sb.append("true");
                    }
                    preconditionSMTStaticPredicate_sb.append(")))\n"); 
                }
                preconditionSMTStaticPredicates_sb.append(preconditionSMTStaticPredicate_sb.toString());
            }
            else {
                boolean shouldAddIntoPseudoFactsToGround = true;
                String namePseudoFactPrecondition = precondition.toSmt(0);
                for (CertifiedPredicate pseudoFactToGround : pseudoFactsToGround) {
                    if (pseudoFactToGround.toSmt(0).equals(namePseudoFactPrecondition)) {
                        shouldAddIntoPseudoFactsToGround = false;
                        break;
                    }
                }

                if (shouldAddIntoPseudoFactsToGround) {
                    pseudoFactsToGround.add(precondition);
                }
            
                if (precondition.isGroundFact()) {
                    groundFactsToDefine.add(precondition.toSmt(this.getMaxStepFromRootNode()));
                } else {
                    // Add this pseudo fact to the list of pseudo facts to define (only if it is not already in it)
                    boolean alreadyIn = false;
                    for (CertifiedPredicate certPredAlreadyDefined : pseudoFactsToDefine) {
                        if (certPredAlreadyDefined.isEqualOrOppositeTo(precondition)) {
                            alreadyIn = true;
                            break;
                        }   
                    }
                    if (!alreadyIn) {
                        pseudoFactsToDefine.add(precondition);
                    }
                } 

                // Get the timestep
                int timeStep = this.stepFromRoot;
                if (precondition.isGroundFact()) {
                    // Get the last time that this ground fact was defined
                    ArrayList<String> groundParams = new ArrayList<String>();
                    for (ScopeVariable scopeVar : precondition.scope) {
                        groundParams.add(scopeVar.getPossibleValueVariable().iterator().next());
                    }
                    timeStep = UtilsStructureProblem.getLastTimePredicateDefined(precondition.predicateName, groundParams);
                }

                String predNameAndTimeStep = precondition.toSmt(timeStep);
                varsToDefine.add(predNameAndTimeStep);
                if (!precondition.isPositive) {
                    preconditionsSMT_sb.append("(not " + predNameAndTimeStep + ") ");
                } else {
                    preconditionsSMT_sb.append(predNameAndTimeStep + " ");
                }
            }

            int a = 0;
        }

        preconditionsSMT_sb.append(")))\n");

        this.preconditionsSMT = preconditionsSMT_sb.toString();
        if (preconditionSMTStaticPredicates_sb.length() > 0) {
            this.preconditionsSMT += preconditionSMTStaticPredicates_sb.toString();
        }
        int a = 0;
    }




    public void determinateHowToResolveEffectsWithoutLFG3(HashSet<CertifiedPredicate> pseudoFactsToGround, 
    HashSet<String> varsToDefine, 
    HashSet<String> pseudoFacstToDefine, 
    HashSet<String> groundFactsToDefine,
    HashMap<Integer, HashMap<LiftedFlow, HashSet<CertifiedPredicate>>> allPosPredicatesWhichCanBeChangedByThisAction, 
    HashMap<Integer, HashMap<LiftedFlow, HashSet<CertifiedPredicate>>> allNegPredicatesWhichCanBeChangedByThisAction, 
    HashSet<String> pseudoFactsAlreadyDefined) {

        StringBuilder effectsSMT_sb = new StringBuilder();

        if (this.effectPredicates.size() == 0) {
            return;
        }

        effectsSMT_sb.append("(assert (=> " + this.getUniqueName() + " (and ");

        for (CertifiedPredicate effect : this.effectPredicates) {

            System.out.println("Node: " + this.getUniqueName() + " Effect: " + effect);

            if (effect.predicateName.equals("=")) {

                System.out.println("Handle the case of = for the effect: " + effect);
                System.exit(1);
            }
            // Add the effect into the list of predicates to ground if it not already here
            String predNameAndTimeStep = effect.toSmt(this.stepFromRoot + 1);

            if (!pseudoFactsAlreadyDefined.contains(predNameAndTimeStep)) {
                pseudoFactsAlreadyDefined.add(predNameAndTimeStep);
                // No need to define the pseudo fact if it is a ground fact (and we are not using the SAS+ encoding)
                if (!effect.isGroundFact() || LiftedTreePathConfig.useSASPlusEncoding) {
                    pseudoFactsToGround.add(effect);
                    varsToDefine.add(predNameAndTimeStep);
                    pseudoFacstToDefine.add(predNameAndTimeStep);
                } else {
                    groundFactsToDefine.add(predNameAndTimeStep);
                }
            }
            

            if (!effect.isPositive) {
                effectsSMT_sb.append("(not " + predNameAndTimeStep + ") ");
            } else {
                effectsSMT_sb.append(predNameAndTimeStep + " ");
            }

            // Indicate that this predicate can be changed by this action

            // First, find all the ground predicate which can be represented by this certifiedPredicate
            ArrayList<ArrayList<String>> allPossibleGrounding = UtilsStructureProblem.getAllPossibleCombinaisonsOfCertifiedPredicate(effect);

            // Now, we iterate over all the possible grounding, and indicate that this flow may change this predicate (with this effect)
            for (ArrayList<String> possibleGrounding : allPossibleGrounding) {
                // Get the id of this predicate (not the same ID for a negative predicate and its positive conterpart)
                int id = UtilsStructureProblem.getPredicateID(effect.predicateName, possibleGrounding);
                if (effect.isPositive && !allPosPredicatesWhichCanBeChangedByThisAction.containsKey(id)) {
                    allPosPredicatesWhichCanBeChangedByThisAction.put(id, new HashMap<LiftedFlow, HashSet<CertifiedPredicate>>());
                }
                if (!effect.isPositive && !allNegPredicatesWhichCanBeChangedByThisAction.containsKey(id)) {
                    allNegPredicatesWhichCanBeChangedByThisAction.put(id, new HashMap<LiftedFlow, HashSet<CertifiedPredicate>>());
                }
                // Add the pair (this flow, this effect)
                if (effect.isPositive) {
                    // Add the effect to the list of effects that can change this predicate
                    if (!allPosPredicatesWhichCanBeChangedByThisAction.get(id).containsKey(this)) {
                        allPosPredicatesWhichCanBeChangedByThisAction.get(id).put(this, new HashSet<CertifiedPredicate>());
                    }
                    allPosPredicatesWhichCanBeChangedByThisAction.get(id).get(this).add(effect);
                }
                else {
                    // Add the effect to the list of effects that can change this predicate
                    if (!allNegPredicatesWhichCanBeChangedByThisAction.get(id).containsKey(this)) {
                        allNegPredicatesWhichCanBeChangedByThisAction.get(id).put(this, new HashSet<CertifiedPredicate>());
                    }
                    allNegPredicatesWhichCanBeChangedByThisAction.get(id).get(this).add(effect);
                }
            }
            

            int a = 0;
        }

        effectsSMT_sb.append(")))\n");

        this.effectsSMT = effectsSMT_sb.toString();
        int a = 0;
    }


    /**
     * A predicate is SAS+ pruned, if whatever the value that takes the scope of the
     * predicate to check,
     * there is already a predicate in the effects that is among the same lifted fam
     * group
     * 
     * @param predicateToCheck
     * @param liftedFamGroup
     * @return
     */
    public boolean predicateCanBeSASPlusPruned(CertifiedPredicate predicateToCheck, Candidate liftedFamGroup,
            AtomCandidate atomThatCanBeBound) {

        HashSet<AtomVariable> varsBoundByPredicateToCheck = new HashSet<AtomVariable>();

        // First bound the predicate to check
        for (int argi = 0; argi < predicateToCheck.scope.size(); argi++) {
            AtomVariable var = liftedFamGroup.variables.get(atomThatCanBeBound.paramsId.get(argi));

            // If the variable is a counted variable, it can take any value, there is no
            // need to bound
            if (var.isCountedVar) {
                continue;
            }
            // If the predicate to check can take multiple value for this argument, and the
            // lifted fam
            // group can only takes one argument, then we cannot check for lifte fam group
            // here...
            // e.g: predicate to check: in {pkg_0, pkg_1} {truck_0, truck_1} and lifted fam
            // group is (in V0: pkg C0: truck}
            // we can have as effect both in pkg_0 truck_0 and in pkg_1 truck_1)
            else if (predicateToCheck.scope.get(argi).getPossibleValueVariable().size() > 1) {

                // Here we can bound the variable with the name of the scope value.
                var.value = predicateToCheck.scope.get(argi).getUniqueName();
                varsBoundByPredicateToCheck.add(var);
            } else {
                // Bound the variable
                var.value = predicateToCheck.scope.get(argi).getPossibleValueVariable().iterator().next();
                varsBoundByPredicateToCheck.add(var);
            }
        }

        // Now, iterate over all effects of the lifted flow and see if another lifted
        // flow can be bound to this liftedFamGroup
        for (CertifiedPredicate outputCertifiedPredicate : this.outputCertifiedPredicates) {

            for (AtomCandidate atomCandidate : liftedFamGroup.mutexGroup) {
                if (atomCandidate.predSymbolName.equals(outputCertifiedPredicate.predicateName)) {

                    boolean canBeRepresentedByLiftedFamGroup = true;
                    // Check if the type of each arg is also identical
                    for (int argi = 0; argi < outputCertifiedPredicate.scope.size(); argi++) {
                        AtomVariable var = liftedFamGroup.variables.get(atomCandidate.paramsId.get(argi));
                        if (!var.typeName.equals(outputCertifiedPredicate.scope.get(argi).getType())) {
                            canBeRepresentedByLiftedFamGroup = false;
                            break;
                        }
                        // Bound the variable
                        if (var.isCountedVar) {
                            continue;
                        } else if (outputCertifiedPredicate.scope.get(argi).getPossibleValueVariable().size() > 1) {
                            String valueOutputCertifiedPredArgi = outputCertifiedPredicate.scope.get(argi)
                                    .getUniqueName();
                            // Check if the variable is correctly bound by the predicate to check
                            if (var.value != null && var.value.equals(valueOutputCertifiedPredArgi)) {
                                // It's correct here, we can continue
                                continue;
                            } else {
                                // The var is bound to another value... No correct here
                                canBeRepresentedByLiftedFamGroup = false;
                                break;
                            }
                        } else {
                            String valueOutputCertifiedPredArgi = outputCertifiedPredicate.scope.get(argi)
                                    .getPossibleValueVariable().iterator().next();
                            // Check if the variable is correctly bound by the predicate to check
                            if (var.value != null && var.value.equals(valueOutputCertifiedPredArgi)) {
                                // It's correct here, we can continue
                                continue;
                            } else {
                                // The var is bound to another value... No correct here
                                canBeRepresentedByLiftedFamGroup = false;
                                break;
                            }
                        }

                    }
                    if (!canBeRepresentedByLiftedFamGroup) {
                        continue;
                    }
                    // Else, it means that we already have a predicate of the lifted fam ground in
                    // output
                    // Clean the variable
                    for (AtomVariable varBound : varsBoundByPredicateToCheck) {
                        varBound.value = null;
                    }
                    return true;
                }
            }
        }

        // Clean the variables
        for (AtomVariable varBound : varsBoundByPredicateToCheck) {
            varBound.value = null;
        }
        return false;
    }

   
    /**
     * Return a string containing an action in easily readable format
     * 
     * @param a       The action to display in easily readable format
     * @param problem The problem to solve
     * @return A String representing the action in easily readable format
     */
    public String prettyDisplay(Problem problem) {
        StringBuilder flowToDisplay = new StringBuilder();
        flowToDisplay.append("Flow [");

        if (methodName != null) {
            flowToDisplay.append(methodName);
            for (int i = 0; i < this.scopeMethod.size(); i++) {
                flowToDisplay.append(" arg" + i + ": " + scopeMethod.get(i));
            }
        } else {
            for (int idx_action = 0; idx_action < this.macroAction.size(); idx_action++) {
                String actionName = this.macroAction.get(idx_action);
                flowToDisplay.append(actionName);
                for (int i = 0; i < this.scopeMacroAction.get(idx_action).size(); i++) {
                    flowToDisplay.append(" arg" + i + ": " + this.scopeMacroAction.get(idx_action).get(i));
                }
                if (idx_action != this.macroAction.size() - 1) {
                    flowToDisplay.append("->");
                }
            }
        }
        flowToDisplay.append("]");

        return flowToDisplay.toString();
    }

    @Override
    public String toString() {
        StringBuilder flowToDisplay = new StringBuilder();
        flowToDisplay.append(this.getUniqueName() + " [");

        if (methodName != null) {
            flowToDisplay.append(methodName);
            for (int i = 0; i < this.scopeMethod.size(); i++) {
                flowToDisplay
                        .append(" arg" + i + ": (" + scopeMethod.get(i).getUniqueName() + ") " + scopeMethod.get(i));
            }
        } else {
            for (int idx_action = 0; idx_action < this.macroAction.size(); idx_action++) {
                String actionName = this.macroAction.get(idx_action);
                flowToDisplay.append(actionName);
                for (int i = 0; i < this.scopeMacroAction.get(idx_action).size(); i++) {
                    flowToDisplay.append(" " + this.scopeMacroAction.get(idx_action).get(i));
                }
                if (idx_action != this.macroAction.size() - 1) {
                    flowToDisplay.append("->");
                }
            }
        }
        flowToDisplay.append("]");

        return flowToDisplay.toString();
    }

    public String getUniqueName() {
        StringBuilder uniqueFlowName = new StringBuilder();
        uniqueFlowName.append("FLOW_");



        //DEBUG, add the name of all the parents into the name of the flow

        // Indicate is the flow is an action or a method
        if (this.methodName == null) {
            uniqueFlowName.append("A_");
        } else {
            uniqueFlowName.append("M_");
        }

        StringBuilder parentsName = new StringBuilder();
        LiftedFlow parent = this.parentFlow;
        while (parent != null) {
            // The parent will be added in reverse order (and it is a method)
            parentsName.insert(0, parent.methodName + "-");
            parent = parent.parentFlow;
        }

        uniqueFlowName.append(parentsName);
        // END DEBUG



        if (this.methodName != null) {
            uniqueFlowName.append(this.methodName);
        } else {
            for (int idx_action = 0; idx_action < this.macroAction.size(); idx_action++) {
                String actionName = this.macroAction.get(idx_action);
                uniqueFlowName.append(actionName);
                if (idx_action != this.macroAction.size() - 1) {
                    uniqueFlowName.append("->");
                }
            }
        }

        // uniqueFlowName.append("_" + uniqueId);
        uniqueFlowName.append("%" + uniqueId);

        return uniqueFlowName.toString();
    }

    public int getMaxStepFromRootNode() {
        return this.stepFromRoot;
    }

    public void setMaxStepFromRootNode(int step) {
        this.stepFromRoot = step;
    }

    public void cleanInputAndOutputCertifiedPredicate() {
        this.inputCertifiedPredicates.clear();
        this.outputCertifiedPredicates.clear();
    }

    public void cleanPreconditionAndEffectsSMT() {
        this.preconditionsSMT = "";
        this.effectsSMT = "";
    }
}
