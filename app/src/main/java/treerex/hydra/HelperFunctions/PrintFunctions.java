package treerex.hydra.HelperFunctions;

import java.util.List;

import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import treerex.hydra.Preprocessing.LiftedSasPlus.Strips2SasPlus;

public class PrintFunctions {
    public static String taskToString(int index, Problem problem) {
        Task t = problem.getTasks().get(index);
        String res = "(";

        res += problem.getParsedProblem().getTasks().get(0).getName() + " ";

        int[] params = t.getArguments();
        for (int i = 0; i < params.length; i++) {
            res += problem.getConstantSymbols().get(params[i]) + " ";
        }
        res += ")";
        System.out.println(res);
        return res;
    }

    public static String methodToString(int index, Problem problem) {
        Method m = problem.getMethods().get(index);
        String res = "(";
        res += m.getName() + " ";
        int[] params = m.getInstantiations();
        for (int i = 0; i < params.length; i++) {
            res += problem.getConstantSymbols().get(params[i]) + " ";
        }
        res += ")";
        // System.out.println(res);
        return res;
    }

    public static String actionToString(int index, Problem problem) {
        Action a = problem.getActions().get(index);

        String res = "";
        res += a.getName() + " ";
        int[] params = a.getInstantiations();
        for (int i = 0; i < params.length; i++) {
            res += problem.getConstantSymbols().get(params[i]) + " ";
        }
        res += "";
        // System.out.println(res);
        return res;
    }

    public static String cliqueToString(int cliqueId, Problem problem) {
        String tmp = "clique_" + cliqueId + " = ";
        List<Integer> predicates = Strips2SasPlus.cliques.get(cliqueId);
        for (Integer i : predicates) {
            tmp += predicateToString(i, problem) + " OR ";
        }
        tmp += "none-of-those";
        return tmp;
    }

    public static String predicateToString(int index, Problem problem) {
        Fluent f = problem.getFluents().get(index);
        String tmp = "";
        tmp += problem.getPredicateSymbols().get(f.getSymbol()) + "(";

        for (Integer i : f.getArguments()) {
            tmp += problem.getConstantSymbols().get(i) + ", ";
        }
        tmp += ")";
        return tmp;
    }
}
