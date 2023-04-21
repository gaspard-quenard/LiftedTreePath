package treerex.hydra.HelperFunctions;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.stream.Collectors;

import fr.uga.pddl4j.problem.operator.DefaultOrderingConstraintNetwork;

//Some utility functions
public class UtilFunctions {

    // returns a totally ordered list of task ids of "tasks" in an order that
    // satisfies the ordering "orderingConstraints"
    // VERY IMPORTANT NOTE: WE ASSUME THAT THIS FUNCTION IS DETERMINISTIC, because
    // first we use it to determine what values can a cell take when decomposing
    // layer L into layer L+1, and then we use it when applying Rules 13-14 of
    // TreeRex encoding. If the function is non-deterministic, rule 13-14 may create
    // a constraint that points to a wrong cell, if this
    // makes sense. If it doesn't make sense - check where totallyOrderedList
    // function is used, and
    // you'll figure it out
    public static List<Integer> totallyOrderedList(List<Integer> tasks,
            DefaultOrderingConstraintNetwork orderingConstraints) {
        List<List<String>> orderList = UtilFunctions
                .orderingConstraintsToStringList(orderingConstraints);
        // tmp stores the position of each task from "tasks" in the
        // "tasks_totallyOrdered"
        // we need this, because ordering constraints of task T and task T itself share
        // the same position index in their respective lists
        // even though we can find an index of any task from tasks_totallyOrdered in
        // tasks via .indexOf(), we need to remember that a network can have multiple
        // tasks that share the same id, but have different ordering constraints. For
        // example, we want to clean the room at the start and end of the plan. Both
        // actions have same ids, but different ordering constraints (first clean must
        // precede everyone, last clean should supercede everyone). indexOf() may
        // confuse which is which, which is why tmp will store the positions of every
        // action, rather than their ids.
        List<Integer> tmp = new ArrayList<>();

        // populate tmp
        for (int i = 0; i < tasks.size(); i++) {
            tmp.add(i);
        }

        // for every task
        for (int i = 0; i < orderList.size(); i++) {
            // go through all ordering relations
            for (int j = 0; j < orderList.get(i).size(); j++) {
                if (j != i) {
                    // if task j should be executed after task i
                    if (orderList.get(i).get(j).contains("1")) {
                        // System.out.println(tasks.get(i) + " < " + tasks.get(j));
                        // System.out.println(i + " < " + j);
                        // System.out.println(tmp);
                        // but if task j is positioned before task i
                        if (tmp.indexOf(j) < tmp.indexOf(i)) {
                            // put task j right after task i
                            // System.out.println("pre-delete:" + tmp);
                            tmp.remove(tmp.indexOf(j));
                            // System.out.println("post-delete:" + tmp);
                            tmp.add(tmp.indexOf(i), j);
                        }
                    }
                }

            }
        }

        // now that tmp contains the properly ordered indices, we can move the tasks
        // that correspond to these indices
        List<Integer> tasks_totallyOrdered = new ArrayList<>();

        for (int index : tmp) {
            tasks_totallyOrdered.add(tasks.get(index));
        }

        return tasks_totallyOrdered;
    }

    // Note: for every task i returns a list of 0/1. 1 indicates that a task j
    // happens after task i. 0 means that order doesnt matter
    static List<List<String>> orderingConstraintsToStringList(DefaultOrderingConstraintNetwork bv) {
        // TODO...
        // again, an ugly section, bcz when I implemented this, I didn't know how to
        // iterate through bitvector,
        // maybe improve. Shouldn't matter, because there aren't many ordering
        // constraints
        String unrefined = bv.toBitString();
        String[] unrefinedList = unrefined.split("\\r?\\n");
        List<List<String>> tmp = new ArrayList<>();
        for (String s : unrefinedList) {
            String[] tmp2 = s.split(" ");
            List<String> tmp3 = new ArrayList<>();
            for (String ss : tmp2) {
                tmp3.add(ss);
            }
            tmp.add(tmp3);
        }
        return tmp;

    }

    // HashSetToArray is expensive, but we use it only for debug, and only to
    // process the last layer
    // for pddl output, so is ok
    public static ArrayList<Integer> hashSetToArray(HashSet<Integer> input) {

        ArrayList<Integer> res = (ArrayList<Integer>) input.stream()
                .collect(Collectors.toList());

        return res;
    }
}
