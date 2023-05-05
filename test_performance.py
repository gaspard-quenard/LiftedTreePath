import matplotlib.pyplot as plt
import numpy as np
from matplotlib.transforms import Affine2D
import logging
import os
from typing import List, Tuple
import subprocess
from enum import Enum
import shlex
import time
import pandas as pd

PATH_BENCHMARKS = [
    ("/home/gaspard/LIG/Code/ipc2020-domains/total-order/Transport", 30),
    # ("/home/gaspard/LIG/Code/ipc2020-domains/total-order/AssemblyHierarchical", 5),
    ("/home/gaspard/LIG/Code/ipc2020-domains/total-order/Barman-BDI", 20),
    # ("/home/gaspard/LIG/Code/ipc2020-domains/total-order/Blocksworld-GTOHP", 20),
    ("/home/gaspard/LIG/Code/ipc2020-domains/total-order/Childsnack", 20),
    # ("/home/gaspard/LIG/Code/ipc2020-domains/total-order/Depots", 20),
    ("/home/gaspard/LIG/Code/ipc2020-domains/total-order/Factories-simple", 4),
    ("/home/gaspard/LIG/Code/ipc2020-domains/domains_panda/total-order/Gripper_new", 20),
    ("/home/gaspard/LIG/Code/ipc2020-domains/total-order/Hiking", 20),
    # ("/home/gaspard/LIG/Code/ipc2020-domains/domains_panda/total-order/Miconic", 20),
    ("/home/gaspard/LIG/Code/ipc2020-domains/total-order/Rover-GTOHP", 20),
    ("/home/gaspard/LIG/Code/ipc2020-domains/domains_panda/total-order/Rover-PANDA", 20),
    ("/home/gaspard/LIG/Code/ipc2020-domains/total-order/Satellite-GTOHP", 20),
    # ("/home/gaspard/LIG/Code/ipc2020-domains/total-order/Towers", 9),
    # ("/home/gaspard/LIG/Code/ipc2020-domains/domains_panda/total-order/Zenotravel", 20),
    # ("/home/gaspard/LIG/Code/ipc2020-domains/total-order/Woodworking", 20),
]

# Folder to write the results of the performance of the planner on the benchmarks
PATH_OUTPUT = "Results_benchmark_Lifted_tree_path"

# Command to build the library
BUILD_LIFTED_TREE_PATH = "./gradlew build"

# Launch the jar lib
LAUNCH_LIFTED_TREE_PATH = "./gradlew run"


# Timeout of the planner in second
TIMEOUT_S = 5 * 60


class Lifted_tree_path_config(Enum):
    CLASSIC = 0
    REUSE_SCOPE_VARS = 1


CONFIG_TO_USE = [
    Lifted_tree_path_config.CLASSIC,
    Lifted_tree_path_config.REUSE_SCOPE_VARS,
]

dict_config_to_command_line = {
    Lifted_tree_path_config.CLASSIC: "",
    Lifted_tree_path_config.REUSE_SCOPE_VARS: "--reuseScopeVar",
}

# dict_solver_to_command_line = {
#     Hydra_solver.SMT: "smt",
#     Hydra_solver.SMT_ENUMS: "smt",
#     Hydra_solver.CSP: "csp",
#     Hydra_solver.SAT: "sat",
# }

# dict_solver_to_parameters = {
#     Hydra_solver.SMT: "",
#     Hydra_solver.SMT_ENUMS: "smt_use_sorts",
#     Hydra_solver.CSP: "",
#     Hydra_solver.SAT: "",
# }


def compute_statistics_on_SMT_file(file: str):

    with open(file, 'r') as f:
        lines = f.readlines()
        lines = [line.strip() for line in lines]

    # First, determinate the number of actions
    # Each action is determinate with a line: (declare-const FLOW_

    actions = [line for line in lines if line.startswith('(declare-const FLOW_')]


    # Then determiane the number of scopes 
    # Each scope is determinate with a line: (declare-const SCOPE_, but should not contains __eq__ in the line

    scopes = [line for line in lines if line.startswith('(declare-const SCOPE_') and '__eq__' not in line]

    scope_equality = [line for line in lines if line.startswith('(declare-const SCOPE_') and '__eq__' in line]

    # Then determinate the number of unique scope (from the scopes variable)
    # Each unique scope is determinate with a line: (declare-const SCOPE_<ID_scope>

    unique_scopes = set()
    for scope_line in scopes:
        name_scope = scope_line.split(' ')[1].split('__')[0]
        unique_scopes.add(name_scope)

    # Print the results
    print('Number of actions: {}'.format(len(actions)))
    print('Number of scopes: {}'.format(len(scopes)))
    print('Number of unique scopes: {}'.format(len(unique_scopes)))
    print('Number of scope equality: {}'.format(len(scope_equality)))

    return len(actions), len(scopes), len(unique_scopes), len(scope_equality)


def extract_size_plan_from_output(output_command: str) -> int:
    """ Extract plan size from the output of command line which launch a planner. If no plan is found, return -1

    Args:
        output_command (str): stdout of the command line which launch a planner

    Returns:
        int: The size of the plan
    """

    all_lines_output = output_command.splitlines()

    # Check for each line if it contains the string "counted length of "
    for line in all_lines_output:
        if "counted length of " in line:
            size_plan_str = line.split()[-1][:-1]
            return int(size_plan_str)

    return -1


def find_if_plan_is_valid(output_command: str) -> bool:
    """ Find if the plan is valid from the output of command line which launch a planner. If no plan is found, return False

    Args:
        output_command (str): stdout of the command line which launch a planner

    Returns:
        bool: True if the plan is valid, False otherwise
    """

    all_lines_output = output_command.splitlines()

    # Check for each line if it contains the string "counted length of "
    for line in all_lines_output:
        if "Plan is valid !" in line:
            return True

    return False


def launch_planner(full_path_file_domain: str, full_path_file_problem: str, config_to_use: Lifted_tree_path_config) -> Tuple[List[str], float]:
    """ Launch the TreeRex planner with the configuration specified and return the plan if found as well as the total runtime of the planner

    Args:
        full_path_file_domain (str): Full path of the domain file
        full_path_file_problem (str): Full path of the problem file
        solver_touse: The solver to use

    Returns:
        Tuple[List[str], float]: A tuple where the first argument contains the plan (or None if no plan is found), and the second argument contains the total runtime of the planner)
    """

    # command = f"{LAUNCH_HYDRA} --args=\"{dict_solver_to_command_line[solver_to_use]} {full_path_file_domain} {full_path_file_problem} {dict_solver_to_parameters[solver_to_use]}\""
    command = f"{LAUNCH_LIFTED_TREE_PATH} --args=\"-d {full_path_file_domain} -p {full_path_file_problem} {dict_config_to_command_line[config_to_use]}\""

    logging.info(f"Command: {command}")

    begin_time_command = time.time()
    try:
        output = subprocess.run(
            shlex.split(command), check=True, stdout=subprocess.PIPE, universal_newlines=True, timeout=TIMEOUT_S)
        end_time_command = time.time()
        # size_plan = extract_size_plan_from_output(output_command=output.stdout)
        plan_is_valid = find_if_plan_is_valid(output_command=output.stdout)
    # except subprocess.TimeoutExpired:
    except Exception as e:
        logging.error(
            f"Failed to find a plan with exception: {type(e).__name__}")
        end_time_command = time.time()
        # size_plan = -1
        return (False, 0, 0,   0, 0, 0, 0)

    lines = output.stdout.split('\n')

    total_time_s = round(end_time_command - begin_time_command, 2)
    # Get as well the time use by the solver for finding the plan
    total_solver_time_s = -1
    total_execution_time_s = -1
    for line in lines:
        if "Total solver time:" in line:
            total_solver_time_s = float(line.split()[-2])
            total_solver_time_s = round(total_solver_time_s, 2)

        if "Total time execution:" in line:
            total_execution_time_s = float(line.split()[-2])
            total_execution_time_s = round(total_execution_time_s, 2)

    # Get some information about the file SMT generated
    path_smt_file = "/home/gaspard/LIG/Code/lifted_tree_path/app/LiftedTreePathFrameAxioms.SMT"
    num_actions, num_scopes_values, num_unique_scopes, num_scope_equals = compute_statistics_on_SMT_file(file=path_smt_file)

    return (plan_is_valid, total_execution_time_s, total_solver_time_s, num_actions, num_scopes_values, num_unique_scopes, num_scope_equals)


def build_lifted_tree_path() -> None:
    """
    Build the pddl4J library
    """

    output = subprocess.run(
        shlex.split(BUILD_LIFTED_TREE_PATH), check=True, stdout=subprocess.PIPE, universal_newlines=True, timeout=TIMEOUT_S)



# def generate_figures():
#     """Generate figures to compare the results of the planners on two metrics: the total time spent to find a plan on a problem and the size of the plan generated. 
#     For each benchmark, there will be 1 file generated containing 2 figures: one for each of these metrics. Figures will be saved in the folder PATH_OUTPUT.
#     """

#     # Get all csv files in the output folder
#     files_name = os.listdir(PATH_OUTPUT)
#     csv_files_names = [file for file in files_name if file.endswith('.csv')]

    


#     for file_name in csv_files_names:

#         print(f"Generate figure for {file_name}")

#         path_file_name = os.path.join(PATH_OUTPUT, file_name)

#         benchmark_name = file_name.split('.')[0]

#         data = pd.read_csv(path_file_name, comment='#')

#         # Get all the differents configurations that was used in the test
#         # solver_used = data['solver_used'].unique()

#         # We need to set the lilotane_totale run time to Nan and the lilotane_solver_time to Nan if the plan size is -1
#         data.loc[(data['total_execution_time'] == 0), 'total_solver_time'] = np.nan
#         data.loc[(data['total_execution_time'] == 0), 'solver_time'] = np.nan
#         data.loc[(data['total_execution_time'] == 0), 'total_execution_time'] = np.nan

#         data.loc[(data['total_execution_time'] == -1), 'total_solver_time'] = np.nan
#         data.loc[(data['total_execution_time'] == -1), 'solver_time'] = np.nan
#         data.loc[(data['total_execution_time'] == -1), 'total_execution_time'] = np.nan
        

#         # Create the configuration fot each
#         dict_conf_used_to_df = {}

#         fig = plt.figure()
#         fig.suptitle(f"On domain {benchmark_name}")

#         # for solver in SOLVERS_TO_USE:
#         #     dict_conf_used_to_df[solver] = data[data['solver_used'] == str(solver)]

#         # Sort data by hsp_total_run_time
#         # data.sort_values(["hsp_total_run_time"], axis=0,
#         #                  ascending=[True], inplace=True)

#         # Some clean of the data: Do not display bar of total run time of the planner if there is no plan found
#         # data.loc[(data['plan_size'] == 0),
#         #          'rantanplan_total_run_time'] = 0
#         # data.loc[(data['hsp_plan_size'] == 0), 'hsp_total_run_time'] = 0

#         # We will encode the initialization time, encoding time and solver time and total time in 4 different graph


#         fields_to_display = ["total_execution_time", "total_solver_time"]



#         a = 0

#         for field in fields_to_display:

#             abcisse = [name.split('.')[0] for name in data["problem_name"].tolist()]

#             if (a == 0):
#                 ax1 = fig.add_subplot(211)
#                 a += 1
#             else:
#                 ax1 = fig.add_subplot(212)
#             # for solver in dict_conf_used_to_df:

                
#             ordinate = data[field].tolist()

#             ax1.set_title(
#                 f"{field}")
#             ax1.set_xlabel("Problem")
#             ax1.set_ylabel("Time (s)")

#             ax1.scatter(abcisse, ordinate, label=str("lifted tree path"))
#             ax1.plot(abcisse, ordinate)

#             plt.legend(loc='upper left')

#         # plt.plot()
#         # plt.show()

#         path_figure = os.path.join(
#             PATH_OUTPUT, f"figure_result_{benchmark_name}.png")

#         logging.info(f"Save figure {path_figure}")

#         # Set the figure width enough to prevent xlabel from overlapping
#         fig.set_size_inches((18, 11), forward=False)

#         plt.savefig(path_figure)
#         plt.show()


def generate_figures():
    """Generate figures to compare the results of the planners on two metrics: the total time spent to find a plan on a problem and the size of the plan generated. 
    For each benchmark, there will be 1 file generated containing 2 figures: one for each of these metrics. Figures will be saved in the folder PATH_OUTPUT.
    """

    # Get all csv files in the output folder
    files_name = os.listdir(PATH_OUTPUT)
    csv_files_names = [file for file in files_name if file.endswith('.csv')]

    


    for file_name in csv_files_names:

        if (file_name != "Transport.csv"):
            continue

        print(f"Generate figure for {file_name}")



        path_file_name = os.path.join(PATH_OUTPUT, file_name)

        benchmark_name = file_name.split('.')[0]

        data = pd.read_csv(path_file_name, comment='#')

        # Get all the differents configurations that was used in the test
        solver_used = data['config_used'].unique()

        # We need to set the lilotane_totale run time to Nan and the lilotane_solver_time to Nan if the plan size is -1
        data.loc[(data['total_execution_time'] == 0), 'total_solver_time'] = np.nan
        data.loc[(data['total_execution_time'] == 0), 'solver_time'] = np.nan
        data.loc[(data['total_execution_time'] == 0), 'total_execution_time'] = np.nan

        data.loc[(data['total_execution_time'] == -1), 'total_solver_time'] = np.nan
        data.loc[(data['total_execution_time'] == -1), 'solver_time'] = np.nan
        data.loc[(data['total_execution_time'] == -1), 'total_execution_time'] = np.nan
        

        # Create the configuration fot each
        dict_conf_used_to_df = {}


        SOLVERS_TO_USE = ["Lifted_tree_path_config.CLASSIC", "Lifted_tree_path_config.REUSE_SCOPE_VARS", "lilotane"]

        for solver in SOLVERS_TO_USE:
            dict_conf_used_to_df[solver] = data[data['config_used'] == str(solver)]

        # Sort data by hsp_total_run_time
        # data.sort_values(["hsp_total_run_time"], axis=0,
        #                  ascending=[True], inplace=True)

        # Some clean of the data: Do not display bar of total run time of the planner if there is no plan found
        # data.loc[(data['plan_size'] == 0),
        #          'rantanplan_total_run_time'] = 0
        # data.loc[(data['hsp_plan_size'] == 0), 'hsp_total_run_time'] = 0

        # We will encode the initialization time, encoding time and solver time and total time in 4 different graph


        fields_to_display = ["total_execution_time", "Lifted_tree_path_config.REUSE_SCOPE_VARS", "total_solver_time"]



        a = 0

        fig, axs = plt.subplots(len(fields_to_display), 1, figsize=(8, 10))
        fig.suptitle(f"On domain {benchmark_name}")

        for i, field in enumerate(fields_to_display):
            for solver in dict_conf_used_to_df:
                abcisse = [name.split('.')[0] for name in dict_conf_used_to_df[solver]["problem_name"].tolist()]
                ordinate = dict_conf_used_to_df[solver][field].tolist()

                ax = axs[i]
                ax.set_title(f"{field}")
                ax.set_xlabel("Problem")
                ax.set_ylabel("")
                ax.scatter(abcisse, ordinate, label=str(solver))
                ax.plot(abcisse, ordinate)

            ax.legend(loc='upper left')

        plt.subplots_adjust(hspace=0.5)  # increase the vertical space between subplots

        # plt.plot()
        # plt.show()

        path_figure = os.path.join(
            PATH_OUTPUT, f"figure_result_{benchmark_name}.png")

        logging.info(f"Save figure {path_figure}")

        # Set the figure width enough to prevent xlabel from overlapping
        fig.set_size_inches((18, 11), forward=False)

        plt.savefig(path_figure)
        plt.show()



def generate_figures_stats():
    """Generate figures to compare the results of the planners on two metrics: the total time spent to find a plan on a problem and the size of the plan generated. 
    For each benchmark, there will be 1 file generated containing 2 figures: one for each of these metrics. Figures will be saved in the folder PATH_OUTPUT.
    """

    # Get all csv files in the output folder
    files_name = os.listdir(PATH_OUTPUT)
    csv_files_names = [file for file in files_name if file.endswith('.csv')]

    


    for file_name in csv_files_names:

        print(f"Generate figure for {file_name}")



        path_file_name = os.path.join(PATH_OUTPUT, file_name)

        benchmark_name = file_name.split('.')[0]

        data = pd.read_csv(path_file_name, comment='#')

        # Get all the differents configurations that was used in the test
        solver_used = data['config_used'].unique()

        # We need to set the lilotane_totale run time to Nan and the lilotane_solver_time to Nan if the plan size is -1
        data.loc[(data['total_execution_time'] == 0), 'total_solver_time'] = np.nan
        data.loc[(data['total_execution_time'] == 0), 'solver_time'] = np.nan
        data.loc[(data['total_execution_time'] == 0), 'num_actions'] = np.nan
        data.loc[(data['total_execution_time'] == 0), 'num_scopes_values'] = np.nan
        data.loc[(data['total_execution_time'] == 0), 'num_unique_scope'] = np.nan
        data.loc[(data['total_execution_time'] == 0), 'num_scope_equals'] = np.nan

        data.loc[(data['total_execution_time'] == 0), 'total_execution_time'] = np.nan

        data.loc[(data['total_execution_time'] == -1), 'total_solver_time'] = np.nan
        data.loc[(data['total_execution_time'] == -1), 'solver_time'] = np.nan
        data.loc[(data['total_execution_time'] == -1), 'num_actions'] = np.nan
        data.loc[(data['total_execution_time'] == -1), 'num_scopes_values'] = np.nan
        data.loc[(data['total_execution_time'] == -1), 'num_unique_scope'] = np.nan
        data.loc[(data['total_execution_time'] == -1), 'num_scope_equals'] = np.nan

        data.loc[(data['total_execution_time'] == -1), 'total_execution_time'] = np.nan

        

        # Create the configuration fot each
        dict_conf_used_to_df = {}

        SOLVERS_TO_USE = ["Lifted_tree_path_config.CLASSIC", "lilotane"]

        for solver in SOLVERS_TO_USE:
            dict_conf_used_to_df[solver] = data[data['config_used'] == str(solver)]

        # Sort data by hsp_total_run_time
        # data.sort_values(["hsp_total_run_time"], axis=0,
        #                  ascending=[True], inplace=True)

        # Some clean of the data: Do not display bar of total run time of the planner if there is no plan found
        # data.loc[(data['plan_size'] == 0),
        #          'rantanplan_total_run_time'] = 0
        # data.loc[(data['hsp_plan_size'] == 0), 'hsp_total_run_time'] = 0

        # We will encode the initialization time, encoding time and solver time and total time in 4 different graph


        fields_to_display = ["num_actions", "num_unique_scope", "num_scopes_values"]

        fig, axs = plt.subplots(len(fields_to_display), 1, figsize=(8, 10))
        fig.suptitle(f"On domain {benchmark_name}")

        for i, field in enumerate(fields_to_display):
            for solver in dict_conf_used_to_df:
                abcisse = [name.split('.')[0] for name in dict_conf_used_to_df[solver]["problem_name"].tolist()]
                ordinate = dict_conf_used_to_df[solver][field].tolist()

                ax = axs[i]
                ax.set_title(f"{field}")
                ax.set_xlabel("Problem")
                ax.set_ylabel("")
                ax.scatter(abcisse, ordinate, label=str(solver))
                ax.plot(abcisse, ordinate)

            ax.legend(loc='upper left')

        plt.subplots_adjust(hspace=0.5)  # increase the vertical space between subplots

        # plt.plot()
        # plt.show()

        path_figure = os.path.join(
            PATH_OUTPUT, f"figure_result_{benchmark_name}_stats.png")

        logging.info(f"Save figure {path_figure}")

        # Set the figure width enough to prevent xlabel from overlapping
        fig.set_size_inches((18, 11), forward=False)

        plt.savefig(path_figure)
        plt.show()


if __name__ == '__main__':

    # Initialize logging
    logging.basicConfig(
        format='%(asctime)s %(levelname)s:%(message)s', level=logging.DEBUG)

    # generate_figures()
    generate_figures_stats()
    exit(0)

    # First, build the library
    logging.info("Build lifted_tree_path")
    build_lifted_tree_path()

    for (path_benchmark, highest_instance_to_solve) in PATH_BENCHMARKS:

        name_benchmark = path_benchmark.split('/')[-1]
        logging.info(
            f"Test benchmark {name_benchmark}")

        # Create the file to write results if not exist
        file_to_write_result = os.path.join(
            PATH_OUTPUT, "{name_benchmark}.csv".format(name_benchmark=name_benchmark))
        if (not os.path.exists(file_to_write_result)):
            # Initialize the file by writing the name of all the columns
            with open(file_to_write_result, 'a') as f:
                f.write(
                    "benchmark_name,problem_name,config_used,total_execution_time,total_solver_time,plan_is_valid,num_actions,num_scopes_values,num_unique_scope,num_scope_equals\n")

        # Load all the problems
        files_in_benchmark = sorted(os.listdir(path_benchmark))

        # Remove all files which do not end with hddl
        files_in_benchmark = [f for f in files_in_benchmark if f.endswith("hddl")]

        if ("domain.hddl" not in files_in_benchmark):
            logging.error(
                f"Domain file does not exist for benchmark path: {path_benchmark}. Skip this benchmark")
            continue

        logging.info(f"Domain file found for benchmark path: {path_benchmark}")

        full_path_benchmark = os.path.abspath(path_benchmark)

        full_path_file_domain = os.path.join(
            full_path_benchmark, "domain.hddl")

        files_in_benchmark.remove("domain.hddl")

        # Keep only the first 20 level of each benchmark
        num_level_to_keep = min(highest_instance_to_solve, len(files_in_benchmark))
        files_in_benchmark = files_in_benchmark[:num_level_to_keep]
        

        for problem_file in files_in_benchmark:

            for config_to_use in CONFIG_TO_USE:

                with open(file_to_write_result, 'r') as f:
                    skip_problem = False
                    lines = f.readlines()
                    for line in lines:
                        if (f"{name_benchmark},{problem_file},{config_to_use}" in line):
                            logging.info(
                                f"Problem {problem_file} of benchmark: {name_benchmark} already done with solver {config_to_use}")
                            skip_problem = True
                            break

                    if (skip_problem):
                        continue

                full_path_file_problem = os.path.join(
                    full_path_benchmark, problem_file)

                logging.info(f"For problem: {full_path_file_problem}")

                logging.info(
                    f"Launch lifted tree path planner with config: {config_to_use}")
                plan_is_valid, total_execution_time_s, total_solver_time_s, num_actions, num_scopes_values, num_unique_scopes, num_scope_equals = launch_planner(
                    full_path_file_domain=full_path_file_domain,
                    full_path_file_problem=full_path_file_problem,
                    config_to_use=config_to_use)

                if (not plan_is_valid):
                    logging.error(
                        f"Failed to find a plan for problem {problem_file} of benchmark {path_benchmark} with Hydra planner")


                logging.info(
                    f"total execution time: {total_execution_time_s} s, total solver time: {total_solver_time_s} s, plan is valid: {plan_is_valid}")

                with open(file_to_write_result, 'a') as f:
                    line_to_write = f"{name_benchmark},{problem_file},{config_to_use},{total_execution_time_s},{total_solver_time_s},{plan_is_valid},{num_actions},{num_scopes_values},{num_unique_scopes},{num_scope_equals}\n"
                    f.write(line_to_write)

        # logging.info("Generate figure")
        # generate_figures()
