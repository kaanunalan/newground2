import argparse
import os
import pathlib
import sys

parser = argparse.ArgumentParser(prog=sys.argv[0], usage="%(prog)s [PROXY_TOOL_COMMAND]")
parser.add_argument("proxy_tool_command", metavar="PROXY_TOOL_COMMAND", nargs="?", default=".",
                    help="Command for the proxy tool supporting the benchmark process. ")
parser.add_argument("--variant", metavar="VARIANT", nargs="?",
                    help="Variant of additional rules for normal programs, 'v2' for variant 2, nothing for variant 1.")
args = parser.parse_args()

proxy_tool_command = args.proxy_tool_command

benchmark_instances_path = "../instances/benchmark_instances/"
encodings_path = benchmark_instances_path + "encodings/"
graphs_path = benchmark_instances_path + "graphs/"
graphs_v2_path = benchmark_instances_path + "graphs_newground2_v2/"


def execute_test(command, output_dir):
    encoding_no_ext = os.path.splitext(command.split()[-1])[0]
    encoding_no_ext_base = encoding_no_ext.split("/")[-1]
    graph_no_ext = os.path.splitext(os.path.basename(graph))[0]
    watcher_log = "-w " + output_dir + encoding_no_ext_base + "_" + graph_no_ext + "_watch.log"
    key_value_log = "--var " + output_dir + encoding_no_ext_base + "_" + graph_no_ext + "_values.log"
    # tool_output = "-o " + encoding_no_ext_base + "_" + graph_no_ext + "_output.log"
    execute_grounding_list = [proxy_tool_command, watcher_log, key_value_log, command, str(graph)]
    # execute_grounding_list.append(tool_output)
    execute_grounding = " ".join(execute_grounding_list)
    get_grounding_size = execute_grounding + " | wc > " + output_dir + encoding_no_ext_base + "_" + graph_no_ext \
        + "_wc.log"
    execute_overall_list = [command, str(graph)]
    execute_overall = " ".join(execute_overall_list)
    get_overall_time = execute_overall + " | clingo --stats=2 --project -q > " + output_dir + encoding_no_ext_base \
       + "_" + graph_no_ext + "_overall.log"
    os.system(get_grounding_size)
    os.system(get_overall_time)
    print("Test " + command + " for " + str(graph_no_ext) + " accomplished")


# Execute tests for nprc
newground_nprc_command = "python3 ../newground2.py " + encodings_path + "nprc_newground.lp"
newground2_nprc_command = "python3 ../newground2.py " + encodings_path + "nprc_newground2.lp"
gringo_nprc_command = "gringo --verbose=2 --output text " + encodings_path + "nprc_gringo.lp"
nprc_commands_list = [newground_nprc_command, gringo_nprc_command]
if args.variant != "v2":
    nprc_commands_list.append(newground2_nprc_command)

nprc_output_dir = "results_nprc/"
if not os.path.exists(nprc_output_dir):
    os.system("mkdir " + nprc_output_dir)

for graph in pathlib.Path(graphs_path).iterdir():
    for c in nprc_commands_list:
        execute_test(c, nprc_output_dir)

if newground2_nprc_command not in nprc_commands_list:
    for graph in pathlib.Path(graphs_v2_path).iterdir():
        execute_test(newground2_nprc_command, nprc_output_dir)


