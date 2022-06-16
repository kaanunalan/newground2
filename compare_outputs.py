"""
Compares differences between same named files in two directories and writes them into a
user specified or default directory.
"""
import argparse
import os
import pathlib
import sys

parser = argparse.ArgumentParser(prog=sys.argv[0], usage="%(prog)s DIR_PATH1 DIR_PATH2 OUTPUT_DIR_PATH")
parser.add_argument("dir_path1", metavar="DIR_PATH1", help="First directory for comparison.")
parser.add_argument("dir_path2", metavar="DIR_PATH2", help="Second directory for comparison.")
parser.add_argument("output_path", metavar="OUTPUT_DIR_PATH", nargs="?",
                    help="Third directory where the results are printed.")
args = parser.parse_args()

if not os.path.exists(args.dir_path1):
    raise NotADirectoryError(args.dir_path1 + "is not a directory")
if not os.path.exists(args.dir_path2):
    raise NotADirectoryError(args.dir_path2 + "is not a directory")
output_path = args.output_path
if output_path is None:
    output_path = "comparison_results"
    if not os.path.exists(output_path):
        os.system("mkdir " + output_path)
else:
    if not os.path.exists(output_path):
        os.system("mkdir " + output_path)
for path1 in pathlib.Path(args.dir_path1).iterdir():
    for path2 in pathlib.Path(args.dir_path2).iterdir():
        if path1.is_file() and path2.is_file() and path1.name == path2.name:
            if sys.platform == "win32":
                os.system("FC " + path1.__str__() + " " + path2.__str__() + " > "
                          + output_path + "/" + os.path.basename(path1) + "_"
                          + os.path.basename(path2))
            else:
                os.system("diff " + path1.__str__() + " " + path2.__str__() + " > "
                          + output_path + "/" + os.path.basename(path1) + "_"
                          + os.path.basename(path2))
