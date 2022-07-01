"""
Computes the results of newground2 for input files in a specified input directory and
writes them into output files in a specified output directory for each instance and
for each option.
"""

import argparse
import os
import pathlib
import sys

program_name = "../newground2.py"

parser = argparse.ArgumentParser(prog=sys.argv[0], usage="%(prog)s --input DIR_PATH --output DIR_PATH")
parser.add_argument("--input", metavar="INPUT_DIR_PATH", required=True,
                    help="Input directory where input files are placed.")
parser.add_argument("--output", metavar="OUTPUT_DIR_PATH", required=True,
                    help="Output directory where output files are written.")
args = parser.parse_args()

if not os.path.exists(args.output):
    os.system("mkdir " + args.output)
for path in pathlib.Path(args.input).iterdir():
    if path.is_file():
        options = ["", "--ground", "--ground-guess", "--no-show"]
        for option in options:
            os.system("python3 " + program_name + " " + option + " " + path.__str__() + " > "
                      + args.output + "/" + option + "_" + os.path.basename(path))
