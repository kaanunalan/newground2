# newground2
Reduction of **non-ground** logic programs to **disjunctive** logic programs using body-decoupled grounding. Branch **auxiliary-atoms** contains *Variant 1 (using orderings)*, branch **provability-without-level-mappings** 
contains *Variant 2 (proving via ordered derivations)*, branch **newground-refactoring** contains the variant for tight programs. Experiment encodings and test instances are in the branch **experiments**.

## Requirements
* clingo 
* clingo's Python module >= *v5.5*
* clingox
* future-fstrings (for compatibility with older versions)
* networkx
```
pip install -r requirements.txt
```

## Input Format
The input format is equivalent to clingos input format.

Based on the principle of partial reducibility, inputs can be divided into parts that shall be part of the reduction. For this reason, please use `#program rules.` for tight (non-ground) program parts and `#program normal.` for normal (non-ground) program parts that shall be reduced by **newground2**. The subprogram `#program insts.` on the other hand can be used for instantiating the program.

Without explicit domains given the reduction uses the complete set of terms to fill the variables in the grounding process. This process can be reduced by giving a domain for each variable, e.g. `_dom_X(1..5).`, or by `_dom_X(X) :- a(X,_).` in the instantiating part of the program. This information is then processed automatically and considered in the reduction.

## Usage
```
$ python3 newground2.py -h
usage: newground2.py file1 [file2 ...]

positional arguments:
  file1 [file2 ...]

optional arguments:
  -h, --help      show this help message and exit
  --no-show       Do not print #show-statements to avoid compatibility issues.
  --ground-guess  Additionally ground guesses which results in (fully) grounded output.
  --ground        Output program fully grounded.
```