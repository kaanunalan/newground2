"""
This module manages the instantiation which is specified through the subprogram #program insts
"""

import re

from clingo.control import Control
from clingox.program import Program, ProgramObserver

from add_subdom import add_to_subdom


class InstsManager:
    def __init__(self, files):
        self.__files = files

    def manage_insts(self):
        """
        This method manages the subprogram '#program insts.
        The subprogram '#program insts.' can be used for instantiating the program. Without explicit domains given the
        reduction uses the complete set of terms to fill the variables in the grounding process. This process can be
        reduced by giving a domain for each variable, e.g. '_dom_X(1..5).', or by '_dom_X(X) :- a(X,_).' in the
        instantiating part of the program. This information is then processed automatically and considered in the
        reduction.
        """
        # Ground program representation
        prg = Program()
        # Control object for grounding and solving of instantiation (#program insts)
        ctl_insts = Control()
        # Register the observer to build a ground program representation while grounding
        ctl_insts.register_observer(ProgramObserver(prg))

        # read subdomains in #program insts.
        self.__read_subdoms(ctl_insts)
        print(prg)

    def __read_subdoms(self, ctl_insts):
        """
        Reads subdomains of each variable separately and saves them.

        :param ctl_insts: Control object for instantiation.
        """
        for f in self.__files:
            # Extend the logic program with a (non-ground) logic program in a file.
            ctl_insts.load(f)

        # Ground the program parts after #program insts
        # (and also other parts for the case of grounding without any subprograms).
        ctl_insts.ground([("base", []), ("insts", [])])

        subdoms = {}
        for k in ctl_insts.symbolic_atoms:
            if str(k.symbol).startswith("_dom_"):
                # Get "_dom_X"
                var = str(k.symbol).split("(", 1)[0]
                # Replace all patterns of arbitrary characters up to the first opening parenthesis in strings
                # with an empty string and remove also the last character: e.g. _dom_X(1) -> 1
                atom = re.sub(r"^.*?\(", "", str(k.symbol))[:-1]
                # Add the domains for variables and corresponding list of atoms to the dictionary of subdomains
                add_to_subdom(subdoms, var, atom)
