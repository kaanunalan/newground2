"""
This module extends the standard clingo application.
"""

import re

from clingo.application import Application
from clingo.ast import parse_files, ProgramBuilder
from clingo.control import Control
from clingox.program import Program, ProgramObserver

from add_subdom import add_to_subdom
from nglp_transformer import NglpDlpTransformer
from term_transformer import TermTransformer


class ClingoApp(Application):
    def __init__(self, name, no_show=False, ground_guess=False, ground=False):
        self.__program_name = name
        self.__subdoms = {}
        self.__no_show = no_show
        self.__ground_guess = ground_guess
        self.__ground = ground

    def main(self, ctl, files):
        # ground program representation
        prg = Program()
        # Control object for grounding and solving
        ctl_insts = Control()
        # Register the observer to build a ground program representation while grounding
        ctl_insts.register_observer(ProgramObserver(prg))

        # read subdomains in #program insts.
        self.__read_subdoms(ctl_insts, files)
        if self.__ground:
            print(prg)

        self.__transform_nglp_dlp(ctl, files)

    def __read_subdoms(self, ctl_insts, files):
        for f in files:
            # Extend the logic program with a (non-ground) logic program in a file.
            ctl_insts.load(f)

        # Ground the program parts after #program insts (and other parts).
        # ctl_insts.ground([("insts", [])]) # Why not?
        ctl_insts.ground([("base", []), ("insts", [])])

        for k in ctl_insts.symbolic_atoms:
            if str(k.symbol).startswith("_dom_"):
                # Get "_dom_X"
                var = str(k.symbol).split("(", 1)[0]
                # Replace all patterns of arbitrary characters up to the first opening parenthesis in strings
                # with an empty string and remove also the last character: e.g. _dom_X(1) -> 1
                atom = re.sub(r"^.*?\(", "", str(k.symbol))[:-1]
                # Add the domains for variables and corresponding list of atoms to the dictionary of subdomains
                add_to_subdom(self.__subdoms, var, atom)

    def __transform_nglp_dlp(self, ctl, files):
        # Initialize the term transformer
        term_transformer = TermTransformer(self.__subdoms, self.__no_show)
        # Parse the programs in the given files and return an abstract syntax tree for each statement via a callback
        parse_files(files, lambda stm: term_transformer(stm))

        with ProgramBuilder(ctl) as bld:
            transformer = NglpDlpTransformer(bld, term_transformer.terms, term_transformer.facts,
                                             term_transformer.ng_heads, term_transformer.shows,
                                             term_transformer.subdoms, self.__ground_guess, self.__ground)
            parse_files(files, lambda stm: bld.add(transformer(stm)))

            transformer.print_sat_and_foundedness_rules(bld)
            transformer.handle_ground_guess()
            transformer.handle_no_show(term_transformer, self.__no_show)

    def __handle_ground_guess(self, nglp_dlp_transformer):
        if not self.__ground_guess:
            for t in nglp_dlp_transformer.__terms:
                print(f"dom({t}).")
