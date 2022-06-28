"""
This module extends the standard clingo application and manages the body-decoupled grounding.
"""

from clingo.application import Application
from clingo.ast import parse_files, ProgramBuilder

from insts_manager import InstsManager
from nglp_transformer import NglpDlpTransformer
from term_transformer import TermTransformer


class ClingoApp(Application):
    def __init__(self, name, no_show=False, ground_guess=False, ground=False):
        self.program_name = name  # Name of the program
        self.__subdoms = {}  # Domains of each variable separately
        self.__no_show = no_show  # --no-show
        self.__ground_guess = ground_guess  # --ground-guess
        self.__ground = ground  # --ground

    def main(self, ctl, files):
        """
        This function replaces clingo's default main function
        in order to apply the reduction of body-decoupled grounding.

        :param ctl: The main control object.
        :param files: The files passed to clingo.
        """
        # Read subdomains in #program insts.
        if self.__ground:
            InstsManager(files).manage_insts()

        self.__transform_nglp_dlp(ctl, files)

    def __transform_nglp_dlp(self, ctl, files):
        """
        Transforms a non ground logic program into a disjunctive logic program by applying the reduction.

        :param ctl: The main control object.
        :param files: The files passed to clingo.
        """
        # Initialize the term transformer
        term_transformer = TermTransformer(self.__subdoms, self.__no_show)
        # Parse the programs in the given files and return an abstract syntax tree for each statement via a callback
        parse_files(files, lambda stm: term_transformer(stm))

        with ProgramBuilder(ctl) as bld:
            transformer = NglpDlpTransformer(bld, term_transformer.terms, term_transformer.facts,
                                             term_transformer.heads, term_transformer.shows,
                                             term_transformer.subdoms, self.__ground_guess,
                                             self.__ground, term_transformer.all_vars)

            parse_files(files, lambda stm: bld.add(transformer(stm)))

            transformer.check_if_all_sat(bld)
            transformer.prevent_unfounded_rules()
            transformer.handle_normal_programs()
            transformer.handle_ground_guess()
            transformer.handle_no_show(self.__no_show)
