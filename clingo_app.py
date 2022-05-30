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
        # Read subdomains in #program insts.
        if self.__ground:
            InstsManager(files).manage_insts()

        self.__transform_nglp_dlp(ctl, files)

    def __transform_nglp_dlp(self, ctl, files):
        # Initialize the term transformer
        term_transformer = TermTransformer(self.__subdoms, self.__no_show)
        # Parse the programs in the given files and return an abstract syntax tree for each statement via a callback
        parse_files(files, lambda stm: term_transformer(stm))

        #print("subdoms: " + str(term_transformer.subdoms))
        #print("terms: " + str(term_transformer.terms))
        #print("heads: " + str(term_transformer.ng_heads))
        #print("shows: " + str(term_transformer.shows))
        #print("facts: " + str(term_transformer.facts))

        with ProgramBuilder(ctl) as bld:
            transformer = NglpDlpTransformer(bld, term_transformer.terms, term_transformer.facts,
                                             term_transformer.ng_heads, term_transformer.shows,
                                             term_transformer.subdoms, self.__ground_guess, self.__ground)

            parse_files(files, lambda stm: bld.add(transformer(stm)))

            transformer.check_if_all_sat(bld)
            transformer.prevent_unfounded_rules()
            transformer.handle_ground_guess()
            transformer.handle_no_show(self.__no_show)

            #print("terms: " + str(transformer.terms))
            #print("facts: " + str(transformer.facts))
            #print("ng_heads: " + str(transformer.ng_heads))
            #print("cur_anon: " + str(transformer.cur_anon))
            #print("cur_var: " + str(transformer.cur_var))
            #print("cur_func: " + str(transformer.cur_func))
            #print("cur_func_sign: " + str(transformer.cur_func_sign))
            #print("rule_counter: " + str(transformer.rule_counter))
            #print("g_counter: " + str(transformer.g_counter))
