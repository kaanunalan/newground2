"""
This module collects some information about the program for further processing.
"""

import re

from clingo.ast import Transformer

from subdom_adder import add_to_subdom


class TermTransformer(Transformer):
    def __init__(self, subdoms, no_show=False):
        self.__terms = []  # Terms occurring in the program, e.g., ['1', '2']
        self.__subdoms = subdoms  # Domains of each variable separately, e.g.,  {'Y': ['1', '2'], 'Z': ['1', '2']}
        self.__facts = {}  # Facts, arities and arguments, e.g., {'_dom_X': {1: {'1'}}, '_dom_Y': {1: {'(1..2)'}}}
        self.__ng_heads = {}  # Rule heads with their arities, e.g., {'d': {1}, 'a': {2}}
        self.__ng = False  # If the program is non-ground
        self.__shows = {}  # Predicates (and functions) with their arities, e.g., {'a': {2}, 'f': {1}}
        self.__current_f = None  # Current predicate (or function) name
        self.__no_show = no_show  # --no-show
        self.__all_vars = []  # List of all variables occurring in the program, e.g., ['X', 'Y', 'Z']

    def visit_Rule(self, node):
        """
        Visits rules of the program and saves non-ground head predicates with their arities
        or saves facts with their arities and arguments.

        :param node: Rule in the program.
        :return Node of the AST.
        """
        self.visit_children(node)
        # Get rule head predicate name
        pred = str(node.head).split("(", 1)[0]
        # Get list of arguments of the rule head
        arguments = re.sub(r"^.*?\(", "", str(node.head))[:-1].split(",")
        # Get arity (length of arguments) of predicate
        arity = len(arguments)

        # If program non-ground, save pred and arity (except #false) for later use
        if self.__ng:
            self.__ng = False
            if str(node.head) != "#false":
                # save pred and arity for later use
                if pred not in self.__ng_heads:
                    self.__ng_heads[pred] = {arity}
                else:
                    self.__ng_heads[pred].add(arity)
        # Add to facts if body length is zero
        elif node.body.__len__() == 0:
            arguments = ",".join(arguments)
            if pred not in self.__facts:
                self.__facts[pred] = {}
                self.__facts[pred][arity] = {arguments}
            elif arity not in self.__facts[pred]:
                self.__facts[pred][arity] = {arguments}
            else:
                self.__facts[pred][arity].add(arguments)
        return node

    def visit_Function(self, node):
        """
        Visits predicates (and functions) of the program and saves their names and arities.

        :param node: Function node of the program.
        :return: Node of the AST.
        """
        self.__current_f = str(node).split("(", 1)[0] if len(node.arguments) > 0 else node
        # shows
        # if not str(node.name).startswith('_dom_'):
        if node.name in self.__shows:
            self.__shows[node.name].add(len(node.arguments))
        else:
            self.__shows[node.name] = {len(node.arguments)}
        self.visit_children(node)
        return node

    def visit_Variable(self, node):
        """
        Visits variables of the program in order to determine if the program
        is non-ground and save them for later use.

        :param node: Variable in the program.
        :return Node of the AST.
        """
        self.__ng = True
        self.__all_vars.append(str(node))
        self.__all_vars = list(dict.fromkeys(self.__all_vars))
        return node

    def visit_Interval(self, node):
        """
        Visits intervals of the program in order to add them to subdomains.

        :param node: Interval in the program.
        :return Node of the AST.
        """
        for i in range(int(str(node.left)), int(str(node.right)) + 1):
            if str(i) not in self.__terms:
                self.__terms.append(str(i))
            add_to_subdom(self.__subdoms, self.__current_f, str(i))
        return node

    def visit_SymbolicTerm(self, node):
        """
        Visits symbolic terms in order to save them for later use.

        :param node: Symbolic term in the program.
        :return: Node of the AST.
        """
        if str(node) not in self.__terms:
            self.__terms.append(str(node))
        add_to_subdom(self.__subdoms, self.__current_f, str(node))
        return node

    def visit_ShowSignature(self, node):
        """
        Visits the show directives in the program and prints them (if the
        --no-show option is not used)

        :param node: Show directive in the program.
        :return: Node of the AST.
        """
        if not self.__no_show:
            print(node)
        return node

    def __get_terms(self):
        return self.__terms

    def __get_subdoms(self):
        return self.__subdoms

    def __get_facts(self):
        return self.__facts

    def __get_ng_heads(self):
        return self.__ng_heads

    def __get_shows(self):
        return self.__shows

    def __get_all_vars(self):
        return self.__all_vars

    terms = property(__get_terms)
    subdoms = property(__get_subdoms)
    facts = property(__get_facts)
    ng_heads = property(__get_ng_heads)
    shows = property(__get_shows)
    all_vars = property(__get_all_vars)
