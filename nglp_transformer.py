"""
This module reduces a (non-ground) logic program into a disjunctive logic program using
body-decoupled grounding.
"""

import re

import clingo
from clingo.ast import Transformer

from candidate_guesser import CandidateGuesser
from sat_ensurer import SatEnsurer
from unfoundedness_preventer import UnfoundednessPreventer


class NglpDlpTransformer(Transformer):
    def __init__(self, bld, terms, facts, ng_heads, shows, subdoms, ground_guess, ground):
        self.__bld = bld  # Object to build non-ground programs
        self.__terms = terms  # Terms occurring in the program, e.g., ['1', '2']
        self.__facts = facts  # Facts, arities and arguments
        self.__ng_heads = ng_heads  # Rule heads with their arities, e.g., {'d': {1}, 'a': {2}}
        self.__shows = shows  # Predicates (and functions) with their arities, e.g., {'a': {2}, 'f': {1}}
        self.__subdoms = subdoms  # Domains of each variable separately, e.g.,  {'Y': ['1', '2'], 'Z': ['1', '2']}
        self.__ground_guess = ground_guess  # --ground-guess
        self.__ground = ground  # --ground

        self.__rules = False  # If this is rule is under #program rules (reduction applied)
        self.__ng = False  # If the program is non-ground
        self.__cur_anon = 0  # Number of anonymous variables in a rule
        self.__cur_var = []
        self.__cur_func = []
        self.__cur_func_sign = []  # Boolean list for signs of literals
        self.__cur_comp = []
        self.__f = {}
        self.__rule_counter = 0  # Counts rules in the program
        self.__g_counter = "A"

    def __reset_after_rule(self):
        """
        Resets configuration after processing of a rule.
        """
        self.__cur_var = []
        self.__cur_func = []
        self.__cur_func_sign = []
        self.__cur_comp = []
        self.__cur_anon = 0
        self.__ng = False

    def visit_Rule(self, node):
        # if not part of #program rules
        if not self.__rules:
            self.__reset_after_rule()
            if not self.__ground:
                self.__output_node_format_conform(node)
            return node

        # check if AST is non-ground
        self.visit_children(node)

        # if so: handle grounding
        self.__handle_grounding(node)
        self.__reset_after_rule()
        return node

    def visit_Literal(self, node):
        """
        Visits literals in the program. If it is not #false, its sign is saved.

        :param node: Literal in the program.
        :return: Node of the AST.
        """
        if str(node) != "#false":
            if node.atom.ast_type is clingo.ast.ASTType.SymbolicAtom:
                # comparisons are reversed by parsing, therefore always using not is sufficient
                self.__cur_func_sign.append(str(node).startswith("not "))
        self.visit_children(node)
        return node

    def visit_Function(self, node):
        """
        Visits non-ground predicates of the program and saves their names and arities.

        :param node: Function node of the program.
        :return: Node of the AST.
        """
        # shows
        if node.name in self.__shows:
            self.__shows[node.name].add(len(node.arguments))
        else:
            self.__shows[node.name] = {len(node.arguments)}

        node = node.update(**self.visit_children(node))
        self.__cur_func.append(node)

        return node

    def visit_Variable(self, node):
        """
        Visits variables of the program in order to determine if the program is non-ground and
        saves them. It also distinguishes anonymous variables.

        :param node: Variable in the program.
        :return Node of the AST.
        """
        self.__ng = True
        if (str(node) not in self.__cur_var) and (str(node) not in self.__terms):
            if str(node) == "_":
                node = node.update(name=f"Anon{self.__cur_anon}")
                self.__cur_anon += 1
            self.__cur_var.append(str(node))
        return node

    def visit_SymbolicTerm(self, node):
        return node

    def visit_Program(self, node):
        """
        Visits the program directives in order to activate the partial body-decoupled grounding
        if #program rules.

        :param node: Program directive in the program.
        :return: Node of the AST.
        """
        if node.name == "rules":
            self.__rules = True
        else:
            self.__rules = False
        return node

    def visit_Comparison(self, node):
        """
        Checks if the comparison operands are variables or terms and saves them.

        :param node: Comparison in the program.
        :return: Node of the AST.
        """
        # currently implements only terms/variables
        assert (
                node.left.ast_type is clingo.ast.ASTType.Variable or node.left.ast_type is clingo.ast.ASTType.SymbolicTerm)
        assert (
                node.right.ast_type is clingo.ast.ASTType.Variable or node.right.ast_type is clingo.ast.ASTType.SymbolicTerm)

        self.__cur_comp.append(node)
        self.visit_children(node)
        return node

    def __output_node_format_conform(self, node):
        """
        Prints the rule node as a valid program rule.

        :param node: Rule in the program.
        """
        if str(node.head) == "#false":  # catch constraints and print manually since clingo uses #false
            print(f":- {', '.join(str(n) for n in node.body)}.")
        else:
            if len(node.body) > 0:
                if str(node.head).startswith('{'):
                    print(f"{str(node.head)} :- {', '.join([str(b) for b in node.body])}.")
                else:
                    print(f"{str(node.head).replace(';', ',')} :- {', '.join([str(b) for b in node.body])}.")
            else:
                if str(node.head).startswith('{'):
                    print(f"{str(node.head)}.")
                else:
                    print(f"{str(node.head).replace(';', ',')}.")

    def __handle_grounding(self, node):
        if self.__ng:
            self.__rule_counter += 1
            if str(node.head) != "#false":
                head = self.__cur_func[0]
            else:
                head = None

            # SAT
            sat_ensurer = SatEnsurer(self.__rule_counter, self.__terms, self.__subdoms, self.__cur_var,
                                     self.__cur_func, self.__cur_func_sign, self.__cur_comp)
            # Print rules (3) and (7)
            sat_ensurer.guess_sat_saturate_assignments()
            # Print rules (4) and (5)
            sat_ensurer.ensure_sat(head)

            if head is not None:
                CandidateGuesser().guessCandidates(head, self.__terms, self.__subdoms, self.__ground_guess,
                                                   self.__cur_var)

                unfoundedness_preventer = UnfoundednessPreventer(self.__terms, self.__facts, self.__subdoms,
                                                                 self.__ground_guess,
                                                                 self.__cur_var, self.__cur_func, self.__cur_func_sign,
                                                                 self.__cur_comp, self.__f, self.__rule_counter)
                unfoundedness_preventer.prevent_unfoundedness(head)

        else:  # found-check for ground-rules (if needed) (pred, arity, combinations, rule, indices)
            head_pred = str(node.head).split('(', 1)[0]
            head_arguments_list = re.sub(r'^.*?\(', '', str(node.head))[:-1].split(',')
            arity = len(head_arguments_list)
            head_arguments = ','.join(head_arguments_list)

            # If such a head predicate with the given arity exists but there is no such fact
            if head_pred in self.__ng_heads and arity in self.__ng_heads[head_pred] \
                    and not (head_pred in self.__facts and arity in self.__facts[head_pred]
                             and head_arguments in self.__facts[head_pred][arity]):
                for body_atom in node.body:
                    if str(body_atom).startswith("not "):
                        neg = ""
                    else:
                        neg = "not "
                    print(f"r{self.__g_counter}_unfound({head_arguments}) :- "
                          + f"{neg + str(body_atom)}.")

                self.__g_counter = chr(ord(self.__g_counter) + 1)

            # print rule as it is
            self.__output_node_format_conform(node)

        self.__reset_after_rule()
        return node

    def check_if_all_sat(self, bld):
        SatEnsurer(self.__rule_counter).check_if_all_sat(bld)

    def prevent_unfounded_rules(self):
        """
        Prints rule (17), which prevents unfounded results.

        :return:
        """
        if self.__rule_counter > 0:
            for p in self.__f:
                for arity in self.__f[p]:
                    for c in self.__f[p][arity]:
                        rule_sets = []
                        for r in self.__f[p][arity][c]:
                            sum_sets = []
                            for subset in self.__f[p][arity][c][r]:
                                # print ([c[int(i)] for i in subset])
                                sum_sets.append(
                                    f"1:r{r}_unfound{'_' + ''.join(subset) if len(subset) < arity else ''}"
                                    + (f"({','.join([c[int(i)] for i in subset])})"
                                       if len(subset) > 0 else ""))
                            sum_atom = f"#sum {{{'; '.join(sum_sets)}}} >= 1"
                            rule_sets.append(sum_atom)
                        head = ','.join(c)
                        print(f":- {', '.join([f'{p}' + (f'({head})' if len(head) > 0 else '')] + rule_sets)}.")


    def handle_ground_guess(self):
        """
        If no --ground-guess, then this method uses and prints the complete set of terms as domain for all variables.
        """
        if not self.__ground_guess:
            for t in self.__terms:
                print(f"dom({t}).")

    def handle_no_show(self, no_show):
        """
        If no --no-show, then this method prints #show directives for all predicates.

        :param no_show: Boolean variable indicating if --no-show or not.
        """
        if not no_show:
            for f in self.__shows.keys():
                for l in self.__shows[f]:
                    print(f"#show {f}/{l}.")




    def __get_terms(self):
        return self.__terms

    def __get_facts(self):
        return self.__facts

    def __get_ng_heads(self):
        return self.__ng_heads

    def __get_cur_anon(self):
        return self.__cur_anon

    def __get_cur_var(self):
        return self.__cur_var

    def __get_cur_func(self):
        return self.__cur_func

    def __get_cur_func_sign(self):
        return self.__cur_func_sign

    def __get_rule_counter(self):
        return self.__rule_counter

    def __get_g_counter(self):
        return self.__g_counter

    terms = property(__get_terms)
    facts = property(__get_facts)
    ng_heads = property(__get_ng_heads)
    cur_anon = property(__get_cur_anon)
    cur_var = property(__get_cur_var)
    cur_func = property(__get_cur_func)
    cur_func_sign = property(__get_cur_func_sign)
    rule_counter = property(__get_rule_counter)
    g_counter = property(__get_g_counter)
