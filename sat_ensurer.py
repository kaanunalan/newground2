import itertools
import re

import clingo
from clingo.ast import parse_string


class SatEnsurer:
    def __init__(self, rule_counter, terms=None, subdoms=None, cur_var=None, cur_func=None, cur_func_sign=None, cur_comp=None):
        if cur_func_sign is None:
            cur_func_sign = []
        self.__terms = terms  # Terms occurring in the program, e.g., ['1', '2']
        self.__subdoms = subdoms  # Domains of each variable separately, e.g.,  {'Y': ['1', '2'], 'Z': ['1', '2']}
        self.__cur_var = cur_var
        self.__cur_func = cur_func
        self.__cur_func_sign = cur_func_sign  # Boolean list for signs of literals ('True' for negative literal)
        self.__cur_comp = cur_comp
        self.__rule_counter = rule_counter

    def guess_sat_saturate_assignments(self):
        """
        Prints rules (3) and (7) which are responsible for guessing and saturating assignments
        of variables to domain values.
        """
        # MOD
        # domaining per rule variable
        # Print rule (3)
        for v in self.__cur_var:  # variables
            disjunction = ""
            if v in self.__subdoms:
                for t in self.__subdoms[v]:  # domain
                    disjunction += f"r{self.__rule_counter}_{v}({t}) | "
            else:
                for t in self.__terms:  # domain
                    disjunction += f"r{self.__rule_counter}_{v}({t}) | "
            if len(disjunction) > 0:
                disjunction = disjunction[:-3] + "."
                print(disjunction)

            # Print rule (7)
            if v in self.__subdoms:
                for t in self.__subdoms[v]:  # domain
                    # r1_x(1) :- sat. r1_x(2) :- sat. ...
                    print(f"r{self.__rule_counter}_{v}({t}) :- sat.")
            else:
                for t in self.__terms:  # domain
                    # r1_x(1) :- sat. r1_x(2) :- sat. ...
                    print(f"r{self.__rule_counter}_{v}({t}) :- sat.")

    def ensure_sat(self, head):
        """
        Prints rules (4) and (5) which are responsible for ensuring satisfiability.

        :param head: Head of the rule.
        """
        # SAT
        # Print rule (4) and (5)
        covered_cmp = {}  # reduce SAT rules when compare-operators are pre-checked
        for f in self.__cur_comp:
            arguments = [str(f.left), str(f.right)]  # all arguments (incl. duplicates / terms)
            var = list(dict.fromkeys(arguments))  # arguments (without duplicates / incl. terms)
            vars = list(dict.fromkeys(
                 [a for a in arguments if a in self.__cur_var]))  # which have to be grounded per combination

            dom_list = [self.__subdoms[v] if v in self.__subdoms else self.__terms for v in vars]
            combinations = [p for p in itertools.product(*dom_list)]

            vars_set = frozenset(vars)
            if vars_set not in covered_cmp:
                covered_cmp[vars_set] = set()

            for c in combinations:
                c_varset = tuple([c[vars.index(v)] for v in vars_set])
                if not self.__check_for_covered_subsets(covered_cmp, list(vars_set),
                                                         c_varset):  # smaller sets are also possible
                    # if c_varset not in covered_cmp[vars_set]:
                    f_args = ""
                    # vars in atom
                    interpretation = ""
                    for v in var:
                        interpretation += f"r{self.__rule_counter}_{v}({c[vars.index(v)]}), " if v in self.__cur_var else f""
                        f_args += f"{c[vars.index(v)]}," if v in self.__cur_var else f"{v},"
                    c1 = int(c[vars.index(var[0])] if var[0] in vars else var[0])
                    c2 = int(c[vars.index(var[1])] if var[1] in vars else var[1])
                    if not self.__compare_terms(f.comparison, c1, c2):
                        covered_cmp[vars_set].add(c_varset)
                        print(f"sat_r{self.__rule_counter} :- {interpretation[:-2]}.")

            self.__ensure_sat_pred(head, covered_cmp)

    def __ensure_sat_pred(self, head, covered_cmp):
        """
        Prints rules (4) and (5) for normal predicates.

        :param head: Head of the rule.
        """
        for f in self.__cur_func:
            args_len = len(f.arguments)
            if args_len == 0:
                print(
                    f"sat_r{self.__rule_counter} :-{'' if (self.__cur_func_sign[self.__cur_func.index(f)] or f is head) else ' not'} {f}.")
                continue
            arguments = re.sub(r'^.*?\(', '', str(f))[:-1].split(',')  # all arguments (incl. duplicates / terms)
            args_without_dup = list(
                dict.fromkeys(arguments)) if args_len > 0 else []  # arguments (without duplicates / incl. terms)
            # Variables which have to be grounded per combination
            vars = list(dict.fromkeys([a for a in arguments if
                                       a in self.__cur_var])) if args_len > 0 else []

            dom_list = [self.__subdoms[v] if v in self.__subdoms else self.__terms for v in vars]
            combinations = [p for p in itertools.product(*dom_list)]
            vars_set = frozenset(vars)

            for c in combinations:
                c_varset = tuple([c[vars.index(v)] for v in vars_set])
                if not self.__check_for_covered_subsets(covered_cmp, list(vars_set),
                                                        c_varset):  # smaller sets are also possible
                    # if vars_set not in covered_cmp or c_varset not in covered_cmp[vars_set]:
                    f_args = ""
                    # vars in atom
                    interpretation = ""
                    for v in args_without_dup:
                        interpretation += f"r{self.__rule_counter}_{v}({c[vars.index(v)]}), " if v in self.__cur_var else f""
                        f_args += f"{c[vars.index(v)]}," if v in self.__cur_var else f"{v},"

                    if len(f_args) > 0:
                        f_args = f"{f.name}({f_args[:-1]})"
                    else:
                        f_args = f"{f.name}"

                    print(
                        f"sat_r{self.__rule_counter} :- {interpretation}{'' if (self.__cur_func_sign[self.__cur_func.index(f)] or f is head) else 'not '}{f_args}.")

    def __check_for_covered_subsets(self, base, current, c_varset):
        """
        Checks if subset is already covered
        :param base: Dictionary of covered tuple subsets for a given variable set.
        :param current: List of given variables.
        :param c_varset: Tuple subset.
        :return: 'True' if subset is already covered, 'False' otherwise.
        """
        for key in base:
            if key.issubset(current):
                c = tuple([c_varset[current.index(p)] for p in list(key)])
                if c in base[key]:
                    return True
        return False

    def __compare_terms(self, comp, c1, c2):
        """
        Compares terms using the comparison opeator.

        :param comp: Given comparison operator.
        :param c1: First operand.
        :param c2: Second operand.
        :return: 'True' if comparison is true, 'False' otherwise.
        """
        if comp is int(clingo.ast.ComparisonOperator.Equal):
            return c1 == c2
        elif comp is int(clingo.ast.ComparisonOperator.NotEqual):
            return c1 != c2
        elif comp is int(clingo.ast.ComparisonOperator.GreaterEqual):
            return c1 >= c2
        elif comp is int(clingo.ast.ComparisonOperator.GreaterThan):
            return c1 > c2
        elif comp is int(clingo.ast.ComparisonOperator.LessEqual):
            return c1 <= c2
        elif comp is int(clingo.ast.ComparisonOperator.LessThan):
            return c1 < c2
        else:
            assert (False)  # not implemented

    def check_if_all_sat(self, bld):
        """
        Prints rules (6) and (8), which are responsible for checking if all rules
        of the program are satisfiable.
        """
        if self.__rule_counter > 0:
            parse_string(":- not sat.", lambda stm: bld.add(stm))
            # Prints rule (8)
            print(":- not sat.")
            # parse_string(f"sat :- {','.join([f'sat_r{i}' for i in range(1, transformer.counter+1)])}.",
            # lambda stm: self.bld.add(stm))

            # Prints rule (6)
            print(f"sat :- {','.join([f'sat_r{i}' for i in range(1, self.__rule_counter + 1)])}.")