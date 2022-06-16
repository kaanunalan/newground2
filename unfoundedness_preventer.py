"""
This module prevents unfoundedness.
"""

import itertools
import re

import networkx as nx

from comparison_precompiling_utils import ComparisonPrecompilingUtils


class UnfoundednessPreventer:
    def __init__(self, terms, facts, subdoms, ground_guess, cur_var, cur_func,
                 cur_func_sign, cur_comp, f, normal_program_handler):
        self.__terms = terms  # Terms occurring in the program, e.g., ['1', '2']
        self.__facts = facts  # Facts, arities and arguments, e.g., {'_dom_X': {1: {'1'}}, '_dom_Y': {1: {'(1..2)'}}}
        self.__subdoms = subdoms  # Domains of each variable separately, e.g.,  {'Y': ['1', '2'], 'Z': ['1', '2']}
        self.__ground_guess = ground_guess  # --ground-guess
        self.__cur_var = cur_var  # List of variables occurring in the rule, e.g., ['X', 'Y', 'Z']
        self.__cur_func = cur_func  # List of current predicates (and functions)
        self.__cur_func_sign = cur_func_sign  # Boolean list for signs of literals
        self.__cur_comp = cur_comp  # List of comparison operations occurring in the rule
        self.__f = f  # Contains information about foundedness rules
        self.__normal_program_handler = normal_program_handler

    def prevent_unfoundedness(self, head, rule_counter):
        """
        Prints the rules (8), (14) and (15) to prevent unfoundedness.

        :param head: Head of the rule.
        :param rule_counter: Counts the rules in the program.
        """
        # head
        h_args_len = len(head.arguments)
        h_args = re.sub(r'^.*?\(', '', str(head))[:-1].split(',')  # all arguments (incl. duplicates / terms)
        h_args_nd = list(dict.fromkeys(h_args))  # arguments (without duplicates / incl. terms)
        h_vars = list(dict.fromkeys(
            [a for a in h_args if a in self.__cur_var]))  # which have to be grounded per combination

        rem = [v for v in self.__cur_var if
               v not in h_vars]  # remaining variables not included in head atom (without facts)

        # dictionary that maps variables in the variable graph that do not occur in the head to variables in the head
        # if there is an edge between these two variables in the variable graph (reachable variables),
        # e.g., {'Z': ['Y']}
        g_r = {}

        # path checking
        g = nx.Graph()
        for f in self.__cur_func:
            f_args_len = len(f.arguments)
            f_args = re.sub(r'^.*?\(', '', str(f))[:-1].split(',')  # all arguments (incl. duplicates / terms)
            if f != head and f_args_len > 0:
                f_vars = list(dict.fromkeys(
                    [a for a in f_args if a in self.__cur_var]))  # which have to be grounded per combination
                for v1 in f_vars:
                    for v2 in f_vars:
                        g.add_edge(v1, v2)

        # Add an edge between comparison operands
        for comp in self.__cur_comp:
            g.add_edge(str(comp.left), str(comp.left))

        # Print rule (8) after determining the dependent variables
        for r in rem:
            g_r[r] = []
            for n in nx.dfs_postorder_nodes(g, source=r):
                if n in h_vars:
                    g_r[r].append(n)

            dom_list = [self.__subdoms[v] if v in self.__subdoms else self.__terms for v in g_r[r]]
            needed_combs = [p for p in itertools.product(*dom_list)]
            for c in needed_combs:
                if not self.__ground_guess:
                    head_interpretation = f"{head.name}" + (
                        f"({','.join([c[g_r[r].index(a)] if a in g_r[r] else a for a in h_args])})" if h_args_len > 0 else "")
                    rem_interpretation = ','.join([r] + [c[g_r[r].index(v)] for v in h_args_nd if v in g_r[r]])
                    doms = ','.join(f'dom({v})' for v in h_vars if v not in g_r[r])
                    if len(h_vars) == len(g_r[r]):  # removed none
                        print(
                            f"1<={{r{rule_counter}f_{r}({rem_interpretation}): dom({r})}}<=1 :- {head_interpretation}.")
                    elif len(g_r[r]) == 0:  # removed all
                        print(f"1<={{r{rule_counter}f_{r}({rem_interpretation}): dom({r})}}<=1.")
                    else:  # removed some
                        print(
                            f"1<={{r{rule_counter}f_{r}({rem_interpretation}): dom({r})}}<=1 :- {head_interpretation}, {doms}.")
                else:
                    head_interpretation = f"{head.name}" + (
                        f"({','.join([c[g_r[r].index(a)] if a in g_r[r] else a for a in h_args])})" if h_args_len > 0 else "")
                    rem_interpretation = ','.join([c[g_r[r].index(v)] for v in h_args_nd if v in g_r[r]])
                    rem_interpretations = ';'.join(
                        [f"r{rule_counter}f_{r}({v}{',' + rem_interpretation if h_args_len > 0 else ''})"
                         for v
                         in (self.__subdoms[r] if r in self.__subdoms else self.__terms)])
                    mis_vars = [v for v in h_vars if v not in g_r[r]]
                    if len(h_vars) == len(g_r[r]):  # removed none
                        print(f"1{{{rem_interpretations}}}1 :- {head_interpretation}.")
                    elif len(g_r[r]) == 0:  # removed all
                        print(f"1{{{rem_interpretations}}}1.")
                    else:  # removed some
                        dom_list = [self.__subdoms[v] if v in self.__subdoms else self.__terms for v in
                                    mis_vars]
                        combinations = [p for p in itertools.product(*dom_list)]
                        h_interpretations = [
                            f"{head.name}({','.join(c2[mis_vars.index(a)] if a in mis_vars else c[g_r[r].index(a)] for a in h_args)})"
                            for c2 in combinations]
                        for hi in h_interpretations:
                            print(f"1{{{rem_interpretations}}}1 :- {hi}.")

        covered_cmp = {}  # Compare-operators are pre-checked
        self.__derive_unjustifiability_comp(covered_cmp, head, h_args, h_vars, h_args_len, rem, g, g_r, rule_counter)
        self.__derive_unjustifiability_pred(covered_cmp, head, h_args, h_vars, h_args_len, rem, g, g_r, rule_counter)

    def __derive_unjustifiability_comp(self, covered_cmp, head, h_args, h_vars, h_args_len, rem, g, g_r, rule_counter):
        """
        Derives unjustifiability for comparison operators by printing the rules (14) and (15)
        in order to achieve more compact programs.

        :param covered_cmp: Dictionary of covered tuple subsets (combinations) of comparisons for a given variable set.
        :param head: Head of the rule.
        :param h_args: Head arguments with duplicates and terms.
        :param h_vars: Head variables (without duplicates and terms).
        :param h_args_len: Length of head arguments.
        :param rem: Variables that are not in head.
        :param g: Variable graph.
        :param g_r: Data structure representing variable dependencies for further processing.
        :param rule_counter: Counts the rules in the program.
        """
        # for every cmp operator
        for f in self.__cur_comp:
            f_args = [str(f.left), str(f.right)]  # all arguments (incl. duplicates / terms)
            f_args_nd = list(dict.fromkeys(f_args))  # arguments (without duplicates / incl. terms)
            f_vars = list(dict.fromkeys(
                [a for a in f_args if a in self.__cur_var]))  # which have to be grounded per combination

            f_rem = [v for v in f_vars if v in rem]  # remaining vars for current function (not in head)
            f_vars_needed = self.__get_vars_needed(h_vars, f_vars, f_rem, g)

            vars_set = frozenset(f_vars_needed + f_rem)
            if vars_set not in covered_cmp:
                covered_cmp[vars_set] = set()

            combs = [p for p in itertools.product(self.__terms, repeat=len(f_vars_needed) + len(f_rem))]
            for c in combs:
                c_varset = tuple(
                    [c[f_vars_needed.index(v)] if v in f_vars_needed else c[len(f_vars_needed) + f_rem.index(v)]
                     for v in vars_set])

                if not ComparisonPrecompilingUtils.check_for_covered_subsets(covered_cmp, list(vars_set),
                                                                             c_varset):  # smaller sets are also possible
                    # if c_varset not in covered_cmp[vars_set]:  # smaller sets are also possible
                    interpretation, interpretation_incomplete, combs_covered, index_vars = self.__generate_combination_information(
                        h_args, f_vars_needed, c, head)
                    if combs_covered is None or combs_covered == []:
                        continue
                    # generate body for unfound-rule
                    f_args_unf_left = f"{c[f_vars_needed.index(f_args[0])]}" if f_args[
                                                                                    0] in f_vars_needed else (
                        f"{f_args[0]}" if f_args[
                                              0] in self.__terms else f"{c[len(f_vars_needed) + f_rem.index(f_args[0])]}")
                    f_args_unf_right = f"{c[f_vars_needed.index(f_args[1])]}" if f_args[
                                                                                     1] in f_vars_needed else (
                        f"{f_args[1]}" if f_args[
                                              1] in self.__terms else f"{c[len(f_vars_needed) + f_rem.index(f_args[1])]}")

                    if not ComparisonPrecompilingUtils.compare_terms(f.comparison, f_args_unf_left, f_args_unf_right):
                        f_rem_atoms = [
                            f"r{rule_counter}f_{v}({','.join([c[len(f_vars_needed) + f_rem.index(v)]] + [i for id, i in enumerate(interpretation) if h_args[id] in g_r[v]])})"
                            for v in f_args_nd if v in rem]

                        covered_cmp[vars_set].add(c_varset)

                        unfound_atom = f"r{rule_counter}_unfound" + (
                            f"_{''.join(index_vars)}" if len(f_vars_needed) < len(h_vars) else "") + (
                                           f"({','.join(interpretation_incomplete)})" if len(
                                               interpretation_incomplete) > 0 else "")
                        print(unfound_atom + (
                            f" :- {', '.join(f_rem_atoms)}" if len(f_rem_atoms) > 0 else "") + ".")
                        # print (f"{h_args_len} | {combs_covered} | {index_vars}")
                        self.__add_to_foundedness_check(head.name, h_args_len, combs_covered,
                                                        rule_counter, index_vars)

    def __derive_unjustifiability_pred(self, covered_cmp, head, h_args, h_vars, h_args_len, rem, g, g_r, rule_counter):
        """
        Derives unjustifiability for body predicates by printing the rules (14) and (15).

        :param covered_cmp: Dictionary of covered tuple subsets (combinations) of comparisons for a given variable set.
        :param head: Head of the rule.
        :param h_args: Head arguments with duplicates and terms.
        :param h_vars: Head variables (without duplicates and terms).
        :param h_args_len: Length of head arguments.
        :param rem: Variables that are not in head.
        :param g: Variable graph.
        :param g_r: Data structure representing variable dependencies for further processing.
        :param rule_counter: Counts the rules in the program.
        """
        print(covered_cmp)
        # over every body-atom
        for f in self.__cur_func:
            if f != head:
                f_args_len = len(f.arguments)
                f_args = re.sub(r'^.*?\(', '', str(f))[:-1].split(
                    ',')  # all arguments (incl. duplicates / terms)
                f_args_nd = list(dict.fromkeys(f_args))  # arguments (without duplicates / incl. terms)
                f_vars = list(dict.fromkeys(
                    [a for a in f_args if a in self.__cur_var]))  # which have to be grounded per combination

                f_rem = [v for v in f_vars if v in rem]  # remaining vars for current function (not in head)

                f_vars_needed = self.__get_vars_needed(h_vars, f_vars, f_rem, g)

                vars_set = frozenset(f_vars_needed + f_rem)

                dom_list = [self.__subdoms[v] if v in self.__subdoms else self.__terms for v in
                            f_vars_needed + f_rem]
                combs = [p for p in itertools.product(*dom_list)]

                for c in combs:
                    c_varset = tuple(
                        [c[f_vars_needed.index(v)] if v in f_vars_needed else c[
                            len(f_vars_needed) + f_rem.index(v)]
                         for v in vars_set])
                    if not ComparisonPrecompilingUtils.check_for_covered_subsets(covered_cmp, list(vars_set),
                                                                                 c_varset):  # smaller sets are also possible
                        # if vars_set not in covered_cmp or c_varset not in covered_cmp[vars_set]:
                        interpretation, interpretation_incomplete, combs_covered, index_vars = self.__generate_combination_information(
                            h_args, f_vars_needed, c, head)
                        if combs_covered is None or combs_covered == []:
                            continue

                        # generate body for unfound-rule
                        if f_args_len > 0:
                            f_args_unf = ""
                            for v in f_args:
                                f_args_unf += f"{c[f_vars_needed.index(v)]}," if v in f_vars_needed else \
                                    (
                                        f"{v}," if v in self.__terms else f"{c[len(f_vars_needed) + f_rem.index(v)]},")
                            f_interpretation = f"{f.name}({f_args_unf[:-1]})"
                        else:
                            f_interpretation = f"{f.name}"

                        f_rem_atoms = [
                            f"r{rule_counter}f_{v}({','.join([c[len(f_vars_needed) + f_rem.index(v)]] + [i for id, i in enumerate(interpretation) if h_args[id] in g_r[v]])})"
                            for v in f_args_nd if v in rem]

                        f_interpretation = ('' if self.__cur_func_sign[
                            self.__cur_func.index(f)] else "not ") + f_interpretation
                        # r1_unfound(V1,V2) :- p(V1,V2), not f(Z), r1_Z(Z,V1,V2).
                        unfound_atom = f"r{rule_counter}_unfound" + (
                            f"_{''.join(index_vars)}" if len(f_vars_needed) < len(h_vars) else "") + (
                                           f"({','.join(interpretation_incomplete)})" if len(
                                               interpretation_incomplete) > 0 else "")
                        print(unfound_atom + f" :- "
                                             f"{', '.join([f_interpretation] + f_rem_atoms)}.")

                        # Ensure justifiability of normal programs if #program normal
                        if self.__normal_program_handler.normal:
                            body_literal = ("" if self.__cur_func_sign[self.__cur_func.index(f)] else "not ") + str(f)
                            self.__normal_program_handler.derive_unjustifiability_normal(
                                unfound_atom, f_interpretation, f_rem_atoms, str(head), body_literal)

                        # predicate arity combinations rule indices
                        self.__add_to_foundedness_check(head.name, h_args_len, combs_covered,
                                                        rule_counter, index_vars)

    def __add_to_foundedness_check(self, pred, arity, combinations, rule, indices):
        """
        Adds to list of unfoundedness rules in order to use the information
        to print rules that prevent unfoundedness.

        :param pred: Predicate.
        :param arity: Arity of the predicate.
        :param combinations: List of possible grounding combinations.
        :param rule: Dictionary that maps rule numbers to unfoundedness rule indices.
        :param indices: Indices of the unfoundedness rules.
        :return:
        """
        indices = tuple(indices)

        for c in combinations:
            c = tuple(c)
            if pred not in self.__f:
                self.__f[pred] = {}
                self.__f[pred][arity] = {}
                self.__f[pred][arity][c] = {}
                self.__f[pred][arity][c][rule] = {indices}
            elif arity not in self.__f[pred]:
                self.__f[pred][arity] = {}
                self.__f[pred][arity][c] = {}
                self.__f[pred][arity][c][rule] = {indices}
            elif c not in self.__f[pred][arity]:
                self.__f[pred][arity][c] = {}
                self.__f[pred][arity][c][rule] = {indices}
            elif rule not in self.__f[pred][arity][c]:
                self.__f[pred][arity][c][rule] = {indices}
            else:
                self.__f[pred][arity][c][rule].add(indices)

    def __get_vars_needed(self, h_vars, f_vars, f_rem, g):
        """
        Gets bounded head variables which are needed for foundedness.
        :param h_vars: Variables occurring in head.
        :param f_vars: Variables occurring in a predicate of rule body.
        :param f_rem: Variables occurring in body predicate but not in head.
        :param g: Variable graph.
        :return: List of needed head variables in order to ensure foundedness.
        """
        f_vars_needed = [f for f in f_vars if f in h_vars]  # bounded head vars which are needed for foundation
        for r in f_rem:
            for n in nx.dfs_postorder_nodes(g, source=r):
                if n in h_vars and n not in f_vars_needed:
                    f_vars_needed.append(n)
        return f_vars_needed

    def __generate_combination_information(self, h_args, f_vars_needed, c, head):
        """
        Generates some information using the grounding combination in order to use it for ensuring justifiability.

        :param h_args: List of head arguments.
        :param f_vars_needed: List of bounded head variables needed to get combination information.
        :param c: A possible combination.
        :param head: Head node.
        :return: Information about combinations needed for unfoundedness checks.
        """
        interpretation = []  # interpretation-list
        interpretation_incomplete = []  # uncomplete; without removed vars
        nnv = []  # not needed vars
        combs_covered = []  # combinations covered with the (reduced combinations); len=1 when no variable is removed

        if h_args == ['']:  # catch head/0
            return interpretation, interpretation_incomplete, [['']], [str(h_args.index(v)) for v in h_args if
                                                                       v in f_vars_needed or v in self.__terms]

        for id, v in enumerate(h_args):
            if v not in f_vars_needed and v not in self.__terms:
                nnv.append(v)
            else:
                interpretation_incomplete.append(c[f_vars_needed.index(v)] if v in f_vars_needed else v)
            interpretation.append(c[f_vars_needed.index(v)] if v in f_vars_needed else v)

        head_interpretation = ','.join(interpretation)  # can include vars

        nnv = list(dict.fromkeys(nnv))

        if len(nnv) > 0:
            dom_list = [self.__subdoms[v] if v in self.__subdoms else self.__terms for v in nnv]
            combs_left_out = [p for p in itertools.product(*dom_list)]  # combinations for vars left out in head
            # create combinations covered for later use in constraints
            for clo in combs_left_out:
                covered = interpretation.copy()
                for id, item in enumerate(covered):
                    if item in nnv:
                        covered[id] = clo[nnv.index(item)]
                if head.name in self.__facts and len(h_args) in self.__facts[head.name] and ','.join(covered) in \
                        self.__facts[head.name][len(h_args)]:
                    # no foundation check for this combination, its a fact!
                    continue
                combs_covered.append(covered)
        else:
            if head.name in self.__facts and len(h_args) in self.__facts[head.name] and head_interpretation in \
                    self.__facts[head.name][len(h_args)]:
                # no foundation check for this combination, its a fact!
                return None, None, None, None
            combs_covered.append(interpretation)

        index_vars = [str(h_args.index(v)) for v in h_args if v in f_vars_needed or v in self.__terms]

        return interpretation, interpretation_incomplete, combs_covered, index_vars

    def check_found_ground_rules(self, node, ng_heads, g_counter):
        """
        Checks foundedness of ground rules if needed.

        :param node: Node of the rule.
        :param ng_heads: Rule heads with their arities, e.g., {'d': {1}, 'a': {2}}.
        :param g_counter: Counts the ground rules that are checked for unfoundedness.
        :return: Next character for g_counter.
        """
        head_pred = str(node.head).split('(', 1)[0]
        head_arguments_list = re.sub(r'^.*?\(', '', str(node.head))[:-1].split(',')
        arity = len(head_arguments_list)
        head_arguments = ','.join(head_arguments_list)
        # If such a (non-ground) head predicate with the given arity exists but there is no such fact
        if head_pred in ng_heads and arity in ng_heads[head_pred] \
                and not (head_pred in self.__facts and arity in self.__facts[head_pred]
                         and head_arguments in self.__facts[head_pred][arity]):
            for body_atom in node.body:
                if str(body_atom).startswith("not "):
                    neg = ""
                else:
                    neg = "not "
                print(f"r{g_counter}_unfound({head_arguments}) :- "
                      + f"{neg + str(body_atom)}.")

                # Ensure justifiability of normal programs if #program normal
                if self.__normal_program_handler.normal:
                    self.__normal_program_handler.derive_unjustifiability_normal(
                        f"r{g_counter}_unfound({head_arguments})",
                        str(body_atom), [],
                        str(node.head), neg + str(body_atom))

            self.__add_to_foundedness_check(head_pred, arity, [head_arguments.split(',')], g_counter, range(0, arity))
            return chr(ord(g_counter) + 1)

    def prevent_unfounded_rules(self, rule_counter):
        """
        Prints rules (16), which prevent unfounded results.

        :param rule_counter: Counts the rules in the program.
        """
        if rule_counter > 0:
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
