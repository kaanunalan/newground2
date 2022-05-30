# TODO: Add doc, smaller methods, less duplicates and dependencies
import itertools
import re

import clingo.ast
import networkx as nx


class UnfoundednessPreventer:

    def __init__(self, terms, facts, subdoms, ground_guess, cur_var, cur_func, cur_func_sign, cur_comp, f, rule_counter):
        self.__terms = terms
        self.__facts = facts
        self.__subdoms = subdoms
        self.__ground_guess = ground_guess
        self.__cur_var = cur_var
        self.__cur_func = cur_func
        self.__cur_func_sign = cur_func_sign  # Boolean list for signs of literals
        self.__cur_comp = cur_comp
        self.__f = f
        self.__rule_counter = rule_counter

    def prevent_unfoundedness(self, head):
        # TODO: Duplicate
        # head
        h_args_len = len(head.arguments)
        h_args = re.sub(r'^.*?\(', '', str(head))[:-1].split(',')  # all arguments (incl. duplicates / terms)
        h_args_nd = list(dict.fromkeys(h_args))  # arguments (without duplicates / incl. terms)
        h_vars = list(dict.fromkeys(
            [a for a in h_args if a in self.__cur_var]))  # which have to be grounded per combination

        rem = [v for v in self.__cur_var if
               v not in h_vars]  # remaining variables not included in head atom (without facts)

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

        # Print rule (9) after creating the variable graph
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
                            f"1<={{r{self.__rule_counter}f_{r}({rem_interpretation}): dom({r})}}<=1 :- {head_interpretation}.")
                    elif len(g_r[r]) == 0:  # removed all
                        print(f"1<={{r{self.__rule_counter}f_{r}({rem_interpretation}): dom({r})}}<=1.")
                    else:  # removed some
                        print(
                            f"1<={{r{self.__rule_counter}f_{r}({rem_interpretation}): dom({r})}}<=1 :- {head_interpretation}, {doms}.")
                else:
                    head_interpretation = f"{head.name}" + (
                        f"({','.join([c[g_r[r].index(a)] if a in g_r[r] else a for a in h_args])})" if h_args_len > 0 else "")
                    rem_interpretation = ','.join([c[g_r[r].index(v)] for v in h_args_nd if v in g_r[r]])
                    rem_interpretations = ';'.join(
                        [f"r{self.__rule_counter}f_{r}({v}{',' + rem_interpretation if h_args_len > 0 else ''})"
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

        covered_cmp = {}
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

                if not self.__check_for_covered_subsets(covered_cmp, list(vars_set),
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

                    if not self.__compare_terms(f.comparison, f_args_unf_left, f_args_unf_right):
                        f_rem_atoms = [
                            f"r{self.__rule_counter}f_{v}({','.join([c[len(f_vars_needed) + f_rem.index(v)]] + [i for id, i in enumerate(interpretation) if h_args[id] in g_r[v]])})"
                            for v in f_args_nd if v in rem]

                        covered_cmp[vars_set].add(c_varset)

                        unfound_atom = f"r{self.__rule_counter}_unfound" + (
                            f"_{''.join(index_vars)}" if len(f_vars_needed) < len(h_vars) else "") + (
                                           f"({','.join(interpretation_incomplete)})" if len(
                                               interpretation_incomplete) > 0 else "")
                        print(unfound_atom + (
                            f" :- {', '.join(f_rem_atoms)}" if len(f_rem_atoms) > 0 else "") + ".")
                        # print (f"{h_args_len} | {combs_covered} | {index_vars}")
                        self.__add_to_foundedness_check(head.name, h_args_len, combs_covered,
                                                        self.__rule_counter,
                                                        index_vars)

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
                    if not self.__check_for_covered_subsets(covered_cmp, list(vars_set),
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
                            f"r{self.__rule_counter}f_{v}({','.join([c[len(f_vars_needed) + f_rem.index(v)]] + [i for id, i in enumerate(interpretation) if h_args[id] in g_r[v]])})"
                            for v in f_args_nd if v in rem]

                        f_interpretation = ('' if self.__cur_func_sign[
                            self.__cur_func.index(f)] else 'not ') + f_interpretation
                        # r1_unfound(V1,V2) :- p(V1,V2), not f(Z), r1_Z(Z,V1,V2).
                        unfound_atom = f"r{self.__rule_counter}_unfound" + (
                            f"_{''.join(index_vars)}" if len(f_vars_needed) < len(h_vars) else "") + (
                                           f"({','.join(interpretation_incomplete)})" if len(
                                               interpretation_incomplete) > 0 else "")
                        print(unfound_atom + f" :- "
                                             f"{', '.join([f_interpretation] + f_rem_atoms)}.")

                        # predicate arity combinations rule indices
                        self.__add_to_foundedness_check(head.name, h_args_len, combs_covered,
                                                        self.__rule_counter,
                                                        index_vars)

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

    def __add_to_foundedness_check(self, pred, arity, combinations, rule, indices):
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
        f_vars_needed = [f for f in f_vars if f in h_vars]  # bounded head vars which are needed for foundation
        for r in f_rem:
            for n in nx.dfs_postorder_nodes(g, source=r):
                if n in h_vars and n not in f_vars_needed:
                    f_vars_needed.append(n)
        return f_vars_needed

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

    def __generate_combination_information(self, h_args, f_vars_needed, c, head):
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
