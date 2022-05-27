import itertools
import re

import clingo
import networkx as nx
from clingo.ast import Transformer, parse_string


class NglpDlpTransformer(Transformer):
    def __init__(self, bld, terms, facts, ng_heads, shows, subdoms, ground_guess, ground):
        self.__rules = False
        self.__ng = False  # If the program is non-ground
        self.__bld = bld
        self.__terms = terms  # Terms occuring in the program
        self.__facts = facts  # Facts, arities and arguments
        self.__ng_heads = ng_heads  # Rule heads with their arities
        self.__subdoms = subdoms  # Subdomains
        self.__ground_guess = ground_guess
        self.__ground = ground

        self.__cur_anon = 0  # Number of anonymous variables in a rule
        self.__cur_var = []  # List of variables in a rule
        self.__cur_func = []
        self.__cur_func_sign = []
        self.__cur_comp = []
        self.__shows = shows  # Predicates and their arities (for #show)
        self.__founded = {}
        self.__f = {}
        self.__rule_counter = 0  # Counts rules in the program
        self.__g_counter = 'A'

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
        # self.head = None

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
        if self.__ng:
            self.__rule_counter += 1
            if str(node.head) != "#false":
                head = self.__cur_func[0]
            else:
                head = None

            # MOD
            # domaining per rule variable
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

                if v in self.__subdoms:
                    for t in self.__subdoms[v]:  # domain
                        # r1_x(1) :- sat. r1_x(2) :- sat. ...
                        print(f"r{self.__rule_counter}_{v}({t}) :- sat.")
                else:
                    for t in self.__terms:  # domain
                        # r1_x(1) :- sat. r1_x(2) :- sat. ...
                        print(f"r{self.__rule_counter}_{v}({t}) :- sat.")

            # SAT
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

            for f in self.__cur_func:
                args_len = len(f.arguments)
                if args_len == 0:
                    print(
                        f"sat_r{self.__rule_counter} :-{'' if (self.__cur_func_sign[self.__cur_func.index(f)] or f is head) else ' not'} {f}.")
                    continue
                arguments = re.sub(r'^.*?\(', '', str(f))[:-1].split(',')  # all arguments (incl. duplicates / terms)
                var = list(
                    dict.fromkeys(arguments)) if args_len > 0 else []  # arguments (without duplicates / incl. terms)
                vars = list(dict.fromkeys([a for a in arguments if
                                           a in self.__cur_var])) if args_len > 0 else []  # which have to be grounded per combination

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
                        for v in var:
                            interpretation += f"r{self.__rule_counter}_{v}({c[vars.index(v)]}), " if v in self.__cur_var else f""
                            f_args += f"{c[vars.index(v)]}," if v in self.__cur_var else f"{v},"

                        if len(f_args) > 0:
                            f_args = f"{f.name}({f_args[:-1]})"
                        else:
                            f_args = f"{f.name}"

                        print(
                            f"sat_r{self.__rule_counter} :- {interpretation}{'' if (self.__cur_func_sign[self.__cur_func.index(f)] or f is head) else 'not '}{f_args}.")

            # FOUND NEW
            if head is not None:
                # head
                h_args_len = len(head.arguments)
                h_args = re.sub(r'^.*?\(', '', str(head))[:-1].split(',')  # all arguments (incl. duplicates / terms)
                h_args_nd = list(dict.fromkeys(h_args))  # arguments (without duplicates / incl. terms)
                h_vars = list(dict.fromkeys(
                    [a for a in h_args if a in self.__cur_var]))  # which have to be grounded per combination

                rem = [v for v in self.__cur_var if
                       v not in h_vars]  # remaining variables not included in head atom (without facts)

                # GUESS head
                if not self.__ground_guess:
                    print(f"{{{head}" + (
                        f" : {','.join(f'_dom_{v}({v})' if v in self.__subdoms else f'dom({v})' for v in h_vars)}}}." if h_args_len > 0 else "}."))
                else:
                    dom_list = [self.__subdoms[v] if v in self.__subdoms else self.__terms for v in h_vars]
                    combinations = [p for p in itertools.product(*dom_list)]
                    h_interpretations = [
                        f"{head.name}({','.join(c[h_vars.index(a)] if a in h_vars else a for a in h_args)})" for c in
                        combinations]
                    print(f"{{{';'.join(h_interpretations)}}}." if h_args_len > 0 else f"{{{head.name}}}.")
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

                for comp in self.__cur_comp:
                    g.add_edge(str(comp.left), str(comp.left))

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
                                dom_list = [self.__subdoms[v] if v in self.__subdoms else self.__terms for v in mis_vars]
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
                                self.__add_to_foundedness_check(head.name, h_args_len, combs_covered, self.__rule_counter,
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

                        dom_list = [self.__subdoms[v] if v in self.__subdoms else self.__terms for v in f_vars_needed + f_rem]
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
                                self.__add_to_foundedness_check(head.name, h_args_len, combs_covered, self.__rule_counter,
                                                                index_vars)

        else:  # found-check for ground-rules (if needed) (pred, arity, combinations, rule, indices)
            pred = str(node.head).split('(', 1)[0]
            arguments = re.sub(r'^.*?\(', '', str(node.head))[:-1].split(',')
            arity = len(arguments)
            arguments = ','.join(arguments)

            # If such a head predicate with the given arity exists but there is no such fact
            if pred in self.__ng_heads and arity in self.__ng_heads[pred] \
                    and not (pred in self.__facts and arity in self.__facts[pred] and arguments in self.__facts[pred][arity]):

                for body_atom in node.body:
                    if str(body_atom).startswith("not "):
                        neg = ""
                    else:
                        neg = "not "
                    print(f"r{self.__g_counter}_unfound({arguments}) :- "
                          f"{neg + str(body_atom)}.")
                self.__add_to_foundedness_check(pred, arity, [arguments.split(',')], self.__g_counter, range(0, arity))
                self.__g_counter = chr(ord(self.__g_counter) + 1)
            # print rule as it is
            self.__output_node_format_conform(node)

        self.__reset_after_rule()
        return node

    def visit_Literal(self, node):
        """
        Visits literal in the program. If it is not #false, its sign is saved.

        :param node: Literal in the program.
        :return: Node of the AST.
        """
        if str(node) != "#false":
            if node.atom.ast_type is clingo.ast.ASTType.SymbolicAtom:  # comparisons are reversed by parsing, therefore always using not is sufficient
                self.__cur_func_sign.append(str(node).startswith("not "))
        self.visit_children(node)
        return node

    def visit_Function(self, node):
        """
        Visits functions (or predicates) of the program and saves their names and arities.

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
        if (str(node) not in self.__cur_var) and str(node) not in self.__terms:
            if str(node) == '_':
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
        if node.name == 'rules':
            self.__rules = True
        else:
            self.__rules = False
        return node

    def visit_Comparison(self, node):
        """
        Checks if the comparison operands are variables or terms and saves them.
        
        :param node: Comparison in the program.
        :return: Ndoe of the AST.
        """
        # currently implements only terms/variables
        assert (
                node.left.ast_type is clingo.ast.ASTType.Variable or node.left.ast_type is clingo.ast.ASTType.SymbolicTerm)
        assert (
                node.right.ast_type is clingo.ast.ASTType.Variable or node.right.ast_type is clingo.ast.ASTType.SymbolicTerm)

        self.__cur_comp.append(node)
        self.visit_children(node)
        return node

    def __get_comp_operator(self, comp):
        """
        Gets the comparison operator as string.

        :param comp: Given comparison operator.
        :return: Corresponding string representing the comparison operator.
        """
        if comp is int(clingo.ast.ComparisonOperator.Equal):
            return "="
        elif comp is int(clingo.ast.ComparisonOperator.NotEqual):
            return "!="
        elif comp is int(clingo.ast.ComparisonOperator.GreaterEqual):
            return ">="
        elif comp is int(clingo.ast.ComparisonOperator.GreaterThan):
            return ">"
        elif comp is int(clingo.ast.ComparisonOperator.LessEqual):
            return "<="
        elif comp is int(clingo.ast.ComparisonOperator.LessThan):
            return "<"
        else:
            assert False  # not implemented

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

    def __get_vars_needed(self, h_vars, f_vars, f_rem, g):
        f_vars_needed = [f for f in f_vars if f in h_vars]  # bounded head vars which are needed for foundation
        for r in f_rem:
            for n in nx.dfs_postorder_nodes(g, source=r):
                if n in h_vars and n not in f_vars_needed:
                    f_vars_needed.append(n)
        return f_vars_needed

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

    def __output_node_format_conform(self, node):
        """
        Prints the rule node as a valid program rule.

        :param node: Rule in  the program.
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

    def print_sat_and_foundedness_rules(self, bld):
        if self.__rule_counter > 0:
            self.__print_sat_rules(bld)
            self.__print_foundedness_rules()


    def __print_sat_rules(self, bld):
        parse_string(":- not sat.", lambda stm: bld.add(stm))
        # Prints rule (8)
        print(":- not sat.")
        # parse_string(f"sat :- {','.join([f'sat_r{i}' for i in range(1, transformer.counter+1)])}.",
        # lambda stm: self.bld.add(stm))

        # Prints rule (6)
        print(f"sat :- {','.join([f'sat_r{i}' for i in range(1, self.__rule_counter + 1)])}.")

    def __print_foundedness_rules(self):
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
        if not self.__ground_guess:
            for t in self.__terms:
                print(f"dom({t}).")

    def handle_no_show(self, term_transformer, no_show):
        if not no_show:
            if not term_transformer.show:
                for f in self.__shows.keys():
                    for l in self.__shows[f]:
                        print(f"#show {f}/{l}.")
