"""
This module adds additional rules in order to ensure the justifiability in normal programs.
"""


import itertools
import re


class NormalProgramHandler:
    def __init__(self, terms, facts, subdoms):
        self.__terms = terms  # Terms occurring in the program, e.g., ['1', '2']
        self.__facts = facts  # Facts, arities and arguments, e.g., {'_dom_X': {1: {'1'}}, '_dom_Y': {1: {'(1..2)'}}}
        self.__subdoms = subdoms  # Domains of each variable separately, e.g.,  {'Y': ['1', '2'], 'Z': ['1', '2']}
        self.__cur_func = []  # List of current predicates (and functions)
        self.__normal = False  # If this rule is under #program normal (extra rules for normal programs are added)
        self.__provability_dict = {}  # Maps index of body to proved body {1: ['r1_posbody1_ok(1)', 'r1_posbody1_ok(2)']

    def ensure_justifiability_normal_programs(self, f_interpretation, f_rem_atoms, rule_counter, body_literal,
                                              cur_func):
        """
        Ensures the justifiability for normal programs by deriving their provability.

        :param f_interpretation: Ground body literal. Positive body literals start with "not ".
        :param f_rem_atoms: Atoms needed to prevent unfoundedness.
        :param rule_counter: Counts the rules in the program.
        :param body_literal: (Non-ground) body literal.
        :param cur_func: Predicates of the current rule.
        """
        if f_interpretation.startswith("not "):
            self.__derive_provability_positive_body_atom(f_interpretation, f_rem_atoms,
                                                         rule_counter, body_literal, cur_func)
        else:
            self.__derive_provability_negative_body_atom(f_interpretation, f_rem_atoms,
                                                         rule_counter, body_literal, cur_func)

    def __derive_provability_positive_body_atom(self, f_interpretation, f_rem_atoms,
                                                rule_counter, body_literal, cur_func):
        """
        Derives the provability of a positive body atom.

        :param f_interpretation: Ground body literal. It starts with "not ".
        :param f_rem_atoms: Atoms needed to prevent unfoundedness.
        :param rule_counter: Counts the rules in the program.
        :param body_literal: (Non-ground) body literal.
        :param cur_func: Predicates of the current rule.
        """
        f_interpretation = f_interpretation[4:]
        pos_body_ok = f"r{rule_counter}_posbody{cur_func.index(body_literal)}_ok"
        joined_args = self.__get_joined_arguments(f_interpretation)
        pos_body_ok += f"({joined_args})" if joined_args != "" else ""
        provability_pos_atom_rule = f"{pos_body_ok} :- {', '.join(f_rem_atoms)}"
        provability_pos_atom_rule += ", " if len(f_rem_atoms) > 0 else ""
        provability_pos_atom_rule += f"{f_interpretation}, proven_{f_interpretation}."

        print(provability_pos_atom_rule)
        self.__add_to_provability_list(cur_func.index(body_literal), pos_body_ok)

    def __derive_provability_negative_body_atom(self, f_interpretation, f_rem_atoms,
                                                rule_counter, body_literal, cur_func):
        """
        Derives the provability of a negative body atom.

        :param f_interpretation: Ground body literal. It starts with "not ".
        :param f_rem_atoms: Atoms needed to prevent unfoundedness.
        :param rule_counter: Counts the rules in the program.
        :param body_literal: (Non-ground) body literal.
        :param cur_func: Predicates of the current rule.
        """
        f_interpretation = "not " + f_interpretation
        neg_body_ok = f"r{rule_counter}_negbody{cur_func.index(body_literal)}_ok"
        joined_args = self.__get_joined_arguments(f_interpretation)
        neg_body_ok += f"({joined_args})" if joined_args != "" else ""
        provability_neg_atom_rule = f"{neg_body_ok} :- {', '.join(f_rem_atoms)}"
        provability_neg_atom_rule += ", " if len(f_rem_atoms) > 0 else ""
        provability_neg_atom_rule += f"{f_interpretation}."

        print(provability_neg_atom_rule)
        self.__add_to_provability_list(cur_func.index(body_literal), neg_body_ok)

    def __add_to_provability_list(self, body_index, body_ok):
        """
        Saves the rule indicating that the body is derived.

        :param body_index: Index indicating which literal in the rule the body is.
        :param body_ok: Rule showing that the body is derived.
        """
        if body_index not in self.__provability_dict:
            self.__provability_dict[body_index] = []
        self.__provability_dict[body_index].append(body_ok)

    def prove_head(self, head, cur_var, cur_func):
        """
        Proves the head of the rule.

        :param head: Rule head.
        :param cur_var: List of variables occurring in the rule, e.g., ['X', 'Y', 'Z'].
        :param cur_func: List of current predicates.
        """
        grounded_heads = self.__ground_head(head, cur_var)
        for h in grounded_heads:
            self.__ensure_provability_head(h)
            self.__derive_provability_head(h, head, cur_var, cur_func)
        self.__reset_dict()

    def __ensure_provability_head(self, head):
        """
        Ensures that the head is provable.

        :param head: Rule head.
        """
        print(f":- {head}, not proven_{head}.")

    def __derive_provability_head(self, ground_head, non_ground_head, cur_var, cur_func):
        """
        Derives that the rule head is provable.

        :param ground_head: Ground head.
        :param non_ground_head: Non-ground head.
        :param cur_var: List of variables occurring in the rule, e.g., ['X', 'Y', 'Z'].
        :param cur_func: List of current predicates.
        """
        # Get all combinations of values for provable bodies
        provable_combs = list(itertools.product(*(self.__provability_dict[index] for index in self.__provability_dict)))
        #  For each combination to prove the head
        for c in provable_combs:
            same_variables_counter = 0  # Count the same variables of head and body
            same_values_counter = 0  # Count the same values at places of same variables
            # For each predicate of the current rule
            for body in cur_func:
                # If this predicate is not the head
                if cur_func.index(body) != 0:
                    h_args = re.sub(r'^.*?\(', "", str(non_ground_head))[:-1].split(
                        ",")  # all head arguments (incl. duplicates / terms)
                    # For each head argument
                    for h_arg in h_args:
                        b_args = re.sub(r'^.*?\(', "", str(body))[:-1].split(
                            ",")  # all body arguments (incl. duplicates / terms)
                        # For each body argument
                        for b_arg in b_args:
                            # If head and body variables are the same
                            if h_arg == b_arg and h_arg in cur_var:
                                # Get the value of provable body at the place of the variable in body
                                same_variables_counter += 1
                                body_index = cur_func.index(body)
                                provable_body = c[body_index-1]
                                provable_body_args = re.sub(r'^.*?\(', "", str(provable_body))[:-1].split(",")  # all body arguments (incl. duplicates / terms)
                                body_value = provable_body_args[b_args.index(b_arg)]
                                ground_head_args = re.sub(r'^.*?\(', "", str(ground_head))[:-1].split(",")  # all body arguments (incl. duplicates / terms)
                                ground_head_value = ground_head_args[h_args.index(h_arg)]
                                # If provable body and ground head have the same values for the specific variable
                                if body_value == ground_head_value:
                                    same_values_counter += 1
            #  Print the rule if the number of same variables and same values the same
            if same_values_counter == same_variables_counter:
                print(f"proven_{ground_head} :- {', '.join(c)}.")

    def derive_provability_ground_head(self, node, cur_var, cur_func, g_counter):
        """
        Derives that the ground head, which may also be a fact, is provable.

        :param node: Rule node of the syntax tree.
        :param cur_var: List of variables occurring in the rule, e.g., ['X', 'Y', 'Z'].
        :param cur_func: List of current predicates.
        :param g_counter: Counts the ground rules that are checked for unfoundedness.
        """
        head = str(node.head)
        if self.__is_in_facts(head):
            print(f"proven_{head}.")
        if self.__is_interval(head):
            decomposed_preds = self.__decompose_interval(head)
            for dp in decomposed_preds:
                print(f"proven_{dp}.")
        else:
            self.__derive_provability_ground_head_no_fact(node, cur_func, g_counter)
            self.prove_head(head, cur_var, cur_func)

    def __decompose_interval(self, pred):
        """
        Decomposes an interval into its arguments.

        :param pred: Predicate with interval argument.
        :return: List of predicates with the decomposed interval.
        """
        pred_name = pred.split("(", 1)[0]
        body_args = re.sub(r'^.*?\(', "", str(pred))[:-1].split(",")  # all arguments (incl. duplicates / terms)
        interval_args = body_args[0].split("..")
        interval_args[0] = interval_args[0][1:]
        interval_args[1] = interval_args[1][:-1]
        decomposed_pred1 = f"{pred_name}({interval_args[0]})"
        decomposed_pred2 = f"{pred_name}({interval_args[1]})"
        return [decomposed_pred1, decomposed_pred2]

    def __reset_dict(self):
        """
        Resets the proved bodies.
        """
        self.__provability_dict = {}

    def __get_joined_arguments(self, pred):
        """
        Gives the arguments of a predicate as a string joined by commas, e.g., "1,2,3".
        :param pred: A predicate.
        :return: String of arguments.
        """
        # Return an empty string for atoms with arity 0
        if "()" in pred or "(" not in pred:
            return ""
        pred_args = re.sub(r'^.*?\(', "", str(pred))[:-1].split(",")  # all arguments (incl. duplicates / terms)
        
        return ",".join(arg for arg in pred_args)

    def __is_in_facts(self, pred):
        """
        Checks if the given predicate is a fact.

        :param pred: A predicate.
        :return: 'True' if the given predicate is a fact, 'False' otherwise.
        """
        pred_name = pred.split("(", 1)[0]
        if pred_name.startswith("not "):
            pred_name = pred_name[4:]
        body_args = re.sub(r'^.*?\(', "", str(pred))[:-1].split(",")  # all arguments (incl. duplicates / terms)
        body_args_joined = ",".join(body_args)
        if pred_name in self.__facts and len(body_args) in self.__facts[pred_name] \
                and body_args_joined in self.__facts[pred_name][len(body_args)]:
            return True
        return

    def __is_interval(self, pred):
        """
        Checks if the given predicate has an interval argument.

        :param pred: A predicate.
        :return: 'True' if the given arguments represent an interval, 'False' otherwise.
        """
        pred_name = pred.split("(", 1)[0]
        args = re.sub(r'^.*?\(', "", str(pred))[:-1].split(",")  # all arguments (incl. duplicates / terms)
        if len(args) == 1:
            interval_args = args[0].split("..")
            if len(interval_args) == 2 and interval_args[0].startswith("(") and interval_args[1].endswith(")"):
                return True
        return False


    def __ground_head(self, head, cur_var):
        """
        Grounds a (non-ground) head.

        :param head: Rule head.
        :param cur_var: List of variables occurring in the rule, e.g., ['X', 'Y', 'Z'].
        :return: List of ground combinations of the head.
        """
        head_args = re.sub(r'^.*?\(', '', str(head))[:-1].split(',')  # all arguments (incl. duplicates / terms)
        head_vars = list(dict.fromkeys(
            [a for a in head_args if a in cur_var]))  # which have to be grounded per combination
        if len(head_vars) == 0:
            return [head]
        dom_list = [self.__subdoms[v] if v in self.__subdoms else self.__terms for v in head_vars]
        combs = [p for p in itertools.product(*dom_list)]
        heads_grounded = []
        for c in combs:
            head_pred = str(head).split("(", 1)[0] if len(head_args) > 0 else head
            atoms = ",".join(atom for atom in c)
            heads_grounded.append(f"{head_pred}({atoms})" if len(c) > 0 else f"{head_pred}")
        return heads_grounded

    def __derive_provability_ground_head_no_fact(self, node, cur_func, g_counter):
        """
        Derives that the ground head, which is not a fact, is provable.

        :param node: Rule node of the syntax tree.
        :param cur_func: List of current predicates.
        :param g_counter: Counts the ground rules that are checked for unfoundedness.
        """
        for index, body_pred in enumerate(cur_func):
            # Ensure that the predicate is not the head
            if index != 0:
                if str(node.body[index-1]).startswith("not "):
                    neg = ""
                else:
                    neg = "not "
                self.ensure_justifiability_normal_programs(neg + str(body_pred), [], g_counter, body_pred, cur_func)

    def __get_normal(self):
        return self.__normal

    def __set_normal(self, normal):
        self.__normal = normal

    normal = property(__get_normal, __set_normal)
