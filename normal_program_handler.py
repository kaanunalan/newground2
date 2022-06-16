"""
This module adds additional rules in order to ensure the justifiability in normal programs.
"""


import itertools
import re


class NormalProgramHandler:
    def __init__(self, terms, facts, subdoms, all_vars):
        self.__terms = terms  # Terms occurring in the program, e.g., ['1', '2']
        self.__facts = facts  # Facts, arities and arguments, e.g., {'_dom_X': {1: {'1'}}, '_dom_Y': {1: {'(1..2)'}}}
        self.__subdoms = subdoms  # Domains of each variable separately, e.g.,  {'Y': ['1', '2'], 'Z': ['1', '2']}
        self.__normal = False  # If this rule is under #program normal (extra rules for normal programs are added)
        self.__heads_complete = []  # Rule heads together with their arguments, e.g., ['a(X,Y)', 'b(2)']
        self.__all_vars = all_vars  # List of all variables occurring in the program, e.g., ['X', 'Y', 'Z']

    def add_auxiliary_predicates(self):
        """
        Adds auxiliary predicates modeling the precedence in the order of derivation
        and corresponding constraints taking care of transitivity by printing the rules
        (18) and (19).
        """
        for h1 in self.__heads_complete:
            for h2 in self.__heads_complete:
                if h1 != h2:
                    h1s_grounded = self.__ground_head(h1)
                    h2s_grounded = self.__ground_head(h2)
                    for h1_grounded in h1s_grounded:
                        for h2_grounded in h2s_grounded:
                            if h1_grounded != h2_grounded:
                                print(
                                    f"{h1_grounded}__before__{h2_grounded} | {h2_grounded}__before__{h1_grounded}.")
                                self.__prevent_transitivity(h1, h2, h1_grounded, h2_grounded)

    def __prevent_transitivity(self, h1, h2, h1_grounded, h2_grounded):
        """
        Prevents transitive relations between the auxiliary predicates
        added for the normal programs by printing the rules (19).

        :param h1: (non-ground) head
        :param h2: (non-ground) head
        :param h1_grounded: ground head
        :param h2_grounded: ground head
        """
        for h3 in self.__heads_complete:
            if h3 != h1 and h3 != h2:
                h3s_grounded = self.__ground_head(h3)
                for h3_grounded in h3s_grounded:
                    if h1_grounded != h2_grounded and h2_grounded != h3_grounded and h1_grounded != h3_grounded:
                        print(
                            f":- {h1_grounded}__before__{h2_grounded}, {h2_grounded}__before__{h3_grounded}, {h3_grounded}__before__{h1_grounded}.")

    def __ground_head(self, head):
        """
        Grounds a head (or an arbitrary predicate) and returns the possible groundings in a format
        that can be used as part of an auxiliary predicate, e.g., ['a__1_2', 'b__1'].
        If the given head is already ground, then this ground head is reformatted and returned.
        :param head: head (or an arbitrary predicate).
        :return: List of all possible groundings of the head.
        """
        head_args = re.sub(r'^.*?\(', '', str(head))[:-1].split(',')  # all arguments (incl. duplicates / terms)
        head_vars = list(dict.fromkeys(
            [a for a in head_args if a in self.__all_vars]))  # which have to be grounded per combination
        heads_grounded = []  # List for ground heads

        # If head does not have any variables, i.e., head is ground, return the head directly
        if len(head_vars) == 0:
            head_pred = str(head).split("(", 1)[0] if len(head_args) > 0 else head
            atoms = "_".join(arg for arg in head_args)
            heads_grounded.append(f"{head_pred}__{atoms}" if len(head_args) > 0 else f"{head_pred}")
            return heads_grounded

        # Ground the head using all combinations
        dom_list = [self.__subdoms[v] if v in self.__subdoms else self.__terms for v in head_vars]
        combs = [p for p in itertools.product(*dom_list)]
        for c in combs:
            head_pred = str(head).split("(", 1)[0] if len(head_args) > 0 else head
            atoms = "_".join(atom for atom in c)
            heads_grounded.append(f"{head_pred}__{atoms}" if len(c) > 0 else f"{head_pred}")
        return heads_grounded

    def derive_unjustifiability_normal(self, unfound_atom, f_interpretation, f_rem_atoms, head):
        """
        Derives the unjustifiability of an interpretation by printing the rule (20).

        :param unfound_atom: Atom indicating the unfoundedness of the rule.
        :param f_interpretation: Ground body literal. It should start with "not " so that the
        rule can be printed.
        :param f_rem_atoms: Atoms needed to prevent unfoundedness.
        :param head: Head of the rule.
        """
        if f_interpretation.startswith("not "):
            if not self.__is_in_facts(f_interpretation):
                heads_grounded = self.__ground_head(head)
                for head_grounded in heads_grounded:
                    unjustifiability_rule = f"{unfound_atom} :- {', '.join(f_rem_atoms)}"
                    unjustifiability_rule += ", " if len(f_rem_atoms) > 0 else ""
                    unjustifiability_rule += self.__reformat_pred(f_interpretation) + "__before__" + head_grounded + "."
                    print(unjustifiability_rule)

    def __is_in_facts(self, atom):
        """
        Determines if the given atom is a fact.

        :param atom: An atom.
        :return: 'True' if the given atom is a fact, 'False' otherwise.
        """
        atom_name = atom.split("(", 1)[0]
        if atom_name.startswith("not "):
            atom_name = atom_name[4:]
        # If the predicate arity is 0, check only if there is such an atom in facts
        if "()" in atom or "(" not in atom:
            if atom_name in self.__facts:
                return True
        body_args = re.sub(r'^.*?\(', "", str(atom))[:-1].split(",")  # all arguments (incl. duplicates / terms)
        body_args_joined = ",".join(body_args)
        if atom_name in self.__facts and len(body_args) in self.__facts[atom_name] \
                and body_args_joined in self.__facts[atom_name][len(body_args)]:
            return True
        return False

    def __reformat_pred(self, pred):
        """
        Reformats the predicate so that it can be processed as part of an auxiliary predicate,
        e.g., 'a(1,2)' to 'a__1_2'.

        :param pred: Predicate to be reformatted.
        :return: Reformatted predicate.
        """
        pred_name = pred.split("(", 1)[0]
        # If the predicate arity is 0, return the pred_name directly
        if "()" in pred or "(" not in pred:
            return pred_name
        pred_args = re.sub(r'^.*?\(', "", str(pred))[:-1].split(",")  # all arguments (incl. duplicates / terms)
        joined_args = "_".join(arg for arg in pred_args)
        return pred_name + "__" + joined_args

    def __get_normal(self):
        return self.__normal

    def __set_normal(self, normal):
        self.__normal = normal

    def __get_heads_complete(self):
        return self.__heads_complete

    normal = property(__get_normal, __set_normal)
    heads_complete = property(__get_heads_complete)
