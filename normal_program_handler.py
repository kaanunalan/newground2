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
                                self.__ensure_transitivity(h1, h2, h1_grounded, h2_grounded)

    def __ensure_transitivity(self, h1, h2, h1_grounded, h2_grounded):
        for h3 in self.__heads_complete:
            if h3 != h1 and h3 != h2:
                h3s_grounded = self.__ground_head(h3)
                for h3_grounded in h3s_grounded:
                    if h1_grounded != h2_grounded and h2_grounded != h3_grounded and h1_grounded != h3_grounded:
                        print(
                            f":- {h1_grounded}__before__{h2_grounded}, {h2_grounded}__before__{h3_grounded}, {h3_grounded}__before__{h1_grounded}.")

    def __ground_head(self, head):
        head_args = re.sub(r'^.*?\(', '', str(head))[:-1].split(',')  # all arguments (incl. duplicates / terms)
        head_vars = list(dict.fromkeys(
            [a for a in head_args if a in self.__all_vars]))  # which have to be grounded per combination
        dom_list = [self.__subdoms[v] if v in self.__subdoms else self.__terms for v in head_vars]
        combs = [p for p in itertools.product(*dom_list)]
        heads_grounded = []
        for c in combs:
            head_pred = str(head).split("(", 1)[0] if len(head_args) > 0 else head
            atoms = "_".join(atom for atom in c)
            heads_grounded.append(f"{head_pred}__{atoms}" if len(c) > 0 else f"{head_pred}")
        return heads_grounded

    def derive_unjustifiability_normal(self, unfound_atom, f_interpretation, f_rem_atoms, head, body_pred):
        if not self.__is_in_facts(f_interpretation):
            heads_grounded = self.__ground_head(head)
            for head_grounded in heads_grounded:
                unjustifiability_rule = f"{unfound_atom} :- {', '.join(f_rem_atoms)}"
                unjustifiability_rule += ", " if len(f_rem_atoms) > 0 else ""
                unjustifiability_rule += self.__reformat_pred(f_interpretation) + "__before__" + head_grounded + "."
                print(unjustifiability_rule)

    def __is_in_facts(self, body_pred):
        body_pred_name = body_pred.split("(", 1)[0]
        if body_pred_name.startswith("not "):
            body_pred_name = body_pred_name[4:]
        body_args = re.sub(r'^.*?\(', "", str(body_pred))[:-1].split(",")  # all arguments (incl. duplicates / terms)
        body_args_joined = ",".join(body_args)
        if body_pred_name in self.__facts and len(body_args) in self.__facts[body_pred_name] \
                and body_args_joined in self.__facts[body_pred_name][len(body_args)]:
            return True
        return False

    def __reformat_pred(self, pred):
        pred_name = pred.split("(", 1)[0]
        pred_args = re.sub(r'^.*?\(', "", str(pred))[:-1].split(",")  # all arguments (incl. duplicates / terms)
        if pred_args == [''] or pred_args == ["not "]:
            return pred_name
        joined_args = "_".join(arg for arg in pred_args)
        return pred_name + "__" + joined_args

    def __get_normal(self):
        return self.__normal

    def __set_normal(self, normal):
        self.__normal = normal

    def __get_heads_complete(self):
        return self.__heads_complete

    def __set_heads_complete(self, heads_complete):
        self.__heads_complete = heads_complete

    def __get_all_vars(self):
        return self.__all_vars

    def __set_all_vars(self, all_vars):
        self.__all_vars = all_vars

    normal = property(__get_normal, __set_normal)
    heads_complete = property(__get_heads_complete)
    all_vars = property(__get_all_vars, __set_all_vars)
