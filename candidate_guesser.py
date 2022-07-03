"""
This module guesses answer set candidates.
"""

import itertools
import re


class CandidateGuesser:
    def guess_candidates(self, head, terms, subdoms, ground_guess, cur_var):
        """
        Prints rules that are responsible for guessing answer set candidates.

        :param head: Head of the rule.
        :param terms: Terms occurring in the program, e.g., ['1', '2'].
        :param subdoms: Domains of each variable separately, e.g.,  {'Y': ['1', '2'], 'Z': ['1', '2']}.
        :param ground_guess: 'True', if the option --ground-guess is used, 'False' otherwise.
        :param cur_var: List of variables occurring in the rule, e.g., ['X', 'Y', 'Z'].
        """
        # head
        h_args_len = len(head.arguments)
        h_args = re.sub(r'^.*?\(', '', str(head))[:-1].split(',')  # all arguments (incl. duplicates / terms)
        h_vars = list(dict.fromkeys(
            [a for a in h_args if a in cur_var]))  # which have to be grounded per combination

        # GUESS head
        # Print rule (1)
        if not ground_guess:
            print(f"{{{head}" + (
                f" : {','.join(f'_dom_{v}({v})' if v in subdoms else f'dom({v})' for v in h_vars)}}}."
                if h_args_len > 0 else "}."))
        else:
            dom_list = [subdoms[v] if v in subdoms else terms for v in h_vars]
            combinations = [p for p in itertools.product(*dom_list)]
            h_interpretations = [
                f"{head.name}({','.join(c[h_vars.index(a)] if a in h_vars else a for a in h_args)})" for c in
                combinations]
            print(f"{{{';'.join(h_interpretations)}}}." if h_args_len > 0 else f"{{{head.name}}}.")
