import itertools
import re


class CandidateGuesser:

    def guessCandidates(self, head, terms, subdoms, ground_guess, cur_var):
        # head
        h_args_len = len(head.arguments)
        h_args = re.sub(r'^.*?\(', '', str(head))[:-1].split(',')  # all arguments (incl. duplicates / terms)
        h_args_nd = list(dict.fromkeys(h_args))  # arguments (without duplicates / incl. terms)
        h_vars = list(dict.fromkeys(
            [a for a in h_args if a in cur_var]))  # which have to be grounded per combination

        rem = [v for v in cur_var if
               v not in h_vars]  # remaining variables not included in head atom (without facts)

        # GUESS head
        # Print rule (2)
        if not ground_guess:
            print(f"{{{head}" + (
                f" : {','.join(f'_dom_{v}({v})' if v in subdoms else f'dom({v})' for v in h_vars)}}}." if h_args_len > 0 else "}."))
        else:
            dom_list = [subdoms[v] if v in subdoms else terms for v in h_vars]
            combinations = [p for p in itertools.product(*dom_list)]
            h_interpretations = [
                f"{head.name}({','.join(c[h_vars.index(a)] if a in h_vars else a for a in h_args)})" for c in
                combinations]
            print(f"{{{';'.join(h_interpretations)}}}." if h_args_len > 0 else f"{{{head.name}}}.")