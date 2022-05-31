"""
This module contains a utility class providing methods to help
with precompiling of comparison operators.
"""

import clingo.ast


class ComparisonPrecompilingUtils:

    @staticmethod
    def check_for_covered_subsets(base, current, c_varset):
        """
        Checks if a combination is already covered for given variable set.

        :param base: Dictionary of covered tuple subsets (combinations) for a given variable set.
        :param current: List of given variables.
        :param c_varset: Tuple subset.
        :return: 'True' if combination is already covered, 'False' otherwise.
        """
        for key in base:
            if key.issubset(current):
                c = tuple([c_varset[current.index(p)] for p in list(key)])
                if c in base[key]:
                    return True
        return False

    @staticmethod
    def compare_terms(comp, c1, c2):
        """
        Compares terms using the comparison operator.

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
