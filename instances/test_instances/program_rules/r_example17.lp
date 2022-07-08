% Cyclic program. False solution with #program rules, #program normal instead.
% Syntax error with --ground and --ground-guess.
#program rules.
b(1) :- a(X).
a(1) :- d(1), b(1).
d(1).
