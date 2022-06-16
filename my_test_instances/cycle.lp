% Syntax error with --ground and --ground-guess
#program normal.
b(1) :- a(X).
a(1) :- d(1), b(1).
d(1).
