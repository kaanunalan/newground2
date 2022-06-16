% Syntax error with --ground and --ground-guess
#program rules.
a(X) :- a(2), c(X,Y).
a(2) :- a(X).
a(X) :- c(X,Y).
c(1,2).
b(2).