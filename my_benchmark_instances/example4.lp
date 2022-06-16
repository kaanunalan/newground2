% Unsatisfiable with --ground, false solution otherwise
a(X,Y) :- c(X,Y).
d :- c(X,Y).
#program rules.
a(X,Y) :- b(X), c(Y,Z).
c(1,2).
b(1).
