% Unsatisfiable with --ground-guess and no option, false solution if 'ground'
a(X,Y) :- c(X,Y).
d :- c(X,Y).
#program normal.
a(X,Y) :- b(X), c(Y,Z).
c(1,2).
b(1).
