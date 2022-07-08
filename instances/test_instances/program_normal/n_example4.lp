% False solution if 'ground', unsatisfiable otherwise (see partial reducibility in tight ASP).
% --ground does not print the first two rules (those without #program rules.)
a(X,Y) :- c(X,Y).
d :- c(X,Y).
#program normal.
a(X,Y) :- b(X), c(Y,Z).
c(1,2).
b(1).