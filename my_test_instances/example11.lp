#program normal.
a(X,Y) :- b(X), c(Y,Z).
a(1,2) :- a(1,1).
b(1).
c(1,2).