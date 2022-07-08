#program normal.
a(X,Y) :- b(X), c(Y,Z).
b(1).
c(1,2).
c(Y,X) :- b(X), a(Y,X).