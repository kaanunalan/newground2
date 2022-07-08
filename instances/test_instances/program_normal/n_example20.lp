#program normal.
a(X,Y) :- b(X), c(Y,Z).
a(X,Y) :- d(X,Y).
c(X,Y) :- a(X,Y).
d(2,2).
b(1).
c(1,2).