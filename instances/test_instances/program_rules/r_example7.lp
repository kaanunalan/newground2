#program rules.
a(X,Y) :- b(X), c(Y,Z).
b(T) :- a(T,T).
b(1).
c(1,2).
