% Facts beginning with _dom_ are always grounded even without #program insts.
#program insts.
_dom_X(1).
_dom_Y(1..2).
_dom_Z(1..2).

#program normal.
a(X,Y) :- b(X), c(Y,Z).
b(1).
c(1,2).
