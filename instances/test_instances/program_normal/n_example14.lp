% Error due to same comparison operands (Y <= Y).
#program normal.
a(X,Y) :- b(X), Y < Y, c(Y,Z), d.
d.
b(1).
c(1,2).