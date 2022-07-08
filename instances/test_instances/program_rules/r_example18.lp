% False solution and false #show directive for function because functions are not supported.
#program rules.
a(X,Y) :- b(X), c(Y,Z).
b(f(1)).
c(1,2).