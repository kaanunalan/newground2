% Endless sequence of the same model if no option.
% Syntax error with --ground or --ground-guess
#program normal.
a(X,Y) :- b(X), c(Y,Z,T), d(U,V), e(A,B), f(C,D,D), g(G,H,G), h(J,K,L), i(L,M,N), j(O,P,Q), k(R,S,AB), l(CD,EF,_).
b(1).
c(1,2,2).
