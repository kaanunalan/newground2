% Cannot be grounded because variables in intervals are not supported.
vertex(X) :- edge(X,_).
vertex(Y) :- edge(_,Y).

keep(X) :- vertex(X), not delete(X).
delete(X) :- vertex(X), not keep(X).
:- #count{X : delete(X)} > 1.

edge(X,Y,0) :- edge(X,Y). % original directed edge
edge(Y,X,1) :- edge(X,Y). % reversed directed edge

% associate successors (K=0) and predecessors (K=1) Y of X with integer index M
index(X,Y,M,K) :- edge(X,Y,K), M = #count{Z : edge(X,Z,K), Z <= Y}.
index(X,M,K)   :- index(X,Y,M,K).
final(X,N,K)   :- index(X,N,K), not index(X,N+1,K).

% determine reachability from successors or predecessors of some deleted vertex
% - successors (K=0) if maximum integer index is less or equal to predecessors
% - predecessors (K=1) if maximum integer index is less than for successors
occur(M,K) :- index(X,M,K).
limit(N,K) :- occur(N,K), not occur(N+1,K).
proceed(K) :- limit(N,K), occur(N+K,1-K).

% determine reachability forward from predecessors (K=1) of deleted vertex or in
% reverse direction from successors (K=0), without continuing from deleted vertex
reachable(Y,M) :- kept_edge(X,Y), initial(X,M).
reachable(Y,M) :- kept_edge(X,Y), reachable(X,M).

% require successors (K=1) or predecessors (K=0) to be reachable for every index
:- edge(Y,X,K), delete(X), proceed(K), final(X,N,K), M = 1..N, not reachable(Y,M).

blue(N) :- keep(N), not red(N), not green(N).
red(N) :- keep(N), not blue(N), not green(N).
green(N) :- keep(N), not red(N), not blue(N).
:- edge(N1,N2), blue(N1), blue(N2).
:- edge(N1,N2), red(N1), red(N2).
:- edge(N1,N2), green(N1), green(N2).

#program rules.
% map either successors (K=0) or predecessors (K=1) of deleted vertex to indexes
initial(Y,M) :- index(X,Y,M,K), delete(X), proceed(K).