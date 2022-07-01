_dom_X(1).
_dom_Y((1..2)).
_dom_Z((1..2)).
r1_X(1). % (3)
r1_X(1) :- sat. % (7)
r1_Y(1) | r1_Y(2). % (3)
r1_Y(1) :- sat. % (7)
r1_Y(2) :- sat. % (7)
r1_Z(1) | r1_Z(2). % (3)
r1_Z(1) :- sat. % (7)
r1_Z(2) :- sat. % (7)
sat_r1 :- r1_X(1), r1_Y(1), a(1,1). % (4)
sat_r1 :- r1_X(1), r1_Y(2), a(1,2). % (4)
sat_r1 :- r1_X(1), not b(1). % (4)
sat_r1 :- r1_Y(1), r1_Z(1), not c(1,1). % (4)
sat_r1 :- r1_Y(1), r1_Z(2), not c(1,2). % (4)
sat_r1 :- r1_Y(2), r1_Z(1), not c(2,1). % (4)
sat_r1 :- r1_Y(2), r1_Z(2), not c(2,2). % (4)
{a(X,Y) : _dom_X(X),_dom_Y(Y)}. % (2)
1<={r1f_Z(Z,1): dom(Z)}<=1 :- a(X,1), dom(X). % (9)
1<={r1f_Z(Z,2): dom(Z)}<=1 :- a(X,2), dom(X). % (9)
r1_unfound_0(1) :- not b(1). % (15)
r1_unfound_1(1) :- not c(1,1), r1f_Z(1,1). % (15)
r1_unfound_1(1) :- not c(1,2), r1f_Z(2,1). % (15)
r1_unfound_1(2) :- not c(2,1), r1f_Z(1,2). % (15)
r1_unfound_1(2) :- not c(2,2), r1f_Z(2,2). % (15)
b(1). % Fact
c(1,2). % Fact
:- not sat. % (8)
sat :- sat_r1. % (6)
:- a(1,2), #sum {1:r1_unfound_0(1); 1:r1_unfound_1(2)} >= 1. % (17)
dom(1). % Numeric constant 1 is element of domain
dom(2). % Numeric constant 2 is element of domain
#show _dom_X/1.
#show _dom_Y/1.
#show _dom_Z/1.
#show a/2.
#show b/1.
#show c/2.
