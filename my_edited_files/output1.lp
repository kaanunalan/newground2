r1_X(1) | r1_X(2). % (3) r1_X(2) not necessary?
r1_X(1) :- sat. % (7)
r1_X(2) :- sat. % (7) not necessary?
r1_Y(1) | r1_Y(2). % (3)
r1_Y(1) :- sat. % (7)
r1_Y(2) :- sat. % (7)
r1_Z(1) | r1_Z(2). % (3)
r1_Z(1) :- sat. % (7)
r1_Z(2) :- sat. % (7) % Confirms the mistakes in Appendix C
sat_r1 :- r1_X(1), r1_Y(1), a(1,1). % (4)
sat_r1 :- r1_X(1), r1_Y(2), a(1,2). % (4)
sat_r1 :- r1_X(2), r1_Y(1), a(2,1). % (4) not necessary?
sat_r1 :- r1_X(2), r1_Y(2), a(2,2). % (4) not necessary?
sat_r1 :- r1_X(1), not b(1). % (4)
sat_r1 :- r1_X(2), not b(2). % (4) not necessary?
sat_r1 :- r1_Y(1), r1_Z(1), not c(1,1). % (4)
sat_r1 :- r1_Y(1), r1_Z(2), not c(1,2). % (4) Confirms the mistakes in Appendix c
sat_r1 :- r1_Y(2), r1_Z(1), not c(2,1). % (4)
sat_r1 :- r1_Y(2), r1_Z(2), not c(2,2). % (4) Confirms the mistakes in Appendix c
{a(X,Y) : dom(X),dom(Y)}. % (2)
1<={r1f_Z(Z,1): dom(Z)}<=1 :- a(X,1), dom(X).
1<={r1f_Z(Z,2): dom(Z)}<=1 :- a(X,2), dom(X).
r1_unfound_0(1) :- not b(1). % (15)
r1_unfound_0(2) :- not b(2). % (15) not necessary?
r1_unfound_1(1) :- not c(1,1), r1f_Z(1,1). % (15)
r1_unfound_1(1) :- not c(1,2), r1f_Z(2,1). % (15)
r1_unfound_1(2) :- not c(2,1), r1f_Z(1,2). % (15)
r1_unfound_1(2) :- not c(2,2), r1f_Z(2,2). % (15)
b(1). % Fact
c(1,2). % Fact
:- not sat. % (8)
sat :- sat_r1. % (6)
:- a(1,1), #sum {1:r1_unfound_0(1); 1:r1_unfound_1(1)} >= 1. % (17)
:- a(1,2), #sum {1:r1_unfound_0(1); 1:r1_unfound_1(2)} >= 1. % (17)
:- a(2,1), #sum {1:r1_unfound_0(2); 1:r1_unfound_1(1)} >= 1. % (17)
:- a(2,2), #sum {1:r1_unfound_0(2); 1:r1_unfound_1(2)} >= 1. % (17)
dom(1). % Numeric constant 1 is element of domain
dom(2). % Numeric constant 2 is element of domain
#show a/2.
#show b/1.
#show c/2.
