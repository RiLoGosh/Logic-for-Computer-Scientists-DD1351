box_depth(Index, [[[Row, _, assumption]|Box]|Proofs], Depth + 1) :-
    (Row is Index,
    Depth is 0);
    Index > Row,
    (box_depth(Index, Box, Depth);
    box_depth(Index, Proofs, Depth - 1)). % wasnt in this box so go up a level again

box_depth(Index, [[Index, _, _]|_], 0).
box_depth(Index, [_|Proofs], Depth) :-
    box_depth(Index, Proofs, Depth).

box_depth_relative(BaseIndex, Index, AllProofs, Depth) :-
    box_depth(BaseIndex, AllProofs, D1),
    box_depth(Index, AllProofs, D2),
    Depth is D2-D1.

ref(Index, [[[Row, Statement, assumption]|Box]|Proofs], Proof, SrcRow) :- % Box check
    ref(Index, [[Row, Statement, assumption]|Box], Proof, SrcRow), % search ref in box
    ref(SrcRow, [[Row, Statement, assumption]|Box], _, SrcRow); % is src also in this box?
    ref(Index, Proofs, Proof, SrcRow). % otherwise keep scrolling the proofs

ref(Index, [[Index, Statement, Operation]|_], [Index, Statement, Operation], _). % Extract proof (outside of boxes)
ref(Index, [[_,_,_]|Proofs], Proof, SrcRow) :-
    ref(Index, Proofs, Proof, SrcRow).


% Rule implementations:
% [x] premise
% [x] assumption
% [x] copy(x)
% [x] andint(x,y)
% [x] andel1(x)
% [x] andel2(x)
% [x] orint1(x)
% [x] orint2(x)
% [x] orel(r,x,y,i,j) -- implement impint first
% [x] impint(x,y) -- maybe also need to make sure Y is last statement in box.
% [x] impel(x,y)
% [x] negint(x,y)
% [x] negel(x,y)
% [x] contel(x)
% [x] negnegint(x)
% [x] negnegel(x)
% [x] mt(x,y)
% [x] pbc(x,y)
% [x] lem


% Rule 1: Premises.
% Takes in the premise(s) and a statement and then checks if that statement is written as one of the premises
validate(Prems, _, [_, Statement, premise]) :-                          % premise
    member(Statement, Prems).

validate(Prems, AllProofs, [[Row, _, assumption] | Proofs]) :-          % assumption
    \+ box_depth_relative(Row-1, Row, AllProofs, 0), % make sure it is the first statement in box
    % no validation of an assumption
    validate(Prems, AllProofs, Proofs).

validate(_, AllProofs, [Row, Statement, copy(X)]) :-                    % copy(x)
    Row > X,
    ref(X, AllProofs, [X, Statement, _], Row).

validate(_, AllProofs, [Row, Statement, andint(X,Y)]) :-                % andint(x,y)
    Row > X, Row > Y,
    ref(X, AllProofs, [X, Xvar, _], Row),
    ref(Y, AllProofs, [Y, Yvar, _], Row),
    \+ Xvar = neg(_),
    \+ Yvar = neg(_),
    Statement = and(Xvar, Yvar).

validate(_, AllProofs, [Row, Statement, andel1(X)]) :-                  % andel1(x)
    Row > X,
    ref(X, AllProofs, [X, and(Statement, Var), _], Row),
    \+ Var = neg(_),
    \+ Statement = neg(_).

validate(_, AllProofs, [Row, Statement, andel2(X)]) :-                  % andel2(x)
    Row > X,
    ref(X, AllProofs, [X, and(Var, Statement), _], Row),
    \+ Var = neg(_),
    \+ Statement = neg(_).

validate(_, AllProofs, [Row, or(Var, _), orint1(X)]) :-                 % orint1(x)
    Row > X,
    ref(X, AllProofs, [X, Var, _], Row),
    \+ Var = neg(_).

validate(_, AllProofs, [Row, or(_, Var), orint2(X)]) :-                 % orint2(x)
    Row > X,
    ref(X, AllProofs, [X, Var, _], Row),
    \+ Var = neg(_).

validate(_, AllProofs, [Row, imp(A, B), impint(X, Y)]) :-               % impint(x,y) -- maybe also need to make sure Y is last statement in box.
    Row > X, Row > Y,
    box_depth_relative(Row, X, AllProofs, 1),
    ref(X, AllProofs, [X, A, _], X), % tell ref we are in same box as X
    ref(Y, AllProofs, [Y, B, _], X). % make sure Y is from same box as X

validate(_, AllProofs, [Row, Statement, orel(OR, X1, Y1, X2, Y2)]) :-   % orel(r,x,y,i,j)
    Row > OR, Row > X1, Row > Y1, Row > X2, Row > Y2,
    ref(OR, AllProofs, [OR, or(A, B), _], Row),
    validate(_, AllProofs, [Row, imp(A, Statement), impint(X1, Y1)]), % validate A->Statement
    validate(_, AllProofs, [Row, imp(B, Statement), impint(X2, Y2)]). % validate B->Statement


validate(_, AllProofs, [Row, Statement, impel(X, Y)]) :-                % impel(x,y)
    Row > X, Row > Y,
    ref(X, AllProofs, [X, XStatement, _], Row),
    ref(Y, AllProofs, [Y, imp(XStatement, Statement), _], Row).

validate(_, AllProofs, [Row, neg(Statement), negint(X,Y)]) :-           % negint(x,y)
    Row > X, Row > Y,
    box_depth_relative(Row, X, AllProofs, 1),
    ref(X, AllProofs, [X, Statement, assumption], X), % tell ref we are in same box as X
    ref(Y, AllProofs, [Y, cont, _], X), % make sure Y is from same box as X
    \+ Statement = neg(_).

validate(_, AllProofs, [Row, cont, negel(X, Y)]) :-                     % negel(x,y)
    Row > X, Row > Y,
    ref(X, AllProofs, [X, XVar, _], Row),
    ref(Y, AllProofs, [Y, neg(XVar), _], Row),
    \+ XVar = neg(_).

validate(_, AllProofs, [Row, _, contel(X)]) :-                          % contel(x)
    Row > X,
    ref(X, AllProofs, [X, cont, _], Row).

validate(_, AllProofs, [Row, neg(neg(Statement)), negnegint(X)]) :-     % negnegint(x)
    Row > X,
    ref(X, AllProofs, [X, Statement, _], Row),
    \+ Statement = neg(_).

validate(_, AllProofs, [Row, Statement, negnegel(X)]) :-                % negnegel(x)
    Row > X,
    ref(X, AllProofs, [X, neg(neg(Statement)), _], Row),
    \+ Statement = neg(_).

validate(_, AllProofs, [Row, neg(Statement), mt(X,Y)]) :-               % mt(x,y)
    Row > X, Row > Y,
    ref(Y, AllProofs, [Y, neg(YVar), _], Row),
    ref(X, AllProofs, [X, imp(Statement, YVar), _], Row),
    \+ Statement = neg(_),
    \+ YVar = neg(_).

validate(_, AllProofs, [Row, Statement, pbc(X,Y)]) :-                   % pbc(x,y)
    Row > X, Row > Y,
    box_depth_relative(Row, X, AllProofs, 1),
    ref(X, AllProofs, [X, neg(Statement), assumption], X), % tell ref we are in same box as X
    ref(Y, AllProofs, [Y, cont, _], X), % make sure Y is from same box as X
    \+ Statement = neg(_).

validate(_, _, [_, or(Var, neg(Var)), lem]) :-                          % lem
    \+ Var = neg(_).

validate(_, _, []).
validate(_, _, [[]]). % Box ending

validate(Prems, AllProofs, [Proof | Proofs]) :- % Box validation
    validate(Prems, AllProofs, Proof),
    validate(Prems, AllProofs, Proofs).

proves_goal(Goal, [[_, Goal, _]]).
proves_goal(Goal, [_|Proofs]) :-
    proves_goal(Goal, Proofs).


% Nästan identisk med validate men lättare att se när en box avslutades (eller bläddrades) så användes vid debugging för boxarna
validate_proof(_, [], _).
validate_proof(Prems, [Proof | Proofs], AllProofs) :-
    validate(Prems, AllProofs, Proof),
    validate_proof(Prems, Proofs, AllProofs).


valid_proof(_, _, []) :- \+ write("No").
valid_proof(Prems, Goal, [Proof | Proofs]) :-
    proves_goal(Goal, [Proof | Proofs]),
    validate_proof(Prems, [Proof | Proofs], [Proof | Proofs]),
    write("Yes. ");
    \+ write("No. ").

% swipl -g "[labb2], verify('test1.txt')" -g halt
% swipl -g "[run_all_tests], run_all_tests('../labb2.pl')" -g halt
% verify('C:\\Dev\\kth\\dd1351\\labb2\\test1.txt').
verify(InputFileName) :- % verify('test1.txt').
    see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof).