t([], _).
t([H|_], H) :- fail.
t([_|T], X) :- t(T, X).