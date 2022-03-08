
food(burger).
food(pizza).
food(sushi).

activity(programming).
activity(magic).
activity(drinking).
activity(sleeping).


class(tcomk).
class(cinte).

class(simon).
class(pontus).

class([simon, pontus, andre]).



likes(pontus, activity(_)).
likes(andre, programming).
likes(andre, movies).

likes(justin, Pizza) :- food(Pizza); activity(Pizza).

likes(simon, Y):-likes(Y, programming). 

sameclass(X, Y) :- class(X), class(Y).

% Task 1

% ?- T=f(a,Y,Z), T=f(X,X,b).

% 1. X = a eftersom att a är en konstant vilket innebär att värdet är redan beslutat medan X är en variabel där värdet är obestämt.
% 2. X = X = a. Alltså T=f(a, a, _) på den andra eftersom att vi vet att X = a och det finns ju två styckna X där. Alltså är båda a.
% 3. Y = X = a. Y:et i den första är också en variabel, vilket innebär att den också or obestämd men eftersom  att den delar plats med X  och X är a så är Y = a.
% 4. Z = b. Precis som tidigare, så är Z en variabel  medan b är ett fast värde vilket  betyder att Z kommer vara lika med b.
% 5. T = f(a, a, b).




% Task 2

% It will recursively test the sub goal of "member(Head, Tail)" 
remove_duplicates([], []).

remove_duplicates([Head|Tail], Fixedlist) :-  
    member(Head, Tail), !,
    remove_duplicates(Tail, Fixedlist).
    

remove_duplicates([Head|Tail], [Head|Fixedlist]) :-
    remove_duplicates(Tail, Fixedlist).


% Task 3

% append will run for every possible consecutive combination of elements in the supplied list

partstring(List, Length, Fixed) :- 
    append([_, Fixed, _], List), 
    length(Fixed, Length), 
    Fixed\=[].
    
    

% Task 4

%

link(a, e).
link(a, b).
link(b, c).
link(b, d).
link(d, c).
link(c, e).
link(d, e).
edge(N1,N2) :- link(N1,N2);link(N2,N1).

path(Start, End, Path) :-
    path(End, Start, [], Path).

path(End, End, Visited, Path) :-
    Path = [End | Visited].

path(Start, End, Visited, Path) :-
    edge(Start, Neighbour),
    \+ member(Neighbour, Visited),
    path(Neighbour, End, [Start|Visited], Path).
    
    
        
        
    
    