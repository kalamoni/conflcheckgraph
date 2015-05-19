/*=============================================================================


    File:       termlib.pl

    Author:     Johannes Langbein, Ulm University, Germany, 
                jolangbein at gmail dot com

    Date:       02-05-2010
    
    Version:    1.0
    
    Copyright:  2010, Johannes Langbein

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.

=============================================================================*/



/*============================== termlib ======================================

This file defines a number of predicates for handling terms, as well as lists
and sets of terms. Some of the predicates already exist in common
implementations of Prolog although most of them do not work as intended if
called with unbound variables or complex terms. For this purpose, every
predicate whose implementation involves comparison of two terms is a
higher-order predicate allowing the user to pass his own definition of equality
as parameter to the predicate. 

All predicates are guaranteed to not alter any unbound variable occurring in
the arguments

Also, all predicates give a unique solution and thus are not backtrackable.


Predicates in this file:
========================

    tl_member/3         Element member of list

    tl_remove/4         Removes first occurence of element from list

    tl_member_remove/4  Removes first occurence of element from list if
                        present

    tl_remove_all/4     Removes all occurences of element from list

    tl_filter/3         Filters list according to predicate

    tl_make_set/3       Turns list into set

    tl_set_equality/3   Decides whether two lists contain the same
                        elements

    tl_intersect/4      Computes set intersection of two lists

    tl_diff/4           Computes set difference of two lists

==============================================================================*/

:- module(termlib, [    tl_member/3, 
                        tl_remove/4,
                        tl_member_remove/4,
                        tl_remove_all/4,
                        tl_filter/3,
                        tl_make_set/3,
                        tl_set_equality/3,
                        tl_intersect/4,
                        tl_diff/4]).


%% tl_member(+T, +L, +P)
%
% This predicate is true, iff the term T is equal to at least one member of L.
% The equality is decided using the predicate P. Therefore P must be a
% predicate of arity 2.

tl_member(T, [H|_], P) :- call(P,T,H), !.

tl_member(T, [_|R], P) :- tl_member(T, R, P).


%% tl_remove(+T, +L, +P ~R)
%
% This predicate removes the first occurrence of a term in the list L which is
% equal to the term T and returns the resulting List in R. The equality is
% decided using the predicate P. Therefore P must be a predicate of arity 2.

tl_remove(_, [], _, []) :- !.

tl_remove(T, [H|R], P, R) :- call(P,T,H), !.

tl_remove(T, [H|R], P, [H|R1]) :- tl_remove(T, R, P, R1).


%% tl_member_remove(+T, +L, +P ~R)
%
% Combination of tl_member/3 and tl_remove/4, but more efficient than a
% consecutive call. This predicate removes the first occurrence of a term in
% the list L which is equal to the term T and returns the resulting List in R,
% but only succeeds if such a term is found. Again, equality is decided using
% the predicate P. Therefore P must be a predicate of arity 2.

tl_member_remove(T, [H|R], P, R) :- call(P,T,H), !.

tl_member_remove(T, [H|R], P, [H|R1]) :- tl_member_remove(T, R, P, R1).


%% tl_remove_all(+T, +L, +P ~R)
%
% This predicate removes all occurrences of terms in the list L which are
% equal to the term T and returns the resulting List in R. The equality is
% decided using the predicate P. Therefore P must be a predicate of arity 2.

tl_remove_all(_, [], _, []) :- !.

tl_remove_all(T, [H|R], P, R1) :- call(P,T,H),!, tl_remove_all(T, R, P, R1).

tl_remove_all(T, [H|R], P, [H|R1]) :- tl_remove_all(T, R, P, R1).


%% tl_filter(+L, +P ~R)
%
% This predicate filters the list L according to the unary predicate P. The
% list R contains all elements t of L for which P(i) is true.

tl_filter([], _, []) :- !.

tl_filter([H|R], P, [H|R1]) :- call(P, H), !, tl_filter(R, P, R1). 

tl_filter([_|R], P, R1) :- tl_filter(R, P, R1).


%% tl_make_set(+L, +P, ~R)
%
% This predicate turns the list L into a set (i.e. removes duplicate
% occurrences) and returns the result in R. The binary predicate P is used to
% determine equivalence of two members of L.

tl_make_set([], _, []) :- !.

tl_make_set([T|R], P, [T|R2]) :- 
    tl_remove_all(T, R, P, R1), !,
    tl_make_set(R1, P, R2).


%% tl_set_equality(+L1, +L2, +P)
%
% Checks, whether the two sets L1 and L2 are equal, i.e. whether L1 is a
% permutation of L2. The binary predicate P is used to compare the elements
% of L1 and L2.

tl_set_equality([], [], _) :- !.

tl_set_equality([H1|R1], L2, P) :- 
    tl_member_remove(H1, L2, P, L3), !,
    tl_set_equality(R1, L3, P).


%% tl_intersect(+L1, +L2, +P ~R)
%
% Calculates the intersection of the two lists L1, L2 and returns the result
% in R. The intersection R contains all elements that appear in L1 and L2.
% The binary predicate P is used to decide equality between two elements of
% L1 and L2.

tl_intersect([], _, _, []) :- !.

tl_intersect([H1|R1], L2, P, [H1|R]) :- 
    tl_member(H1, L2, P), !,
    tl_intersect(R1, L2, P, R).

tl_intersect([_|R1], L2, P, R) :- 
    tl_intersect(R1, L2, P, R).


%% tl_diff(+L1, +L2, +P, ~R)
%
% Calculates the difference L1-L2 of the two lists L1 and L2 and returns the
% result in R. The binary predicate P is used to decide equality between two
% elements of L1 and L2.

tl_diff(L1, [], _, L1) :- !.

tl_diff(L1, [H2|R2], P, R) :- 
    tl_remove(H2, L1, P, S), !,
    tl_diff(S, R2, P, R).

