/*=============================================================================


    File:       chrlib.pl

    Author:     Johannes Langbein, Ulm University, Germany, 
                jolangbein at gmail dot com

    Date:       02-06-2010
    
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

/*=============================== chrlib ======================================

This file defines a number of auxiliary predicates related to properties of CHR
rules, programs, and states.

Predicates in this file:
========================

    builtins_failed/1           Inconsistent (failed) built-in store

    builtins_consistent/1       Consistent built-in store

    propagate_builtins/1        Unify variables in built-in store

    unifier/3                   Calculate MGU of two terms

==============================================================================*/


:- module(chrlib, [ builtins_failed/1,
                    builtins_consistent/1,
                    propagate_builtins/1,
                    unifier/3]).


:- use_module(termlib, [tl_member/3, tl_filter/3]).


%% builtins_failed(+B)
%
% This predicate succeeds iff the conjunction of the built-ins in the list B is
% failed i.e. contains logical contradictions. This predicate does not bind any
% variables occuring in B

builtins_failed(B) :- \+ builtins_consistent(B).


%% builtins_consistent(+B)
%
% This predicate succeeds, iff the conjunction of the built-ins in the list B
% is consistent, i.e. contains no logical contradictions. This predicate does
% not bind any variables occuring in B

builtins_consistent(B) :- 
    \+ tl_member(false, B, ==), 
    tl_filter(B, \==(true), B1),
    equalities_consistent(B1).


%% propagate_builtins(+B)
%
% This predicate takes a list of built-in constraints B and tries to unify
% them according to the equalities. The predicate only succeeds if the
% built-ins are consistent and fails if the built-ins in B contain logical
% contradictions or the literal false.

propagate_builtins([]).

propagate_builtins([true|Bs]) :- propagate_builtins(Bs).

propagate_builtins([B|Bs]) :-
    functor(B, =, 2), 
    call(B), 
    propagate_builtins(Bs).


%% unifier(+Term1, +Term2, -Unifier)
%
% This predicate calculates the MGU (most general unifier) of the two terms
% Term1 and Term2 according to the Herbrand Algorithm without occur check. If
% Term1 and Term2 are not unifiable, unifier/3 fails. If they are unifiable,
% Unifier is a list of =/2 terms, which represent the resulting MGU. This
% predicate does not bind any variables occuring in Term1 or Term2.

unifier(T1, T2, []) :- T1 == T2, !.

unifier(T1, T2, [T1 = T2]) :- var(T1), !.

unifier(T1, T2, [T2 = T1]) :- var(T2), !.

unifier(T1, T2, U) :- 
    compound(T1), 
    compound(T2), 
    functor(T1, F, N), 
    functor(T2, F, N), 
    T1 =.. [_|[X1|R1]], 
    T2 =.. [_|[X2|R2]],
    unifier(X1, X2, U1),
    unifier(R1, R2, U2),
    append(U1, U2, U),
    equalities_consistent(U).


% equalities_consistent(+E)
%
% This predicate succeeds, if all equalities (=/2 terms) in the list
% E are logically consistent. This predicate does not bind any variables 
% occuring in E.

equalities_consistent(E) :- 
    copy_term(E, E1), 
    equalities_consistent_aux(E1).

equalities_consistent_aux([]).

equalities_consistent_aux([E|R]) :- 
    functor(E, =, 2),
    call(E), 
    equalities_consistent_aux(R).

