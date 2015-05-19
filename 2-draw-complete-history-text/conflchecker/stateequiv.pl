/*=============================================================================


    File:       stateequiv.pl

    Authors:    Johannes Langbein, Ulm University, Germany, 
                jolangbein at gmail dot com

    Date:       02-07-2010
    
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


/*=============================== state equivalence ===========================

The predicates in this file implement the theorem giving a criterion for state 
equivalence presented in [RBF09]. The predicate equivalent_states/2 decides 
whether the two states. In other words, given two states state(G, B, V) and 
state(G', B', V'), the predicate succeeds iff 
Ex y (B' -> ((G = G') %% B)) && Ex y' (B -> ((G = G') %% B')) where y and y' 
are the renamed apart local variables of the two states. Furthermore the two 
sets of global variables V and V' have to be equal, when reduced to only those 
variables actually occurring in the two states.

Predicates in this file:
========================
    
    equivalent_states/2  Decides, whether two CHR states are equivalent.
    
    
Datastructures used:
====================

    state(G, B, V)
        A term representing a CHR state. 
        G is a list of CHR constraints, represented as Prolog terms. 
        B is a list of built-in constraints, represented as Prolog terms.
        V is the list of global variables, represented as unbound Prolog 
        variables. This list must not contain duplicates.

        Example: the term state([c(X),[X=0],[X]) represents the CHR state 
        ([c(X)], (X=0), {X}) according to the definition of CHR states in 
        [RBF09].


=============================================================================*/


:- module(stateequiv, [equivalent_states/2]).

:- use_module(termlib, [tl_member/3,
                        tl_diff/4,
                        tl_set_equality/3,
                        tl_intersect/4]).

:- use_module(chrlib, [ builtins_failed/1,
                        propagate_builtins/1]).
                        
                        

%% equivalent_states(+S1, +S2)
%
% This predicate succeeds if the two states S1 and S2, represented as terms of 
% the form state(...), are equivalent according to [RBF09]. This is the case if 
% either both built-in stores are failed or if the global variables are 
% equivalent and the built-ins of one state imply the buil-ins of the other one 
% as well as the equivalence of the goal store and vice versa.

equivalent_states(state(_, B1, _), state(_, B2, _)) :- 
    builtins_failed(B1), 
    builtins_failed(B2).

equivalent_states(S1, S2) :- 
    eq_glob_vars(S1,S2),
    rename_states_apart(S1, S2, R1 ,R2),
    implies(R1, R2),
    implies(R2, R1).


% implies(+S1, +S2)
%
% This predicate checks the implication B -> Ex y' ((G = G') && B') used in the 
% theorem in [RBF09] In other words, given two states state(G1, B1, V1) and 
% state(G2, B2, V2), it checks whether B1 -> Ex y (G1 = G2 && B2) where y are 
% the local variables of the state S2. The local variables of the two states 
% S1 and S2 have to be disjunct.
%
% Example 1: implies(   state([c(2),c(Y)],[Y=1],[Y]),
%                       state([c(X),c(Y)],[Y=1],[Y]))
% is true, because Y=1 -> Ex X [c(2), c(Y)] = [c(X), c(Y)] && Y=1.

% Example 2: implies(   state([c(X),c(Y)],[Y=1],[]), 
%                       state([c(2),c(Z)],[Z=1],[]))
% is false, because Y=1 -> Ex Z [c(X), c(Y)] = [c(2), c(Z)] && Z=1 does not
% hold since Ex Z ([c(X), c(Y)] = [c(2), c(Z)]) is not true.
%
% Example 3: implies(state([c(X)], [], [X]), state([c(X)], [X=1], [X]))
% is false, because true -> (([c(X)] = [c(X)]) && X=1) is false since 
% true -> X=1 does not hold.
%
% To check the implication, a copy of the two states is made. The built-ins of 
% the first state are propagated. After this, the built-ins of the second state 
% need to be implied as well as the equivalence of the goal stores. The global 
% variables of the second state are passed along to those checks to calculate 
% the set of local variables.

implies(S1, S2) :-
    copy_term((S1, S2), (state(G1s, B1s, _), state(G2s, B2s, V2s))),
    propagate_builtins(B1s),
    builtins_implied(B2s, V2s),
    goal_eq_implied(G1s, G2s, V2s).


% builtins_implied(+Bs, +Vs)
%
% This predicate is true iff the conjunction of built-ins is true. In other
% words, the predicate checks, whether the formula
% Ex Ls (b1 && b2 && ... && bn) holds. In this formula Ls is the list of the 
% local variables of Bs, i.e. all variables in B except those appearing in Vs 
% and [b1, .., bn] = B.
%
% Example 1: builtins_implied([X=1, X=Z, Y=Z], []) is true since the
% formula Ex X,Y,Z (X=1 && X=Z && Y=Z) is true.
%
% Example 2: builtins_implied([X=1, X=Z, Y=Z], [Y,Z]) is false since the
% formula Ex X (X=1 && X=Z && Y=Z) does not hold in general.

builtins_implied([], _).

builtins_implied([true|Bs], Vs) :-
    builtins_implied(Bs, Vs).

builtins_implied([B|Bs], Vs) :- 
    arg(1, B, X), 
    arg(2, B, Y), 
    local_vars(B, Vs, Ls),
    eq_term(Ls, X, Y), 
    builtins_implied(Bs, Vs).


% goal_eq_implied(+G1s, +G2s, +V2s) 
%
% This predicate checks whether the two lists of constraints G1s and G2s are
% "equal". The lists G1s and G2s are "equal" if there exists are permutation
% of G1s such that all members of G1 and G2 are pairwise equal according to
% eq_term/3. The list V2s contains the global variables of the state from
% which G2s is taken.
%
% Example 1: goal_eq_implied([c(1), c(Y)], [c(Y), c(X)], [Y]) is true
% since Ex X (c(1) = c(X) && c(Y) = c(Y)). 
%
% Example 2: goal_eq_implied([c(1), c(Z)], [c(Y), c(X)], [Y]) is false
% since Ex X (c(Y) = c(1) || c(Y) = c(Z)).

goal_eq_implied([], [], _).

goal_eq_implied([G1|G1s], G2s, V2s) :-
    remove_eq_goal(G1, G2s, V2s, H2s),
    goal_eq_implied(G1s, H2s, V2s).


% remove_eq_goal(+G1, +G2s, +V2s ~Hs) 
%
% This predicate removes the first constraint G2 from the list of constraints
% G2s which is equal to the constraint G1 according to eq_term/3 and returns
% the remaining list of constraints as Hs. The list V2s contains the global 
% variables of the state from which G2s is taken.
%
% Example 1: remove_eq_goal(c(2), [c(Y), c(X)], [Y],  R)
% results in R = [c(Y)]
%
% Example 1: remove_eq_goal(c(2), [c(Y), c(X)], [], R) 
% results in R = [c(X)] and R = [c(Y)]

remove_eq_goal(G1, [G2|G2s], V2s, G2s) :- 
    local_vars(G2, V2s, L2s), 
    eq_term(L2s, G1, G2).

remove_eq_goal(G1, [G2|G2s], V2s, [G2|Hs]) :- 
    remove_eq_goal(G1, G2s, V2s, Hs).


% eq_term(+Ls, +T1, +T2) 
%
% This predicate checks whether two terms T1 and T2 are equivalent, given the
% existential quantification of the variables in L. In other words, it checks
% whether Ex L (T1 = T2) holds.
%
% Examples: Let t be an arbitrary Prolog term
%
% Example 1: eq_term([], t, t) is true, because the two terms are syntactically
% equivalent.
%
% Example 2: eq_term([X], X, t) is true, because the formula Ex X (X=t) holds.
%
% Example 3: eq_term([Y], t, Y) is true, because the formula Ex Y (t=Y) holds.
%
% Example 4: eq_term([], X, t) is false, because the formula (X=t) does not
% hold in general.
%
% Example 5: eq_term([X], f(X), f(t)) holds iff eq_terms([X], X, t) holds (see 
% Example 2).

eq_term(_, T1, T2) :- T1 == T2, !.

eq_term(Ls, T1, T2) :- var(T1), tl_member(T1, Ls, ==), T1 = T2, !.

eq_term(Ls, T1, T2) :- var(T2), tl_member(T2, Ls, ==), T2 = T1, !.

eq_term(Ls, T1, T2) :- 
    compound(T1),
    compound(T2), 
    T1 =.. [F1|U1s], 
    T2 =.. [F2|U2s], 
    F1 == F2, 
    eq_term_list(Ls, U1s, U2s).


% eq_term_list(+Ls, +T1s, T2s)

% This predicate is true, if the two lists of terms T1s and T2s are pairwise
% equal according to eq_term/3 under the existential quantification of the
% variables in the variable list Ls.
%
% Example 1: eq_term_list([X], [X, f(X), 1], [Y, f(Y), 1]) is true.
%
% Example 1: eq_term_list([X], [X, f(X), 1], [Y, f(Y), Z]) is false since
% eq_term([X], 1 Z) is false.

eq_term_list(_, [], []).

eq_term_list(Ls, [T1|T1s], [T2|T2s]) :- 
    eq_term(Ls, T1, T2),
    eq_term_list(Ls, T1s, T2s).


% local_vars(+T, +Vs, ~Ls)
%
% Auxiliary predicate to calculate the local variables of an arbitrary term. 
% This predicate calculates all variables of the term T, removes the ones
% appearing in Vs and returns the result in Ls.

local_vars(T, Vs, Ls) :- 
    term_variables(T, TVs),
    tl_diff(TVs, Vs, ==, Ls).


%%%%%%%%%%%%%%%%%%%%%%%% Equality of global variables %%%%%%%%%%%%%%%%%%%%%%%%%

% The predicates in this section test, whether two sets of global variables are
% "equal" according to the axiomatization introduced in [RBF09]. 

% In the predicates in this section, global variables are represented as lists,
% although a set-based view of this list is assumed. This means those list must
% not contain multiple occurrences of the same variable. Also, the order in 
% which the variables appear in the lists does not matter, for example the two
% lists [X,Y] and [Y,X] are considered equal.


% eq_glob_vars(+ST1, +ST2)
%
% This predicate is true, iff the set of global variables of the states ST1 and
% ST2 are "equal" according to the axiomatization introduced in [RBF09]. This 
% means the predicate is true, iff the following condition holds:
% The list of global variables of ST1, without those not appearing in the 
% goal or the built-in constraints of ST1, is a permutation
% of the global variables of ST2, also without those not appearing in the 
% goal or the built-in constraints of ST2.
%
% Example 1: eq_glob_vars(  state([c(X)],[X==0],[X]), 
%                           state([c(0)],[X==0],[X])) succeeds.
%
% Example 2: eq_glob_vars(  state([c(0)],[],[X]), 
%                           state([c(0)],[],[])) succeeds.
%
% Example 3: eq_glob_vars(  state([c(X)],[],[X]), 
%                           state([c(Y)],[],[Y])) fails.
%
% Checks whether the "cleaned up" versions of the global variables are a 
% permutation of each other calling eq_glob_vars_cleaned/2. The "cleaned up"
% versions of the global variables are obtained by calling clean_glob_vars/2
% for each state.

eq_glob_vars(state(G1s,B1s,V1s), state(G2s,B2s,V2s)) :-
	clean_glob_vars(state(G1s,B1s,V1s), W1s),
	clean_glob_vars(state(G2s,B2s,V2s), W2s),
	tl_set_equality(W1s,W2s, ==).


% clean_glob_vars(+ST, ~Ws)
%
% This predicate is true, iff the list of variables Ws contains all global
% variables of the state ST except those not appearing in the goal or built-in
% constraints of ST.
%
% Example: clean_glob_vars(state([c(X)],[],[X,Y]), Ws) results in 
% VsNew = [X].
%
% Calculates the list of all variables occurring in the goal and built-ins and
% returns the intersection of the set of those variables with the set of global
% variables.

clean_glob_vars(state(Gs, Bs, Vs), Ws) :-  
    term_variables((Gs,Bs), GBVs), 
    tl_intersect(GBVs, Vs, ==, Ws). 



%%%%%%%%%%%%%%%%%%%% Renaming variables in states apart %%%%%%%%%%%%%%%%%%%%%%%

% The predicates in this section are for renaming apart the variables in the 
% states for which equivalence is checked. The renaming preserves the naming of
% global variables with the same name that occur in both states (for more 
% details, see rename_states_apart/4 below).


% rename_states_apart(+S1, +S2, -R1, -R2).
%
% This predicate is true, iff the states R1 and R2 are the states S1 and 
% S2 respectively in which the local variables have been renamed apart
% according to the precondition of the theorem in [RBF09].
%
% This means that for the new states R1 and R2, the following holds:
% 1.    All variables are replaced by new ones with fresh names.
% 2.    All variables of the state S1 do not occur in R2 except for those which
%       are global variables of both states S1 and S2. This also holds vice
%       versa for the states S2 and R1.
% 3.    Variables occurring as global variables in both states S1 and S2 are 
%       still named the same in both states R1 and R2.
%
% Example: rename_states_apart(state([c(X), c(Y)], [X=1], [X,Y]), 
%                             state([c(X), c(Y), c(Z)], [Y=1], [Z,X]), R1, R2).
% will result in 
% 
% R1 = state([c(_A),c(_B)],[_A=1],[_A,_B]),
% R2 = state([c(_A),c(_C),c(_D)],[_C=1],[_D,_A])
%
% rename_states_apart first calls copy_term twice, once for each term 
% representing a state and then calls unify_varlists to unify the global
% variables that occur in both states.

rename_states_apart(state(G1s, B1s, V1s), state(G2s, B2s, V2s), 
                    state(H1s, C1s, W1s), state(H2s, C2s, W2s)) :- 
    copy_term(state(G1s, B1s, V1s), state(H1s, C1s, W1s)), 
    copy_term(state(G2s, B2s, V2s), state(H2s, C2s, W2s)),
    unify_varlists(V1s, V2s, W1s, W2s).


% unify_varlist(+V1s, +V2s, +W1s, +W2s).
%
% This predicate is true, iff the following conditions hold for the list of 
% list of variables V1s, V2s, W1s, and W2s:
% 1. If a variable appears in V1s at position n and in V2s at position m, then 
%   the n-th variable in W1s is unified with the m-th variable of W2s.
% 2. All other variables are not bound in any way.
%
% This predicate can be used to (re-) unify a list of variables, which have 
% been renamed apart but share some common members. Therefore, the original
% list of variables are given as the two lists V1s and V2s. The predicate
% unifies all variables which have been the same at some point.
% If the two list V1s and V2s are disjunct, no unification will be preformed.
%
% Example: unify_varlist([X,Y,Z],[Y,Z],[A,B,C],[D,E]) results 
% in the unifications D = B and E = C.

unify_varlists([], _, _, _).

unify_varlists([V1|V1s], V2s, [W1|W1s], W2s) :- 
	unify_var(V1, V2s, W1, W2s),
	unify_varlists(V1s, V2s, W1s, W2s).


% unify_var(+X, +Vs, +Y, +Ws). 
%
% This predicate is true iff the following condition holds for the variables
% X and Y and the list of variables Vs and Ws:
% If X occurs in the list Vs at position n, then Y is unified with the n-th
% member of the list Ws.
%
% This predicate can be used to unify two variables which have been renamed 
% apart but had the same name originally.
%
% Example 1: unify_var(Y, [X,Y,Z], L, [A,B,C]) will perform the
% unification B = L.
%
% Example 2: unify_var(X, [Y,Z], A, [B,C]) will not perform any unification.

unify_var(_, [], _, _).

unify_var(X, [V|_], Y, [W|_]) :- X == V, Y = W.

unify_var(X, [V|Vs], Y, [_|Ws]) :- X \== V, unify_var(X, Vs, Y, Ws).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Literature %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [RBF09] Frank Raiser, Hariolf Betz, and Thom Frühwirth: Equivalence of CHR 
% states revisited, 2009.

