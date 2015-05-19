/*=============================================================================


    File:       criticalpairs.pl

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

/*============================ critical pairs =================================

The predicates in this file implement an algorithm to find overlaps of rules 
and create critical pairs from this overlap. The algorithm is loosely based on 
the section on confluence in [DSS07]. The input for this program is a file 
containing a CHR program. The file has to be syntactically correct in order 
for the program to work correctly, therefore loading the file into a CHR 
runtime system previous to running this program is highly recommended.

IMPORTANT NOTE: The underlying constraint theory is restricted to CET, thus 
only = is allowed as built-in constraint in the rules.

Predicates in this file:
========================
    critical_pairs/2            Calculate non-trivial CPs of all rules in file

    critical_pairs/4            Calculate non-trivial CPs of a given rule pair

    all_critical_pairs/2        Calculate all CPs of all rules in file

    all_critical_pairs/4        Calculate all CPs of a given rule pair

    show_critical_pairs/1       Print non-trivial CPs of all rules in file

    show_critical_pairs/3       Print non-trivial CPs of a given rule pair

    show_all_critical_pairs/1   Print all CPs of all rules in file

    show_all_critical_pairs/3   Print all CPs of a given rule pair


Datastructures used:
====================

    state(G, B, V)
        A term representing a CHR state. 
        G is a list of CHR constraints, represented as Prolog terms. 
        B is a list of built-in constraints, represented as Prolog terms.
        V is the list of global variables, represented as unbound Prolog 
        variables. This list must not contain duplicates.
        
    rule(S, KH, RH, G, B)
        A term representing a CHR rule. S is the rule together with its name as 
        string as it is represented in the source file. KH, RH, G, B are lists 
        representing the kept head constraints, the removed head constraints, 
        the guard and the body of the rule. KH, and G are possibly empty. 

    cp(S1, S2, R1, R2, O, CAS)
        A term representing a critical pair. 
        S1 and S2 are the two states of the critical pair represented as 
        state(...) terms according to the definition above. 
        R1 and R2 are the CHR rules the critical pair is stemming from. They 
        are represented as rule(...) terms according to the definition above. 
        O is a list of tuples, consisting of pairs of constraints. Those pairs 
        describe the overlap of the two rules which leads to the critical pair. 
        The list [(a(X),a(Y)), (b(X),b(Y))] means, that the head constraint 
        a(X) of the first rule is overlapped with the head constraint a(Y) of 
        the second rule and also the head constraint b(X) of the first rules is 
        overlapped with the head constraint b(Y) of the second rule. 
        The list CAS contains the critical ancestor state of this critical pair.


=============================================================================*/

:- module(criticalpairs, [  critical_pairs/2, 
                            critical_pairs/4,
                            all_critical_pairs/2,
                            all_critical_pairs/4,
                            show_critical_pairs/1,
                            show_critical_pairs/3,
                            show_all_critical_pairs/1,
                            show_all_critical_pairs/3]).

:- use_module(chrparser, [read_rules/3]).

:- use_module(termlib, [tl_member/3, tl_filter/3, tl_make_set/3]).

:- use_module(chrlib, [builtins_consistent/1, unifier/3]).

:- use_module(stateequiv, [equivalent_states/2]).


%% critical_pairs(+FilePath, -CPS)
%
% This predicate calculates a duplicate free list of all non-trivial critical
% pairs of all rules given in the file specified by the string FilePath.
% This file can be any valid CHR program file. The elements of the list are
% terms representing critical pairs in the way described above.

critical_pairs(File, CPS) :-
    all_critical_pairs(File, CPSA),
    process_cps(CPSA, CPS).


%% critical_pairs(+FilePath, +RuleName1, +RuleName2, -CPS)
%
% This predicate calculates a duplicate free list of all non-trivial critical
% pairs of two rules given in the file specified by the string FilePath. 
% This file can be any valid CHR program file. The elements of the list are
% terms representing critical pairs in the way described above. Critical pairs 
% are only calculated for the two rules whose names are given as 
% RuleName1 and RuleName2. To calculate the critical pairs of a rule with 
% itself RuleName1 and RuleName2 have to be the same. If a rule with the name 
% RuleName1 or RuleName2 does not exists in the program, the predicate returns 
% an empty list in CPS.

critical_pairs(File, RuleName1, RuleName2, CPS) :-
    all_critical_pairs(File, RuleName1, RuleName2, CPSA),
    process_cps(CPSA, CPS).



%% all_critical_pairs(+FilePath, -CPS)

% This predicate calculates all critical pairs stemming from every possible
% overlap of all rules in the CHR program file specified by the string
% FilePath. This file can be any valid CHR program file The elements of the
% list are terms representing critical pairs in the way described above.
%
% First, all rules are read from the file using the predicate read_rules/3 from
% the module parser. The returned list of rules then is used to calculate all
% possible rule pairs and the resulting critical pairs from every possible
% overlap.

all_critical_pairs(File, CPS) :-
    read_rules(File, R, CHRC),
    findall(CP, 
            (pick_rule_pair(R, R1, R2), 
             critical_pair(R1, R2, CHRC, CP)), 
             CPS).


%% all_critical_pairs(+FilePath, +RuleName1, +RuleName2, -CPS)

% This predicate calculates all critical pairs stemming from every possible
% overlap of two rules in the CHR program file specified by the string
% FilePath. This file can be any valid CHR program file The elements of the
% list are terms representing critical pairs in the way described above. 
% Critical pairs are only calculated for the two rules whose names are given as 
% RuleName1 and RuleName2. To calculate the critical pairs of a rule with 
% itself RuleName1 and RuleName2 have to be the same. If a rule with the name 
% RuleName1 or RuleName2 does not exists in the program, the predicate returns 
% an empty list in CPS.
%
% First, all rules are read from the file using the predicate read_rules/3 from
% the module parser. The returned list of rules then is used to calculate all
% possible rule pairs and the resulting critical pairs from every possible
% overlap.

all_critical_pairs(File, RuleName1, RuleName2, CPS) :-
    read_rules(File, R, CHRC),
    findall(CP,
            (pick_rule_pair(R, RuleName1, RuleName2, R1, R2),
             critical_pair(R1, R2, CHRC, CP)), 
             CPS).


%% show_critical_pairs(+File)
%
% This predicate prints a duplicate free list of all non-trivial critical
% pairs of all rules given in the file specified by the string File.
% This file can be any valid CHR program file.

show_critical_pairs(File) :- 
    critical_pairs(File, CPS), 
    pretty_print(CPS), 
    print_lenght(CPS).


%% show_all_critical_pairs(+File)
%
% This predicate prints all critical pairs stemming from every possible
% overlap of all rules in the CHR program file specified by the string
% File. This file can be any valid CHR program file.

show_all_critical_pairs(File) :- 
    all_critical_pairs(File, CPS), 
    pretty_print(CPS), 
    print_lenght(CPS).


% show_critical_pairs(+File, +RuleName1, +RuleName2)
%
% This predicate prints a duplicate free list of all non-trivial critical
% pairs of two rules given in the file specified by the string File. 
% This file can be any valid CHR program file. Critical pairs 
% are only printed for the two rules whose names are given as 
% RuleName1 and RuleName2. To print the critical pairs of a rule with 
% itself RuleName1 and RuleName2 have to be the same. 

show_critical_pairs(File, RuleName1, RuleName2) :- 
    critical_pairs(File, RuleName1, RuleName2, CPS), 
    pretty_print(CPS), 
    print_lenght(CPS).


% show_all_critical_pairs(+File, +RuleName1, +RuleName2)
%
% This predicate prints all critical pairs stemming from every possible
% overlap of two rules in the CHR program file specified by the string
% File. This file can be any valid CHR program file. Critical pairs are 
% only printed for the two rules whose names are given as  RuleName1 and 
% RuleName2. To print the critical pairs of a rule with itself RuleName1 
% and RuleName2 have to be the same.

show_all_critical_pairs(File, RuleName1, RuleName2) :- 
    all_critical_pairs(File, RuleName1, RuleName2, CPS), 
    pretty_print(CPS), 
    print_lenght(CPS).


% critical_pair(+Rule1, +Rule2, +CHRC -CP)
%
% This predicate calculates one critical pair, stemming from one possible
% overlap of the two rules R1 and R2 according to the definition in [Fru09].
% To construct the critical pair correctly, the list CHRC contains the names of
% all CHR constraints as specified by the directive :- chr_constraint in the
% source file.
%
% Backtracking this predicate eventually reveals all possible critical pairs,
% stemming from every possible overlap.
%
% The critical pair is calculated by first renaming the variables of the two
% rules apart with a call of copy_term for each rule. After appending the kept 
% and removed head constraints into one list, a possible match is created 
% calling the predicate match/5 which reveals the equalities necessary to make 
% the overlapping part match, as well as the non-overlapping parts of the two 
% rules. The built-in store of the states in the critical pair consists of the 
% equality revealed by match in conjunction with the two guards of the two 
% rules. Finally, the two goal stores and the set of global variables are 
% calculated according to the definition in [DSS07].

critical_pair(R1, R2, CHRC, 
        cp(state(GS1, BS1, VS), state(GS2, BS2, VS), R1, R2, O, CAS)) :- 
    copy_term(R1, rule(_N1, KH1, RH1, G1, B1)),
    copy_term(R2, rule(_N2, KH2, RH2, G2, B2)),
    append(KH1, RH1, H1),
    append(KH2, RH2, H2),
    match(H1, H2, O, U, D1, D2),
    append([U, G1, G2], BS),
    builtins_consistent(BS),
    split_body(B1, CHRC, B1CHR, B1BI),
    split_body(B2, CHRC, B2CHR, B2BI),
    append([KH1, D2, B1CHR], GS1),
    append([KH2, D1, B2CHR], GS2),
    append(B1BI, BS, BS1),
    append(B2BI, BS, BS2),
    append([H1, H2, G1, G2], WS),
    term_variables(WS, VS),
    append([H1, D2, U, G1, G2], CAS).


% match(+Head1, +Head2, -Overlap -Unifier, -Diff1, -Diff2)
%
% This predicate calculates an arbitrary non-empty matching of the two list of
% constraints Head1 and Head2. The list Overlap consisting of pairs of
% constraints indicating which head constraint have been matched. The
% overlapping part of the two heads is not unified but the unifier needed for
% the match is returned as a list of =/2 terms in Unifier. The lists Diff1,
% and Diff2 contain all the constraints which are not part of the overlap of
% Head1 and Head2, respectively. 
%
% On backtracking, this predicate eventually calculates all possible non-empty
% matches.

% Example: match([a(X),b(Y),c(Z)], [b(V), c(W)], U, D1, D2, O) results in
%
% 1)    Overlap: b(Y) = b(V)
%   O = [(b(Y),b(V))],      U = [Y=V], 
%   D1 = [a(X), c(Z)],      D2 = [c(W)],
%
% 2)    Overlap: b(Y) = b(V), c(Z) = c(W)
%   O = [(b(Y),b(V)),(c(Z),c(W))],  U = [Y=V, Z=W],
%   D1 = [a(X)],                    D2 = [],
%
% 3)    Overlap: c(Z) = c(W)
%   O = [(c(Z),c(W))],      U = [Z=W], 
%   D1 = [a(X), b(Y)],      D2 = [b(V)],
%
% The predicate traverses the first list of constraints recursively and in
% every step performs one of the following actions, in case they are possible.
% 1) Match the first constraint from the first list against one from the second
%    list (In this case, this is the whole overlap).
% 2) Match the first constraint from the first list against one from the second
%   list and continue recursively with the rest of the list.
% 3) Ignore the first constraint of the first list (thus excluding it from the
%    match) and continue recursively with the rest of the list.

match([H1|R1], L2, [(H1,M)], U, R1, R) :- 
    match_one(H1, L2, M, U, R).

match([H1|R1], L2, [(H1,M)|O], U, D1, D2) :- 
    match_one(H1, L2, M, U1, S), 
    match(R1, S, O, U2, D1, D2),
    append(U1, U2, U).

match([H1|R1], L2, O, U, [H1|D1], D2) :- 
    match(R1, L2, O, U, D1, D2).


% match_one(+Head, +List, -Match -Unifier, -Rest)
%
% This predicate succeeds if the constraint Head can be matched against one
% constraint in the list List. In this case, Match is the constraint which is
% matched against Head, Unifier is a list of =/2 terms
% containing the equations necessary to make Head and the according constraint
% in List syntactically equal, while Rest is List without the matched
% constraint. On backtracking, this predicate will reveal every possible
% matching between Head and constraints in List.
%
% Example 1: match_one(c(X), [a(X), c(Y, Z), c(V)], M, U, R) succeeds and
% results in M = c(V),  U = [X=V], and R = [a(X), c(Y, Z)].
%
% Example 2: match_once(X), [a(X), c(Y, Z), d(V)], M, U, R) fails.
%
% The predicate recursively traverses List and either calculates the unifier of
% Head with the current head of List (if even possible) or continues
% recursively with the rest of List.

match_one(X, [H|R], H, U, R) :-
    unifier(X, H, U).

match_one(X, [H|R], M, U, [H|R1]) :-
    match_one(X, R, M, U, R1).


% split_body(+Body +LCHRCons, ~CHR, ~BI).
%
% This predicate splits the list Body, consisting of user-defined and built-in
% constraints into two lists CHR and BI where CHR contains only user defined
% and BI contains only built-in constraints. The list LCHRCons with terms of
% the form cons(functor, arity) is used to determine if a member of the list
% body is a user-defined constraint or not. If it appears in LCHRCons, it is
% added to the list CHR, if not, it is added to the list BI.

split_body([], _, [], []).

split_body([C|R], CONS, [C|CHR], BI) :- 
    functor(C, F, N), 
    tl_member((F, N), CONS, ==), 
    !,
    split_body(R, CONS, CHR, BI).

split_body([C|R], CONS, CHR, [C|BI]) :- 
    split_body(R, CONS, CHR, BI).


% process_cps(+CPSA, -CPS)
%
% This predicate removes trivial and duplicate critical pairs from the list
% CPSA of critical pairs and returns the result as CPS. A critical pair is
% trivial if its two states are syntactically equal. Two pairs
% cp(S1, S2, _, _, _, _) and cp(S3, S4, _, _, _, _) are duplicates if S1
% equals S3 and S2 equals S4 or if S1 equals S4 and S2 equals S3.

process_cps(CPS, R) :-
    tl_filter(CPS, criticalpairs:non_trivial_cp, CPS1),
    tl_make_set(CPS1, criticalpairs:variant_equal_cp, R).


% non_trivial_cp(+CP)
%
% This predicate is true if the critical pair CP is non-trivial, i.e. if its
% two states are not equivalent.

non_trivial_cp(cp(S1, S2, _, _, _, _)) :- \+equivalent_states(S1, S2).


% variant_equal_cp(+CP1, +CP2)
%
% This predicate succeeds, iff the two critical pairs CP1 and CP2 are variants,
% or if they are equal. Two pairs cp(S1, S2, _, _, _, _) and 
% cp(S3, S4, _, _, _, _)
% are variants if S1 is a variant if S3 and S2 is a variant of S4 or if S1 is a
% variant of S4 and S2 is a variant of S3. The two pairs are equal if
% S1 == S3 and S2 == S4 or if S1 == S4 and S2 == S3, where == denotes state
% equivalence.

variant_equal_cp(cp(S1, S2, _, _, _, _), cp(S3, S4, _, _, _, _)) :-
    S1 =@= S3,
    S2 =@= S4.

variant_equal_cp(cp(S1, S2, _, _, _, _), cp(S3, S4, _, _, _, _)) :-
    S1 =@= S4,
    S2 =@= S3.

variant_equal_cp(cp(S1, S2, _, _, _, _), cp(S3, S4, _, _, _, _)) :- 
    equivalent_states(S1, S3),
    equivalent_states(S2, S4).

variant_equal_cp(cp(S1, S2, _, _, _, _), cp(S3, S4, _, _, _, _)) :- 
    equivalent_states(S1, S4),
    equivalent_states(S2, S3).


% pick_rule_pair(+R, -R1, -R2)
%
% This predicate takes a list of rules R and returns two rules R1 and R2 which
% are both members of the list R. R1 and R2 are not necessarily different, but
% it is guaranteed, that the R2 is at a same or higher list index than R1.
% This avoids selecting (rule1, rule2) as well as (rule2, rule1).
%
% On backtracking, this predicate reveals all possible pairs of rules.
%
% Example: pick_rule_pair([rule1, rule2, rule3], R1, R2) results in
% R1 = rule1
% R2 = rule1

% R1 = rule1
% R2 = rule2

% R1 = rule1
% R2 = rule3

% R1 = rule2
% R2 = rule2

% R1 = rule2
% R2 = rule3

% R1 = rule3
% R2 = rule3 

pick_rule_pair(R, R1, R2) :- 
    pick_first(R, R1, RS), 
    pick_second(RS, R2).

pick_first([H|R], H, [H|R]).

pick_first([_|R], R1, RS) :- 
    pick_first(R, R1, RS).

pick_second([H|_], H).

pick_second([_|R], R1) :- 
    pick_second(R, R1).


% pick_rule_pair(+R, ,+RN1, +RN2, -R1, -R2)
%
% This predicate takes a list of rules R and returns two rules R1 and R2 which
% are both members of the list R and have the names RN1 and RN2 accordingly. If 
% a rule with the name RN1 or RN2 does not exist, the predicate fails.

pick_rule_pair(R, RN1, RN2, R1, R2):-
    pick_by_name(R, RN1, R1),
    pick_by_name(R, RN2, R2).

pick_by_name([rule(RN@RS, KH, RH, G, B)|_], RN, rule(RN@RS, KH, RH, G, B)) :-!.

pick_by_name([rule(_, _, _, _, _)|Rules], RN, R) :-
    pick_by_name(Rules, RN, R).


% pretty_print(+List)
%
% Writes every element of a list of ciritcal pairs list in a new line using
% write/1.

pretty_print([]).
pretty_print([cp(S1, S2, R1, R2, O, CAS)|R]) :- 
    numbervars(cp(S1, S2, R1, R2, O, CAS), 0, _E), 
    write_term(S1, [numbervars(true)]), nl, 
    write_term(S2, [numbervars(true)]), nl,
    write_term(R1, [numbervars(true)]), nl,
    write_term(R2, [numbervars(true)]), nl,
    write_term(O, [numbervars(true)]), nl,
    write_term(CAS, [numbervars(true)]), nl,
    nl, nl, 
    pretty_print(R).


% print_lenght(+List)
%
% Outputs the lenght of the list of critical pairs List.

print_lenght(L) :- 
    length(L,N), write(N),
    write(' critical pairs found'),nl,nl.

%%%%%%%%%%%%%%%%%%%%%%%%%%%% References %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [DSS07]: Gregory J. Duck, Peter J. Stuckey, Martin Sulzmann: Observable
% confluence for constraint handling rules - Lecture Notes in Computer Science,
% 2007 - Springer

% [Fru09] Thom Fruehwirth: Constraint Handling Rules, 2009, Cambridge
% University Press

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

