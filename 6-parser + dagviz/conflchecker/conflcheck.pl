/*=============================================================================


    File:       conflcheck.pl

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


/*=============================== confluence check ===========================

The predicates in this file implement a confluence checker for CHR programs
according to the definition of confluence in [Fru09]. There are two
restrictions to the CHR programs that can be used with this confluence
checker:

 1.) No propagation rules: The CHR program to use with this file must not
    contain propagation rules. 
    
 2.) Restricted built-ins: Only = is allowed as built-in constraint.

The most important predicate in this file is the predicate check_confluence/1. 
This predicate checks all CHR rules in a Prolog file and decides whether or not
they are confluent.

IMPORTANT NOTE:
    The predicates in this file write temporary files to your hard-drive. Thus, 
    it needs to be executed in a directory with write access. All files are 
    deleted after the execution.



Predicates in this file:
========================

    check_confluence/1          Checks confluence for a program
    
    check_confluence/2          Checks confluence for a program and returns the 
                                number of non-joinable critical pairs
    
    check_confluence/3          Checks confluence for two rules in a program
    
    check_confluence/4          Checks confluence for two rules in a program 
                                and returns the number or non-joinable critical
                                pairs
    
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

:- module(conflcheck, [ check_confluence/1, 
                        check_confluence/2,
                        check_confluence/3, 
                        check_confluence/4,
                        show_critical_pairs/1,
                        show_critical_pairs/3,
                        show_all_critical_pairs/1,
                        show_all_critical_pairs/3,
                        show_me_the_money/1,
                        all_critical_pairs/2,
                        pretty_print/1,
                        pretty_print_to_graph/1,
                        getCAS/2,
                        getState/2,
                        pretty_print_to_graph_CAS/1]).


:- use_module(criticalpairs, [  critical_pairs/2,
                                critical_pairs/4,
                                show_critical_pairs/1,
                                show_critical_pairs/3,
                                show_all_critical_pairs/1,
                                show_all_critical_pairs/3,
                                all_critical_pairs/2,
                                pretty_print/1]).


:- use_module(stateequiv, [equivalent_states/2]).

:- use_module(termlib, [tl_member/3]).

:- use_module(chrparser, [read_rules/3]).

%% check_confluence(+FileName)
%
% This predicate checks all CHR rules in the file FileName for confluence and
% prints the according output. If the program is not confluent, i.e. if
% there are non-joinable critical pairs, for those critical pairs a message is 
% printed containing the critical pair, together with the according rules and
% overlap. This predicate always succeeds, even if the program is not
% confluent. The confluence check continues after the first non-joinable
% critical pair is found.
%
% The predicate first calculates all critical pairs stemming from all possible
% overlaps of the rules in the file specified by FileName. Second the
% according outputs are made and flags are set before all critical pairs are
% checked for joinability. At last, the final message is printed and the flags
% are set back to their default values.

check_confluence(FileName) :-
    critical_pairs(FileName, CPS),
    all_critical_pairs(FileName, AllCPS),

    %nl, nl,
    %read_rules(FileName, Rules, CHRC),
    %print('==============================================================================='),nl,
    %print('==============================================================================='),nl,
    %print('==============================================================================='),nl,nl,
    start_joinable_check(FileName),
    %print('==> the rule(s) are:'), nl,
    %print(Rules), nl, nl,
    %print('==> the constraint(s) are:'), nl,
    %print(CHRC), nl, nl,
    %print('==> critical pair(s):'), nl,
    %print(CPS), nl, nl,
    %print('==> detailed view for critial pair(s):'), nl,
    %pretty_print(CPS), nl,nl,
    %print('==============================================================================='),nl,nl,
    %print('==> all critical pairs:'), nl,
    %print(AllCPS), nl, nl,
    %print('==============================================================================='),nl,nl,

    cps_joinable(CPS, FileName, NoOfFail),

    %nl,nl,
    %print('==============================================================================='),nl,nl,
    %print('==> detailed view for all pairs stemming from every possible overlap of all rules:'), nl,
    %pretty_print(AllCPS), nl, nl,
    %print('==============================================================================='),nl,nl,

    %print('==============================================================================='),nl,nl,
    %print('==> detailed view for all pairs stemming from every possible overlap of all rules for GRAPH DRAWING:'), nl,
    pretty_print_to_graph(AllCPS), nl, nl,
    %% print('==============================================================================='),nl,nl,

    %write_term('This is a place holder in check_confluence',[]), nl,
    %print('test print in check_confluence!'), nl,
    %write('test write in check_confluence'), nl,
    %show_all_critical_pairs(FileName),
    %print(CPS), nl,

    %% pretty_print_to_graph_CAS(CPS), nl,nl,
    %% print('==============================================================================='),nl,nl,
    
    end_joinable_check(FileName, NoOfFail),!.


%% check_confluence(+FileName, RuleName1, RuleName2)
%
% This predicate checks two Rules from the file specified by FileName for 
% confluence and prints the according output. The Name of the two rules is are 
% given as RuleName1 and RuleName2. To check of only one rule RuleName1 and 
% RuleName2 have to be the same. If a rule with the name RuleName1 or RuleName2 
% does not exists in the program, nothing is checked.

% If the program is not confluent, i.e. if there are non-joinable critical 
% pairs, for those critical pairs a message is printed containing the critical 
% pair, together with the according rules and overlap. This predicate always 
% succeeds, even if the program is not confluent. The confluence check 
% continues after the first non-joinable critical pair is found.
%
% The predicate first calculates all critical pairs stemming from all possible
% overlaps of the two rules in the file specified by FileName. Second the
% according outputs are made and flags are set before all critical pairs are
% checked for joinability. At last, the final message is printed and the flags
% are set back to their default values.

check_confluence(FileName, RuleName1, RuleName2) :-
    critical_pairs(FileName, RuleName1, RuleName2, CPS),
    start_joinable_check(FileName),
    cps_joinable(CPS, FileName, NoOfFail),
    end_joinable_check(FileName, NoOfFail),!.
    

%% check_confluence(+FileName, -NoOfFail)
%
% Like check_confluence/1 but without any  output beeing printed and NoOfFail 
% being bound to the number of non-joinable critical pairs.
    
check_confluence(FileName, NoOfFail) :- 
    critical_pairs(FileName, CPS),
    set_prolog_flag(verbose, silent),
	style_check(-singleton),
	set_prolog_flag(chr_toplevel_show_store, false),
    cps_joinable_no_print(CPS, FileName, NoOfFail),
    set_prolog_flag(chr_toplevel_show_store, true),
    style_check(-singleton),
    set_prolog_flag(verbose, normal).


%% check_confluence(+FileName, +RuleName1, +RuleName2, -NoOfFail)
%
% Like check_confluence/3 but without any  output beeing printed and NoOfFail 
% being bound to the number of non-joinable critical pairs.
  
check_confluence(FileName, RuleName1, RuleName2, NoOfFail) :-
    critical_pairs(FileName, RuleName1, RuleName2, CPS),
    set_prolog_flag(verbose, silent),
	style_check(-singleton),
	set_prolog_flag(chr_toplevel_show_store, false),
    cps_joinable_no_print(CPS, FileName, NoOfFail),
    set_prolog_flag(chr_toplevel_show_store, true),
    style_check(-singleton),
    set_prolog_flag(verbose, normal).


%% cps_joinable(+CPS, +FileName, ~NoOfFail)
%
% This predicate checks joinability of critical pairs. All critical pairs in
% the list CPS are checked for joinability. FileName specifies the file
% containing the CHR rules the critical pairs stems from. NoOfFail is the
% number of critical pairs in CPS which are not joinable. This predicate
% succeeds no matter whether there are non-joinable critical pairs or not.

cps_joinable([], _, 0).

cps_joinable([cp(S1, S2, R1, R2, O, CAS)|CPS], FileName, N) :- 
    %print('this is print test in cps_joinable 1'), nl,
    %write('this is write test in cps_joinable 2'), nl,
    print_joinable(cp(S1, S2, R1, R2, O, CAS)),
    %nl,
    %nl,nl,
    %print('print cp in cps_joinable'),nl,nl,
    %print(cp(S1, S2, R1, R2, O, CAS)),nl,nl,
    %print('test print in XXXXXXX'),

    (states_joinable(S1, S2, FileName) 
    ->
	    (N1 is 0)
    ;
	    (print_not_joinable(cp(S1, S2, R1, R2, O, CAS)),
	    N1 is 1)
    ), !,

    %write_term(cp(S1, S2, R1, R2, O, CAS),[]), nl,
    %print(CAS), print(R1), print(R2),nl,
    %print('this is a print in cps_joinable 3'), nl,
    %write('this is write test in cps_joinable 4'), nl,


    cps_joinable(CPS, FileName, N2),
    N is N1 + N2.


%% cps_joinable_no_print(+CPS, +FileName, ~NoOfFail)
%
% Like cps_joinable/3 but with no output generated.  

cps_joinable_no_print([], _, 0).

cps_joinable_no_print([cp(S1, S2, _, _, _, _)|CPS], FileName, N) :- 
    (states_joinable(S1, S2, FileName) 
    ->
        (N1 is 0)
    ;
        (N1 is 1)
    ), !,
    cps_joinable_no_print(CPS, FileName, N2),
    N is N1 + N2.
    
    
%% states_joinable(+State1, +State2, +FileName)
%
% This predicate succeeds if the two states State1 and State2 are joinable
% given the rules of the program in the file specified by FileName. Joinable in
% this case means that the rules of the program applied until exhaustion lead
% to two states which are equivalent according to the definition of state
% equivalence given in [RBF09].
%
% After merging CHR and built-in constraints together into one list and
% converting this list into a goal, both resulting goals are posed as query to 
% the CHR runtime system. Each time before a query is posed to the CHR system, 
% the CHR program file is consulted in order to reset the CHR runtime system to 
% its original state. After each call, the final state is retrieved using 
% find_chr_constraints/2. Because of the independent calls for each state, the 
% global variables the states share have been disconnected. Thus, they are 
% reconnected by calling reconnect/6. The two final states are then 
% compared using equivalent_states/2.

states_joinable(S1, S2, FileName) :-
    %nl, print('test print in states_joinable'), nl,
    %write_term('write_term in states_joinable',[]), nl,nl,
    copy_term(S1, state(G1, B1, V1)),
    copy_term(S2, state(G2, B2, V2)),
    append(G1, B1, L1),
    append(G2, B2, L2),
    list_to_goal(L1, H1),
    list_to_goal(L2, H2), 
    consult(FileName),
    call(H1), 
    findall_chr_constraints(V1, Result1),
    consult(FileName),
    call(H2), 
    findall_chr_constraints(V2, Result2),
    reconnect(Result1, Result2, G1n, G2n, V1n, V2n),
    % write_term(S1,[]), nl,
    % write_term(S2,[]), nl,
    %list_to_set(G1n,LAST),
    %last(G1n,LAST), nl,
    print('{ " ['),
    print(H1),
    print('] "  " ['),
    print(H2),
    print('] " }'), nl,
    %print(S1), nl,
    %print(S2), nl,nl,
    %print(' '),
    %print(' ---> '),
    %print(' '),
    

    %print('{ " '),
    %print(H1),
    %print(' " " '),
    %print(H2),
    %print(' " }'),
    %print(' -> '),
    %print('" '),
    %print(LAST),
    %print(' "   [label = "*" ]'),nl,
    %nl,nl,


    %print(S1), nl,
    %print(S2), nl,nl,
    %print(' '),
    %print(' ---> '),
    %print(' '),
    %print(LAST),
    %nl,
    %print(G1n), nl,
    %print(G1), nl,
    %print(B1), nl,
    %print(L1), nl,
    %print(V1), nl,
    %print(Result1), nl,
    %print(L1), nl,
    % print(L2), nl,
    %print(H2), 
    %print(' ---> '),
    %print(G2n), nl,
    % print(Result1), nl,
    % print(Result2), nl,
    %length(G1n,X),
    %print('there is a path from ['),
    %print(H1),
    %print('] to '),
    %print(LAST),
    %print('... and ['),
    %print(H2),
    %print('] to '),
    %print(LAST),
    %print('.'), nl,nl,
    %print('==============================================================================='),nl,nl,
    % print(V1n), nl,
    % print(V2n), nl,
    equivalent_states(state(G1n, [], V1n), state(G2n, [], V2n)),!.


% list_to_goal(+L, ~G)
%
% This predicate converts a list of constraints L (user-defined as well as
% built-ins constraints) into a single goal which then can be executed using
% the predicate call/1.

list_to_goal([C], (C)).
list_to_goal([C|R],(C,T)) :- list_to_goal(R, T).


% findall_chr_constraints(+GlobVars, -Res)
%
% This predicate binds Res to the list of all CHR constraints in the store that 
% can be found using find_chr_constraint/1 from the CHR library. The list 
% GlobVars contains all the global variables appearing in the original query 
% which led to the result Res. This is needed to keep the global variables 
% connected to the result of the computation.
%
% This predicate temporarly save the CHR constraints into a file to keep the
% variables connected. Thus it needs to be placed in a directory where the user 
% has write access. The filename is randomly generated and the file is deleted 
% after the computation.

findall_chr_constraints(GlobVars, Res) :-
    create_file_name(Name),
    open(Name, write, Sout, [alias(output)]),
    (
        (
            find_chr_constraint(R),
            write(output, R),
            write(output, ', '),
            nl(output),
            %nl,print('test in Sout output'),nl,
            %print(R),nl,
            fail
        )
        ;
        (
            true
        )
    ),
    write(output, globs(GlobVars)),
    write(output, '.'),
    nl(output),
    close(Sout),
    open(Name, read, Sin, [alias(input)]),
    read(input, T), 
    close(Sin),
    %print('test print in findall_chr_constraints/2'),nl,nl,nl,
    %print(T),nl,
    delete_file(Name),
    to_list(T, Res).


% to_list(+Term, -List)
%
% This predicate converts the conjunction of terms T, ending with a globs(...) 
% term into a list, where each subterm is one element fo the list.
%
% Example: to_list((a(X),b(y,(c(Z)),globs([X,Y,Z])), R), yields 
% R = [a(X), b(y,(c(Z)), globs([X,Y,Z])]

to_list(T, [H|Res]) :- 
    T =.. [_,H,T1],
    to_list(T1, Res).

to_list(T, [T]) :- 
    T =.. [globs, _].


% create_file_name(-Name)
% 
% This predicate randomly generates a filename. If a file with this name does 
% not exist in the execution directory, the filename is returned, otherwise a 
% different name is generated
create_file_name(Name) :-
    random(X),
    string_to_atom(Name, X),
    (exists_file(Name) -> fail; true).


% reconnect(+Res1, +Res2, -Goal1, -Goal2, -GlobVars1, -GlobVars2)
%
% This predicate seperates the results found by findall_chr_constraints/2 into
% the actual goal store and the set of global variables. Furthermore, it
% reconnects the two states by unifiying the global variables of the two states,
% while keeping track, that a global variable from one state is only bound to 
% one global variable from another state (for details see reconnect_globs/3).
% The lists Res1 and Res2 are the results found by findall_chr_constraints/2. 
% Goal1 and Goal2 are lists representing the respective goal stores while 
% GlobVars1 and GlobVars2 are lists containing the global variables.

reconnect(R1, R2, G1, G2, V1, V2):-
    extract_globs(R1, G1, V1),
    extract_globs(R2, G2, V2),
    reconnect_globs(V1, V2).


% extract_globs(+List, -Goal, -GlobVars)
%
% This predicate separates the list List generated by findall_chr_constraints/2
% into the goal store Goal and the list of global variables GlobVars.

extract_globs([globs(V)], [], V).

extract_globs([H|R], [H|G], V) :-
    extract_globs(R, G, V).


% reconnect_globs(+V1, +V2)
%
% Auxilliary predicate, calls reconnect_globs(V1, V2, []).

reconnect_globs(V1, V2) :- reconnect_globs(V1, V2, []).


% reconnect_globs(+V1, +V2, S)
%
% This predicate reconnect the lists of global variables V1 and V2. This needs 
% to be done if the global variables originate from two states of a critical 
% pair that have been executed separately and thus have been disconnected. The 
% predicate makes sure, that every variable occuring in V1 is only unified with 
% one variable occuring in V2 and vice versa. This is needed to take into 
% account different variable bindings that may have occured during execution 
% of the states of the critical pair. If an already reconnected variable is 
% seen again, it needs to be bound to the same variable as before, otherwise 
% the predicate fails. S is a buffer variable wich needs to be instantiated to 
% the empty list when calling the predicate.
%
% Example 1:
% reconnect_globs([X, Y, X], [A, B, A],[]) succeeds with X = A and Y = B.
%
% Example 2:
% reconnect_globs([X, Y, X], [A, B, C],[]) fails.

reconnect_globs([], [], _).

reconnect_globs([V1|R1],[V2|R2], S) :-
    tl_member(V1, S, ==),!,
    V1 == V2,
    reconnect_globs(R1, R2, S).

reconnect_globs([V1|R1],[V2|R2], S) :-
    tl_member(V2, S, ==),!,
    V1 == V2,
    reconnect_globs(R1, R2, S).

reconnect_globs([V1|R1],[V2|R2], S) :-
    \+ tl_member(V1, S, ==),
    \+ tl_member(V2, S, ==),
    var(V1),
    var(V2),
    V1 = V2,
    reconnect_globs(R1, R2, [V1|S]).
    
reconnect_globs([V1|R1],[V2|R2], S) :-
    compound(V1),
    compound(V2),
    V1 =..[_|T1],
    V2 =..[_|T2],
    append(T1, R1, L1),
    append(T2, R2, L2),
    reconnect_globs(L1, L2, S).
    
reconnect_globs([V1|R1],[V2|R2], S) :-
    ground(V1),
    ground(V2),
    V1 == V2,
    reconnect_globs(R1, R2, S).


% start_joinable_check(+FileName)
%
% This predicate prints a message saying that the confluence check for the
% file specified by FileName has been started and sets three different flags.
% Singleton variable warnings are turned of and Prolog as well as CHR execution
% are turned silent. This way, no output is produced while the critical pairs
% are checked for joinability.

start_joinable_check(FileName) :- 
    nl,
    print('Checking confluence of CHR program in '),
    print(FileName),
    print('...'), nl,nl,
    write_term('===============================================================================', []),nl,nl,nl,
    print('digraph G { concentrate=true;'), nl,nl,
    set_prolog_flag(verbose, silent),
    style_check(-singleton),
    set_prolog_flag(chr_toplevel_show_store, false).


% end_joinable_check(+FileName, +NoOfFail)
%
% This predicate prints out the final message after the confluence check and
% turns Prolog's verbosity back to normal. FileName again specifies the file for
% which confluence has been checked while NoOfFail is an integer indicating the
% number of non-joinable critical pairs.
end_joinable_check(FileName, NoFail) :-
    %print('ooooooooo.. this is a test in end_joinable_check..'), nl, nl,
    %show_all_critical_pairs(FileName),
    print_end_result(FileName, NoFail),

    style_check(-singleton).


% print_end_result(+FileName, +NoOfFail)
%
% This predicate prints the end result message after the confluence check is
% done. FileName specifies the file name of the file which was checked. The
% message printed is depending on the number of non-joinable critical pairs
% found.

print_end_result(FileName, 0) :-
    nl,
    print('}'),nl,nl,nl,
    write_term('===============================================================================', []),nl,nl,
    print('The CHR program in '),
    print(FileName),
    print(' is confluent.'), nl, nl.

print_end_result(FileName, N) :-
    N > 0,
    nl,
    print('}'),nl,nl,nl,
    write_term('===============================================================================', []),nl,nl,

    critical_pairs(FileName,CPS),
    pretty_print_to_graph_CAS(CPS), nl,nl,
    print('==============================================================================='),nl,nl,

    print('The CHR program in '),
    print(FileName),
    print(' is NOT confluent! '),
    print(N),
    print(' non-joinable critical pair(s) found!'), nl.


% print_not_joinable(+CP)
%
% This predicate generates a messages for a non-joinable critical pair. The
% critical pair is printed together with the overlap and the rules it stems
% from.


print_not_joinable(cp(S1, S2, rule(N1, _, _, _, _), rule(N2, _, _, _, _), O, CAS)) :-
    numbervars(cp(S1, S2, rule(N1, _, _, _, _), rule(N2, _, _, _, _), O, CAS), 0, _E).
    %getCAS(CAS,CASFinal),
    %% getState(S1,S1Final),
    %% getState(S2,S2Final),
    %nl,nl,nl,
    %% print('{ " '),
    %% print(S1Final),
    %% print(' "  " '),
    %% print(S2Final),
    %% print(' " } '),nl,nl.
    %write_term('===============================================================================', []),nl,
    %write_term('The following critical pair is not joinable:', []),nl,
    %write_term(S1, [numbervars(true)]),nl,
    %write_term(S2, [numbervars(true)]),nl,nl,
    %write_term('This critical pair stems from the critical ancestor state:', []),nl,
    %write_term(CAS, [numbervars(true)]),nl,nl,
    %write_term('with the overlapping part:', []),nl,
    %write_term(O, [numbervars(true)]),nl,nl,
    %write_term('of the following two rules: ', []),nl,
    %write_term(N1, [numbervars(true)]), nl,
    %write_term(N2, [numbervars(true)]), nl, nl,nl,
    %print('state 1 is:'), nl,
    %print(S1Final),nl,nl,
    %print('state 2 is:'), nl,
    %print(S2Final), nl,nl,
    %print('this is final CAS: '),nl,
    %print(CASFinal),nl,nl,
    %write_term('===============================================================================', []),nl,nl.
    %print('"'),
    %print(CAS),
    %print('"'),
    %print(' -> ').




getCAS([X|_],X).


%getState(state(S1,[],_),S1).
%getState(state([],S2,_),S2).
%getState(state(S1,S2,_),[S1|S2]).

getState(state(S1,S2,_),SFinal):- flatten([S1|S2],SFinal).

%getState(state(S1,S2,_),S):- atomic_list_concat(S1,S1semi),atomic_list_concat(S2,S2semi),atomic_list_concat(S1semi,S2semi,S).
%atomic_list_concat([c,S,h,HS],N).










%print_joinable(cp(S1, S2, rule(N1, _, _, _, _), rule(N2, _, _, _, _), O, CAS)) :-
%    numbervars(cp(S1, S2, rule(N1, _, _, _, _), rule(N2, _, _, _, _), O, CAS), 0, _E),
%    write_term('===============================================================================', []),nl,
%    write_term('The following critical pair:', []),nl,
%    write_term(S1, [numbervars(true)]),nl,
%    write_term(S2, [numbervars(true)]),nl,nl,
%    write_term('stems from the critical ancestor state:', []),nl,
%    write_term(CAS, [numbervars(true)]),nl,nl,
%    write_term('because of the following overlapping part:', []),nl,
%    write_term(O, [numbervars(true)]),nl,nl,
%    write_term('of the following two rules: ', []),nl,
%    write_term(N1, [numbervars(true)]), nl,
%    write_term(N2, [numbervars(true)]), nl, 
%    write_term('===============================================================================', []),nl,nl.




print_joinable(cp(S1, S2, rule(N1, _, _, _, _), rule(N2, _, _, _, _), O, CAS)) :-
    numbervars(cp(S1, S2, rule(N1, _, _, _, _), rule(N2, _, _, _, _), O, CAS), 0, _E),
    %write_term('===============================================================================', []),nl,nl,
    %print('digraph G {'), nl,nl,
    %write_term('The following critical pair:', []),nl,
    %write_term(S1, [numbervars(true)]),nl,
    %write_term(S2, [numbervars(true)]),nl,nl,
    %write_term('stems from the critical ancestor state:', []),nl,
    %write_term(CAS, [numbervars(true)]),nl,nl,
    %write_term('because of the following overlapping part:', []),nl,
    %write_term(O, [numbervars(true)]),nl,nl,
    %write_term('of the following two rules: ', []),nl,
    %write_term(N1, [numbervars(true)]), nl,
    %write_term(N2, [numbervars(true)]), nl,
    print('" '),
    print(CAS),
    print(' "'),
    print(' -> ').



pretty_print_to_graph([]).
pretty_print_to_graph([cp(S1, S2, rule(A,B,C,D,E), R2, O, CAS)|R]) :- 
    numbervars(cp(S1, S2, rule(A,B,C,D,E), R2, O, CAS), 0, _E), 
    nl,nl,
    %print_rule_to_graph(R1,R2),
    %print('this is a graph test'),nl,nl,
    %write_term(S1, [numbervars(true)]), nl, 
    %write_term(S2, [numbervars(true)]), nl,
    %write_term(R1, [numbervars(true)]), nl,
    %write_term(R2, [numbervars(true)]), nl,
    %write_term(O, [numbervars(true)]), nl,
    %write_term(CAS, [numbervars(true)]), nl,
    print('" '),
    print(C),
    print(' "'),
    print(' -> '),
    print('" '),
    print(E),
    print(' "'),
    %% print(' [label = " '),
    %% print(A),
    %% print(' "]'),
    print(' ;'),
    nl, nl, 
    pretty_print_to_graph(R).





pretty_print_to_graph_CAS([]).
pretty_print_to_graph_CAS([cp(S1, S2, rule(_,_,_,_,_), _, O, CAS)|R]) :- 
    numbervars(cp(S1, S2, rule(_, _, _, _, _), rule(_, _, _, _, _), O, CAS), 0, _E),
    %getCAS(CAS,CASFinal),
    getState(S1,S1Final),
    getState(S2,S2Final),
    %nl,nl,nl,
    write_term('===============================================================================', []),nl,nl,nl,
    print('digraph G { concentrate=true;'), nl,nl,
    print('"  '),
    print(CAS),
    print('  "'),
    print(' -> '),
    print('{ " '),
    print(S1Final),
    print(' "  " '),
    print(S2Final),
    print(' " } '),nl,nl,
    print('} '), nl,nl,
    write_term('===============================================================================', []),nl,nl,nl,
    pretty_print_to_graph_CAS(R).










% R1 = rule((a<=>b),[],[a],[],[b])


%print_rule_to_graph(R,R):- nl,nl,print(R),nl,nl.



%% show_me_the_money(+File)
% THIS IS WHERE THE MAGIC HAPPENS
% This predicate prints all critical pairs stemming from every possible
% overlap of all rules in the CHR program file specified by the string
% File. This file can be any valid CHR program file.

show_me_the_money(File) :- 
    all_critical_pairs(File, CPS), 
    pretty_print(CPS), 
    print_lenght(CPS).
















%%%%%%%%%%%%%%%%%%%%%%%%%%%% References %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [Fru09] Thom Fruehwirth: Constraint Handling Rules, 2009, Cambridge
% University Press

% [RBF09] Frank Raiser, Hariolf Betz, and Thom Frühwirth: Equivalence of CHR 
% states revisited, 2009.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

