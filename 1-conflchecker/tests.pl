/*=============================================================================


    File:       tests.pl

    Authors:    Johannes Langbein, Ulm University, Germany, 
                jolangbein at gmail dot com

    Date:       02-09-2010
    
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

/*=================================== tests ===================================


This file contains predicates for automated testing along with testcases for
the implementation of the confluence checker.


How to use the test framework:
==============================

1. Defining testcases.

Testcases are defined using the predicate test/3. Each testcase consists of 
a identifier (for example a string describing the test), the goal to call
(with all its arguments) and the expected outcome. This can be either the
term "success" or the term "failure", depending on whether the goal is expected
to succeed or fail. The goal can either be a single goal or a goal composed of 
multiple subgoals. In this case, the first subgoal has to be the goal to be 
tested. Those three components are the arguments of the predicate test/3, in 
this order.

Example 1: test('plus success', plus(2, 3, 5), success).
Example 2: test('plus fail', plus(2, 3, 3), failure).
Example 3: test('plus success', (plus(2, 3, X), X = 5) success).
Example 4: test('plus fail', (plus(2, 3, X), plus(X, 2, 7)), failure).


2. Executing the tests.

Test can be executed using the predicate run_tests/1, which takes the name of
a goal as argument and executes all test-cases containing this goal.
This predicates also produces output about which test is run, what goal is
executed, and what the expected and actual result is. After all tests are
executed, the number of failed testcases is printed.

Example: run_tests(equivalent_states) executes all test-cases defined for 
            equivalent_states.



Predicates in this file:
========================

    test_equivalent_states/0    Executes all tests for the predicate 
                                equivalent_states from the modul stateequiv
    
    test_all_critical_pairs/0   Executes all tests for the predicate 
                                all_critical_pairs from the modul criticalpairs
    
    test_critical_pairs/0       Executes all tests for the predicate 
                                critical_pairs from the modul criticalpairs
    
    test_check_confluence/0     Executes all tests for the predicate 
                                check_confluence from the modul conflcheck
    
    run_tests/1                 Runs tests for predicates whose names are 
                                given in the argument

=============================================================================*/


:- module(tests, [  test_equivalent_states/0, 
                    test_all_critical_pairs/0,
                    test_critical_pairs/0,
                    test_check_confluence/0,
                    run_tests/1]).

:- use_module(stateequiv, [equivalent_states/2]).
:- use_module(criticalpairs, [critical_pairs/2, all_critical_pairs/2]).
:- use_module(conflcheck, [check_confluence/2, check_confluence/4]).
:- use_module(library(lists)).

/*================================== Tests ==================================*/

test_equivalent_states :- 
    run_tests(equivalent_states).

test_all_critical_pairs :- 
    run_tests(all_critical_pairs).

test_critical_pairs :-
    run_tests(critical_pairs).
    
test_check_confluence :-
    run_tests(check_confluence).


/*=============================== Testcases =================================*/

% To prevent warnings about singleton variables in testcases
:- style_check(-singleton).


% equivalent_states

test(   'renaming local var', 
        equivalent_states(
            state([c(X)], [], []), 
            state([c(Y)], [], [])), 
        success).

test(   'replacing global var',
        equivalent_states(
            state([c(X)], [X==0], [X]),
            state([c(0)], [X==0], [X])),
        success).

test(   'omitting global var',
        equivalent_states(
            state([c(0)], [], []),
            state([c(0)], [], [X])),
        success).

test(   'renaming global var',
        equivalent_states(
            state([c(Y)], [], [Y]),
            state([c(X)], [], [X])),
        failure).

test(   'function terms 1',
        equivalent_states(
            state([c(f(Y))], [], []),
            state([c(X)],    [], [])),
        failure).

test(   'function terms 2',
        equivalent_states(
            state([c(f(Y))], [],          []),
            state([c(X)],    [X = f(Y)], [])),
        success).

test(   'local and global vars together 1', 
        equivalent_states(
            state([c(X), c(Y)], [], [Y]),
            state([c(Y), c(Y)], [], [Y])),
        failure).

test(   'local and global vars together 2',
        equivalent_states(
            state([c(Y), c(Y)], [],      [Y]), 
            state([c(X), c(Y)], [X = Y], [Y])),
        success).

test(   'local and global vars together 3',
        equivalent_states(
            state([c(X), c(Y), c(Z)], [X = 1], [Y]),
            state([c(Z), c(Y), c(X)], [X = 1], [Y])),
        success).

test(   'different built-ins',
        equivalent_states(
            state([c(X), c(Y), c(Z)], [X = 1, Y=0], [Y]),
            state([c(Z), c(Y), c(X)], [X = 1],      [Y])),
        failure).

test(   'different built-ins and function terms', 
        equivalent_states(
            state([c(Z), c(Y), c(f(X))],    [Z = f(1), X = 1], [Y]),
            state([c(f(V)), c(Y), c(f(Z))], [Z = 1, V = 1],    [Y])),
        success).

test(   'different number of arguments',
        equivalent_states(
            state([c(X,Y), c(Z)],    [], []),
            state([c(Z,Y), c(V, W)], [], [])),
        failure).

test(   'different number of constraints', 
        equivalent_states(
        state([c(1), c(1)], [], []),
        state([c(1)],       [], [])),
        failure).

test(   'failed and implied built-in stores',
        equivalent_states(
            state([c(X)], [X = 1, X = 2], []),
            state([c(X)], [X = 1],        [])),
        failure).

test(   'both built-in stores failed', 
        equivalent_states(
            state([c(X)], [X = 1, X = 2],        []),
            state([c(X)], [X = 1, Z = 3, X = Z], [])),
        success).


% all_ciritcal_pairs and critical_pairs

test(   'simple1.pl: only two trivial critical pairs because the two rules only overlap with themselves',
       (
            all_critical_pairs('examples/simple1.pl', Res), 
            permutation(Res, [
                cp( state([], [true], []), 
                    state([], [true], []), 
                    rule((p<=>true),[],[p],[],[true]), 
                    rule((p<=>true),[],[p],[],[true]), 
                    [(p,p)],
                    [p]),
                cp( state([], [true], []), 
                    state([], [true], []), 
                    rule((q<=>true),[],[q],[],[true]), 
                    rule((q<=>true),[],[q],[],[true]), 
                    [(q,q)],
                    [q])])
        ),
        success).

test(   'simple1.pl: no actual critical pairs',
    critical_pairs('examples/simple1.pl', []),
    success).



test(   'simple2.pl: three critical pairs, one of each rule with itself (trivial) and one between the rules',
        (
            all_critical_pairs('examples/simple2.pl', Res),
            permutation(Res, [
                cp( state([q], [], []), 
                    state([q], [], []), 
                    rule((p<=>q), [], [p], [], [q]), 
                    rule((p<=>q), [], [p], [], [q]), 
                    [ (p, p)], 
                    [p]), 
                    
                cp( state([q], [], []),
                     state([], [false], []), 
                     rule((p<=>q), [], [p], [], [q]), 
                     rule((p<=>false), [], [p], [], [false]), 
                     [ (p, p)], 
                     [p]), 
                     
                cp( state([], [false], []), 
                    state([], [false], []), 
                    rule((p<=>false), [], [p], [], [false]), 
                    rule((p<=>false), [], [p], [], [false]), 
                    [ (p, p)], 
                    [p])])
         ), 
         success).
         
         
test(   'simple2.pl: one non-trivial critical pair',
        critical_pairs('examples/simple2.pl', [
            cp( state([q], [], []),
                 state([], [false], []), 
                 rule((p<=>q), [], [p], [], [q]), 
                 rule((p<=>false), [], [p], [], [false]), 
                 [ (p, p)], 
                 [p])]), 
         success).


test(   'simple3.pl: three trivial critical pairs from each rule with themselves and one non-trivial critical pair between the two rules',
        (
            all_critical_pairs('examples/simple3.pl', Res), 
            permutation(Res, [
                cp( state([q], [true], []), 
                state([q], [true], []), 
                rule((p, q<=>true), [], [p, q], [], [true]), 
                rule((p, q<=>true), [], [p, q], [], [true]), 
                [ (p, p)],
                [p, q, q]),

            cp( state([], [true], []), 
                state([], [true], []), 
                rule((p, q<=>true), [], [p, q], [], [true]), 
                rule((p, q<=>true), [], [p, q], [], [true]), 
                [ (p, p), (q, q)],
                [p, q]),

            cp( state([p], [true], []), 
                state([p], [true], []), 
                rule((p, q<=>true), [], [p, q], [], [true]), 
                rule((p, q<=>true), [], [p, q], [], [true]), 
                [ (q, q)],
                [p, q, p]),

            cp( state([r], [true], []), 
                state([p], [true], []), 
                rule((p, q<=>true), [], [p, q], [], [true]), 
                rule((q, r<=>true), [], [q, r], [], [true]), 
                [ (q, q)],
                [p, q, r]),

            cp( state([r], [true], []), 
                state([r], [true], []), 
                rule((q, r<=>true), [], [q, r], [], [true]), 
                rule((q, r<=>true), [], [q, r], [], [true]), 
                [ (q, q)],
                [q, r, r]),

            cp( state([], [true], []), 
                state([], [true], []), 
                rule((q, r<=>true), [], [q, r], [], [true]), 
                rule((q, r<=>true), [], [q, r], [], [true]), 
                [ (q, q), (r, r)],
                [q, r]),

            cp( state([q], [true], []), 
                state([q], [true], []), 
                rule((q, r<=>true), [], [q, r], [], [true]), 
                rule((q, r<=>true), [], [q, r], [], [true]), 
                [ (r, r)],
                [q, r, q])])
            ),
            success).
            

test(   'simple3.pl: one non-trivial critical pair between the two rules',
        critical_pairs('examples/simple3.pl', [
            cp( state([r], [true], []), 
                state([p], [true], []), 
                rule((p, q<=>true), [], [p, q], [], [true]), 
                rule((q, r<=>true), [], [q, r], [], [true]), 
                [ (q, q)],
                [p, q, r])]),
        success).

test(   'simple4.pl: three trivial critical pairs (from the three rules with themselves) and one non-trivial critical pair stemming from the overlap of the second and third rule.',
        (
            all_critical_pairs('examples/simple4.pl',  Res), 
            permutation(Res,[
                cp( state([], [true, _X=_Y, _X=1, _Y=1], [_X, _Y]), 
                    state([], [true, _X=_Y, _X=1, _Y=1], [_X, _Y]), 
                    rule((p(_Z)<=>_Z=1|true), [], [p(_Z)], [_Z=1], [true]), 
                    rule((p(_Z)<=>_Z=1|true), [], [p(_Z)], [_Z=1], [true]), 
                    [ (p(_X), p(_Y))],
                    [p(_X), _X=_Y, _X=1, _Y=1]),

                cp( state([], [true, _A=_B, _A=2, _B=2], [_A, _B]), 
                    state([], [true, _A=_B, _A=2, _B=2], [_A, _B]), 
                    rule((p(_C)<=>_C=2|true), [], [p(_C)], [_C=2], [true]), 
                    rule((p(_C)<=>_C=2|true), [], [p(_C)], [_C=2], [true]), 
                    [ (p(_A), p(_B))],
                    [p(_A), _A=_B, _A=2, _Y=2]),

                cp( state([], [true, _D=2, _D=2], [_D]), 
                    state([], [true, _D=2, _D=2], [_D]), 
                    rule((p(_E)<=>_E=2|true), [], [p(_E)], [_E=2], [true]), 
                    rule((p(2)<=>true), [], [p(2)], [], [true]), 
                    [ (p(_D), p(2))],
                    [p(_D), _D=2, _D=2]),

                cp( state([], [true], []), 
                    state([], [true], []), 
                    rule((p(2)<=>true), [], [p(2)], [], [true]), 
                    rule((p(2)<=>true), [], [p(2)], [], [true]), 
                    [ (p(2), p(2))],
                    [p(2)])])
        ),
        success).
    
test(   'simple4.pl: no non-trivial critical pair',
        critical_pairs('examples/simple4.pl', []),
        success).
    
test(   'xor.pl: six trivial critical pairs from the first rule with itself, three from the second rule with itself. Four critical pairs between first and second rule',
        (
            all_critical_pairs('examples/xor.pl', Res), 
            permutation(Res,[
                cp( state([xor(_A), xor(0)], [_B=_A], [_B, _A]), 
                    state([xor(_B), xor(0)], [_B=_A], [_B, _A]), 
                    rule((xor(_C), xor(_C)<=>xor(0)), [], [xor(_C), xor(_C)], [], [xor(0)]), 
                    rule((xor(_C), xor(_C)<=>xor(0)), [], [xor(_C), xor(_C)], [], [xor(0)]), 
                    [ (xor(_B), xor(_A))],
                    [xor(_B), xor(_B), xor(_A), _B=_A]),

                cp( state([xor(_D), xor(0)], [_F=_D], [_F, _D]), 
                    state([xor(_F), xor(0)], [_F=_D], [_F, _D]), 
                    rule((xor(_G), xor(_G)<=>xor(0)), [], [xor(_G), xor(_G)], [], [xor(0)]), 
                    rule((xor(_G), xor(_G)<=>xor(0)), [], [xor(_G), xor(_G)], [], [xor(0)]), 
                    [ (xor(_F), xor(_D))],
                    [xor(_F), xor(_F), xor(_D), _F=_D]),

                cp( state([xor(0)], [_H=_I, _H=_I], [_H, _I]), 
                    state([xor(0)], [_H=_I, _H=_I], [_H, _I]), 
                    rule((xor(_J), xor(_J)<=>xor(0)), [], [xor(_J), xor(_J)], [], [xor(0)]), 
                    rule((xor(_J), xor(_J)<=>xor(0)), [], [xor(_J), xor(_J)], [], [xor(0)]), 
                    [ (xor(_H), xor(_I)), (xor(_H), xor(_I))],
                    [xor(_H), xor(_H), _H=_I, _H=_I]),

                cp( state([xor(0)], [_K=_L, _K=_L], [_K, _L]), 
                    state([xor(0)], [_K=_L, _K=_L], [_K, _L]), 
                    rule((xor(_M), xor(_M)<=>xor(0)), [], [xor(_M), xor(_M)], [], [xor(0)]), 
                    rule((xor(_M), xor(_M)<=>xor(0)), [], [xor(_M), xor(_M)], [], [xor(0)]), 
                    [ (xor(_K), xor(_L)), (xor(_K), xor(_L))],
                    [xor(_K), xor(_K), _K=_L, _K=_L]),

                cp( state([xor(_N), xor(0)], [_O=_N], [_O, _N]), 
                    state([xor(_O), xor(0)], [_O=_N], [_O, _N]), 
                    rule((xor(_P), xor(_P)<=>xor(0)), [], [xor(_P), xor(_P)], [], [xor(0)]), 
                    rule((xor(_P), xor(_P)<=>xor(0)), [], [xor(_P), xor(_P)], [], [xor(0)]), 
                    [ (xor(_O), xor(_N))],
                    [xor(_O), xor(_O), xor(_N), _O=_N]),

                cp( state([xor(_Q), xor(0)], [_R=_Q], [_R, _Q]), 
                    state([xor(_R), xor(0)], [_R=_Q], [_R, _Q]), 
                    rule((xor(_S), xor(_S)<=>xor(0)), [], [xor(_S), xor(_S)], [], [xor(0)]), 
                    rule((xor(_S), xor(_S)<=>xor(0)), [], [xor(_S), xor(_S)], [], [xor(0)]), 
                    [ (xor(_R), xor(_Q))],
                    [xor(_R), xor(_R), xor(_Q), _R=_Q]),

                cp( state([xor(0), xor(0)], [_T=1], [_T]), 
                    state([xor(1), xor(_T)], [true, _T=1], [_T]), 
                    rule((xor(_U), xor(_U)<=>xor(0)), [], [xor(_U), xor(_U)], [], [xor(0)]), 
                    rule((xor(1)\xor(0)<=>true), [xor(1)], [xor(0)], [], [true]), 
                    [ (xor(_T), xor(1))],
                    [xor(_T), xor(_T), xor(0), _T=1]),

                cp( state([xor(1), xor(0)], [_V=0], [_V]), 
                    state([xor(1), xor(_V)], [true, _V=0], [_V]), 
                    rule((xor(_W), xor(_W)<=>xor(0)), [], [xor(_W), xor(_W)], [], [xor(0)]), 
                    rule((xor(1)\xor(0)<=>true), [xor(1)], [xor(0)], [], [true]), 
                    [ (xor(_V), xor(0))],
                    [xor(_V), xor(_V), xor(1), _V=0]),

                cp( state([xor(0), xor(0)], [_X=1], [_X]), 
                    state([xor(1), xor(_X)], [true, _X=1], [_X]), 
                    rule((xor(_Y), xor(_Y)<=>xor(0)), [], [xor(_Y), xor(_Y)], [], [xor(0)]), 
                    rule((xor(1)\xor(0)<=>true), [xor(1)], [xor(0)], [], [true]), 
                    [ (xor(_X), xor(1))],
                    [xor(_X), xor(_X), xor(0), _X=1]),

                cp( state([xor(1), xor(0)], [_Z=0], [_Z]), 
                    state([xor(1), xor(_Z)], [true, _Z=0], [_Z]), 
                    rule((xor(_E), xor(_E)<=>xor(0)), [], [xor(_E), xor(_E)], [], [xor(0)]), 
                    rule((xor(1)\xor(0)<=>true), [xor(1)], [xor(0)], [], [true]), 
                    [ (xor(_Z), xor(0))],
                    [xor(_Z), xor(_Z), xor(1), _Z=0]),

                cp( state([xor(1), xor(0)], [true], []), 
                    state([xor(1), xor(0)], [true], []), 
                    rule((xor(1)\xor(0)<=>true), [xor(1)], [xor(0)], [], [true]), 
                    rule((xor(1)\xor(0)<=>true), [xor(1)], [xor(0)], [], [true]), 
                    [ (xor(1), xor(1))],
                    [xor(1), xor(0), xor(0)]),

                cp( state([xor(1)], [true], []), 
                    state([xor(1)], [true], []), 
                    rule((xor(1)\xor(0)<=>true), [xor(1)], [xor(0)], [], [true]), 
                    rule((xor(1)\xor(0)<=>true), [xor(1)], [xor(0)], [], [true]), 
                    [ (xor(1), xor(1)), (xor(0), xor(0))],
                    [xor(1), xor(0)]),

                cp( state([xor(1), xor(1)], [true], []), 
                    state([xor(1), xor(1)], [true], []), 
                    rule((xor(1)\xor(0)<=>true), [xor(1)], [xor(0)], [], [true]), 
                    rule((xor(1)\xor(0)<=>true), [xor(1)], [xor(0)], [], [true]), 
                    [ (xor(0), xor(0))],
                    [xor(1), xor(0), xor(1)])])
        ),
        success).
        
test(   'xor.pl: Two non-trivial critical pairs between first and second rule',
        critical_pairs('examples/xor.pl', [
            cp( state([xor(0), xor(0)], [_T=1], [_T]), 
                state([xor(1), xor(_T)], [true, _T=1], [_T]), 
                rule((xor(_U), xor(_U)<=>xor(0)), [], [xor(_U), xor(_U)], [], [xor(0)]), 
                rule((xor(1)\xor(0)<=>true), [xor(1)], [xor(0)], [], [true]), 
                [ (xor(_T), xor(1))],
                [xor(_T), xor(_T), xor(0), _T=1])]),
        success).


test(   'mem.pl: Three overlaps of the rule with itself.',
        (
            all_critical_pairs('examples/mem.pl',  Res), 
            permutation(Res,[
                cp( state([cell(_A, _B), cell(_C, _D)], [_C=_A, _D=_E], [_C, _D, _F, _A, _E, _B]), 
                    state([cell(_C, _F), cell(_A, _E)], [_C=_A, _D=_E], [_C, _D, _F, _A, _E, _B]), 
                    rule((assign(_G, _H), cell(_G, _I)<=>cell(_G, _H)), [], [assign(_G, _H), cell(_G, _I)], [], [cell(_G, _H)]), 
                    rule((assign(_G, _H), cell(_G, _I)<=>cell(_G, _H)), [], [assign(_G, _H), cell(_G, _I)], [], [cell(_G, _H)]), 
                    [ (assign(_C, _D), assign(_A, _E))],
                    [assign(_C, _D), cell(_C, _F), cell(_A, _B), _C=_A, _D=_E]),

                cp( state([cell(_J, _K)], [_J=_L, _K=_M, _J=_L, _N=_O], [_J, _K, _N, _L, _M, _O]), 
                    state([cell(_L, _M)], [_J=_L, _K=_M, _J=_L, _N=_O], [_J, _K, _N, _L, _M, _O]), 
                    rule((assign(_P, _Q), cell(_P, _R)<=>cell(_P, _Q)), [], [assign(_P, _Q), cell(_P, _R)], [], [cell(_P, _Q)]), 
                    rule((assign(_P, _Q), cell(_P, _R)<=>cell(_P, _Q)), [], [assign(_P, _Q), cell(_P, _R)], [], [cell(_P, _Q)]), 
                    [ (assign(_J, _K), assign(_L, _M)), (cell(_J, _N), cell(_L, _O))],
                    [assign(_J, _K), cell(_J, _N), _J=_L, _K=_M, _J=_L, _N=_O]),

                cp( state([assign(_S, _T), cell(_U, _V)], [_U=_S, _W=_X], [_U, _V, _W, _S, _T, _X]), 
                    state([assign(_U, _V), cell(_S, _T)], [_U=_S, _W=_X], [_U, _V, _W, _S, _T, _X]), 
                    rule((assign(_Y, _Z), cell(_Y, _ZZ)<=>cell(_Y, _Z)), [], [assign(_Y, _Z), cell(_Y, _ZZ)], [], [cell(_Y, _Z)]), 
                    rule((assign(_Y, _Z), cell(_Y, _ZZ)<=>cell(_Y, _Z)), [], [assign(_Y, _Z), cell(_Y, _ZZ)], [], [cell(_Y, _Z)]), 
                    [ (cell(_U, _W), cell(_S, _X))],
                    [assign(_U, _V), cell(_U, _W), assign(_S, _T), _U=_S, _W=_X])])
            ),
            success).
    
test(   'mem.pl: Two actual critical pairs.',
        (
            critical_pairs('examples/mem.pl',  Res), 
            permutation(Res,[
            cp( state([cell(_A, _B), cell(_C, _D)], [_C=_A, _D=_E], [_C, _D, _F, _A, _E, _B]), 
                state([cell(_C, _F), cell(_A, _E)], [_C=_A, _D=_E], [_C, _D, _F, _A, _E, _B]), 
                rule((assign(_G, _H), cell(_G, _I)<=>cell(_G, _H)), [], [assign(_G, _H), cell(_G, _I)], [], [cell(_G, _H)]), 
                rule((assign(_G, _H), cell(_G, _I)<=>cell(_G, _H)), [], [assign(_G, _H), cell(_G, _I)], [], [cell(_G, _H)]), 
                [ (assign(_C, _D), assign(_A, _E))],
                [assign(_C, _D), cell(_C, _F), cell(_A, _B), _C=_A, _D=_E]),

            cp( state([assign(_S, _T), cell(_U, _V)], [_U=_S, _W=_X], [_U, _V, _W, _S, _T, _X]), 
                state([assign(_U, _V), cell(_S, _T)], [_U=_S, _W=_X], [_U, _V, _W, _S, _T, _X]), 
                rule((assign(_Y, _Z), cell(_Y, _ZZ)<=>cell(_Y, _Z)), [], [assign(_Y, _Z), cell(_Y, _ZZ)], [], [cell(_Y, _Z)]), 
                rule((assign(_Y, _Z), cell(_Y, _ZZ)<=>cell(_Y, _Z)), [], [assign(_Y, _Z), cell(_Y, _ZZ)], [], [cell(_Y, _Z)]), 
                [ (cell(_U, _W), cell(_S, _X))],
                [assign(_U, _V), cell(_U, _W), assign(_S, _T), _U=_S, _W=_X])])
        ),
        success).
        
        
% check_confluence

test(   'coin.pl',
        check_confluence('examples/coin.pl', 1),
        success).
        
test(   'leq.pl',
        check_confluence('examples/leq.pl', 0),
        success).
        
test(   'mem.pl',
        check_confluence('examples/mem.pl', 2),
        success).
        
test(   'merge.pl',
        check_confluence('examples/merge.pl',1),
        success).
        
test(   'twocoins.pl',
        check_confluence('examples/twocoins.pl', 1),
        success).
        
test(   'xor.pl',
        check_confluence('examples/xor.pl',0),
        success).

test(   'simple1.pl',
        check_confluence('examples/simple1.pl',0),
        success).
        
test(   'simple2.pl',
        check_confluence('examples/simple2.pl',1),
        success).

test(   'simple3.pl',
        check_confluence('examples/simple3.pl',1),
        success).

test(   'simple4.pl',
        check_confluence('examples/simple4.pl',0),
        success).
        

:- style_check(+singleton).


/*============================= General predicates ==========================*/

% run_tests(+GoalName)

% This predicate executes all testcases for the goal whose name is given as the
% argument GoalName.
% Simply calls run_tests/2 with an initial number of 0 failed testcases and all
% testcases with the according GoalName found in this file.
run_tests(GoalName) :- 
    findall(Test, find_test(GoalName, Test), Tests),
    run_tests(Tests, 0).


% find_test(+GoalName, ~Test)

% This predicate unifies Test with a testcase from the database whose goal is
% a term whose functor is GoalName or is composed of multiple sub-goals of 
% which the first one has a functor called GoalName.
find_test(GoalName, Test) :-
    test(Id, Goal, ExpRes),
    functor(Goal, GoalName, _),
    Test = test(Id, Goal, ExpRes).
    
find_test(GoalName, Test) :-
    test(Id, Goal, ExpRes),
    Goal =.. [','|[G|_]],
    functor(G, GoalName, _),
    Test = test(Id, Goal, ExpRes).


% run_tests(+Tests, +FailedCases)

% This predicate executes all testcases given in the list of testcase Tests.
% Furthermore it counts the number of already failed testcases
% in FailedCases in order to generate a report of success or failure after all
% testcases have been executed.
run_tests([], 0) :- write('All tests passed successfully'), nl,!.
run_tests([], X) :- write(X), write(' Test(s) failed!'), nl,!.
run_tests([T|TS], FC) :-
    run_test(T, Res),
    (Res ->  FC1 is FC ; FC1 is FC + 1),!,
    run_tests(TS, FC1).


% run_test(+Test, ~Res)

% This predicate runs the testcase Tes and returns the outcome
% bound to the variable Res. Res is true iff the test had the expected outcome.
run_test(test(Id, Goal, ExpRes), Res) :- 
    output_pre_test(Id, Goal, ExpRes),
    execute(Goal, ActRes),
    (
        ExpRes == ActRes ->
        (
            output_success(ActRes),
            Res = true
        )
        ;
        (
            output_failure(ActRes),
            Res = false
        )
    ).


% execute(+Goal, +ExpectedResult)

% Checks if Goal succeeds or fails. execute succeeds either when Goal succeeds
% and ExpectedResult is bound to the term "success" or if Goal fails and
% ExpectedResult is bound to failure.
execute(Goal, success) :-
    call(Goal).

execute(Goal, failure) :-
    call(\+ Goal).


% output_pre_test(+Id, +Goal, +ExpRes)

% This predicate creates the output displayed before the test is run. It
% generates the following output:
% "Test \Id"
% " Calling \Goal, expected result \ExpRes".
output_pre_test(Id, Goal, ExpRes) :- 
    write('Test '), 
    write(Id), nl,
    write('Calling '), 
    write(Goal), 
    write(', expected result: '), 
    write(ExpRes),
    write('...'), nl.


% output_success(+ActualResult)

% This predicate prints the string 
% "Test successful with result: \ActualResult"
output_success(ActRes) :- 
    write('Test successful with result: '),
    write(ActRes), nl, nl.


% output_failure(+ActualResult)

% This predicate prints the string 
% "Test NOT successful with result: \ActualResult"

output_failure(ActRes) :-
    write('Test NOT successful with result: '),
    write(ActRes), nl, nl.

/* t1 :- check_confluence('examples/ufd_basic.pl').

t2 :- check_confluence('examples/ufd_basic1.pl', link1, linkeq1).

t3 :- check_confluence('examples/ufd_found_compr.pl', compress, compress).

t4 :- check_confluence('examples/ufd_found_compr.pl', linkeq1c, linkeq1c).

t5(N) :- check_confluence('examples/ufd_basic.pl', N).

t6(N) :- check_confluence('examples/ufd_basic.pl', link, link, N). */


