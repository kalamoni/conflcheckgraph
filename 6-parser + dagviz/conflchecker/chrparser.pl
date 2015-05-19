/*=============================================================================


    File:       chrparser.pl

    Authors:    Johannes Langbein, Ulm University, Germany, 
                jolangbein at gmail dot com
                (all predicates except read_file/2 and read_file_/1)
                
                Tom Schrijvers, K.U. Leuven, Belgium,
                tom.schrijvers at cs.kuleuven dot be
                (predicates read_file/2 and read_file_/1)

    Date:       02-06-2010
    
    Version:    1.0
    
    Copyright:  2010, Johannes Langbein, Tom Schrijvers

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



/*============================== chrparser ====================================

The predicates in this file implement a very simple CHR parser. The parser only
works correctly on syntactically correct files and provides no means for error
handling. CHR programs should be checked for syntactical correctness by one of
the established CHR systems before they are used with this parser.

The parser ignores everything in the file expect CHR simplification and
simpagation rules and the chr_constraint directive defining the CHR constraints
and their arity. This means the file can contain arbitrary Prolog predicates,
directives and CHR propagation rules as long as they are syntactical correct.

The syntax of rules supported by this parser is given by the following EBNF
grammar.

Rule        --> [rulename '@'] ActualRule
ActualRule  --> LHS '<=>' RHS
LHS         --> [KeptHead '\'] RemHead
RHS         --> [Guard '|'] Body
KeptHead    --> Constraints
RemHead     --> Constraints
Guard       --> Constraints
Body        --> Constraints
Constraints --> constraint {',' Constraints}

Shortly, a rule recognized by this parser is of the form 
    name @ KH \ RM <=> G | B
where name, KH, and G can be omitted, together with the according symbols.


Predicates in this file:
========================

    read_rules/3    Read rules and list of CHR constraints from a file.
    
    
Datastructures used:
====================

    rule(S, KH, RH, G, B)
        A term representing a CHR rule. S is the rule together with its name as 
        string as it is represented in the source file. KH, RH, G, B are lists 
        representing the kept head constraints, the removed head constraints, 
        the guard and the body of the rule. KH, and G are possibly empty. 

    con(F, N)
         A term representing a declaration of a CHR constraint. F is the name 
         of the constraint and N is its arity.

==============================================================================*/


:- module(parser, [read_rules/3]).

:- user:use_module(library(chr)).


%% read_rules(+FileName, -Rules, -CHRC)
%
% This predicate which extracts all rules from a file with the given name.
% The file name must be given as Prolog string, for example: 'src/program.pl'
% Rules is unified with a list of terms of the form rule(S, N, KH, RH, G, B).
% The list CHRC is the list of all CHR constraints appearing in the program. It
% contains terms of the form con(F, N).

read_rules(File, Rules, CHRC) :-
    read_file(File, Clauses),
    extract_constraint_list(Clauses, CHRC),
    extract_rules(Clauses, Rules).


% read_file(+FileName -Clauses)
%
% This predicate reads a Prolog source file provided its file name and returns
% a list of all clauses appearing in the source file. In case the source file
% contains an operator precedence declaration, this precedence is set in the
% runtime system

read_file(File,Clauses) :-
        see(File),
        read_file_aux(Clauses),
        seen.


% read_file_(-Clauses)
%
% This predicate returns a list of all clauses of the currently opened source
% file. In case the source file contains an operator precedence declaration,
% this precedence is set in the runtime system.

read_file_aux([Clause|Clauses]) :-
    read(Clause),
    (Clause == end_of_file ->
         Clauses = []
    ;
         (Clause = (:- op(A,B,C)) ->
            op(A,B,C)
         ;
            true
         ),
         read_file_aux(Clauses)
    ).
	

% extract_rules(+Clauses, -Rules)
%
% Given a list of Prolog clauses, this predicate returns a list of rules in
% the format described above. This predicate ignores all clauses
% which are not built according to the aforementioned grammar.

extract_rules([end_of_file|_], []) :- !.

extract_rules([H|R], [Rule|Rules]) :- 
    parse_rule(H, Rule),
    !,
    extract_rules(R, Rules).

extract_rules([_|R], Rules) :-
    extract_rules(R, Rules).


% parse_rule(+Term -Rule)
%
% This predicate succeeds if Term is a CHR rule according to the aforementioned
% grammar. In this case, Rule is unified with a term of the form
% rule(N, KH, RH, G, B) representing the rule.

parse_rule(Term, rule(Term, KH, RH, G, B)) :-
    Term = (_@ActRule),
    !,
    parse_actrule(ActRule, KH, RH, G, B).

parse_rule(Term, rule(Term, KH, RH, G, B)) :-
    parse_actrule(Term, KH, RH, G, B).


% parse_actrule(+Term, -KH, -RH, -G, -B)
%
% This predicate succeeds if Term is constructed according to the grammar rule
% for ActualRule in the aforementioned grammar. In this case, KH and RH are
% unified with the list of kept and removed head constraints respectively,
% while G and B are unified with the lists of constraints from the guard and
% body of the rule, respectively.

parse_actrule(Term, KH, RH, G, B) :-
    Term = (LHS<=>RHS),
    !,
    parse_lhs(LHS, KH, RH),
    parse_rhs(RHS, G, B).


% parse_lhs(+LHS, -KH, -RH)
%
% This predicate succeeds, if LHS is the left-hand side of a CHR rule according
% to the above grammar. In this case, KH is the list of kept head constraints,
% RH is the list of removed head constraints. If the left-hand side of a
% simplification rule is parsed, KH is the empty list.

parse_lhs(LHS, KH, RH) :- 
    LHS = (KHS\RHS),!,
    parse_constraints(KHS, KH),
    parse_constraints(RHS, RH).

parse_lhs(LHS, [], RH) :- 
    parse_constraints(LHS, RH).


% parse_rhs(+RHS, -G, -B)
%
% This predicate succeeds, if RHS is the right-hand side of a CHR rule
% according to the above grammar. In this case, G is the list of the built-in
% constraints from the guard of the rule and B is the list containing the
% constraints from the body of the rule. G is the empty list if the rule
% contains no guard.

parse_rhs(RHS, G, B) :-
    RHS = (GS|BS),
    !,
    parse_constraints(GS, G),
    parse_constraints(BS, B).

parse_rhs(RHS, [], G) :-
    parse_constraints(RHS, G).


% parse_constraints(+Term, -List)
%
% This predicate succeeds if term is an arbitrary term or a sequence of terms,
% separated by (,). In this case List is the list containing all the terms
% from the sequence. This predicate is used to parse the head, guard, or body
% of a rule into a list of constraints.
	
parse_constraints(Term, [C|Res]) :-
    Term = (C,CS),
    !,
    parse_constraints(CS, Res).
	
parse_constraints(Term, [Term]).


% extract_constraint_list(+Clauses ~CHRCons)
%
% This predicate takes a list of read-in Prolog clauses and extracts the list
% of CHR constraints as defined by the directive ":- chr_constraints..." in
% the source file. The resulting list CHRCons consists of terms of the form
% (F, N), where F is the functor and N the arity of a CHR constraint as
% defined by the directive. If no such directive is found in the list Clauses,
% the predicate fails.

extract_constraint_list([C|_], CHRC) :- 
    C = (:- chr_constraint CS),
    !,
    parse_constraint_list(CS, CHRC).
	
extract_constraint_list([_|R], CHRC) :- 
    extract_constraint_list(R, CHRC).


% parse_constraint_list(+ConList, ~CHRCons)
%
% This predicate parses the term ConList of the form (F1/N1, F2/N2, ...) where
% the Fi's are functors and the Ni's are arities, into a list CHRCons of terms
% of the form (Fi, Ni).

parse_constraint_list(CL, [(F, A)|CHRC]) :-
    CL = (C,R),
    C = (F/A),!,
    parse_constraint_list(R, CHRC).

parse_constraint_list(C, [(F, A)]) :- C = (F/A).

