% ufd_basic1.pl
%
% Basic parallel union-find
%
% CPS       Thom Frühwirth: Parallelizing Union-Find in Constraint Handling
%           Rules Using Confluence Analysis, ICLP 2005, LNCS 3668
%
%   Rule        Rule        CPS     Found by conflcheck
%
%   findnode    findnode    1       yes
%   findnode    findroot1   1       yes
%   linkeq1     linkeq1     6       yes
%   link1       linkeq1     13      yes
% ! link1       link1       65      contains non-terminating computation
%   found       link1       2       yes
%   found       found       1       yes


:- use_module(library(chr)).

:- op(700, xfx, '~>').

:- chr_constraint 
    find/2,
    found/2,
    (~>)/2,
    link/2,
    root/1.


findnode @ A ~> B \ find(A,X) <=> find(B,X).  

findroot1 @ root(A) \ find(A,X) <=> found(A,X).

found @ A ~> B \ found(A,X) <=> found(B,X).

linkeq1   @ link(X,Y), found(A,X), found(A,Y) <=> true.  

link1     @ link(X,Y), found(A,X), found(B,Y), root(A), root(B) <=> B ~> A, root(A).  

