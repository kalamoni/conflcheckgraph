% ufd_basic.pl
%
% Basic parallel union-find
%
% CPS   Thom Frühwirth: Parallelizing Union-Find in Constraint Handling
%       Rules Using Confluence Analysis, ICLP 2005, LNCS 3668
%
%   Rule        Rule        CPS     Found by conflcheck
%
%   findnode    findnode    1       yes
%   findnode    findroot    1       yes
%   linkeq      link        1       yes
%   findroot    link        1       yes
%   link        link        4       yes

:- use_module(library(chr)).

:- chr_constraint 
    make/1,
    find/2,
    union/2,
    arrow/2,
    link/2,
    root/1.


make     @ make(A) <=> root(A).

union    @ union(A,B) <=> find(A,X), find(B,Y), link(X,Y).

findnode @ arrow(A,B) \ find(A,X) <=> find(B,X).  

findroot @ root(B) \ find(B,X) <=> X=B.

linkeq   @ link(A,A) <=> true.  

link     @ link(A,B), root(A), root(B) <=>  arrow(B,A), root(A).

