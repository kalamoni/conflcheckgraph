% ufd_rank.pl
%
% Optimized union-find
%
% CPS           Schrijvers, Frühwirth: Implementing and Analysing Union-Find in
%               CHR, Report CW 389, July 2004, K.U. Leuven
%
%   Rule        Rule        CPS     Found by conflcheck
%
%   findroot    linkleft    1       guard contains >=
%   findroot    linkright   1       guard contains >=
%   findnode    findnode    2       yes
%   findnode    findroot    1       yes
%
%   linkeq      linkleft    1       guard contains >=
%   linkeq      linkright   1       guard contains >=
%   linkleft    linkleft    20      guard contains >=
%   linkleft    linkright   26      guard contains >=
%   linkright   linkright   20      guard contains >=

:- use_module(library(chr)).

:- op(700, xfx, '~>').

:- chr_constraint
    make/1,
    root/2,
    find/2,
    union/2,
    (~>)/2,
    link/2.

make     @ make(A) <=> root(A,0).

union    @ union(A,B) <=> find(A,X), find(B,Y), link(X,Y).

findnode @ A ~> B, find(A,X) <=> find(B,X), A ~> X.

findroot @ root(A,_) \ find(A,X) <=> X=A.

linkqq   @ link(A,A) <=> true.  

linkleft @ link(A,B), root(A,N), root(B,M) <=> N>=M | 
                B ~> A, N1 is max(N,M+1), root(A,N1).
                
linkright@ link(B,A), root(A,N), root(B,M) <=> N>=M |
                B ~> A, N1 is max(N,M+1), root(A,N1).

