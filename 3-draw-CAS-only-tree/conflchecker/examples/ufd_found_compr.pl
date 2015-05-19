% ufd_found_compr.pl
%
% Parallelized optimal union-find
%
% CPS       Thom Frühwirth: Parallelizing Union-Find in Constraint Handling
%           Rules Using Confluence Analysis, ICLP 2005, LNCS 3668
%
%   Rule        Rule        CPS     Found by conflcheck
%
%   findnode1   findnode1   1       yes
%   findnode1   findnroot1  1       yes
% ! findroot1   findroot1   1       0, all joinable
%
%   found1      found1      1       yes
%   found1      linkeq1c    2       yes
%   found1      linkleft1c  2       guard contains >=
%   found1      linkright1c 2       guard contains >=
%
%   compress    findnode1   1       yes
%   compress    found1      1       yes
% ! compress    compress    3       4 *
%
% ! linkeq1c    linkeq1c    18      6 **
%   linkeq1c    linkleft1c  39      guard contains >=
%   linkeq1c    linkright1c 39      guard contains >=
%   linkleft1c  linkleft1c  191     guard contains >=
%   linkleft1c  linkright1c 193     guard contains >=
%   linkright1c linkright1c 191     guard contains >=
%
%   *   1, 3, and 4: no rules applicable, 
%       2: no rules applicable after 1 application of compress
%
%   **  18 seems impossible. There are only 13 possible matchings of
%       head constraints.

:- use_module(library(chr)).

:- op(700, xfx, '~>').

:- chr_constraint
    (~>)/2,
    find/2,
    compr/2,
    root/2,
    found/2,
    foundc/2,
    link/2.

findnode1 @ 	A ~> B \ find(A,X) 	<=> find(B,X), compr(A,X).

findroot1 @ 	root(A,_) \ find(A,X) 	<=> found(A,X).

found1 @ 	A ~> B \ found(A,X) 	<=> found(B,X), compr(A,X).

compress @ 	foundc(C,X) \ A ~> B, compr(A,X) <=> A ~> C.

linkeq1c @ 	found(A,X), found(A,Y), link(X,Y) <=> foundc(A,X), foundc(A,Y).

linkleft1c @ 	found(A,X), found(B,Y), link(X,Y), root(A,N), root(B,M) 
			<=> N>=M | foundc(A,X), foundc(B,Y), B ~> A, 
					N1 is max(N,M+1), root(A, N1).

linkright1c @ 	found(A,X), found(B,Y), link(Y,X), root(A,N), root(B,M) 
			<=> N>=M | foundc(A,X), foundc(B,Y), B ~> A, 
					N1 is max(N,M+1), root(A, N1).

