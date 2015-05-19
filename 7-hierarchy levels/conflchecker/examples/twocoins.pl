:- use_module(library(chr)).
:- chr_constraint throw_coin/2.

throw_coin(X,Y) <=> X = head, Y = tail.
throw_coin(X,Y) <=> X = tail, Y = head.

