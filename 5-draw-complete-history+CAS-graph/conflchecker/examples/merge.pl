:- use_module(library(chr)).
:- chr_constraint merge/3, globvars/1.


merge([], L2, L3)       <=> L2 = L3.
merge(L1, [], L3)       <=> L1 = L3.
merge([X|R1], L2, L3)   <=> L3 = [X|R3], merge(R1, L2, R3).
merge(L1, [Y|R2], L3)   <=> L3 = [Y|R3], merge(L1, R2, R3).




