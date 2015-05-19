:- use_module(library(chr)).
:- chr_constraint p/0, q/0, r/0.

% One overlap between rules possible leading to a non-trivial critical pair.
% Six more trivial critical pairs arise from the overlaps of the rules with
% itself.

p,q <=> true.
q,r <=> true.
