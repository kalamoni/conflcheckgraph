:- use_module(library(chr)).
:- chr_constraint p/0, q/0.

% One overlap, leading to the non-joinable critical pair (q, false)

% Program is not confluent.

p <=> q.
p <=> false.
