:- use_module(library(chr)).
:- chr_constraint p/0, q/0.

% Most simple program. No overlap in between rules, only simple overlaps of
% rules with themselves, leading to trivial critical pairs.

% Program is confluent.

p <=> true.
q <=> true.
