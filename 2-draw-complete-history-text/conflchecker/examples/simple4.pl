:- use_module(library(chr)).
:- chr_constraint p/1.

% Guards: All rules overlap with each other, although the first and second rule
% lead to an inconsistent built-in store and thus create no critical pair. The
% first and third rule also lead to a unification which then leads to an
% inconsistent built-in store. The second and third rule lead to an critical
% pair as well as every rule does with itself.

% The program is confluent

p(X) <=> X = 1 | true.
p(X) <=> X = 2 | true.
p(2) <=> true.

