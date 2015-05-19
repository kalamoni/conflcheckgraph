:- use_module(library(chr)).
:- chr_constraint xor/1.

% Multiple overlaps: The first rule overlaps with itself in six different ways,
% leading to six critical pairs, all of them trivial. The second rule overlaps
% with itself in three different ways, also leading to to three different
% trivial critical pairs. The first and second rule overlaps in four different
% ways which lead to four different non-trivial critical pairs. Two of those
% critical pairs are duplicates of the other two, leading to a total of
% thirteen critical pairs, two of them non-trivial and unique.

xor(X), xor(X) <=> xor(0).
xor(1) \ xor(0) <=> true.

