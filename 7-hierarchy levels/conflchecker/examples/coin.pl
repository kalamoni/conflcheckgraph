:- use_module(library(chr)).
:- chr_constraint throw_coin/1.

% One non-trivial overlap, leading to non-joinable critical pair

% Program is not confluent.

throw_coin(Coin) <=> Coin = head.
throw_coin(Coin) <=> Coin = tail.
