:- use_module(library(chr)).
:- chr_constraint assign/2, cell/2.

assign(V,N), cell(V,O) <=> cell(V,N).
