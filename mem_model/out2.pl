:- module(test_parameters).
:- import create_input_val/3 from substitution.
:- export dom/4.
:- export create_input_vals/2.
:- export unquantif_preconds/2.
:- export quantif_preconds/2.
:- export strategy/2.
:- export precondition_of/2.


max_len(32).

dom(0,0,0,0).
dom('f',cont('mem',_),[],int([-128..127])).
dom('f',cont('inc',_),[],int([0..X])) :- max_len(X).
dom('f',cont('dec',_),[],int([0..X])) :- max_len(X).
dom('pathcrawler__f_precond',A,B,C) :- dom('f',A,B,C).

create_input_vals('f', Ins):-
  max_len(X),
  Y is X-1,
  create_input_val(dim('mem'), int([X..X]),Ins),
  create_input_val(dim('inc'), int([X..X]),Ins),
  create_input_val(dim('dec'), int([X..X]),Ins),
  create_input_val('max_len', int([X..X]), Ins),
  create_input_val('n', int([0..Y]), Ins),
  create_input_val('m', int([0..Y]), Ins),
  true.
create_input_vals('pathcrawler__f_precond',Ins) :- create_input_vals('f',Ins).

quantif_preconds('f',[]).
quantif_preconds('pathcrawler__f_precond',A) :- quantif_preconds('f',A).
unquantif_preconds('f',[]).
unquantif_preconds('pathcrawler__f_precond',A) :- unquantif_preconds('f',A).
strategy('f',[]).
strategy('pathcrawler__f_precond',A) :- strategy('f',A).
precondition_of('f','pathcrawler__f_precond').
