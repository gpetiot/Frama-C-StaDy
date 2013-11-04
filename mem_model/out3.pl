:- module(test_parameters).
:- import create_input_val/3 from substitution.
:- export dom/4.
:- export create_input_vals/2.
:- export unquantif_preconds/2.
:- export quantif_preconds/2.
:- export strategy/2.
:- export precondition_of/2.

maxlen(5).

dom(0,0,0,0).
dom('f',cont('mem',_),[],int([-128..127])).
dom('f',cont('inc',_),[],int([0..X])) :- maxlen(X).
dom('f',cont('dec',_),[],int([0..X])) :- maxlen(X).
dom('pathcrawler__f_precond',A,B,C) :- dom('f',A,B,C).

create_input_vals('f', Ins):-
  maxlen(X),
  Y is X-1,
  create_input_val(dim('mem'), int([0..X]),Ins),
  create_input_val(dim('inc'), int([0..X]),Ins),
  create_input_val(dim('dec'), int([0..X]),Ins),
  create_input_val('max_len', int([0..X]), Ins),
  create_input_val('n', int([0..Y]), Ins),
  create_input_val('m', int([0..Y]), Ins),
  true.
create_input_vals('pathcrawler__f_precond',Ins) :- create_input_vals('f',Ins).

quantif_preconds('f',
		 [
		  uq_cond([I],
			  [cond(infegal,0,I,pre), cond(inf,I,'max_len',pre)],
			  infegal,
			  cont('dec',I),
			  -(int(math),'max_len',I))
		 ]).
quantif_preconds('pathcrawler__f_precond',A) :- quantif_preconds('f',A).

unquantif_preconds('f',[
		       cond(egal,dim('inc'),dim('dec'),pre),
		       cond(egal,dim('inc'),dim('mem'),pre),
		       cond(egal,dim('inc'),'max_len',pre),
		       cond(egal,cont('dec',0),0,pre),
		       cond(egal,cont('inc',0),0,pre)
		   ]).
unquantif_preconds('pathcrawler__f_precond',A) :- unquantif_preconds('f',A).

strategy('f',[]).
strategy('pathcrawler__f_precond',A) :- strategy('f',A).
precondition_of('f','pathcrawler__f_precond').
