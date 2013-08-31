% Written in 1983 by Ken Kahn and Mats Carlsson.

% lispify(IN,OUT) translates file IN in Edinburgh (Prolog-10/20) syntax
% into file OUT in LM-Prolog syntax.

:- public lispify/2.

lispify(In,Out) :- 
	see(In), tell(Out), nl,
	(recorded(warned,_,Ref), erase(Ref), fail; true),
	read_exp(Term),
	lispify2(Term),
	seen, told, nl.

mvar('$VAR'(_)).

read_exp(X) :- read(X0), expand_term(X0,X).

do_mode_decl((X,Y)) :- !, do_mode_decl(X), do_mode_decl(Y).
do_mode_decl(M) :- recorda(M,'MODE'(M),_).


lispify2(end_of_file).
lispify2((?- Query)) :- !, lispify2((:- Query)).	
lispify2((:- mode M)) :-
	do_mode_decl(M),
	read_exp(A),
	!, lispify2(A).
lispify2((:- op(X,Y,Z))) :- 
	op(X,Y,Z),
	read_exp(A),
	!, lispify2(A).
lispify2((:- Query)) :-
	numbervars(Query,0,N),
	first_translation(Query,pred,Pred1,N,_),
	print_for_lisp(['query-once',[quote,Pred1]]), nl, nl,
	read_exp(Y),
	!, lispify2(Y).
lispify2(Clause) :-
	f_of(Clause,Key),
	read_exp(Y),
	!, lispify3(Y,Key,[Clause|C],C).

lispify3(end_of_file,Key,Clauses,[]) :-
	lispify_pred(Key,Clauses),
	!.
lispify3((?- Query),Key,Clauses,[]) :- 
	lispify_pred(Key,Clauses),
	!, lispify2((:- Query)).
lispify3((:- mode M),Key,Clauses,[]) :-
	do_mode_decl(M),
	lispify_pred(Key,Clauses),
	read_exp(A),
	!, lispify2(A).
lispify3((:- op(X,Y,Z)),Key,Clauses,[]) :- 
	op(X,Y,Z),
	lispify_pred(Key,Clauses),
	read_exp(A),
	!, lispify2(A).
lispify3((:- Query),Key,Clauses,[]) :-
	lispify_pred(Key,Clauses),
	numbervars(Query,0,N),
	first_translation(Query,pred,Pred1,N,_),
	print_for_lisp(['query-once',[quote,Pred1]]), nl, nl,
	read_exp(A),
	!, lispify2(A).
lispify3(Clause,Key,Clauses,[Clause|C]) :-
	f_of(Clause,Key),
	read_exp(A),
	!, lispify3(A,Key,Clauses,C).
lispify3(Clause,Key,Clauses,[]) :-
	lispify_pred(Key,Clauses),
	f_of(Clause,Key1),
	read_exp(A),
	!, lispify3(A,Key1,[Clause|C],C).

f_of((H :- _),Key) :- !, f_of(H,Key).
f_of(H,N/A) :- functor(H,N,A).

lispify_pred(Name/Ar,Clauses) :- 
	(lm(Name), warn_mask(Name,Name1); Name=Name1),
	lisp_clauses(Clauses,Clauses1,Name1),
	optionpart(Name/Ar,Clauses1,Clauses2),
	print_for_lisp(['define-predicate',Name1|Clauses2]),
	!, nl, nl, ttyput(".").

optionpart(Name/Ar,Clauses,
	   [[do(w(':options')),[do(w(':argument-list')),L]]|Clauses]):-
	functor(Key,Name,Ar),
	recorded(Key,'MODE'(Key),Ref),
	erase(Ref),
	!, trans_arglist(0,Ar,Key,L,[]).
optionpart(_,Clauses,Clauses).

trans_arglist(A,A,_,L,L) :- !.
trans_arglist(A0,A,Key,[X|L0],L) :-
	A1 is A0+1,
	arg(A1,Key,X0),
	(X0 = ?, X = *;  X0 = X),
	!, trans_arglist(A1,A,Key,L0,L).

lisp_clauses([],[],_).
lisp_clauses([((H:-B))|Rest],[do(nl),[Head1|Body1]|Rest1],Rename) :-
	numbervars((H:-B),0,N),
	first_translation(H,pred,Head1,Rename,N,N1),
	conjunction_list(B,Body1,N1,_),
	!, lisp_clauses(Rest,Rest1,Rename).
lisp_clauses([H|Rest],L,R) :- lisp_clauses([(H:-true)|Rest],L,R).

append([],X,X).
append([A|X],Y,[A|Z]) :- append(X,Y,Z).

name_append(Prefix,Name,Prefixed) :-
	name(Name,Namelist), append(Prefix,Namelist,PNamelist),
	name(Prefixed,PNamelist).

warn1 :- ttynl, display('WARNING: ').

warn_mask(Pred,PPred) :-
	name_append("defined-",Pred,PPred),
	(recorded(warned,Pred,_), !; 
	 recorda(warned,Pred,_),
	 warn1, display('The predicate '),
	 display(Pred),	
	 ttynl, display(' is already defined in LM-Prolog, renamed to '),
	 display(PPred)).


warn_udf(F,Translation) -->
	{functor(F,Name,Arity),
	 (recorded(warned,Name/Arity,_), !;
	  recorda(warned,Name/Arity,_),
	  warn1, display(Name), ttyput("/"), display(Arity), 
	  display(' is undefined in LM-Prolog')),
	 name_append("undefined-",Name,Newname),
	 F=..[_|Args]},
	translation([Newname|Args],term,Translation).

warn_md(F) :-
	recorded(warned,F,_), !;
	recorda(warned,F,_),
	warn1, display(F), display(' is implementation dependent').

lpar :- put("(").
rpar :- put(")").

print_for_lisp(do(nl)) :- nl, !.
print_for_lisp(do(w(X))) :- write(X), !.
print_for_lisp([quote,X]) :- put("'"), print_for_lisp(X), !.
print_for_lisp([]) :- write('()'), !.
print_for_lisp([X|Y]) :-
	lpar, print_for_lisp(X), print_for_lisp_rest(Y), rpar, !.
print_for_lisp(X) :- mvar(X), put("?"), write(X).
print_for_lisp(S) :- number(S), write(S); name(S,T), mput0(S,T), !.

print_for_lisp_rest([]) :- !.
print_for_lisp_rest([X|Y]) :-
	tab(1), print_for_lisp(X), print_for_lisp_rest(Y), !.
print_for_lisp_rest(X) :- write(' . '), print_for_lisp(X), !.

slashp([A|_]) :- memb(A," /?|#(),.;:`'""").
slashp([_|X]) :- slashp(X).

%Heuristic: if needs slashification, we print with |'s
%unless length=1, in which case we print a slashified character.
mput0(_,[A]) :- slashp([A]), !, put("/"), put(A).
mput0(_,X) :- slashp(X), !, put("|"), mput1(X), put("|").
mput0(Name,_) :- write(Name).

mput1([A|B]) :- memb(A,"/|"), !, put("/"), put(A), mput1(B).
mput1([A|B]) :- !, put(A), mput1(B).
mput1([]).

conjunction_list(true,[]) --> !.
conjunction_list((A,B),[A1|B1]) --> !,
	first_translation(A,pred,A1), conjunction_list(B,B1).
conjunction_list(A,[A1]) --> first_translation(A,pred,A1).

disjunction_list(fail,[]) --> !.
disjunction_list((A;B),[A1|B1]) --> !,
	first_translation(A,pred,A1), 
	disjunction_list(B,B1).
disjunction_list(A,[A1]) --> first_translation(A,pred,A1).

cases_list((P->Q;R->S),[Case1,Case2]) -->
	first_translation((P->Q),pred,[cases,Case1]),
	first_translation((R->S),pred,[cases,Case2]).
cases_list((P->Q;R),[Thiscase|Rest]) -->
	first_translation((P->Q),pred,[cases,Thiscase]),
	(cases_list(R,Rest); 
	 first_translation(R,pred,R2), {Rest=[[[true],R2]]}).

% --- Free variable hackery.

unquant(_^X,Y) :- !, unquant(X,Y).
unquant(X,X).

global_vas(Term, Bound, VarList, [Term|VarList]) :-
	mvar(Term),
	not_in_term(Bound, Term),
	not_in_list(VarList, Term),
	!.
global_vas(Term, _, VarList, VarList) :-
	mvar(Term),
	!.
global_vas(Term, Bound, OldList, NewList) :-
	quant_check(Term, Bound, NewTerm, NewBound),
	!,
	global_vas(NewTerm, NewBound, OldList, NewList).
global_vas(Term, Bound, OldList, NewList) :-
	functor(Term, _, N),
	global_vas(N, Term, Bound, OldList, NewList).

global_vas(0, _, _, VarList, VarList) :- !.
global_vas(N, Term, Bound, OldList, NewList) :-
	arg(N, Term, Argument),
	global_vas(Argument, Bound, OldList, MidList),
	M is N-1, !,
	global_vas(M, Term, Bound, MidList, NewList).

quant_check(\+ _,	       Bound, fail,	Bound      ) :- !.
quant_check(not(_),	       Bound, fail,	Bound	   ) :- !.
quant_check(Var^Goal,	       Bound, Goal,	Bound+Var) :- !.
quant_check(setof(Var,Goal,Set),  Bound, Goal-Set, Bound+Var) :- !.
quant_check(bagof(Var,Goal,Bag),  Bound, Goal-Bag, Bound+Var) :- !.


not_in_term(Term, Var) :-
	mvar(Term), !,
	Term \== Var.
not_in_term(Term, Var) :-
	functor(Term, _, N),
	not_in_term(N, Term, Var).

not_in_term(0, _, _) :- !.
not_in_term(N, Term, Var) :-
	arg(N, Term, Argument),
	not_in_term(Argument, Var),
	M is N-1, !,
	not_in_term(M, Term, Var).


not_in_list([Head|Tail], Var) :-
	Head \== Var,
	!,
	not_in_list(Tail, Var).
not_in_list([], _).

% --- End free variable hackery.


memb(X,[X|_]).
memb(X,[_|L]) :- memb(X,L).

assertion((P:-Q),[[P]|Q1]) --> {atom(P)}, conjunction_list(Q,Q1).
assertion((P:-Q),[P1|Q1]) --> translation(P,term,P1), conjunction_list(Q,Q1).
assertion(P,P1) --> assertion((P:-true),P1).

%the second argument of is/2.
arith_translation(X,X) --> {mvar(X)}.
arith_translation(B,B1) --> translation(B,arith,B1).

first_translation(X,Y,Z,Rename) -->
	{functor(X,Rename,_)}, translation(X,Y,Z), !.
first_translation(X,Y,Z,Rename) -->
	{X=..[_|L], X1=..[Rename|L]}, translation(X1,Y,Z), !.


first_translation(X,Y,Z) --> translation(X,Y,Z), !.

translation(X,arith,[quote,X]) --> {mvar(X)}.
translation(X,arith,X) --> {atom(X)}.
translation([X|_],arith,X) --> {number(X)}.
translation(X,term,X) --> {atom(X)}.
translation([A|B],term,[A1|B1]) -->
	translation(A,term,A1), 
	translation(B,term,B1).
translation(X,_,X) --> {number(X)}.
translation(X,_,X) --> {mvar(X)}.
translation(consult(A),pred,[load,A1]) --> {translation(A,term,A1)}.
translation(reconsult(A),pred,[load,A1]) --> {translation(A,term,A1)}.
translation([F|Fs],pred,[map,load,L]) --> {translation([F|Fs],term,L)}.
translation(see(X),pred,T) --> warn_udf(see(X),T).
translation(seeing(X),pred,T) --> warn_udf(seeing(X),T).
translation(seen,pred,T) --> warn_udf(seen,T).
translation(tell(X),pred,T) --> warn_udf(tell(X),T).
translation(telling(X),pred,T) --> warn_udf(telling(X),T).
translation(told,pred,T) --> warn_udf(told,T).
translation(write(A),pred,[princ,A1]) -->
	translation(A,term,A1).
translation(writeq(A),pred,[prin1,A1]) -->
	translation(A,term,A1).
translation(nl,pred,[tyo,do(w('#\return'))]) --> [].
translation(display(A),pred,[princ,A1,t]) -->
	translation(A,term,A1).
translation(portray(X),pred,[grind,X1]) --> 
	translation(X,term,X1).
translation(format(X,L),pred,[format,t,X1|L1]) --> 
	translation(X,term,X1),
	translation(L,term,L1).
translation(ttynl,pred,[tyo,do(w('#\return')),t]) --> [].
translation(ttyflush,pred,[true]) --> [].
translation(ttyget0(A),pred,[tyi,A1,t]) -->
	{warn_md('ttyget0/1')}, translation(A,term,A1).
translation(ttyput(A),pred,[tyo,A1,t]) -->
	translation(A,term,A1), {warn_md('ttyput/1')}.
translation(get0(A),pred,[tyi,A1]) -->
	translation(A,term,A1), {warn_md('get0/1')}.
translation(put(A),pred,[tyo,A1]) --> 
	translation(A,term,A1), 
	{warn_md('put/1')}.
translation(tab(A),pred,[format,t,do(w('"~VX"')),A1]) -->
	translation(A,term,A1).
translation(read(A),pred,[read,A1]) --> translation(A,term,A1).
translation(putatom(X),pred,T) --> warn_udf(putatom(X),T).
translation(close(X),pred,T) --> warn_udf(close(X),T).
translation(fileerrors,pred,T) --> warn_udf(fileerrors,T).
translation(nofileerrors,pred,T) --> warn_udf(nofileerrors,T).
translation(rename(X,Y),pred,T) --> warn_udf(rename(X,Y),T).
translation(A is B,pred,['lisp-value',A1,B1]) -->
	translation(A,term,A1), 
	arith_translation(B,B1).
translation(A+B,arith,[+,A1,B1]) -->
	translation(A,arith,A1), 
	translation(B,arith,B1).
translation(A-B,arith,[-,A1,B1]) -->
	translation(A,arith,A1), 
	translation(B,arith,B1).
translation(A*B,arith,[*,A1,B1]) -->
	translation(A,arith,A1), 
	translation(B,arith,B1).
translation(A/B,arith,[/,A1,B1]) -->
	translation(A,arith,A1), 
	translation(B,arith,B1).
translation(A mod B,arith,[\,A1,B1]) -->
	translation(A,arith,A1), 
	translation(B,arith,B1).
translation(-A,arith,[-,A1]) --> translation(A,arith,A1).
translation(A /\ B,arith,[logand,A1,B1]) -->
	translation(A,arith,A1), translation(B,arith,B1).
translation(A \/ B,arith,[logior,A1,B1]) -->
	translation(A,arith,A1), translation(B,arith,B1).
translation(\(A),arith,[lognot,A1]) --> translation(A,arith,A1).
translation(A << B,arith,[lsh,A1,B1]) -->
	translation(A,arith,A1), translation(B,arith,B1).
translation(A >> B,arith,[lsh,A1,[-,B1]]) -->
	translation(A,arith,A1), translation(B,arith,B1).
translation(true,pred,[true]) --> [].
translation(otherwise,pred,[true]) --> [].
translation(fail,pred,[fail]) --> [].
translation(false,pred,[fail]) --> [].
translation((A,B),pred,[and|Conj]) --> conjunction_list((A,B),Conj).
translation((P->Q;R),pred,[cases|Cases]) --> cases_list((P->Q;R),Cases).
translation((A;B),pred,[or|Disj]) --> disjunction_list((A;B),Disj).
translation(length(A,B),pred,[length,B1,A1]) -->
	translation(A,term,A1), translation(B,term,B1).
translation(!,pred,[cut]) --> [].
translation(\+ A,pred,['cannot-prove',A1]) -->
	translation(A,pred,A1).
translation((A->B),pred,[cases,[['prove-once',A1],B1]]) -->
	translation(A,pred,A1), translation(B,pred,B1).
translation(abort,pred,[error,do(w('si:abort'))]) --> [].
translation(log,pred,T) --> warn_udf(log,T).
translation(nolog,pred,T) --> warn_udf(nolog,T).
translation(compare(X,Y,Z),pred,[compare,X1,Y1,Z1]) -->
	translation(X,term,X1), 
	translation(Y,term,Y1), 
	translation(Z,term,Z1).
translation(sort(X,Y),pred,[sort,Y1,X1,'standard-order']) -->
	translation(X,term,X1), 
	translation(Y,term,Y1).	
translation(X @< Y,pred,[compare,<,X1,Y1]) -->
	translation(X,term,X1), 
	translation(Y,term,Y1).	
translation(X @> Y,pred,[compare,>,X1,Y1]) -->
	translation(X,term,X1), 
	translation(Y,term,Y1).	
translation(X @=< Y,pred,['cannot-prove',[compare,>,X1,Y1]]) -->
	translation(X,term,X1), 
	translation(Y,term,Y1).	
translation(X @>= Y,pred,['cannot-prove',[compare,<,X1,Y1]]) -->
	translation(X,term,X1), 
	translation(Y,term,Y1).	
translation(X>Y,pred,[>,X1,Y1]) -->
	translation(X,term,X1), 
	translation(Y,term,Y1).
translation(X<Y,pred,[<,X1,Y1]) -->
	translation(X,term,X1), 
	translation(Y,term,Y1).
translation(X=Y,pred,[=,X1,Y1]) -->
	translation(X,term,X1), 
	translation(Y,term,Y1).
translation(A=:=B,pred,
	['lisp-predicate',[=,A1,B1]]) -->
	translation(A,arith,A1), translation(B,arith,B1).
translation(A=\=B,pred,
	['lisp-predicate',[not,[=,A1,B1]]]) -->
	translation(A,arith,A1), translation(B,arith,B1).
translation(A=<B,pred,['<=',A1,B1]) -->
	translation(A,term,A1), translation(B,term,B1).
translation(A>=B,pred,['>=',A1,B1]) -->
	translation(A,term,A1), translation(B,term,B1).
translation(A==B,pred,[identical,A1,B1]) -->
	translation(A,term,A1), translation(B,term,B1).
translation(A\==B,pred,['not-identical',A1,B1]) -->
	translation(A,term,A1), translation(B,term,B1).
translation(sort(X,Y),pred,T) --> warn_udf(sort(X,Y),T).
translation(keysort(X,Y),pred,T) --> warn_udf(keysort(X,Y),T).
translation(var(A),pred,[variable,A1]) --> translation(A,term,A1).
translation(nonvar(A),pred,['not-variable',A1]) --> translation(A,term,A1).
translation(atom(A),pred,[symbol,A1]) --> translation(A,term,A1).
translation(atomic(A),pred,[atomic,A1]) --> translation(A,term,A1).
translation(number(A),pred,[number,A1]) --> translation(A,term,A1).
translation(functor(A,B,C),pred,[and,[=,A1,[B1|U]],[length,C1,U]]) -->
	numbervars(U),
	{warn_md('functor/3')},
	translation(A,term,A1),
	translation(B,term,B1),
	translation(C,term,C1).
translation(arg(A,B,C),pred,[nth,C1,A1,B1]) -->
	{warn_md('arg/3')},
	translation(A,term,A1),
	translation(B,term,B1),
	translation(C,term,C1).
translation(A=..B,pred,[=,A1,B1]) -->
	{warn_md('=../2')},
	translation(A,term,A1), translation(B,term,B1).
translation(name(A,B),pred,[exploden,B1,A1]) --> 
	{warn_md('name/2')},
	translation(A,term,A1), translation(B,term,B1).
translation(clause(A,B),pred,[clause,[A1|B1]]) -->
	translation(A,term,A1), translation(B,term,B1).
translation(clause(X,Y,Z),pred,T) --> warn_udf(clause(X,Y,Z),T).
translation(listing,pred,['print-definition',U]) --> 
	numbervars(U).
translation(listing(A),pred,['print-definition',A1]) --> 
	translation(A,term,A1).
translation(setof(A,B,C),pred,['quantified-set-of',C1,Q,A1,B2]) -->
	translation(A,term,A1),
	{unquant(B,B1)},
	translation(B1,term,B2),
	translation(C,term,C1),
	{global_vas(B,A,[],Q)}.
translation(bagof(A,B,C),pred,['quantified-bag-of',C1,Q,A1,B2]) -->
	translation(A,term,A1),
	{unquant(B,B1)},
	translation(B1,term,B2),
	translation(C,term,C1),
	{global_vas(B,A,[],Q)}.
translation(assert(A),pred,[assert,A1]) --> 
	assertion(A,A1).
translation(asserta(A),pred,[asserta,A1]) --> 
	assertion(A,A1).
translation(assertz(A),pred,[assertz,A1]) --> 
	assertion(A,A1).
translation(assert(A,_),pred,[assert,A1]) --> 
	assertion(A,A1).
translation(asserta(A,_),pred,[asserta,A1]) --> 
	assertion(A,A1).
translation(assertz(A,_),pred,[assertz,A1]) --> 
	assertion(A,A1).
translation(retract(A),pred,[retract,A1]) --> assertion(A,A1).
translation(abolish(A,_),pred,['retract-all',A1]) --> translation(A,term,A1).
translation(numbervars(X,Y,Z),pred,T) --> warn_udf(numbervars(X,Y,Z),T).
translation(ancestors(X),pred,T) --> warn_udf(ancestors(X),T).
translation(subgoal_of(X),pred,T) --> warn_udf(subgoal_of(X),T).
translation(current_atom(X),pred,T) --> warn_udf(current_atom(X),T).
translation(current_functor(X,Y),pred,T) --> warn_udf(current_functor(X,Y),T).
translation(current_predicate(N,_),pred,[predicator,N1]) -->
	translation(N,term,N1).
translation(compile(F),pred,[map,'compile-file',F1]) --> 
	translation(F,term,F1).
translation(incore(G),pred,[call,G1]) --> translation(G,pred,G1).
translation(call(G),pred,[call,G1]) --> translation(G,pred,G1).
translation(_^G,pred,[call,G1]) --> translation(G,pred,G1).
translation(revive(X,Y),pred,T) --> warn_udf(revive(X,Y),T).
translation(recorded(X,Y,Z),pred,T) --> warn_udf(recorded(X,Y,Z),T).
translation(recorda(X,Y,Z),pred,T) --> warn_udf(recorda(X,Y,Z),T).
translation(recordz(X,Y,Z),pred,T) --> warn_udf(recordz(X,Y,Z),T).
translation(erase(X),pred,T) --> warn_udf(erase(X),T).
translation(instance(X,Y),pred,T) --> warn_udf(instance(X,Y),T).
translation('NOLC',pred,T) --> warn_udf('NOLC',T).
translation('LC',pred,T) --> warn_udf('LC',T).
translation(prompt(X,Y),pred,T) --> warn_udf(prompt(X,Y),T).
translation(current_op(X,Y,Z),pred,T) --> warn_udf(current_op(X,Y,Z),T).
translation(op(X,Y,Z),pred,T) --> warn_udf(op(X,Y,Z),T).
translation(break,pred,[break]) --> [].
translation(save(X),pred,T) --> warn_udf(save(X),T).
translation(core_image,pred,T) --> warn_udf(core_image,T).
translation(restore(X),pred,T) --> warn_udf(restore(X),T).
translation(maxdepth(X),pred,T) --> warn_udf(maxdepth(X),T).
translation(depth(X),pred,T) --> warn_udf(depth(X),T).
translation(gcguide(X),pred,T) --> warn_udf(gcguide(X),T).
translation(gc,pred,T) --> warn_udf(gc,T).
translation(nogc,pred,T) --> warn_udf(nogc,T).
translation(trimcore,pred,T) --> warn_udf(trimcore,T).
translation(statistics,pred,T) --> warn_udf(statistics,T).
translation(statistics(X,Y),pred,T) --> warn_udf(statistics(X,Y),T).
translation(debug,pred,T) --> warn_udf(debug,T).
translation(nodebug,pred,T) --> warn_udf(nodebug,T).
translation(trace,pred,T) --> warn_udf(trace,T).
translation(leash(X),pred,T) --> warn_udf(leash(X),T).
translation(spy(X),pred,T) --> warn_udf(spy(X),T).
translation(nospy(X),pred,T) --> warn_udf(nospy(X),T).
translation(debugging,pred,T) --> warn_udf(debugging,T).
translation(expand_term(X,Y),pred,T) --> warn_udf(expand_term(X,Y),T).
translation(phrase(X,Y),pred,T) --> warn_udf(phrase(X,Y),T).
translation(version,pred,T) --> warn_udf(version,T).
translation(version(X),pred,T) --> warn_udf(version(X),T).
translation(plsys(X),pred,T) --> warn_udf(plsys(X),T).
translation(reinitialise,pred,T) --> warn_udf(reinitialise,T).
translation(tmpcor(A,B,C),pred,T) --> warn_udf(tmpcor(A,B,C),T).
translation(run(A,B),pred,T) --> warn_udf(run(A,B),T).
translation(X,pred,T) -->
	{X=..[F|Args], lm(F), warn_mask(F,F1)}, 
	translation([F1|Args],term,T).
translation(X,_,X2) --> 
	{X=..X1}, translation(X1,term,X2). %the default

:- mode lm(+).

lm(<).
lm(=<).
lm(=).
lm(>).
lm(>=).
lm('add-world').
lm('all-worlds').
lm(and).
lm(append).
lm(apropos).
lm(assert).
lm(asserta).
lm(assertz).
lm(assume).
lm(atomic). %
lm('bag-of').
lm(call).
lm('can-prove').
lm('cannot-prove').
lm(cases).
lm('circularity-mode').
lm(clause).
lm(clauses).
lm(compare). %
lm(compile).
lm('compile-file').
lm('condition-protect').
lm(constrain).
lm(cut).
lm('define-predicate').
lm('defined-in-world').
lm(definition).
lm(delete).
lm(demos).
lm('destroy-world').
lm(difference).
lm(documentation).
lm(either).
lm(error).
lm(exploden).
lm(fail). %
lm(false). %
lm(finite).
lm(format). %
lm(freeze).
lm('generate-name').
lm('generate-symbol').
lm(grind).
lm(ground).
lm(identical).
lm(if).
lm(infinite).
lm(interrupts).
lm(intersection).
lm(lambda).
lm('lazy-bag-of').
lm('lazy-set-of').
lm(let).
lm(length). %
lm('lisp-command').
lm('lisp-predicate').
lm('lisp-type').
lm('lisp-value').
lm(load).
lm('make-true').
lm(map).
lm(member).
lm(meter).
lm(not).
lm('not-=').
lm('not-identical').
lm('not-variable').
lm(nth).
lm(number).
lm('open-file').
lm(option).
lm(or).
lm(predicator).
lm(princ).
lm(prin1).
lm(print).
lm('print-definition').
lm(product).
lm('protected-worlds').
lm('prove-once').
lm('quantified-bag-of').
lm('quantified-set-of').
lm(quotient).
lm(read).
lm(remove).
lm('remove-definition').
lm('remove-world').
lm(repeat). %
lm(retract).
lm('retract-all').
lm(reverse).
lm(rules).
lm(same).
lm('save-world').
lm('set-of').
lm(sort). %
lm('standard-order').
lm(step).
lm(substitute).
lm(sum).
lm(symbol).
lm(time).
lm('time-and-print').
lm(trace).
lm(true). %
lm(tyi).
lm(tyo).
lm('undefined-predicate-mode').
lm(union).
lm(universe).
lm(untrace).
lm('untrace-query').
lm('unwind-protect').
lm(variable).
lm(variables).
lm('who-state').
lm(with).
lm('with-world').
lm('without-world').
lm('y-or-n').

