% L0 WAM compiler
%
% L0 compiler written by prolog
% 
% ?- g(p(f(X),h(Y,f(a)),Y),L),write(L).
% [
%    get_structure(p/3,x:1),
%    unify_variable(x:2),
%    unify_variable(x:3),
%    unify_variable(x:4),
%    get_structure(f/1,x:2),
%    unify_variable(x:5),
%    get_structure(h/2,x:3),
%    unify_value(x:4),
%    unify_variable(x:6),
%    get_structure(f/1,x:6),
%    unify_variable(x:7),
%    get_structure(a/0,x:7)
% ]


:- dynamic count/1.
g(T,L):-
  terms(T,_,Ret),
  assert(count(0)),
  reg_assign(Ret,RetL,[],_),!,
  var_assign(RetL,L,[],_).

%% flatten form translater
terms(X,unify_var(N/A)=TmpV,Z):-
  compound(X),!,
  functor(X,N,A),X =.. [N|S],
  sub_terms(S,S_,Ret),
  Z = [[get_structure(N/A)=TmpV|S_]|Ret].

terms(X,unify_var(X),[]):-
  var(X),!.

terms(X,unify_var(X/0)=Tmp,[[get_structure(X/0)=Tmp]]):-
  atom(X),!.

sub_terms([],[],[]).
sub_terms([X|Y],[A|B],Z):-
  terms(X,A,X_),
  sub_terms(Y,B,Y_),
  append(X_,Y_,Z).

counter(X):-
  retract(count(N)),
  X is N + 1,
  assert(count(X)).


%% register assignment (containing reorder register number)
reg_assign([],[],V,V).
reg_assign([X|Y],Z,V,V2):-
  assign_register(X,A,V,V1),
  reg_assign(Y,B,V1,V2),append(A,B,Z).

assign_register([],[],VL,VL).
assign_register([X|Y],[A|B],VL,Vnew2):-
  reg_match(X,A,VL,Vnew),
  assign_register(Y,B,Vnew,Vnew2).

reg_match(get_structure(X),(get_structure(X),x:C),VL,VL):-　counter(C).
reg_match(unify_var(X),(unify_var(X),x:Index),VL,VL):-　find_var(X,VL,Index).
reg_match(unify_var(X),(unify_var(X),x:C),VL,[vpair(C,X)|VL]):-　counter(C).
reg_match(get_structure(X)=V,(get_structure(X),x:C),VL,VL):-　var(V),!,counter(C),V = C.
reg_match(get_structure(X)=V,(get_structure(X),x:V),VL,VL).
reg_match(unify_var(X)=V,(unify_var(X),x:C),VL,VL):-　var(V),!,counter(C),V = C.
reg_match(unify_var(X)=V,(unify_var(X),V),VL,VL).


%% varluable assignment (Building up hole instruction as first, and then reoreder and transform WAM instruction.)
var_assign([],[],VL,VL).
var_assign([X|Y],[A|B],VL,VL__):-
  var_assign(X,A,VL,VL_),
  var_assign(Y,B,VL_,VL__).
% If already exist varluable, call set_value, otherwise call set_variable
var_assign((unify_var(V),x:Index),unify_value(x:Index),VL,VL):-
  find_var(V,VL,Index).
var_assign((unify_var(V),x:Index),unify_variable(x:Index),VL,VL_):-
  VL_ = [vpair(Index,V)|VL].
% If varluable for structure (such as 'X = get_structure' ), entry int VL unconditionally. 
var_assign((get_structure(X),x:Index),get_structure(X,x:Index),VL,[vpair(Index,X)|VL]).


% find_var :checking if valuable already exist.
find_var(Var,[vpair(Index,V)|_],Index):-
    Var == V.
find_var(Var,[_|L],Index):-
    find_var(Var,L,Index).
find_var(_,[],_):-
    false.
