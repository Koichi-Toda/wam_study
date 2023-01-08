:- module(l1_query_compiler, [compile_query/2]).
% ?- query_compile(p(Z,h(Z,W),f(W)),L),write(L).

:- dynamic cnt/1.

compile_query(RootPropaty,L):-
  functor(RootPropaty,Fname,Arity), RootPropaty =.. [Fname|S],
  args(S,S_OUT),
  deep_trans(S_OUT,S_OUT_D,VL),
  writeln(xreg_assign(S_OUT_D,S_OUT_D2,VL,_)),
  xreg_assign(S_OUT_D,S_OUT_D2,VL,_),!,
  var_assign(S_OUT_D2,S_OUT_D3,VL,VL_LAST),writeln(vl_last(VL_LAST)),
  append(S_OUT_D3,[call(Fname/Arity)],L).

args([],[]).
args([X|Z],[X2|Z2]):-
  args_(X,X2),
  args(Z,Z2).
args_(X,(X,a:C)):-
  reg_cnt(C).

deep_trans([],[],[]).
deep_trans([X|Z],[X2|Z2],VL):-
  deep_trans_(X,X2,V),
  deep_trans(Z,Z2,V_),
  append(V_,V,VL).

deep_trans_((V,Arg),put_variable(x:C,Arg),[vpair(C,V)]):-
  var(V),!,
  reg_cnt(C).

deep_trans_((X,Arg),Z,[]):-
  compound(X),!,
  functor(X,Fname,Arity), X =.. [Fname|S],
  sub_terms(S,S_,Reorder),
  Z = [reorder(Reorder,[put_structure(Fname/Arity)=Arg|S_])].


deep_trans_((X,Arg),(put_structure(X/0,Arg),[])):-
  atom(X),!.


sub_terms([],[],[]).
sub_terms([X|Y],[A|B],Z):-
  terms(X,A,X_),
  sub_terms(Y,B,Y_),
  append(X_,Y_,Z).

%% フラット化処理本体
terms(X,assign_var(N/A)=TmpV,Z):-
  compound(X),!,
  functor(X,N,A),X =.. [N|S],
  sub_terms(S,S_,ReOrder),
  Z = [reorder(ReOrder,[put_structure(N/A)=TmpV|S_])].
terms(X,assign_var(X),[]):-
  var(X),!.

%% 引数レジスタのために一枚構造がはさまった
xreg_assign([],[],B,B).
xreg_assign([X|Z],Z3,V,V3):-
  reg_assign(X,X2,V,V2),
  xreg_assign(Z,Z2,V2,V3),
  append(X2,Z2,Z3).

reg_assign(put_variable(A,B),[put_variable(A,B)],V,V).
reg_assign([],[],V,V).
reg_assign([reorder(X1,X2)|Y],Z,V,V3):-
   assign_register(X2,A2,V,V1),
   reg_assign(X1,A1,V1,V2),append(A1,A2,A),
   reg_assign(Y,B,V2,V3),append(A,B,Z).

assign_register([],[],VL,VL).
assign_register([X|Y],[A|B],VL,Vnew2):-
  reg_match(X,A,VL,Vnew),
  assign_register(Y,B,Vnew,Vnew2).

reg_match(put_structure(X),(put_structure(X),x:C),VL,VL):-　reg_cnt(C).
reg_match(assign_var(X),(assign_var(X),x:Index),VL,VL):-　find_var(X,VL,Index).
reg_match(assign_var(X),(assign_var(X),x:C),VL,[vpair(C,X)|VL]):-　reg_cnt(C).
reg_match(put_structure(X)=a:Index,(put_structure(X),a:Index),VL,VL).
reg_match(put_structure(X)=V,(put_structure(X),x:C),VL,VL):-　var(V),!,reg_cnt(C),V = C.
reg_match(put_structure(X)=V,(put_structure(X),x:V),VL,VL).
reg_match(assign_var(X)=V,(assign_var(X),x:C),VL,VL):-　var(V),!,reg_cnt(C),V = C.
reg_match(assign_var(X)=V,(assign_var(X),V),VL,VL).

var_assign([],[],VL,VL).
var_assign([X|Y],[A|B],VL,VL__):-
  var_assign(X,A,VL,VL_),
  var_assign(Y,B,VL_,VL__).

var_assign((assign_var(V),_),set_value(x:Index),VL,VL):-
  find_var(V,VL,Index).
var_assign((assign_var(V),x:Index),set_variable(x:Index),VL,VL_):-
  VL_ = [vpair(Index,V)|VL].

var_assign((put_structure(X),x:Index),put_structure(X,x:Index),VL,[vpair(Index,X)|VL]).
var_assign((put_structure(X),a:Index),put_structure(X,a:Index),VL,[vpair(Index,X)|VL]).
var_assign((put_variable(A,B)),(put_variable(A,B)),VL,VL).

find_var(Var,[vpair(Index,V)|_],Index):-
    Var == V.
find_var(Var,[_|L],Index):-
    find_var(Var,L,Index).
find_var(_,[],_):-
    false.

% register counter
reg_cnt(X):-
  (retract(cnt(N)) ; N is 0),
  X is N + 1,
  assert(cnt(X)).
