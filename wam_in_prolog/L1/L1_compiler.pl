:- use_module(l1_query_compiler, [compile_query/2]).
% L1 prolog WAM compiler
% ?- prolog(p(f(X),h(Y,f(a)),Y),p(Z,h(Z,W),f(W))).
:- dynamic count/1.

prolog(Code,Query):-
    compile_code(Code,WAM_Code),
    compile_query(Query,WAM_Query),
    functor(Code,F,A),
    wam((F/A,WAM_Code),WAM_Query),
    listing([reg_ax,reg_h,reg_p,store]).

%%
%% store[address] を導入すべきか？
%% heap(address):- sore(address).
%% stack(address):- store(address).
%% こうすると、すべてのエリアは、基本的に storeで表現できることになる。(場合分けが不要となる場面が出てくる。addressだけ知っていればよいと。）


:- dynamic code_area/3, store/2.
:- dynamic reg_h/1, reg_s/1, reg_p/1.
:- dynamic reg_ax/2.
:- dynamic unify_mode/1.

% HEAP is part of main memory (all memory accsess can be use store/2 ).
set(heap(ADDRESS,VALUE)):- assert(store(ADDRESS,VALUE)).
reset(heap(ADDRESS,VALUE)):- retract(store(ADDRESS,VALUE)).
heap(ADDRESS,VALUE):- store(ADDRESS,VALUE).



wam((F/A,Code),Query):-
  assert(reg_h(0)),
  store_code(F/A,Code),
  exec_query(Query).

% store wam code into CODE_AREA
store_code(Label,[X|Z]):-
  assert(code_area(0,Label,X)),
  assert(reg_p(1)),
  store_code(Z).
store_code([]).
store_code([X|Z]):-
  store_code_(X),
  store_code(Z).

store_code_(Code):-
  retract(reg_p(N)),
  assert(code_area(N,_,Code)),
  N1 is N + 1,
  assert(reg_p(N1)).

exec_query([]).
exec_query([X|Z]):-
  exec_query_(X),
  exec_query(Z).
exec_query_(X):-
  wam_inst(X).


%% WAM instuctions (for query)
wam_inst(put_variable(x:X,a:A)):-
  retract(reg_h(H)),
  H_VALUE = (ref, H),
  set(heap(H, H_VALUE)),
  assert(reg_ax(x:X, H_VALUE)),
  assert(reg_ax(a:A, H_VALUE)),
  H1 is H + 1,
  assert(reg_h(H1)).

wam_inst(set_variable(AX)):-
  retract(reg_h(H)),
  H_VALUE = (ref, H),
  set(heap(H, H_VALUE)),
  assert(reg_ax(AX, H_VALUE)),
  H1 is H + 1,
  assert(reg_h(H1)).

wam_inst(set_value(AX)):-
  retract(reg_h(H)),
  reg_ax(AX, R_VALUE),
  set(heap(H, R_VALUE)),
  H1 is H + 1,
  assert(reg_h(H1)).

wam_inst(put_structure(F/A,AX)):-
  retract(reg_h(H)),
  H1 is H + 1,
  H_VALUE = (str, H1),
  set(heap(H, H_VALUE)),
  set(heap(H1, F/A)),
  assert(reg_ax(AX, H_VALUE)),
  H2 is H + 2,
  assert(reg_h(H2)).

wam_inst(call(Label)):-
  listing([reg_ax,reg_h,store,code_area]),
  retract(reg_p(_)),
  code_area(N,Label,FastCode),
  N1 is N + 1,
  assert(reg_p(N1)),
  !,wam_inst(FastCode).


%% WAM instructions (for program)
wam_inst(get_structure(F/A,AX)):-
  retract(reg_p(N)),
  deref(AX,ADDR_V),!,
  get_structure_case(ADDR_V,F/A),
  code_area(N,_,Code),
  N1 is N + 1,
  assert(reg_p(N1)),
  !,wam_inst(Code).

wam_inst(get_value(X,A)):-
  unify(X,A),
  retract(reg_p(N)),
  code_area(N,_,Code),
  N1 is N + 1,
  assert(reg_p(N1)),
  !,wam_inst(Code).


wam_inst(unify_variable(AX)):-
  unify_mode(read),!,
  retract(reg_s(S)),
  (retract(reg_ax(AX,_)) ; true),
  heap(S,H_VALUE),
  assert(reg_ax(AX,H_VALUE)),
  S1 is S + 1,
  assert(reg_s(S1)),

  retract(reg_p(N)),
  code_area(N,_,Code),
  N1 is N + 1,
  assert(reg_p(N1)),
  !,wam_inst(Code).

wam_inst(unify_variable(AX)):-
  unify_mode(write),!,
  retract(reg_h(H)),
  H_VALUE = (ref,H),
  set(heap(H,H_VALUE)),
  (retract(reg_ax(AX,_)) ; true),
  assert(reg_ax(AX,H_VALUE)),
  H1 is H + 1, assert(reg_h(H1)),

  retract(reg_p(N)),
  code_area(N,_,Code),
  N1 is N + 1,
  assert(reg_p(N1)),
  !,wam_inst(Code).

wam_inst(proceed). % do nothing.


% irregular pattern (just in case)
wam_inst(Other):-
  writeln(not_impremented_wam_inst(Other)).


get_structure_case((ref,ADDR),F/N):-
  retract(reg_h(H)),
  H1 is H + 1,
  set(heap(H,(str,H1))),
  set(heap(H1,F/N)),
  bind(ADDR,H),
  H2 is H + 2,
  assert(reg_h(H2)),
  (retract(unify_mode(_)) ; true),
  assert(unify_mode(write)).

get_structure_case((str,ADDR),F/N):-
  heap(ADDR,F/N),!,
  (retract(reg_s(_)) ; true),
  S is ADDR + 1,
  assert(reg_s(S)),
  (retract(unify_mode(_)) ; true),
  assert(unify_mode(read)).


% deref(レジスタIndex,HEAP上の値(タグ,値))
deref(A,ADDR_V):-
    reg_ax(A,VALUE),
    deref1(VALUE,ADDR_V).
deref1((str,ADDR),(str,ADDR)).
deref1((ref,ADDR),(ref,ADDR)):-
    heap(ADDR,(ref,ADDR)).
deref1((ref,X),ADDR_V):-
    heap(X,VALUE),
    deref1(VALUE,ADDR_V).
deref1(VALUE,_):-
    writeln(something_wrong_happen(VALUE)).


bind(ADDR1,ADDR2):-
    % checking UNBOUND REF or NOT.
    heap(ADDR1,(ref,ADDR1)),!,
    reset(heap(ADDR1,(ref,ADDR1))),
    set(heap(ADDR1,(ref,ADDR2))).

bind(ADDR1,ADDR2):-
    % checking UNBOUND REF or NOT.
    heap(ADDR2,(ref,ADDR2)),!,
    reset(heap(ADDR2,(ref,ADDR2))),
    set(heap(ADDR2,(ref,ADDR1))).

bind(X,Y):-
    writeln(something_wrong_happen(bind(X,Y))),
    fail.


:- dynamic pdl/1.
pop(pdl,X):-
    retract(pdl([X|Z])),
    assert(pdl(Z)).
push(pdl,X):-
    (retract(pdl(Z)) ; Z = []),
    assert(pdl([X|Z])).

% % wam slide の STORE[addr] 表現に合わせるための述語
% store(ADDR,VALUE):-heap(ADDR,VALUE).

%  unify(x:5,a:3):-writeln(called(unify(x:5,a:3),'---------------')).
unify(x:5,a:3):-
    reg_ax(x:5,V_X5),
    reg_ax(a:3,V_A3),
    push(pdl,V_X5),
    push(pdl,V_A3),
    unify_loop.

unify(_,_):- writeln(unify_failed),fail.

unify_loop:-
    pdl([]).
unify_loop:-
    pop(pdl,X_),pop(pdl,Y_),
    deref1(X_,XV),
    deref1(Y_,YV),
    unify_body(XV,YV),
    unify_loop.

unify_body((_,XADDR),(_,YADDR)):- XADDR = YADDR.
unify_body((ref,XADDR),(_,YADDR)):- bind(XADDR,YADDR).
unify_body((_,XADDR),(ref,YADDR)):- bind(YADDR,XADDR).
unify_body((str,X),(str,Y)):-
    store(X,F1/A1),
    store(Y,F2/A2),
    F1=F2,A1=A2,unify_push_pdl(X,Y,A1).
unify_push_pdl(_,_,0).
unify_push_pdl(X,Y,ArityCntDown):-
    Xplus is X + 1,
    Yplus is Y + 1,
    store(Xplus,X_Value),store(Yplus,Y_Value),
    push(pdl,X_Value),push(pdl,Y_Value),
    ArityCntDown2 is ArityCntDown - 1,
    unify_push_pdl(Xplus,Yplus,ArityCntDown2).




%%%% unify_bind_try(X,Y):-
%% binは、UNBUND REF でなければならないのか？(derefの先がUNBUNDでなければならない、
%% というのはそのとおりではないだろうか)


% queryは別途制作した（今後統合する）
% compile_query(p(Z,h(Z,W),f(W)),Query):-
%    Query = [
%	put_variable(x:4,a:1),
%	put_structure(h/2,a:2),
%	set_value(x:4),
%	set_variable(x:5),
%	put_structure(f/1,a:3),
%	set_value(x:5),
%	call(p/3)
%    ].

compile_code(T,L):-
    assert(count(0)),
    terms_top(T,_,ReOrdered),
    reg_assign(ReOrdered,RetL,[],_),!,
    var_assign(RetL,L,[],_).

terms_top(X,_,ReOrdered2):-
    compound(X),!,
    functor(X,N,_),X =.. [N|S],
    sub_terms_top(S,ZZ),
    pickup_args(ZZ,Args,Subs),
    append(Args,Subs,ReOrdered),
    append(ReOrdered,[[proceed]],ReOrdered2).

pickup_args([],[],[]).
pickup_args([arg_and_sub(A,S)|Z],Args,Subs):-
    pickup_args(Z,A_,S_),
    append(A,A_,Args),
    append(S,S_,Subs).


sub_terms_top([],[]).
sub_terms_top([X|Y],ZZZ):-
    terms_top_down(X,_,ZZ),
    sub_terms_top(Y,ZZ_),
    append(ZZ,ZZ_,ZZZ).

terms_top_down(X,unify_var(N/A)=_,ZZ):-
    compound(X),!,
    functor(X,N,A),X =.. [N|S],
    sub_terms(S,S_,Ret),
    counter(C),
    ZZ = [arg_and_sub([[get_structure(N/A,C)|S_]],Ret)].

terms_top_down(X,unify_var(X),ZZ):-
    var(X),!,
    counter(C),
    ZZ = [arg_and_sub([[unify_var(X,_,C)]],[])].

terms_top_down(X,unify_var(X/0)=Tmp,ZZ):-
    atom(X),!,
    ZZ = [arg_and_sub([[get_structure(X/0)=Tmp]],[])].


%% Frat fomat transform main part
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


%% register assignment main part (with reordering register number)
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
reg_match(get_structure(X,A),(get_structure(X),a:A),VL,VL).
reg_match(get_structure(X)=V,(get_structure(X),x:C),VL,VL):-　var(V),!,counter(C),V = C.
reg_match(get_structure(X)=V,(get_structure(X),x:V),VL,VL).
reg_match(unify_var(X,V,A),(unify_var(X),V,a:A),VL,VL).
reg_match(unify_var(X)=V,(unify_var(X),x:C),VL,VL):-　var(V),!,counter(C),V = C.
reg_match(unify_var(X)=V,(unify_var(X),V),VL,VL).
reg_match(X,X,VL,VL).


%% varuable assignment main part (firstry, all instaction command will build. and then adjust varuable assignment process.) 
%% 変数割り付け処理本体(全ての命令列が出来上がってから、改めて変数処理をWAM命令実行順に従って変換する)
var_assign([],[],VL,VL).
var_assign([X|Y],[A|B],VL,VL__):-
    var_assign(X,A,VL,VL_),
    var_assign(Y,B,VL_,VL__).

% if the valuable has already registerd, use 'set_value' otherwise use 'set_variable'
% 既に変数がVL登録されている場合は、set_value そうでない場合は、 set_variable とする
var_assign((unify_var(V),x:Index,a:A),get_value(x:Index,a:A),VL,VL):-
    find_var(V,VL,Index).
var_assign((unify_var(V),x:Index,a:A),get_variable(x:Index,a:A),VL,VL_):-
    VL_ = [vpair(Index,V)|VL].
var_assign((unify_var(V),x:Index),unify_value(x:Index),VL,VL):-
    find_var(V,VL,Index).
var_assign((unify_var(V),x:Index),unify_variable(x:Index),VL,VL_):-
    VL_ = [vpair(Index,V)|VL].
% assignment for structure should be register with no condition.
% 構造体に対する参照系変数は、無条件で、VLに登録する
var_assign((get_structure(X),x:Index),get_structure(X,x:Index),VL,[vpair(Index,X)|VL]).
var_assign((get_structure(X),a:Index),get_structure(X,a:Index),VL,[vpair(Index,X)|VL]).
var_assign(X,X,VL,VL).

% find_var : cheking variable has already assigned.
%            既に変数が割り付けられていないか確認する処理
find_var(Var,[vpair(Index,V)|_],Index):-
    Var == V.
find_var(Var,[_|L],Index):-
    find_var(Var,L,Index).
find_var(_,[],_):-
    false.


unit_test(Tag:CALL,EXPECTED):-
    CALL,!,
    (CALL = EXPECTED, t_msg(success,Tag) ; t_msg(fail,Tag)).
unit_test(Tag:CALL,_):-
    writeln('exection error(test failed)':CALL:Tag).

t_msg(success,Tag):-
    nl,writeln('test passed':Tag).
t_msg(fail,Tag):-
    nl,writeln('test failed':Tag).


%%?- g(p(f(X),h(Y,f(a)),Y),L),write(L).
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

% q(p(Z,h(Z,W),f(W))
% heap(0,  (ref, 8)).
% heap(1,  (str, 2)).
% heap(2, h/2).
% heap(3,  (ref, 0)).
% heap(4,  (ref, 11)).
% heap(5,  (str, 6)).
% heap(6, f/1).
% heap(7,  (ref, 4)).
% heap(8,  (str, 9)).
% heap(9, f/1).
% heap(10,  (ref, 10)).
% heap(11,  (str, 12)).
% heap(12, f/1).
% heap(13,  (ref, 14)).
% heap(14,  (str, 15)).
% heap(15, a/0).
% W=f(a)



% wam(code(p/3,
% p(f(X),h(Y,f(a)),Y)
% [get_structure(f/1,a:1),
% unify_variable(x:4),
% get_structure(h/2,a:2),
% unify_variable(x:5),
% unify_variable(x:6),
% get_value(x:5,a:3),
% get_structure(f/1,x:6),
% unify_variable(x:7),
% get_structure(a/0,x:7
% )
