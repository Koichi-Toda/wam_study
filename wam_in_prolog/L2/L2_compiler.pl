:- use_module(l2_query_compiler, [compile_query/2]).
% L1 prolog WAM compiler
% ?- prolog(p(f(X),h(Y,f(a)),Y),p(Z,h(Z,W),f(W))).
% ?- prolog_input_code([])
% ?- prolog_query
% <examples>
% ?- prolog2([(p(X,Y) :- q(X,Z),r(Z,Y)),q(a,b),r(c,d)],(p(X,d),q(Y,b))).
% ?- prolog2([(p(f(X),h(Y,f(a)),Y) :- q(X,Z),r(Z,Y)),q(a,b),r(c,d)],(p(X,d),q(Y,b))).
% ?- prolog2([(p(f(X),Y) :- q(X,Z),r(Z,Y)),q(a,b),r(c,d)],(p(X,d),q(Y,b))).
%
% ?- prolog2([(p(X,Y) :- q(X,Z),r(Z,Y)),q(a,b),r(b,d)],(p(A,B))).
% ?- prolog2([p(f(X),h(Y,f(a)),Y)],(p(Z,h(Z,W),f(W)))). 　　　　　　%% 実行結果が OK であることを確認した！
% ?- prolog([(a:-b,c),b,c],a).
% ?- prolog(p(f(a),f(b)),p(Z,W)).
% ?- prolog(p(f(a),f(b)),(p(Z,W),p(A,B))).
%
%
% ?- prolog(p(X,X),(p(a,A),p(b,B))).
% TODO: queryが単一か連言か？をどう判別できるのか？（prologの標準機能でなにかできるのか？）
:- dynamic count/1.

prolog_input_code(L):-
    read(X),
     (
       X=end,read_prolog_code(L);
       append(L,[X],L2),prolog_input_code(L2)
     ).
% TODO: 単一 cluse しかストアできないので、改善する（L2なら、単一ループでいいのではないか？）
read_prolog_code(Code):-
    compile_code(Code,WAM_Code),
    functor(Code,F,A),
    store_code(F/A,WAM_Code).

prolog_query:-
    read(Query),
    compile_query(Query,WAM_Query),
    store_query(WAM_Query),
    wam_vm.

% prolog2(CodeL,Query):-
%    compile_codes(CodeL,WAM_CodeL),writeln(code(CodeL)),writeln(wamcode(WAM_CodeL)),
%    !,compile_query(Query,WAM_Query),writeln(wamquery(Query,WAM_Query)),
%    !,wam2((CodeL,WAM_CodeL),WAM_Query),
%    listing([code_area,reg_ax,reg_h,reg_p,store]).

% for debugging
prolog2(CodeL,Query):-
     compile_codes(CodeL,WAM_CodeL),writeln(code(CodeL)),writeln(wamcode(WAM_CodeL)),
     !,compile_query(Query,WAM_Query),writeln(wamquery(Query,WAM_Query)).


prolog(Code,Query):-
    compile_code(Code,WAM_Code),writeln(wamcode(WAM_Code)),
    compile_query(Query,WAM_Query),writeln(wamquery(WAM_Query)),
    functor(Code,F,A),
    wam((F/A,WAM_Code),WAM_Query),
    listing([code_area,reg_ax,reg_h,reg_p,store]).

:- dynamic code_area/3, store/2.
:- dynamic reg_h/1, reg_s/1, reg_p/1, reg_cp/1, reg_e/1.
:- dynamic reg_ax/2.
:- dynamic unify_mode/1.
:- dynamic y_cnt/1.

% HEAP is part of main memory (all memory accsess can be use store/2 ).
set(heap(ADDRESS,VALUE)):- assert(store(ADDRESS,VALUE)).
reset(heap(ADDRESS,VALUE)):- retract(store(ADDRESS,VALUE)).
heap(ADDRESS,VALUE):- store(ADDRESS,VALUE).

% STACK is also part of main memory. STACK address is start from 10000.
stack(ADDRESS,VALUE):- store(ADDRESS,VALUE).

wam2((CodeL,WAM_CodeL),WAM_Query):-
    assert(reg_h(0)),
    assert(reg_p(0)),
    assert(reg_cp(0)),
    assert(reg_e(10000)),
    store_codes(CodeL,WAM_CodeL),
    store_query(WAM_Query),
    wam_vm.

wam((F/A,WAM_Code),WAM_Query):-
    assert(reg_h(0)),
    assert(reg_p(0)),
    assert(reg_cp(0)),
    assert(reg_e(10000)),
    store_code(F/A,WAM_Code),
    store_query(WAM_Query),
    wam_vm.

% store wam code into CODE_AREA
store_codes([],[]).

store_codes([Head:-_Body|CodeL],[WAM_Code|WAM_CodeL]):-
    functor(Head,F,A),
    writeln(store_code(F/A,WAM_Code)),
    store_code(F/A,WAM_Code),
    store_codes(CodeL,WAM_CodeL).

store_codes([Code|CodeL],[WAM_Code|WAM_CodeL]):-
    functor(Code,F,A),
    writeln(store_code(F/A,WAM_Code)),
    store_code(F/A,WAM_Code),
    store_codes(CodeL,WAM_CodeL).

store_code(Label,[X|Z]):-
    increment(reg_p(N)),
    writeln(reg_p(N)),
    assert(code_area(N,Label,X)),
    store_code(Z).
store_code([]).
store_code([X|Z]):-
    increment(reg_p(N)),
    assert(code_area(N,null,X)),
    store_code(Z).

% store wam query into CODE_AREA
%%
% store_querys(QL):-
%    reg_p(N),
%    store_querys_(QL),
%    update(reg_p(N)).
%
% store_querys_([]).
% store_querys_([Q|QL]):-
%     store_code(Q),
%     store_querys_(QL).

store_query(X):-
    reg_p(N),
    store_code(X),
    update(reg_p(N)).

% looping (when register P is out of code address should be stop)
wam_vm :- reg_p(N),not(code_area(N,_,_)) ; wam_exec, wam_vm.

wam_exec:-
    increment(reg_p(N)),
    code_area(N,_,Instraction),
    !,wam_inst(Instraction).

increment(reg_p(N)):- retract(reg_p(N)), N1 is N + 1, assert(reg_p(N1)).
increment(reg_h(N)):- retract(reg_h(N)), N1 is N + 1, assert(reg_h(N1)).
increment(y_cnt(N)):- retract(y_cnt(N)), N1 is N + 1, assert(y_cnt(N1)).
update(reg_p(N)):- retract(reg_p(_)), assert(reg_p(N)).
update(reg_cp(N)):- retract(reg_cp(_)), assert(reg_cp(N)).
update(reg_e(N)):- retract(reg_e(_)), assert(reg_e(N)).
update(reg_ax(AX,VALUE)):- (retract(reg_ax(AX,_));true), assert(reg_ax(AX,VALUE)).
update(reg_s(N)):- (retract(reg_s(_)); true), assert(reg_s(N)).
update(y_cnt(N)):- (retract(y_cnt(_)); true), assert(y_cnt(N)).
update(unify_mode(M)):- (retract(unify_mode(_)) ; true), assert(unify_mode(M)).
update(stack(ADDRESS,VALUE)):- (retract(store(ADDRESS,_)); true), assert(store(ADDRESS,VALUE)).


%% WAM instuctions (for query)
wam_inst(put_variable(x:X,a:A)):-
    increment(reg_h(H)),
    H_VALUE = (ref, H),
    set(heap(H, H_VALUE)),
    update(reg_ax(x:X, H_VALUE)),
    update(reg_ax(a:A, H_VALUE)).

wam_inst(put_value(V,AX)):-
    update(reg_ax(AX,V)).


wam_inst(get_variable(V,AX)):-
    update(reg_ax(V,AX)).

wam_inst(set_variable(AX)):-
    increment(reg_h(H)),
    H_VALUE = (ref, H),
    set(heap(H, H_VALUE)),
    update(reg_ax(AX, H_VALUE)).

wam_inst(set_value(AX)):-
    reg_ax(AX, R_VALUE),
    increment(reg_h(H)),
    set(heap(H, R_VALUE)).

wam_inst(put_structure(F/A,AX)):-
    increment(reg_h(H)),
    increment(reg_h(H1)),
    H_VALUE = (str, H1),
    set(heap(H, H_VALUE)),
    set(heap(H1, F/A)),
    update(reg_ax(AX, H_VALUE)).

% 「CP ← P + instruction_size(P)」について、この環境の場合 CP ← P + 1 で足りると判断した
% そして、callが呼び出されるときには、既にカウントアップ(+1)しているので、Pの値をCPに単に代入することとした
wam_inst(call(Label)):-
    reg_p(P),
    update(reg_cp(P)), % reg_p(P)は、すでに P+1されているので、そのままセットすればよいと考える
    code_area(N,Label,FirstInst),
    N1 is N + 1,
    update(reg_p(N1)),writeln(reg_cp(P)),
    !,wam_inst(FirstInst).

wam_inst(allocate(N)):-
    reg_e(E),
    reg_cp(CP),
    E2 is E+2, stack(E2,StackE2), NewE is E + StackE2 + 3,
    NewE1 is NewE + 1, update(stack(NewE1,CP)),
    NewE2 is NewE + 2, update(stack(NewE2,N)),
    update(reg_e(NewE)).

wam_inst(deallocate):-
    reg_e(E),
    E1 is E+1, stack(E1,NewP),
    update(reg_p(NewP)),
    stack(E,NewE),
    update(reg_e(NewE)).



%% WAM instructions (for program)
wam_inst(get_structure(F/A,AX)):-
    deref(AX,ADDR_V),!,
    get_structure_case(ADDR_V,F/A).

wam_inst(get_value(X,A)):-
    unify(X,A).

wam_inst(unify_variable(AX)):-
    unify_mode(read),!,
    reg_s(S),
    heap(S,H_VALUE),
    update(reg_ax(AX,H_VALUE)),
    S1 is S + 1,
    update(reg_s(S1)).

wam_inst(unify_variable(AX)):-
    unify_mode(write),!,
    increment(reg_h(H)),
    H_VALUE = (ref,H),
    set(heap(H,H_VALUE)),
    update(reg_ax(AX,H_VALUE)).

% proceed (set P <- CP)
wam_inst(proceed):-
     reg_cp(N),
     update(reg_p(N)).

% catch irregular pattern
wam_inst(Other):-
    writeln(not_impremented_wam_inst(Other)),
    abort.


get_structure_case((ref,ADDR),F/N):-
    increment(reg_h(H)),
    increment(reg_h(H1)),
    set(heap(H,(str,H1))),
    set(heap(H1,F/N)),
    bind(ADDR,H),
    update(unify_mode(write)).

get_structure_case((str,ADDR),F/N):-
    heap(ADDR,F/N),!,
    S is ADDR + 1,
    update(reg_s(S)),
    update(unify_mode(read)).

% deref(A :register index, ADDR_V :value on HEAP)
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

unify(R1,R2):-
    reg_ax(R1,V_R1),
    reg_ax(R2,V_R2),
    push(pdl,V_R1),
    push(pdl,V_R2),
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


compile_codes([],[]).
compile_codes([T|TL],[L|LL]):-
    compile_code(T,L),
    compile_codes(TL,LL).


compile_code(Head:-Body,L2):-
    assert(count(0)),
    assert(y_cnt(1)),

    % parmanent 変数のリストアップ
    vlist(Head:-Body,VLIST),
    find_parmanent(VLIST,ParmList), writeln(parm_list(ParmList)),

    terms_top(ParmList,Head,_,ReOrdered),
    reg_assign(ParmList,ReOrdered,RetL,[],LLL),!,writeln(head(reg_assign(ReOrdered,RetL,[],LLL))),
    var_assign(RetL,L,[],LLL2),writeln(head(var_assign(RetL,L,[],LLL2))),

    Vin = LLL2,
    compile_body(ParmList,Vin,_Vout,Body,WAM_Body),
    append(L,WAM_Body,L2_),
    append(L2_,[proceed],L2).

compile_code(T,L):-
    set_counter(0),
    terms_top([],T,_,ReOrdered),
    reg_assign([],ReOrdered,RetL,[],_),!,
    var_assign(RetL,L_,[],_),
    append(L_,[proceed],L).

% terms_top(Head:-Body,_,ReOrdered):-
%    compound(Head),!,
%    functor(Head,N,_),Head =.. [N|S],
%    sub_terms_top(S,ZZ),
%    pickup_args(ZZ,Args,Subs),
%    append(Args,Subs,ReOrdered),writeln(wam_head_(ReOrdered)),
%    compile_body(Body,_BL),
%    compile_query(Body,WAM_Query),writeln(wam_body_(WAM_Query)).

terms_top(ParmList,X,_,ReOrdered):-
    compound(X),!,
    functor(X,N,_),X =.. [N|S],
    sub_terms_top(ParmList,S,ZZ),
    pickup_args(ZZ,Args,Subs),
    append(Args,Subs,ReOrdered).

compile_body(ParmList,Vin,Vout,(A,B),L3):-
  compile_body(ParmList,Vin,Vout_,A,L),
  retract(cnt(_)),assert(cnt(0)),
  compile_body(ParmList,Vout_,Vout,B,L2),
  append(L,L2,L3).

compile_body(ParmList,Vin,Vout,RootPropaty,L):-
  functor(RootPropaty,Fname,Arity), RootPropaty =.. [Fname|S],
  body_args(S,S_OUT),
  body_deep_trans(ParmList,Vin,S_OUT,S_OUT_D,VL),
  !,body_xreg_assign(ParmList,S_OUT_D,S_OUT_D2,VL,_),!,
  body_var_assign(S_OUT_D2,S_OUT_D3,VL,_),
  Vout = VL,
  append(S_OUT_D3,[call(Fname/Arity)],L).


body_args([],[]).
body_args([X|Z],[X2|Z2]):-
  body_args_(X,X2),
  body_args(Z,Z2).
body_args_(X,(X,a:C)):-
  reg_cnt(C).


body_deep_trans(_ParmList,Vin,[],[],Vin).
body_deep_trans(ParmList,Vin,[X|Z],[X2|Z2],VL):-
  body_deep_trans_(ParmList,Vin,X,X2,Vin_),
  body_deep_trans(ParmList,Vin_,Z,Z2,VL).

body_deep_trans_(ParmList,Vin,(V,Arg),put_value(REG:Index,Arg),Vout):-
  body_find_var(V,Vin,Index),
  Vout = Vin,writeln(chekichek____(V,ParmList)),
  (vmember(V,ParmList), writeln(incincincre_b1_reflaction(Index)), REG=y ; REG=x).
body_deep_trans_(ParmList,Vin,(V,Arg),put_variable(REG:C,Arg),[vpair(C,V)|Vin]):-
  var(V),!,writeln(chekichek(V,vin(Vin),ParmList)),
  (vmember(V,ParmList),increment(y_cnt(C)), writeln(incincincre_b1(C)), REG=y ; counter(C), REG=x).
body_deep_trans_(ParmList,Vin,(X,Arg),Z,[]):- %%% TODO: ここが [] なのが、意味が分かっていない、Vinに置き換える必要があるとおもいいつつ。。。
　writeln(body_deep_trans(Vin)), %%% INSPECT_CODE この辺は、まだちゃんと実装されていないのだろうけど・・・ちょっと後回しにする
  compound(X),!,
  functor(X,Fname,Arity), X =.. [Fname|S],
  body_sub_terms(ParmList,S,S_,Reorder),
  Z = [reorder(Reorder,[put_structure(Fname/Arity)=Arg|S_])].
body_deep_trans_(_ParmList,Vin,(X,Arg),(put_structure(X/0,Arg),Vin)):-
  atom(X),!.


body_sub_terms(_ParmList,[],[],[]).
body_sub_terms(ParmList,[X|Y],[A|B],Z):-
  body_terms(ParmList,X,A,X_),
  body_sub_terms(ParmList,Y,B,Y_),
  append(X_,Y_,Z).


%% body フラット化処理本体
body_terms(ParmList,X,assign_var(N/A)=TmpV,Z):-
  compound(X),!,
  functor(X,N,A),X =.. [N|S],
  body_sub_terms(ParmList,S,S_,ReOrder),
  Z = [reorder(ReOrder,[put_structure(N/A)=TmpV|S_])].
body_terms(_ParmList,X,assign_var(X),[]):-
  var(X),!.

%% 引数レジスタのために一枚構造がはさまった
body_xreg_assign(_ParmList,[],[],B,B).
body_xreg_assign(ParmList,[X|Z],Z3,V,V3):-
  body_reg_assign(ParmList,X,X2,V,V2),
  body_xreg_assign(ParmList,Z,Z2,V2,V3),
  append(X2,Z2,Z3).

body_reg_assign(_ParmList,put_variable(A,B),[put_variable(A,B)],V,V).
body_reg_assign(_ParmList,put_value(A,B),[put_value(A,B)],V,V).
body_reg_assign(_ParmList,[],[],V,V).
body_reg_assign(ParmList,[reorder(X1,X2)|Y],Z,V,V3):-
   body_assign_register(ParmList,X2,A2,V,V1),
   body_reg_assign(ParmList,X1,A1,V1,V2),append(A1,A2,A),
   body_reg_assign(ParmList,Y,B,V2,V3),append(A,B,Z).


body_assign_register(_ParmList,[],[],VL,VL).
body_assign_register(ParmList,[X|Y],[A|B],VL,Vnew2):-
  body_reg_match(ParmList,X,A,VL,Vnew),
  body_assign_register(ParmList,Y,B,Vnew,Vnew2).


body_reg_match(_ParmList,put_structure(X),(put_structure(X),x:C),VL,VL):-　reg_cnt(C).
body_reg_match(_ParmList,assign_var(X),(assign_var(X),x:Index),VL,VL):-　find_var(X,VL,Index).
body_reg_match(ParmList,assign_var(X),(assign_var(X),REG:C),VL,[vpair(C,X)|VL]):-
  (vmember(X,ParmList), increment(y_cnt(C)), writeln(incincincre(C)), REG=y; reg_cnt(C), REG=x).
body_reg_match(_ParmList,put_structure(X)=a:Index,(put_structure(X),a:Index),VL,VL).
body_reg_match(_ParmList,put_structure(X)=V,(put_structure(X),x:C),VL,VL):-　var(V),!,reg_cnt(C),V = C.
body_reg_match(_ParmList,put_structure(X)=V,(put_structure(X),x:V),VL,VL).
body_reg_match(_ParmList,assign_var(X)=V,(assign_var(X),x:C),VL,VL):-　var(V),!,reg_cnt(C),V = C.
body_reg_match(_ParmList,assign_var(X)=V,(assign_var(X),V),VL,VL).


body_var_assign([],[],VL,VL).
body_var_assign([X|Y],[A|B],VL,VL__):-
  body_var_assign(X,A,VL,VL_),
  body_var_assign(Y,B,VL_,VL__).

body_var_assign((assign_var(V),_),set_value(x:Index),VL,VL):-
  body_find_var(V,VL,Index).
body_var_assign((assign_var(V),x:Index),set_variable(x:Index),VL,VL_):-
  VL_ = [vpair(Index,V)|VL].

body_var_assign((put_structure(X),x:Index),put_structure(X,x:Index),VL,[vpair(Index,X)|VL]).
body_var_assign((put_structure(X),a:Index),put_structure(X,a:Index),VL,[vpair(Index,X)|VL]).
body_var_assign((put_variable(A,B)),(put_variable(A,B)),VL,VL).
body_var_assign((put_value(A,B)),(put_value(A,B)),VL,VL).



body_find_var(Var,[vpair(Index,V)|_],Index):-
    Var == V.
body_find_var(Var,[_|L],Index):-
    find_var(Var,L,Index).
body_find_var(_,[],_):-
    false.

vmember(X,[Y|_]):- X == Y.
vmember(X,[_|Y]):- vmember(X,Y).


% register counter
reg_cnt(X):-
  (retract(cnt(N)) ; N is 0),
  X is N + 1,
  assert(cnt(X)).



%% プログラム内変数のリストアップ
%% SWI prolog の term_variables を使用して変数をピックアップしている
vlist(Head:-(FirstBody,RestBody),[L|L2]):-
    term_variables((Head,FirstBody),L),
    vlist_body(RestBody,L2).
vlist(_Head:-_SingleBody,[]).
vlist_body((A,B),[AL|BL]):-
    term_variables(A,AL),
    vlist_body(B,BL).
vlist_body(LastBody,[L]):-
    term_variables(LastBody,L).

%% parmanent 変数のリストアップ
%% 入力 List は (Head + 最初のBody のユニークな変数リスト), (それ以降のBodyのユニークな変数リスト)... の多重リストである
%%
%% これらを比較して、変数が重複する場合、2つ以上の Body に含まれる変数(= parmanent 変数)と判別できる。
%% 以下では List を flatten して、変数の重複を発見することで、この変数を parmanent 変数と判断するようにしている。
find_parmanent(List,ParmList):-
  flatten(List,Rest_),
  find_dup(Rest_,ParmList).

find_dup([_|[]],[]).
find_dup([X|Z],R):-
  fdup(X,Z,R1),
  find_dup(Z,R2),
  append(R1,R2,R).

fdup(_,[],[]).
fdup(V,[W|_],[V]):-
   V == W.
fdup(V,[_|Z],R):-
  fdup(V,Z,R).




pickup_args([],[],[]).
pickup_args([arg_and_sub(A,S)|Z],Args,Subs):-
    pickup_args(Z,A_,S_),
    append(A,A_,Args),
    append(S,S_,Subs).


sub_terms_top(_ParmList,[],[]).
sub_terms_top(ParmList,[X|Y],ZZZ):-
    terms_top_down(ParmList,X,_,ZZ),
    sub_terms_top(ParmList,Y,ZZ_),
    append(ZZ,ZZ_,ZZZ).

% terms_top_down は、述語の引数部分に対応すると理解、
% このため、引数レジスタを指定するよう変換されると理解
terms_top_down(ParmList,X,unify_var(N/A)=_,ZZ):-
    compound(X),!,
    functor(X,N,A),X =.. [N|S],
    sub_terms(ParmList,S,S_,Ret),
    counter(C),
    ZZ = [arg_and_sub([[get_structure(N/A,C)|S_]],Ret)].

terms_top_down(_ParmList,X,unify_var(X),ZZ):-
    var(X),!,counter(AC),
    ZZ = [arg_and_sub([[unify_var(X,_,AC)]],[])].

terms_top_down(_ParmList,X,unify_var(X/0)=_,ZZ):-
    atom(X),!,
    counter(C),
    ZZ = [arg_and_sub([[get_structure(X/0,C)]],[])].


%% Frat fomat transform main part
terms(_ParmList,X,unify_var(N/A)=TmpV,Z):-
    compound(X),!,
    functor(X,N,A),X =.. [N|S],
    sub_terms(S,S_,Ret),
    Z = [[get_structure(N/A)=TmpV|S_]|Ret].

terms(_ParmList,X,unify_var(X),[]):-
    var(X),!.

terms(_ParmList,X,unify_var(X/0)=Tmp,[[get_structure(X/0)=Tmp]]):-
    atom(X),!.

sub_terms(_ParmList,[],[],[]).
sub_terms(ParmList,[X|Y],[A|B],Z):-
    terms(ParmList,X,A,X_),
    sub_terms(ParmList,Y,B,Y_),
    append(X_,Y_,Z).

counter(X):-
    retract(count(N)),
    X is N + 1,
    assert(count(X)).
set_counter(X):-
    (retract(count(_)) ; true),
    assert(count(X)).

%% register assignment main part (with reordering register number)
reg_assign(_ParmList,[],[],V,V).
reg_assign(ParmList,[X|Y],Z,V,V2):-
    assign_register(ParmList,X,A,V,V1),
    reg_assign(ParmList,Y,B,V1,V2),append(A,B,Z).

assign_register(_ParmList,[],[],VL,VL).
assign_register(ParmList,[X|Y],[A|B],VL,Vnew2):-
    reg_match(ParmList,X,A,VL,Vnew),
    assign_register(ParmList,Y,B,Vnew,Vnew2).

reg_match(_ParmList,get_structure(X),(get_structure(X),x:C),VL,VL):-　counter(C).
reg_match(_ParmList,unify_var(X),(unify_var(X),x:Index),VL,VL):-　find_var(X,VL,Index).
reg_match(ParmList,unify_var(X),(unify_var(X),x:C),VL,[vpair(C,X)|VL]):-
  (vmember(X,ParmList),increment(y_cnt(C)), writeln(incincincre3(C)); counter(C)).
reg_match(_ParmList,get_structure(X,A),(get_structure(X),a:A),VL,VL).
reg_match(_ParmList,get_structure(X)=V,(get_structure(X),x:C),VL,VL):-　var(V),!,counter(C),V = C.
reg_match(_ParmList,get_structure(X)=V,(get_structure(X),x:V),VL,VL).

% さらに以下の一行を追加
reg_match(_ParmList,unify_var(X,x:Index,A),(unify_var(X),x:Index,a:A),VL,VL):- find_var(X,VL,Index).
% 以下の一行を追加したが、本当にこれでいいのか？半信半疑、まあ、結果は良好なり。。。
reg_match(ParmList,unify_var(X,V,A),(unify_var(X),REG:C,a:A),VL,VL):-
  var(V),!,
  (vmember(X,ParmList),increment(y_cnt(C)), writeln(incincincre4(C)), REG=y; counter(C), REG=x), writeln(pippin(X,ParmList,C)).

reg_match(_ParmList,unify_var(X,V,A),(unify_var(X),V,a:A),VL,VL).
reg_match(_ParmList,unify_var(X)=V,(unify_var(X),x:C),VL,VL):-　var(V),!,counter(C),V = C.
reg_match(_ParmList,unify_var(X)=V,(unify_var(X),V),VL,VL).
reg_match(_ParmList,X,X,VL,VL).


%% varuable assignment main part (firstry, all instaction command will build. and then adjust varuable assignment process.)
var_assign([],[],VL,VL).
var_assign([X|Y],[A|B],VL,VL__):-
    var_assign(X,A,VL,VL_),
    var_assign(Y,B,VL_,VL__).

% if the valuable has already registerd, use 'set_value' otherwise use 'set_variable'
var_assign((unify_var(V),x:Index,a:A),get_value(x:Index,a:A),VL,VL):-
    find_var(V,VL,Index).
var_assign((unify_var(V),XY:Index,a:A),get_variable(XY:Index,a:A),VL,VL_):-
    VL_ = [vpair(Index,V)|VL].
% var_assign((unify_var(V),y:Index,a:A),get_variable(y:Index,a:A),VL,VL_):-
%    VL_ = [vpair(Index,V)|VL].
var_assign((unify_var(V),x:Index),unify_value(x:Index),VL,VL):-
    find_var(V,VL,Index).
var_assign((unify_var(V),x:Index),unify_variable(x:Index),VL,VL_):-
    VL_ = [vpair(Index,V)|VL].

% assignment for structure should be register with no condition.
var_assign((get_structure(X),x:Index),get_structure(X,x:Index),VL,[vpair(Index,X)|VL]).
var_assign((get_structure(X),a:Index),get_structure(X,a:Index),VL,[vpair(Index,X)|VL]).
var_assign(X,X,VL,VL).

% find_var : cheking variable has already assigned.
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
