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


%% レジスタ割り付け処理本体(順序入れ替え構造を踏まえたレジスタ付番を行う)
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


%% 変数割り付け処理本体(全ての命令列が出来上がってから、改めて変数処理をWAM命令実行順に従って変換する)
var_assign([],[],VL,VL).
var_assign([X|Y],[A|B],VL,VL__):-
  var_assign(X,A,VL,VL_),
  var_assign(Y,B,VL_,VL__).
% 既に変数がVL登録されている場合は、set_value そうでない場合は、 set_variable とする
var_assign((assign_var(V),_),set_value(x:Index),VL,VL):-
  find_var(V,VL,Index).
var_assign((assign_var(V),x:Index),set_variable(x:Index),VL,VL_):-
  VL_ = [vpair(Index,V)|VL].
% 構造体に対する参照系変数は、無条件で、VLに登録する
var_assign((put_structure(X),x:Index),put_structure(X,x:Index),VL,[vpair(Index,X)|VL]).
var_assign((put_structure(X),a:Index),put_structure(X,a:Index),VL,[vpair(Index,X)|VL]).
var_assign((put_variable(A,B)),(put_variable(A,B)),VL,VL).



% find_var :既に変数が割り付けられていないか確認する処理
find_var(Var,[vpair(Index,V)|_],Index):-
    Var == V.
find_var(Var,[_|L],Index):-
    find_var(Var,L,Index).
find_var(_,[],_):-
    false.

% レジスタ番号カウンタ
reg_cnt(X):-
  (retract(cnt(N)) ; N is 0),
  X is N + 1,
  assert(cnt(X)).




% 順序入れ替え構造をそのまま、フックとして利用すればよいと考えたところ、うまくいった（reorderはネーミングを変えた方がいいよなー）
% [reorder(
%   [reorder([],[ref_var(h/2)=h(_5362,_5364)]),reorder([],[ref_var(f/1)=f(_5364)])],
%   [ref_var(p/3)=p(_5362,ref_var(h/2),ref_var(f/1))]
% )]


%% 一応できたが、最後は力ずくみたいな感じになってしまっている（反省）
%% 難しさを感じたのは、変数のセットをどっちでやるか？(set_variable/set_value)は、命令コマンドの列が出来上がった後に、改めて最初から舐め直すような操作をしないと、やりようが無いと感じたこと。
%% 一方で、レジスタ設定の順序を考えると、それはそれで、別個の舐め方をしないといけないと感じたことである(reorder構造に着目して切り抜けた)。
%% ・・・処理の都合上 term単位で順番入れ替えをしてしまったが、レジスタ設定の順序は、入れ替え前の順でやる必要があったが、reorder構造に着目すると、それが辿れるのである。
%% ・・・ならば、term単位で入れ替えする段階でできないのか？となるが、この時点では、termのArgument部分は展開していないので、レジスタ番号を付番できないのである。
%% ・・・reorderをする際に、Argument展開をする前の段階、つまりより大きなterm単位で reorder したことが、ボトムアップ化を破綻せずできた勝因なので、Argument展開は先にしたくないのである。
%% まあ、しかし、初めて機械的な操作と言える方法で合成できたし、ほぼ、そうなる理由についても説明できると感じている点はよかった。（前進はしている）
% [
%   put_structure(h/2,x:3),
%   set_variable(x:2),
%   set_variable(x:5),
%   put_structure(f/1,x:4),
%   set_value(x:5),
%   put_structure(p/3,x:1),
%   set_value(x:2),
%   set_value(x:3),
%   set_value(x:4)
% ]

% 難しかった点のまとめ
% ① Heapに格納することを考えると、ボトムアップに命令を構築する必要があること
% ② 逆に、WAM命令実行時のことを考えると、レジスタの割り付け順は、トップダウンに、p/3が x:1 に割当たり、以下トップダウンに参照可能な順所にすることが望ましいこと
% ③ 上記条件をみたしつつ、出来上がった命令列の実行順番上、最初に変数割り付けしたものと、その後に同じ変数を割り付けするものの順番が正しい順になっていること
% この３つの条件を同時に満たすことは、想像以上に難しかった。（ある観点ではボトムアップに、別の観点ではトップダウンに、さらにもう一つの観点では実行順に、調整する必要があった）
% ・最初は、これらを兼ね備えた１つのコードを作り上げようとしたが、それが「不可能」であることを悟り、処理を分割したことが勝因となった。

% TODO: ユニットテストのような仕組みがあってもよいと思った（たぶん簡単に作れるし）：構文のバリエーションがあった方がテストになるだろう
