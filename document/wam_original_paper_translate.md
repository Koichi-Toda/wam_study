## AN ABSTRACT PROLOG INSTRUCTION SET
### PROLOG抽象化命令セット

  David H D Warren  
  Artificial Intelligence Center  
  SRI International  
  31 August 1983  
:
### 1. はじめに
本レポートでは、PROLOG抽象化命令セットと、それを解釈実行する抽象マシンの実装について解説する。

今回提案するPROLOG抽象化命令セットは、ソフトウェア、ファームウェア、あるいはハードウェアにおける実装上好適なものと考える。  
そこで、本レポートではエンコーディングや実装について明らかににしつつも、本質的でない細かなディティールを省略した命令セットを提示する。  
このため、実際の命令セットとは若干の相違がある。  

本レポートでは以下のことが考慮されている。  
  - コンパクトなバイトコードへの変換（変換処理については、ポータビリティのためＣで書かれたエミュレータとして実装した）
　　　今回ターゲットにしたバイトコードは、Progolと、VAX-730マイクロコードである。（Progolは、マシンコードを生成するマクロ言語
　　　ソフトウェアによる実装の上で効率的な、ほぼダイレクトにマシンコード(VAXなど）へコンパイル可能なものである）
  - 標準的なマシン命令語へのコンパイル（例：VAXやEDCsystem10/20）
  - 特にProlog専用プロセッサのために設計された命令セットに対する、ハードウェア（又はファームウェア）エミュレーション


今回提案する新しい抽象マシンモデルは、前回の論文で説明した旧モデルからの大幅な改版である。  
またこの新モデルは、旧モデルにおけるかつての困難さを克服している(以降の章で詳述する)。  

この改良では、環境フレームと呼ばれるデータをスタック上に置く。  
環境フレームとは、中間言語レベルでは、ソースコードコード上でユーザが定義したゴールをコンパイラがあらかじめ定義した別のゴール形式に置換したものである。  
さらに、実行状態レベルでは、環境フレームは節のボディ部分のひとまとまりのゴールの末尾位置（つまり、これらのゴールが全て実行された結果の状態）に結び付けられている。

今までのモデルはVAX-730マイクロコードによる実装を強く意識して構築されてきた。  
新モデルは、さらにハードウェア実装による適合性をより考慮したものになっている。  
（ただし、VAXのようなマシンへのソフトウェア、あるいはファームウェアへの実装が同等に受け入れられるようにしている）。

新しいモデルは、DEC-10 Pologベースの抽象マシンにかなり近いもの（文献4.参照）であり、これ加えて末尾再帰最適化のための改良を施している。（文献5.参照）

従来のモデルからの主な変更点は以下のとおり。

 - 複合項を構成する方法としては、構造体シェア方式から構造体コピー方式に変更した。
　　（構造体シェア方式は、依然として解法の設立したゴールの表現としては使われている）

 - 選択ポイントは環境フレーム（ローカルスタックフレームである）から分離され、手続呼出ごとでなく、必要なときのみ生成されるようにした。

 - 環境フレームに含まれる変数の一部は、実行処理が確定後これ以上必要なくなった変数を廃棄することで、
　　「刈り取」られるようにした。これは末尾再帰最適化の一般化として捉えることができる。

 - 節の最終ゴールに含まれる、潜在的に「安全でない」変数は、実行中に必要とされる場合に限りグローバル変数として生成し、
　　コンパイル時のデフォルト値としては扱わないようにした。

本アーキテクチャは、Bowenの抽象マシン、Byrの抽象マシンまたは、Clocksinの抽象マシンに多くの共通点を見出すことができるだろう。


　この論文の主旨は、バイトコードエミュレータを通して、ソフトウェアもしくはファームウェアによるアーキテクチャを実現することであり、
今回このアプローチを取ったことを強調する。

　今回のようなバイトコードエミュレータを使用した設計は、広大な仮想メモリへのアクセスを前提としている。  
中でも、メモリ管理に関してはとりわけVAXアーキテクチャを指向している。

　Prologのランタイム時のデータストラクチャは32ビットワードの列としてエンコードされる。  
Prologプログラムは、8ビットバイトの列としてエンコードされる命令の列として表現される。  
各命令は1バイトのオペレーションコードからなり、幾つかの引数（典型的には1個だが、2個もしくは0個の場合もある）をとる。  
１つの引数は、1バイト、2バイト、あるいは4バイト長である。  

　バイトコードエミュレータは、異なるオペレーションを定義した、小さなルーチンの集合体である。  
実行は、１つのルーチンから次へと次の命令についてのオペレーションコードのディスパッチにより進行し、いくつかの命令では２つのモード（読み込みモード／書き込みモード)のいずれかの下で実行されるようになっている。

　最初期のエミュレータ（つまり旧エンジン用の設計で作られた）はProgolで実装されており、VAXマシンコードを生成させていた。  
Progolによる実装はソフトウェア実装が難しくなく、複数のマシンへの移植が容易であることが期待できたからである。

現在では、上記ProgolコードからC言語への置き換えが完了している。  
振り返ってみると、Progol形式のエミュレータという発想は、VAX-730上のマイクロコード（もしくは、他の安定的なマシン）への実装方法を示すためのモデルを提示することだったのだと思う。


### 2. データオブジェクト

Prologの項(term)は、変数（これは一般的にはアドレス指定する）とタグを含むワードからなる。(可能なフォーマットは付録5.参照）  
メモリ空間は、32ビットもの広大なアドレス空間が想定されている（訳註 1983年当時としては非常に広大である）。  
タグは項の型を識別可能にするが、少なくとも2ビット、望ましくは8ビット長を要する。

主たるデータ型は、参照（バインドの有無を問わない）、構造体、リスト、そして定数（アトムや整数を含む）である。  
ここで、バインドとは、ある変数の参照先（構造体、リスト、定数か、別の変数）を実際に結び付けることである。  
このようにバインドされたある変数の参照先がさらに別の変数である場合には、この変数に対して同じようにバインドがなされることになろう。  
場合によってはこのバインドの連鎖が長いチェインをなすことがある。  
（この場合の処理についてはデリファレンスに関する説明を参照されたい。）  
バインドされていない変数の場合は、自分自身を参照するようにセットする。

現実のハードウェア実装では、データ型の識別のために、さらに追加のタグを用意することになるだろう。  
構造体とリストは、非構造体シェア方式で指定される。別の表現をすると、それらは明確にコピーされたファンクタと引数により、
連続したメモリ上のワード上に生成される。

リストは、本来は構造体の一種と考えることができるが、頻繁に登場するため、構造体とは異なる専用のタグを設ける。  
そうすると、タグをチェックするだけでリストであることが判別できるので、ファンクタと引数を利用する必要性がなくなる。  
このような工夫をすることで、メモリ格納時にファンクタ部分を省略でき、メモリを節約できる。


### 3. データアドレス
　メインとなるデータアドレスはコードエリアであり、命令と他のデータ（プログラムポインタ）を含んでいる。  
エリアは３つのスタック領域に分割される。  
各スタック領域はそれぞれ、ローカルスタック、ヒープ（あるいはグローバル）スタック、トレイルスタックとして使用される。  
それら３つのスタックは、ユニフィケーションのため小さなプッシュダウンリスト（PDL)も使用する。

　各スタックの領域は、通常は手続呼出しのたびに拡がり、そして、バックトラックにより縮む。　  
加えて、末尾再帰最適化により（確定した手続き中、最後の手続呼び出しの実行時に）ローカルスタックの情報を削除する。  
カットオペレータは（ローカルスタックとトレイルの両方から）バックトラック情報を切除することで実現可能である。

上記各エリアのメモリレイアウトは以下

```
low                                                                          high
  ______________________________________________________________________________
 | code area     |->    | heap      |->   | stack   |->   | trail |->   <-| PDL |
 |_______________|______|___________|_____|_________|_____|_______|_______|_____|
         :                     :    :          :   :              :
         P                     HB   H          B   E              TR
```

　スタックとヒープが上図のように配置されていることで、単純な戦略が利用可能である。  
つまり、変数-変数間のバインド時に、常に変数を低いメモリアドレスにバインドする。  
というのは、バックトラック等によって、それまでの上位のメモリアドレス参照を一律に無効にするよう動作させることで、変数参照が（参照先を失って）宙ぶらりんの状態になることを防止するのに十分と考えられる。  
つまりこれが、このレイアウトにすることの利点であろう。


　ヒープには、ユニフィケーションか手続呼び出しにより生成された、全ての構造体とリストを格納する。  
トレイルには、変数の参照を格納する。  
ここで、変数の参照は、ユニフィケーションの間バインドされ、バックトラック時には全てアンバインドされる。  
スタックには、２種類のオブジェクト：環境フレームと選択ポイント（付録4.参照）を格納する。  
環境フレームは、（複数の節からなるボディ中に存在する変数のための）変数セルの配列からなり、継続ポインタを伴う。  

継続ポインタは、次の節に対応づけられた環境フレームへのポインタである。  
実際には、継続ポインタは、現在実行中の処理が終わるまでは、インスタンス化された、ゴールのリストとして存在するだけである。  
節に複数の選択肢がある場合に選択ポイントを使用するという考え方なので、
必然的に選択ポイントは、手続が１以上の節を持つ場合にのみ生成される。  
選択ポイントには、バックトラックが発生したとき、計算機処理を以前の状態に復帰させるために必要な情報が含まれる。  
この情報について具体的に説明すると、選択節のポインタに加えて、（その時手続きに処理が移った）後続のレジスタ（下記参照）の値であるH,TR,B,CP,E,A1-Am(mは引数の数）が該当する。

### 4. レジスタと変数の扱い

Prolog処理実行時の現在状態は、特定のレジスタにより定義される。  
このレジスタは、メインデータ領域を指し示している。（付録 2. 3.参照)

主たるレジスタ群は以下

	P	プログラムポインタ（コードエリアをポイントする）
	CP	継続(プログラム)ポインタ（コードエリアをポイントする）

	E	最後の環境フレーム（ローカルスタック上にある）
	B	最後の選択ポイント（バックトラックポイント）（ローカルスタック上にある）
	A	スタックの先頭（厳密には必要とはいえない）

	TR	トレイルスタックの先頭
	H 	ヒープの先頭
	HB	ヒープのバックトラックポイント（例：Hの値は、Bと対応する）

	S	構造体ポインタ（ヒープをポイントする）

	A1, A2, ...	  引数レジスタ群
	X1, X2, ...	  一時変数レジスタ群

　レジスタAとレジスタXは、実のところ全く同じものであり、名称の相違は、使用法の相違によるものである。  
レジスタAは手続きの引数として使用され、レジスタXは節の一時変数として値を保持するために使用される。

　一時変数とは、頭部、構造体中、最終ゴールの中、のいずれかに最初に出現する変数の中で、なおかつ、ボディ中には１回も出現しないものを指す（ここで、節の頭部は、最初のゴールの一部としてカウントされる）。  
以上の条件を満たす場合、この変数を節の環境フレーム中に格納する必要が無いことが分かるだろう。

　永続変数とは、一時変数とは分類されない全ての変数を指す。  
永続変数は、環境フレーム中に格納される。そして、環境フレームポインタからのオフセットとともにアドレスされる。  
これらは、例えば、Y1,Y2などとして参照されるのである。  
これらボディ中の２ゴールより少ない節の変数は、永続変数として分類されないということを銘記しておく。  
そしてそれゆえ、このような節は、環境フレーム中に保持しなくてもよいということである。  
環境フレーム中の永続変数は、もうこれ以上必要なくなったとき速やかに廃棄できるように配置される。  
これにより行われる、環境フレームの「刈込み」は、その環境フレームがより最近の最後の選択ポイントである時にのみ、実質的な影響が生じる。


### 5. 命令セット

　Prologプログラムは、Prolog命令の列としてエンコードされる。  
一般的に、それらは各Prologシンボルに対応した１つの命令である。  
１つの命令は、１つのオペレーションコードと、いくつかのオペラント（典型的にはただ１つ）からなる。  
オペレーションコードは、通常はそれが出現する文脈を伴ったPrologシンボルの型としてエンコードされることになる。  
それはただの１バイト（8ビット）を占有するのみである。オペランドは、小さな整数（オフセットとアドレス）を含んでおり、これにより、異なる種類のPrologシンボルを識別する。  
エンコードの内容に応じて、オペランドは、1，2あるいは4バイトを占有するか、いくつかのケースでは、1バイトも使わない。


Prolog命令セットは、GET命令、PUT命令、UNIFY命令、手続命令、INDEXING命令に分類される。（各命令セットの要約は、付録 1.を参照）

GET命令は、節頭部の引数に関し、手続の引数（Aレジスタにより与えられる）に対するマッチング処理を受け持つ。
                 主たる命令群は以下

     get_variable Yn,Ai		get_variable Xn,Ai
     get_value Yn,Ai		get_value Xn,Ai
     get_constant C,Ai		get_nil Ai
     get_structure F,Ai		get_list Ai

ここでAi は、引数レジスタを表し、引数レジスタ Xn,Yn,C,Fは、それぞれ、一時変数、永続変数、定数、ファンクタを表す（以降の説明でも同様である）。  
GET_VARIABLE命令は、現在の変数がインスタンス化されていない場合（つまりその変数が、節中で最初に登場する場合）に使用される。そうでない場合には、GET_VALUE命令が使用される。


PUT命令は、ある節の、ボディ中に含まれるゴールの引数に対して使用するものであり、引数をAレジスタへロードする処理を受持つ。  

                 主たる命令群は以下

    put_variable Yn,Ai	    	put_variable Xn,Ai
    put_value Yn,Ai		put_value Xn,Ai
    put_unsafe_value Yn,Ai
    put_constant C,Ai		put_nill Ai
    put_structure F,Ai		put_list Ai

PUT_UNSAFE_VALUE命令は、安全でない変数が存在する最終ゴールに対して、PUT_VALUE命令の代りに使用する。  
安全でない変数とは、頭部もしくは構造体中において、最初に出現したものではない永続変数のことである。  
（これは、その変数がPUT_VARIABLE命令によってイニシャライズ化されたことがあった、ということである）  
この、PUT_UNSAFE_VALUE命令は、必要ならば変数をグローバル化（その変数を新しい値をもつヒープ上のセルにバインドする）することで、ある別の環境フレームへ処理が移った後に、この安全でない変数に対してデリファレンスすることを可能とする。  
このように安全でない変数をグローバル化することは、（その後の実行や、命令呼び出しにより廃棄させられることになる）一部の環境フレームからの参照が（参照先を失って）宙ぶらりんになることを阻止するためにも必要なことである。


UNIFY命令は、変数またはリストの引数に対応するもので、かつ、
既存の構造体に対するユニファイや、新しい構造体を生成する処理を担う。

　　　　　　     主たる命令群は以下

    unify_void N
    unify_variable Yn            unify_variable Xn
    unify_value Yn 		 unify_value Xn
    unify_local_value Yn	 unify_local_value Xn
    unify_constant C  		 unify_nil

UNIFY_VOID N 命令は、N回の単独で出現する変数の列を表す。  
これら「VOID」変数ならば、一時変数セルも永続変数セルも必要ないであろう。  
UNIFY_LOCAL_VALUE命令は、もしも変数が、グローバル値としてイニシャライズされていない（例えばUNIFY_VARIABLE命令とか）ときに、UNIFY_VALUE命令の代りに使用される。　　　　　　　　

（一連の）UNIFY命令は、リストに対するGETやPUT命令よりも前に実行される。  
この命令は、２つのモード（読み込みモード／書き込みモード）のいずれを選択するか決定する。  
後に続くUNIFY命令はこの決定されたモードのもと実行される。　
「読み込み」モードでは、UNIFY命令は、後に続く既に存在する構造体と引数とのユニフィケーションを実施する。  
これは、Sレジスタを通じてアドレスされる。  
「書き込み」モードでは、UNIFY命令は後に続く新しい構造体の引数を生成する、これは、Ｈレジスタを通じてアドレスされる。

ネストされたサブ構造体や、サブリストらは、以下のようにコード変換される。

もしサブ構造体やサブリストが、頭部に出現したならば、UNIFY_VARIABLE Xn命令にコード変換される。  
そして現在の一連のユニファイ手順が終了した後は、GET_STRUCTURE F,XnもしくはGET_LIST Xn命令が続く。

もしサブ構造体やサブリストがボディに出現したならば、それらはUNIFY_VALUE Xn命令にコード変換される。  
そして現在の一連のユニファイ手順の開始前に、PUT_STRUCTURE F,Xnもしくは PUT_LIST Xn命令が挿入される。

手続き命令とは、述語に対応するものであり、制御を移す処理と（手続き呼び出しに関連付けられた）環境フレームの割り
付け処理を担う。

　　　　　　　主たる命令群は以下

    proceed        allocate
    execute P			 deallocate
    call P,N

ここで、Pは、述語を意味し、Nは環境フレーム中における変数の数を意味する。  
下記のように、手続き命令は（ボディ中に０個以上のゴールを伴った）節のコード変換に使用される。
```
    P.	      	     	 P :- Q.                 P :- Q, R, S.

    get args of P      get args of P           allocate
    proceed            put args of Q           get args of P
                       execute Q               put args of Q
                                               call Q,N
                                               put args of R
                                               call R,N1
                                               put args of S
                                               deallocate
                                               execute S
```

環境フレームのデータサイズは、呼出し命令により動的に決まることを、銘記しおく。  
データサイズは常に減少していく。それで、N1（のデータサイズ）は、N（のデータサイズ）以下となるのである。

INDEXING命令は、（手続きを構成する）異なる節同士をリンクし、それら節（与えられた手続呼出にマッチする可能性があるもの）の部分集合をフィルタリングして洗い出す処理を担う。  
このフィルタリングもしくはインデキシング機能は、手続きの第一引数（A1レジスタ）により与えられる、第一ファンクタをキーにしている

　　　　　　　　　　　主たる命令群は以下

    try_me_else L          try   L                  switch_on_term Lv,Lc,Ll,Ls
    retry_me_else L        retry L                  switch_on_constant N,Table
    trust_me_else fail     trust L                  switch_on_structure N,Table


ここで、L,Lv,Lc,Ll,Lsはそれぞれ節（あるいは節の集合）のアドレスであり、
テーブルは、サイズNのハッシュテーブルである。

他の処理に先立って、各節は、手続き中の節の位置が最初の場合は、TRY_ME_ELSE命令、中間の場合は、RETRY_ME_ELSE命令、最後の場合は、TRUST_ME_ELSE命令を設定する。  
これらの命令は、全ての節が既にマッチ処理を全て試し、A1をある変数にてデリファレンスする時にのみ実行される。  
オペランドＬは、後続の節をアドレスする。  

SWITCH_ON_TERM命令は、A1に対するデリファレンスの値の型に応じて、
変数の場合はLv,定数の場合はLc,リストの場合はLl,構造体の場合はLsの値（アドレス）をディスパッチする。

Lvレジスタは、TRY_ME_ELSE命令（さもなければTRUST_ME_ELSE命令）のアドレスとなるであろう。  
これは手続きの最初の節に先立って設定される。  
Llレジスタは、単独節(キーはリストである）のアドレスか、節の列に対するアドレスであり、(try,retry,trust)命令の列により識別される。  
LcレジスタとLsレジスタはおそらく、単独節か節の列（Llの場合と同じく）のアドレスとなるであろう。  
もしくは、より一般的には、それぞれ、SWITCH_ON_CONSTNT命令か、SWITCH_ON_STRUCTURES命令かのアドレスとなろうし、それらは
節か、与えられたキーによってマッチする節、へアクセスするためのハッシュテーブルを提供する。


### 6. 最適化
ある種の命令では(引数レジスタと一時的なレジスタを明記しなくても特定できるので)、オペランドをNULLとして省略できる。

    get_variable Xi,Ai
    put_value Xi,Ai

コンパイラはこのような最適化の適用範囲を広げるため、一時変数をXレジスタに割り付けることに労力を費やす。


以下の２つの命令は同じオペレーション（Xiレジスタの内容をXjレジスタに転記する）であることを銘記しておく。

    get_variable Xj,Ai
    put_variable Xi,Aj


### 7. 節エンコーディングのサンプル
節エンコーディングのサンプルとして、リストの連結とクイックソートを挙げる。
```
concatenate([],L,L).
concatenate([X|L1],L2,[X|L3]) :- concatenate(L1,L2,L3).

concatenate/3: switch_on_term C1a,C1,C2,fail

C1a:    try_me_else C2a			            % concatenate(
C1:	    get_nil A1                      %    [],
        get_value A2,A3                 %    L,L
        proceed	                        % ).

C2a:    trust_me_else fail              % concatenate(
C2:     get_list A1                     %    [
        unify_variable X4               %       X|
        unify_variable A1               %       L1], L2,
        get_list A3                     %    [
        unify_value X4                  %       X|
        unify_variable A3               %       L3]) :-
        execute concatenate/3           % concatenate(L1,L2,L3).

qsort([],R,R).
qsort([X|L],R0,R):-
	split(L,X,L1,L2), qsort(L1,R0,[X|R1]), qsort(L2,R1,R).

qsort/3: switch_on_term C1a,C1,C2,fail

C1a:    try_me_else C2a                 % qsort(
C1:     get_nil A1                      %    [],
        get_value A2,A3                 %    R,R
        proceed                         % ).

C2a:    trust_me_else fail              % qsort(
C2:     allocate
        get_list A1                     %    [
        unify_variable Y6               %        X|
        unify_variable A1               %        L],
        get_variable Y5,A2              %    R0,
        get_variable Y3,A3              %    R) :-
        put_value Y6,A2                 % split(L,X,
        put_variable Y4,A3              %    L1,
        put_variable Y1,A4              %    L2
        call split/4,6                  %),
        put_unsafe_value Y4,A1          % qsort(L1,
        put_valuse Y5,A2                %    R0,
        put_list A3                     %    [
        unify_value Y6                  %        X|
        unify_variable Y2               %        R1]
        call qsort/3,3                  % ),
        put_unsafe_value Y1,A1          % qsort(L2,
        put_value Y2,A2                 %    R1,
        put_value Y3,A3                 %    R
        deallocate
        execute qsort/3                 % ).
```
以下に掲げるサンプルは、永続変数の扱いを説明したものである。
```
compile(Clause,Instructions) :-
   preprocess(Clause,C1),
   translate(C1,Symbols),
   number_variables(Symbols,O,N,Saga),
   complete_saga(O,N,Saga),
   allocate_registers(Saga),
   generate(Symbols,Instructions).

       try_me_else fail                 % compile( Clause,
       allocate
       get_variable Y2,A2               %    Instructions) :-
       put_variable Y5,A2               % preprocess(Clause,C1
       call preprocess/2,5              % ),
       put_unsafe_value Y5,A1           % translate(C1,
       put_variable Y1,A2               %    Symbols
       call translate/2,4               % ),
       put_value Y1,A1                  % number_variables(Symbols,
       put_constant O,A2                %    O,
       put_variable Y4,A3               %    N,
       put_variable Y3,A4               %    Saga
       call number_variables/4,4        % ),
       put_constant O,A1                % complete_saga(O,
       put_unsafe_value Y4,A2           %    N,
       put_variable Y3,A3               %    Saga
       call complete_saga/3,3           % ),
       put_unsafe_value Y3,A1           % allocate_registers(Saga
       call allocate_registers/1,2      % ),
       put_unsafe_value Y1,A1           % generate(Symbols,
       put_value Y2,A2                  %    Instructions
       deallocate
       execute generate/2               % ).
```

以下に掲げる２つのサンプルは、ネストされた構造体のエンコーディングについて説明したものである。

`d(U*V,X,(DU*V)+(U*DV)) :- d(U,X,DU), d(V,X,DV).`
```
        try_me_else ...　　　　　         % d(
　　　　　get_structure '*'/2,A1          %     *(
　　　　　unify_variable A1               %        U,
　　　　　unify_variable Y1               %        V),
　　　　　get_variable Y2,A2              %     X,
　　　　　get_structure '+'/2,A3          %     +(
　　　　　unify_variable X4               %        SS1,
　　　　　unify_variable X5               %        SS2),
　　　　　get_structure '*'/2,X4          % SS1 = *(
　　　　　unify_variable A3               %           DU,
　　　　　unify_value Y1                  %           V),
　　　　　get_structure '*'/2,X5          % SS2 = *(
　　　　　unify_value A1                  %           U,
　　　　　unify_variable Y3               %           DV)) :-
　　　　　call d/3,3                      % d(U,X,DU),
　　　　　put_value Y1,A1                 % d(V,
　　　　　put_value Y2,A2                 %    X,
　　　　　put_value Y3,A3                 %    DV
　　　　　execute d/3                     % ).

test :- do(parse(s(np,vp),[birds,fly],[])).

        trust_me_else_fail              % test :-
        put_structure s/2,X2            % do( SS1 = s(
        unify_constant np               %       np,
        unify_constant vp               %       vp),
        put_list X4                     % SS2 = [
        unify_sonstant fly              %       fly|
        unify_nil                       %       []],
        put_list X3                     % SS3 = [
        unify_constant birds            %       birds|
        unify_value X4                  %       SS2],
        put_structure parse/3,A1        %    parse(
        unify_value X2                  %       SS1,
        unify_value X3                  %       SS2,
        unify_nil                       %       [])
        execute do/1                    % ).
```
以下に掲げるサンプルは、インデキシング命令の使われ方を説明したものである。
```
call(X or Y) :- call(X).
call(X or Y) :- call(Y).
call(trace) :- trace.
call(notrace) :- notrace.
call(nl) :- nl.
call(X) :- builtin(X).
call(X) :- ext(X).
call(call(X)) :- call(X).
call(repeat).
call(repeat) :- call(repeat).
call(true).

call/1: try_me_else C6a
        switch_on_type C1a,L1,fail,L2

L1:     switch_on_constant 4, $(trace: C3,
        notrace: C4,
        fail,
        nl: C5)
L2:     switch_on_structure 1, $(or/2: L3)

L3:     try C1
        trust C2

C1a:    try_me_else C2a                 % call(
C1:     get_structure or/2,A1           %    or(
        unify_variable A1               %       X,Y)) :-
        execute call/1.                 % call(X).

C2a:    retry_me else C3a               % call(
C2:     get_structure or/2,A1           %    or(
        unify_void 1                    %       X,
        unify_variable A1               %       Y)) :-
        execute call/1                  % call(Y).

C3a:    retry_me_else C4a               % call(
C3:     get_constant trace,A1           %    trace) :-
        execute trace/0                 % trace.

C4a:    retry_me_else C5a               % call(
C4:     get_constant notrace,A1         %    notrace) :-
        execute notrace/0               % notrace.

C5a     trust_me_else fail              % call(
C5:     get_constant nl ,A1             %    nl) :-
        execute nl/0                    % nl.

C6a:    retry_me_else C7a               % call(X) :-
        execute builtin/1               % builtin(X).

C7a:    retry_me_else L4                % call(X) :-
        execute ext/1                   % ext(X).

L4:     trust_me_else fail
        switch_on_type C8a,L5,fail,L7

L5:     switch_on_constant 2, $(repeat: L6, true: C11)

L6:     try C9
        trust C10

L7:     switch_on_structure 1, $(call/1: C8)

C8a:    try_me_else C9a                  % call(
C8:     get_structure call/1,A1          %    call(
        unify_variable A1                %       X)) :-
        execute call/1                   % call(X).

C9a:    retry_me_else C10a               % call(
C9:     get_constant repeat,A1           %    repeat
        proceed                          % ).

C10a:   retry_me_else C11a               % call(
C10:    get_constant repeat,A1           %    repeat) :-
        put_constant repeat,A1           % call(repeat
        execute call/1                   % ).

C11a:   trust_me_else fail               % call(
C11:    get_constant true,A1             %    true
        proceed                          % ).
```

### 8. 各命令と基本オペレーションについての説明

以降の説明中、Vnは一般的に永続変数Ynもしくは一時変数Xnのどちらかを指し示すために使用されることを銘記しておく。  
説明のいくつかは、動作を単純明快にするために、アルゴリズムを表現するための疑似的なコードを記載している。

#### 8.1. 制御命令

allocate	この命令は、ボディが１以上のゴールからなる節の最初にみられる。
		（これは実際のところ、永続変数が最初に出現する手前ならばどこにでも配置可能である。）
		新しい環境フレームへの空きスペースがスタック上に割り付けられ、最後の選択ポイントもしくは、
		最後の環境フレームの後に配置される。
		そして、Eは、新しい環境フレームへのポインタとしてセットされる。
```
          CE := E
          E := (CE < B -> B | CE + env_size(CP))
          CP(E) := CP
          CE(E) := CE
```


deallocate	この命令は、最後の命令（ボディ部が１以上のゴールからなる）の実行の手前にみられる。
		ひとつ前の継続ポインタが再セットされ、現在の環境フレームは廃棄される。

          CP := CP(E)
          E := CE(E)

call Proc,N	この命令は、ボディ中のゴールを終了させる。  
そしてＣＰに後続のコードへのポインタをセットする処理と、プログラムポインタＰに手続へのポインタセットする処理を担当する。  
Ｎは、この時点での環境フレーム中の変数の数であるが、手続き中の特定の命令からアクセスするために使用されるＣＰからのオフセット値である。

          CP := following code
          P := Proc

execute Proc	この命令は節のボディ中の最終ゴールを終了させる。  
プログラムポインタＰに、手続へのポインタをセットする。

		    	P := Proc

proceed		この命令は、ユニット節を終了させる。プログラムポインタＰに、継続ポインタＣＰの値をセットする。

          P := CP


#### 8.2. PUT命令

put_variable Yn,Ai

		この命令は、ゴールの引数がアンバインドされた永続変数である場合に使用する。
		この命令は、永続変数YnをAiレジスタへセットする。
　　　　　　　　そして、Yn自身を自身の参照先としてイニシャライズする。

           Ai := Yn := ref_to(Yn)

put_variable Xn,Ai

		この命令は、最終ゴールの引数がアンバインドされた変数である場合に使用する。
		この命令は、アンバインドされた変数をヒープ上に生成する。
		そして、これへの参照先をAiレジスタと、Xnレジスタにセットする。

           Ai := Xn := next_term(H) := tag_ref(H)

put_value Vn,Ai

    この命令は、ゴールの引数が、バインドされた変数である場合に使用する。
    この命令は単に、変数Vnの値を、Aiレジスタにセットする。

           Ai := Vn

put_unsafe_value Yn,Ai

    この命令は、安全でない変数が最後に出現した場合に使用する。
    この命令はYnをデリファレンスする。そして結果をAiレジスタにセットする。
    もしも、Ynが現在の環境フレーム中の変数にデリファレンスした場合は、この変数は
    ヒープ上の新しいグローバル変数にバインドされ、このバインドは、
    必要ならばトレイルされる。そしてAiレジスタは、新しいグローバル変数へ
    参照先をセットする。

put_const C,Ai

    この命令は、ゴールの引数が定数である場合に使用する。
    この命令は単に、定数ＣをAiレジスタにセットする。

           Ai := C

put_nil Ai

    この命令は、ゴールの引数が定数空リスト（[]）である場合に使用する。
    この命令は単に、Aiレジスタに定数[]（nilである　訳注）をセットする。

           Ai := nil

put_structure F,Ai

    この命令は、ゴール引数として出現した構造体（埋め込まれたサブ構造体が無い）の開始をマークする時に使用する。
    この命令は、構造体のためのファンクタＦをヒープ上に置き、
    対応する構造体ポインタをAiレジスタへセットする。
    その後「書き込み」モードに移行する。

           Ai := tag_struct(H)
           next_term(H) := F

put_list Ai

    この命令は、ゴール引数として出現したリストの開始をマークする時に使用する。
    この命令は、リストポインタ（ヒープのトップに対応している）を、
    Aiレジスタへセットする。その後「書き込み」モードに移行する。

           Ai := tag_list(H)

### 8.3. GET命令

get_variable Vn,Ai

		この命令は頭部の引数がバインドされていない変数である場合に使用する。
		この命令は単純に、レジスタAiの値を、変数Vnにセットする。

           Vn := Ai

get_value Vn,Ai

    この命令は頭部の引数がバインドされている変数である場合に使用する。
    この命令は、レジスタAiの値を取り、これを変数Vnに対してユニファイする。
    完全にデリファレンスされたユニフィケーションの結果は（もしもVnが一時変数ならば）変数Vnに残される。

get_constant C,Ai

		この命令は頭部の引数が定数である場合に使用する。
		この命令は、レジスタAiの値を取り、これをデリファレンスする。
		もしも、結果が変数の参照ならば、この変数を定数Ｃにバインドする。
		そして、バインドは、必要であればトレイルされる。さもなければ
		結果は、定数Ｃと比較され、もし２つの変数が一致しなければバックトラックが発生する。

get_nil Ai

  	この命令は頭部の引数が空リストである場合に使用する。
		この命令は、レジスタAiの値を取り、これをデリファレンスする。
		もしも、結果が変数の参照ならば、この変数を（定数である）空リストにバインドする。
		そして、バインドは、必要であればトレイルされる。さもなければ
		結果は、（定数である）空リストと比較され、一致しなければバックトラックが発生する。

get_structure F,Ai

		この命令は、頭部の引数として登場する構造体（埋め込まれたサブ構造体が無い）の開始をマークする場合に使用する。
		この命令は、レジスタAiの値を取り、これをデリファレンスする。もしも、
		この結果が、変数の参照であるならば、この変数を新しい構造体のポインタ（
		ヒープの先頭位置をポインティングしている）とバインドする。
		そして、必要ならばトレイルされる。
		ファンクタＦはヒープ上に置かれる。
		その後「書き込み」モードに移行する。
		さもなければ、もし結果が構造体でかつ、それがファンクタＦと一致するならば、
		そのポインタＳを、構造体の引数をポイントするようにセットし、
		その後「読み込み」モードに移行する。さもなければ、バックトラックが発生する。

get_list Ai

    この命令は、頭部の引数として出現する、リストの、開始をマークする場合に使用する。
		この命令は、Aiレジスタの値を取得し、これをデリファレンスする。
		もしも、結果が変数の参照であった場合、この変数を新しいリストのポインタとバインドする。
		このポインタは、ヒープのトップをポイントする。
		このバインドは、必要であればトレイルされる。その後「書き込み」モードに移行する。
		もしも、結果がリストであった場合は、ポインタＳを、リストの引数へ
		セットし、その後「読み込み」モードに移行する。
		さもなければ、バックトラックが発生する。

#### 8.4. UNIFY命令

unify_void N

    この命令は、頭部の構造体引数が単独にて出現するＮ個の列である場合に使用する。
		この命令が「読み込み」モードで実行される場合、それは単純にＳから次のＮ個の引数をスキップする。
		この命令が「書き込み」モードで実行される場合、Ｎ個の新しいバインドされていない変数を、ヒープ上に置く。

    [「読み込み」モード]:
           S := S + N*word_width
    [「書き込み」モード]:
           next_term(H) := tag_ref(H)
           {N回繰り返し...}

unify_variable Vn

		この命令は、頭部の構造体引数がバインドされていない変数である場合に使用する。
		この命令が「読み込み」モードで実行される場合、単純に次の引数をＳから取得して、変数Vnにストアする。
		この命令が「書き込み」モードで実行される場合、新しく未バインドの状態の
		変数を、ヒープ上に置く。そして、変数Vnへの参照を格納する。

    [「読み込み」モード]:
           Vn := next_term(S)
    [「書き込み」モード]:
           Vn := next_term(H) := tag_ref(H)

unify_value Vn

    この命令は、頭部の構造体引数が幾つかのグローバル変数にバインドされている変数である場合に使用する。
		この命令が「読み込み」モードで実行される場合、Ｓから次の引数を取得して、そして、これを変数Vnの値と
		ユニファイする。もしVnが一時変数ならば、デリファレンスされた結果を変数Vnに残す。
		この命令が「書き込み」モードで実行される場合、Vnの値をヒープ上に置く。

    [「書き込み」モード]:
           next_term(H) := Vn

unify_local_value Vn

		この命令は、頭部の構造体引数が、変数がバインドされているので、グローバル変数にする必要性がない場合に使用する。
		１点を除くと、影響はUNIFY_VALUE命令と同じである。
		すなわち、「書き込み」モードにおいて
		これは変数Vnの値をデリファレンスし、もし、その結果がスタック上の変数の参照ではなかった場合は、
		結果をヒープ上に置くだけである。
		もし、その結果がスタック上の変数の参照であるならば、新しく未バインド状態の変数をヒープ上に置く。
		このスタック上の変数は、新しい変数の参照としてバインドされる。このバインドは、必要であればトレイルされる。
		そして変数Vnは、もしもVnが一時変数ならば、新しい変数のポインタとしてセットされる。

unify_constant C

		この命令は、頭部の構造体引数が定数である場合に使用する。
		この命令が「読み込み」モードで実行される場合、次の引数をＳから取得し、これをデリファレンスする。
		もし、結果が変数の参照ならば、この変数を定数Ｃにバインドする。そしてこのバインドは、
		必要ならばトレイルされる。　もし、結果が非参照変数であるならば、この変数を、
		定数Ｃと比較するが、比較の結果が不一致ならばバックトラックが発生する。
		この命令が「書き込み」モードで実行される場合、定数Ｃをヒープ上に置く。

    [「書き込み」モード]:
           next_term(H) := C



#### 8.5. インデキシング命令

try_me_else L

    この命令は、１以上の節を伴った手続き中の、最初の節のための命令の前に実行する。
		選択ポイントは、後続のスタック上のN＋6個の値をセーブすることによって生成させる。

		各値の解説：レジスタAn〜A1、現在の環境フレームポインタＥ、現在の継続ポインタＣＰ，１つ前の選択ポインタＢ
		次の節のアドレスＬ、現在のトレイルポインタＴＲそして、現在のヒープポインタＨである。
		HBを、現在のヒープポインタにセットする。そしてＢを、現在のスタックのトップのポインタにセットする。

retry_me_else L

    この命令は、手続きの中間に位置する節のための命令の前に実行する。
		換言すれば、これは、最初や、最後の節ではない。現在の選択ポイントを
		次の節のアドレスＬによって更新する。

           BP(B) := L

trust_me_else fail

		この命令は、手続き中の最後の節のためのコードの手前で配置する。
		（この命令の引数は任意のものである。しかし、
		節のアサートやリトラクトを促すための命令中のスペースを単純に保持する）　　
		この現在の選択ポイントは廃棄する。そして、
		レジスタBとHBは、対応する前回の選択ポイントに再セットする。

           B := B(B)
           HB := H(B)

try L

 	この命令は、同じキーにより特定された節の命令列の最初に配置する。
		選択ポイントは、スタック上の後続のN+6個の値をセーブすることにより生成させる：
		レジスタAn〜A1、現在の環境フレームポインタＥ
		現在の継続ポインタＣＰ、前回の選択ポイントのポインタB
		後続の命令（選択節）のアドレス、現在のトレイルポインタTR、現在のヒープポインタH、である。
		HBを、現在のヒープポインタにセットする、Bを、現在のスタックのトップ
		のポインタにセットする。最後に、プログラムポインタＰを、節アドレスＬにセットする。

retry L		

    この命令は、同じキーを伴った特定の節（複）の命令列の中間に位置する。
		現在の選択ポイントは、後続の命令（選択節）のアドレスを伴って更新される。
		プログラムポインタPは、節のアドレスＬにセットされる。

           BP(B) := following code
           P := L

trust L 	

    この命令は、同じキーを伴った節（複）の命令列の最後に位置する。
		現在の選択ポイントは廃棄する。そして、
		レジスタBと、HBを、対応する前回の選択ポイントに更新する。
		最後に、プログラムポインタPを、節アドレスＬにセットする。

           B := B(B)
           HB := H(B)
           P := L

switch_on_term Lv,Lc,Ll,Ls

		この命令は、（最初の先頭引数中にある変数のない節）のグループにアクセスする手前に配置する。
		これは、呼び出しの最初の引数のタイプについてのディスパッチの原因である。
		引数A1は、その結果が、変数なのか定数なのか（空でない）リストなのか、構造体なのかによってデリファレンスされる。
		プログラムポインタＰを、それぞれLv,Lc,Ll,Lsにセットする。


switch_on_constant N,table

		この命令は、頭部の引数の位置にある定数を持った節のグループにアクセスするハッシュテーブルを提供する。
		レジスタA1は、定数を保持する。この値は、0からN-1の範囲のインデックス値にてハッシュされる。
		ハッシュテーブルのデータサイズは、Ｎの２乗のサイズである。　ハッシュテーブルのエントリにより
		節もしくは、インデックスされたキーを持つ節へのアクセスを提供する。　
		変数A1中の定数は、異なるキー（だがちょうど符合するものが発見された）により得られたものと比較される。
		プログラムポインタPは、対応する、節もしくは節の集合にポイントされる。
		もしもキーが発見できなければ、バックトラックが発生する。

switch_on_structure N,Table

		この命令は、頭部の引数の最初のものの中の構造体をもつ節のグループに対するハッシュテーブルを提供する。
		影響は、使われるキーが、A1中の構造体の第一ファンクタとして使用されることを除けば
		SWITCH_ON_CONSTANT命令と同一である。

#### 8.6. 他の基本演算
fail		

    この演算は、ユニフィケーション中に失敗が発生した場合に駆動する。
		これは直前の選択ポイントへのバックトラックの原因となる。
		末尾は、トレイルポインタの選択ポイントほどには「巻き取られ」ない。
		参照をトレイルからポップしたり、変数をリセットすることにより、これらアドレス
		をアンバインドする。　レジスタH,A,Cに選択ポイント中の値をセットする。
		Pに次の選択節への選択ポイントをセットする。

trail(R)

    この演算は、変数の参照が、ユニフィケーション中にRがバインドされているときに起動する。
		もし、変数が、ヒープの中にあり、ヒープバックトラックポイントHBの
		手前であるか、あるいは変数がスタックの中にあり、スタックバックトラックポイントBの
		手前であるならば、参照Rは、トレイル上に置かれる。
		さもなければ、何もしない。

### 9. 命令のエンコーディング

　命令（複）のエンコードにはいくつかの方法が考えられる。可能性のあるエンコーディングの方法としては、ソフトウェアによるエミュレーションである。これは付録4.に示す。

各オペレーションコードは、１バイトを占有する。これは、GETやPUT命令のケースでは、もう１バイトにより、Aレジスタについての番号（A1,A2,A3の1,2,3を指すだろう）を与える。  
他の引数は、後述のごとくエンコードされる。

　一時変数や永続変数の番号は、１バイトとしてエンコードされる。  
定数は、32ビットの値（これにはタグを含む）によりエンコードされる。  
特別なオペレーションコードは16ビットにて表記され、この場合、定数の値は、16ビット値として得ることができるだろう。  
ファンクタは、16ビットのファンクタ数としてエンコードされる、これは（32ビットのファンクタ表現を得るための）ファンクタテーブルへのインデックスとして使用される。  
述語と節のアドレスは、現在のセグメントに対する16ビットオフセットにて表記される。

　対応する手続や、節のフルアドレスは現在の命令のアドレスのトップ16ビットに16ビットのオフセットを加えることにより取得することができる。  
セグメント境界を越えるために何らかのエスケープ機構が提供されるであろう。

　この場合は16ビットと32ビット引数が特別な位置合わせをする必要がないということである（現状ではVAXで許容されている）。  
マシンによっては、位置合わせが要求され、ダミーの１バイトスキップ命令がコンパイラにより挿入されるというようなことも起こるだろう。

　命令セットを最適化する際に重要なことは、オペレーションコードに付随する引数の数をでき得る限り少なくしたいということであり、もし引数の数を少なくできれば、命令をより短く（つまり恐らくは高速に）できる。  
このような観点に立った場合、真っ先に頭に浮かぶ最適化の手法としては、１バイト引数を取る命令の場合に、その引数に対応した番号Ｎを与え、
レジスタAn,Xn,Ynを表現する（Ｎは小さい数）ことであろう。  
例示するならば、GET_LIST A3 は、GET_LIST_3という、引数の無い新しい命令に置き換える、ということである。



### 10. 環境フレームスタッキング 対 ゴールスタッキング

 今回は環境フレームスタッキングモデルをベースに設計した。  
さらに言えば、項に関しては非構造体シェア方式により実装した。  
一方で、構造体シェア方式の実装は、スタック上のゴールとしては依然として使われている。

　本設計の初期バージョンは、ゴールスタッキングモデルを使用していた・・・
　ゴールスタッキングモデルは現存する全てのProlog実装系と異なるものであり、私の知る限りでは、構造体シェア方式についてはどんなものであれ存在しなかったはずである。  
これは生成された項（構造体）だけでなく、ゴールについても言えることである。  
　ゴールスタックは、実行される残余のゴールのリストとして明示的に示されている。  
このゴールリストを使うことは伝統的な実現方法である。  
バインドしている環境フレームを表すために、変数セルの配列を格納する必要は無い。  
・・・このようなものである。

ゴールスタッキングモデルは以下の利点を備える

  - 実装の単純さ、実装のコンパクトさ（特にカーネルコード、マイクロコード、専用ハードウェアなどで）

  - ガーベージコレクションの単純さ。

  - 末尾再帰最適化がよりシンプルで、全ての手続き呼び出しに適用可能となること。  
    ・・・もし、それが最後の選択ポイントよりも後であれば、単にゴール呼出を廃棄するだけ。

  - 節中の全ての変数は「一時的」であり、ハードウェアレジスタへと直接指定できる。

  - 一度節の解決が完了したならば、これらは、これ以降の節へのコードについて参照することがない。
      これは、つまり仮想メモリのページングを削減する傾向を示す。
      対照的に、構造体シェア方式（全部もしくは一部の）は、コードエリア全体に対する
      ランダムアクセスを行う傾向にある（これはページングの面で言えばうまくない）。

  - １つ手前のアイテムに引きずられるような節中のジャンプが無い。
    　ジャンプが無いということはパイプライン処理についてより良いパフォーマンスが出せることを意味する。


しかしながら、ゴールスタッキング方式は、環境フレームスタッキング方式に対して顕著な欠点も備える：

  - 不必要なコピー処理により、時間を無駄にしてしまう。
　　　特にボディ（本体）中の早い段階での失敗(Fail)が発生した節ではその無駄が顕著である。
　　　しかしこの欠点は、それほど深刻なものではなく、他のオーバヘッドに比較すれば、コピー処理は相対的に高速であろう。

  - スタックのデータサイズが、安定的ではない。
    そのため（スタックのトップをバッファリングしてレジスタや高速メモリに入れておくなどの）最適化を行いにくい。

  - 各ゴールがスタックからポップされるに際し、（参照先を失って）宙ぶらりん状態になるのを避けるため、
    安全でない変数へのチェックが必須となる。これは、この問題についてのエレガントな答えにはなっていないだろう。

  - ボディ（本体）コードの最適化は困難である。　
    １度ゴールがスタックにコピーされたなら特別なアクションを取ることは難しい。　
    これは、ボディ（本体）コード中の安全でない変数に対してはぎこちない制御になる。

  - 選言肢についてもぎこちない制御になる（前記同じ理由により）

  - スタック上にある、ゴールの表現は、環境フレームモデルに比べてコンパクトさに欠ける。
    少なくとも、現時点での環境フレームモデルについての洗練化についてはそうである。（環境フレームは実行時に刈り込まれている）



　
　ゴールスタッキング方式では、安全でない変数を取り扱う場面で、ランタイム時に大量のチェック処理を行ってしまうために、深刻な性能問題になってしまう。  
一方、環境フレームスタッキングモデルでは、コンパイル時の分析により
必要なときにだけ特定の命令を生成することができ、安全でない変数の取り扱いを広汎に避けることができる。  
このような理由により、ゴールスタッキングモデルを捨てて、環境フレームスタッキングモデルを採用した。

　しかしながら、環境フレームスタッキングモデルは、初期の設計（ゴールスタッキングモデル）からかなり強い影響を受けた。  
そのことは、ソース言語レベルのゴールスタッキングの挙動から読み取ることができる。  
改めてこの観点から見ると、環境フレームはコンパイラにより合成された、節の末尾に対応するゴールになっている。

ある節を例にとり、このことを説明すると：

           P :- Q, R, S.

上記節は、以下のように変換される：

           P :- Q, Z1.
           Z1 :- R, Z2.
           Z2 :- S.

ここで、Z1,Z2は環境フレームの１つ先の状態に対応する。



### 11. 非決定的環境フレームをコピーすることの是非について

　今回のモデルでは、現在の環境フレームはスタックのトップに位置することは必須ではない。  
（スタックのトップの位置は）代りに、選択ポイントのサブシーケンスで「埋められる」ことになるだろう。  
環境フレームがその本来の位置を離れることは、スペースの節約と、コピーによるオーバヘッドを避けることになる。  
しかしながら、「埋められた」環境フレームをスタックのトップの位置にコピーすることにも、いくつもの利点を見出すことができる。

   - 永続変数や一時変数は、スタックのトップに対して、同じ方法でアクセスできるだろう。

   - 環境フレームは、（不要な変数を）刈り取ることと同じくらい変更を加えることができ、データサイズを削減できる。

   - 変数をデリファレンスするとき、これに変更を加えることが許される。
　　　（つまり、永続変数は一時変数と同じように取り扱うことができるだろう）

   - 全ての自己参照に対する（リロケーションが含まれる）環境フレームをコピーしておけば、
      大量のトレイル処理を避けることができるだろう。

   - メモリアクセスのランダム性が抑制され、ページングとスタックバッファリングのパフォーマンスが改善する。

　ソフトウェアによる実装を考えると、これらの利点がコピー処理によるオーバヘッドに勝るとは思えない。  
しかし、専用のファームウェアやハードウェアにより実装する場合に、改めてトレードオフを検討するとなると話しが違ってくるかもしれない。



### 12. 謝辞

　本作は、DEC社の外部研究許可により支援を受けました。  
特に、以下の方々の激励及び支援に感謝の意を表明します：ピータ、ジエッセル,
ニルス、二ルソン,　ダニエル、サガロウビッツ

【付録】
```
I.命令の概要

                HEAD                    BODY

PROCEDURAL      proceed                 execute P
                                        call P,N
                allocate                deallocate

GET/PUT         get_variable Xn,Ai      put_variable Xn,Ai
                get_variable Yn,Ai      put_variable Yn,Ai
                get_value Xn,Ai         put_value Xn,Ai
                get_value Yn,Ai         put_value Yn,Ai
                                        put_unsafe_value Yn,Ai
                get_constant C,Ai       put_constant C,Ai
                get_nil Ai              put_nil Ai
                get_structure F,Ai      put_structure F,Ai
                get_list Ai             put_list Ai

UNIFY           unify_void N
                unify_variable Xn
                unify_variable Yn
                unify_local_value Xn
                unify_local_value Yn
                unify_value Xn
                unify_value Yn
                unify_constant C
                unify_nil

INDEXING        try_me_else L           try L
                retry_me_else L         retry L
                trust_me else fail      trust L

                switch_on_term Lv,Lc,Ll,Ls
                switch_on_constant N,Table
                switch_on_structure N,Table
```


II. Prolog機械状態(ユニフィケーション実行時)
```
               stack                    heap                    trail
         :               :        :               :        :               :
         :               :        :               :        :               :
         |_______________| HB->H' |_______________|    TR' |_______________|
    p  c |            Am |        |               |        |               |
    o  h | goal       :  |        |               |        |  bound        |
    s  o | arguments  A2 |        |               |        |  variable     |
    s  i |____________A1_|        |               |        |  addresses    |
    i  c | contin.   BCE |        | structures    |        |               |
    b  e |___________BCP_|        |               |   TR ->|_______________|
    l    | backtrack  B' |        |               |
    e  P | state      BP |    H ->|_______________|
       t.|            TR'|
   E,B ->|____________H'_|
       e | contin.    CE |
       n |____________CP_|
       v |            Y1 |
       i | permanent  Y2 |
       r | variables  :  |
       o |            :  |
       n |____________Yn_|
       m
       e  _______________
       n |            X1 |
       t | temporary  :  |
         | variables  :  |
         |____________Xm'|
         |            Am |
         | goal       :  |
         | arguments  A2 |
    A  ->|____________A1_|
   (PDL) | unification   |
         | arguments     |
         :               :
```


III. スタック状態 (手続き呼出実行時)
```
         determinate call              nondeterminate call
         |               |             |               |
         |_______________|             |               |
         |               |         E ->|_______________|
         | choice point  |             |               |
     B ->|_______________|             | environment   |
         |               |             |               |
         |               |             |_______________|
     E ->|_______________|             |               |
         |               |             |_______________|
         | environment   |             |               |
         |               |             | choice point  |
         |_______________|         B ->|_______________|
```




IV. 実行時の構造体のフォーマット
```
         ENVIRONMENT                   STRUCTURE (COMPLEX TERM)
          _______________               _______________
         |  cont. env.   |  (CE)       |  functor      |
         |_______________|             |_______________|
         |  cont. code   |  (CP)       |  argument 1   |
         |_______________|             |    :          |
         |  variable 1   |  (Y1)       |    :          |
         |    :          |             |  arguments N  |
         |    :          |             |_______________|
         |  variable N   |  (Yn)
         |_______________|


         CHOICE POINT
          _______________
         |  goal arg. M  |  (Am)
         |    :          |
         |    :          |
         |  goal arg. 1  |  (A1)
         |_______________|
         |  cont. env.   |  (BCE)
         |_______________|
         |  cont. code   |  (BCP)
         |_______________|
         |  prev. choice |  (B')
         |_______________|
         |  next clause  |  (BP)
         |_______________|
         |  trail point  |  (TR')
         |_______________|
         |  heap point   |  (H')
         |_______________|
```


V. データフォーマット(仮)
```
        Value / Address                                                  Tag

bit:    32                                                             2     0
          ___________________________________________________________________
         |          reference address                                  | 0 0 |
         |_____________________________________________________________|_____|

          ___________________________________________________________________
         |          structure (or box) address                         | 0 1 |
         |_____________________________________________________________|_____|

          ___________________________________________________________________
         |          list address                                       | 1 0 |
         |_____________________________________________________________|_____|
        32                                                             2     0

          ___________________________________________________________________
         | + |      integer value                                    | 0 1 1 |
         |___|_______________________________________________________|_______|
        32  31                                                       3       0

          ___________________________________________________________________
         |          atom or functor number                           | 1 1 1 |
         |___________________________________________________________|_______|
        32                                                           3       0

         N.B. Key = Term<32:3>

          ___________________________________________________________________
         |          box "FRACTION"                                   | 1 1 1 |
         |___________________________________________________________|_______|
         |                                                                   |
         |__________floating point number____________________________________|
         |                                                                   |
         |___________________________________________________________________|
```

VI. 命令フォーマット（仮）

フォーマット中で"+"でマークされているものは、オペレーションコード（おそらく１バイトの引数の数により直ちに続いている（GET命令やPUT命令である場合に））である。  
このフォーマットで、"*"で
マークされているものは、必ずしも必須ではない最適化である。
```
           Op-Code  Argument
byte :   0         1         2         3         4         5
          _________
*        |   var   |
         |_________|

          ___________________
       + |   var   | number  |
         |_________|_________|

          _____________________________
*      + |  const  |  short value      |     (sign extended)
         |_________|___________________|

          _________________________________________________
       + |  const  |  long value                           |
         |_________|_______________________________________|

          _____________________________
       + |  struct |  functor no.      |
         |_________|___________________|

          _____________________________
         |  pred   |  procedure addr.  |     (an offset within the segment)
         |_________|___________________|

          _____________________________
         |  try    |  clause address   |     (an offset within the segment)
         |_________|___________________|

          _______________________________________
         |  switch |         |     table size    |
         |_________|_________|___________________|
         |  key              |  clause address   |   (an offset within the segment)
         |___________________|___________________|
         |                   |                   |
```


                                     References

1. D.L.Bowen, L.M.Byrd and W.F.Clocksin. A portable Prolog compiler. Logic
Programming Workshop '83, Universidade Nova de Lisoa, june, 1983, pp.74-83

2. M.Bruynooghe. A note on garbage collection in Prolog interpreters. First
International Logic Programming Conference, University of Marseille, September, 1982,
pp.52-55.

3. E.Tick. An overlapped Prolog processor. Artificial Intelligence Center, SRI
International, Menlo Park, California 924025,1983

4. D.H.D.Warren. Applied Logic -- its use and implementation as programming
tool. Ph.D.Th., University of Edinburgh, Scotland,1977. Available as Technical Note
290, Artificial Intelligence Center, SRI International.

5. D.H.D.Warren. An improved Prolog implementation which optimises tail
recursion. Research Paper 156, Dept. of Artificial Intelligence, University of Edinburgh,
Scotland, 1980. Presented at the 1980 Logic Programming Workshop, Debrecen,
Hungary.