--
-- Agda では一つのファイルが一つのモジュールを表します。また、ある
-- ファイルで定義されているトップレベルのモジュールの名前はファイル名と
-- 一致している必要があります。したがって、ファイルの
-- 先頭には以下のようにファイル名と一致するモジュールを宣言するのが
-- 通例です。
--

module Basic where

--
-- Agda はそのままではほとんどなにもできません。真偽値やリストなどですら
-- 言語の組み込みの機能ではなく、自分で定義するか、ライブラリを利用する
-- 必要があります。
--
--
--
-- § 1. 真偽値
--
--
--
--
-- § 1.1. 真偽値と簡単な関数の定義
-- 
--
-- まずは真偽値を定義してみましょう。真偽値は真(=true)と偽(=false)という
-- ２つの値を要素にもつデータ型と考えられます。このようなデータ型は
-- 次のように定義することができます。
--

data 𝔹 : Set where  -- 𝔹 というデータ型を宣言する (𝔹 は \bb で入力)
  true  : 𝔹         -- 1つ目の値は true
  false : 𝔹         -- 2つ目の値は false

--
-- C-c C-l でファイルをロードすることができます。Agda で開発をする際は、
-- 定義を書き終わったり証明を書き終わったりしたときなど適当な
-- タイミングでファイルをロードする必要があります。
--
-- true や false はあくまで抽象的な要素であり、このままでは何の意味も
-- もちません。真偽値なので、否定をとる関数を考えてみましょう。関数は、
-- まず型を宣言し、次に具体的な振る舞いを記述することで定義できます。
--

neg : 𝔹 → 𝔹        -- 𝔹 を受け取り 𝔹 を返す関数 neg を宣言する
                   -- (→ は \r や \to などで入力)
neg true  = false  -- neg は true を受け取った場合 false を返す
neg false = true   -- neg は false を受け取った場合 true を返す

--
-- 値も関数と同じように型と値を分けて定義します。
--

neg-of-true : 𝔹         -- 𝔹 という型をもつ neg-of-true という値を定義する
neg-of-true = neg true  -- neg-of-true は neg true である

--
-- C-c C-n と打つと下に Expression: というプロンプトが現れ、そこに項を
-- 入力するとその項の正規形を計算することができます。試しに、C-c C-n
-- と打ったあとに neg-of-true と入力してみましょう。false と出力される
-- はずです。ただし、C-c C-n と入力する前に C-c C-l でファイルをロード
-- するのを忘れないようにしてください。
--
--
-- § 1.2. 真偽値に関する等しさの証明
--
--
-- true の否定が false と等しいことを証明してみましょう。
-- 等しさに関する証明を行う場合には、
-- Relation.Binary.PropositionalEquality という標準ライブラリの
-- モジュールを使う必要があります。モジュールをインポートするには
-- 以下のように記述します。
--

open import Relation.Binary.PropositionalEquality

--
-- Corry Howard 同型対応によると、証明を行うこととプログラムを書くことは
-- 等価な操作であるとみなすことができます。命題は型、証明はプログラム
-- (関数本体)と対応します。
--
--    命題 ⟺ 型
--    証明 ⟺ プログラム(関数本体)
--
-- 詳しくは ALM のスライドを参照してください。
--
-- Agda では証明と普通の関数は区別なく記述します。型の部分に命題、
-- 関数本体に証明を記述し、ファイルを読み込んでしてエラーがでなければ
-- 証明できたことになります。
--
-- a と b が等しいという命題(=型)は a ≡ b と書きます
-- (≡ は \equiv などで入力)。a と b が等しい場合、refl という
-- プログラムを与えることで証明することができます。
--

neg-of-true-is-false : neg true ≡ false -- neg true と false が等しいことを表す命題
neg-of-true-is-false = refl             -- neg true を計算すると false になるので、
                                        -- refl を与えることができる。

--
-- 以下では _≡_ の説明を記述します。この説明は、関係について理解したあとに
-- (§2.3 でやります)興味があれば読んでみてください。
--
module Explanation-of-≡ where
  -- 
  -- ある2つの項が等しいという関係はどのようにすれば定義できるでしょうか？
  -- 対象となる項の型を 𝔹 に限定して、𝔹 という型をもつ、ある2つの項が等しい
  -- という関係について考えてみましょう。
  --
  -- a, b を 𝔹 型の項とします。a ≡ b であるのは次の2つの場合です。
  -- 
  --    1. a と b がともに true
  --    2. a と b がともに false
  --
  -- この関係を _≡𝔹₁_ とすると、_≡𝔹₁_ は次のように定義できます。
  --
    
  data _≡𝔹₁_ : 𝔹 → 𝔹 → Set where
    refl-true  : true  ≡𝔹₁ true
    refl-false : false ≡𝔹₁ false

  ex₁ : neg (neg (neg true)) ≡𝔹₁ false
  ex₁ = refl-false

  --
  -- この関係 _≡𝔹₁_ は、以下によって定義される関係 _≡𝔹₂_ と同等です。
  --

  data _≡𝔹₂_ : 𝔹 → 𝔹 → Set where
    refl : (x : 𝔹) → x ≡𝔹₂ x

  ex₂ : neg (neg true) ≡𝔹₂ neg (false)
  ex₂ = refl true

  --
  -- さらに、refl の引数を implicit にすれば標準ライブラリの定義に近づきます。
  --

  data _≡𝔹_ : 𝔹 → 𝔹 → Set where
    refl : {x : 𝔹} → x ≡𝔹 x

  ex₃ : false ≡𝔹 neg true
  ex₃ = refl
  
  --
  -- refl の引数は命題から推論できる(はず)なので、implicit にしたほうが楽です。
  --
  -- 型もパラメータとして受け取るようにすれば、もうこれはほとんど _≡_ と同じです。
  -- 型も推論できる(はず)なので、implicit にしたほうが楽です。
  --

  data _≡′_ {A : Set} : A → A → Set where -- ′ は \' で入力
    refl : ∀ {x} → x ≡′ x

  ex₄ : neg false ≡′ true
  ex₄ = refl

--
-- § 1.3. 真偽値に関する命題の証明
--
--
-- ここでは、以下の命題 (A) を証明してみましょう。
--
--    「真偽値 b に neg を2回作用させた値は元の値に等しい」 -- (A)
--
--     (式で書くと、neg (neg b) と b が等しいということ)
-- 
-- まず、自然言語による証明を行い、その後でAgda を使って証明を行います。
-- Agda のような定理証明支援系を使う場合でも、先に紙とペンを使って証明を
-- 考えてみるのは重要です。
--
--    そのままでは neg (neg b) が計算できないので、b に関する場合分けを行い
--    証明する。
--
--    b が true の場合
--      neg (neg true) を計算する。neg true は false になるので
--      neg (neg true) は true である。これは true と等しいため、この場合はOK
--
--    b が false の場合
--      neg (neg false) を計算する。neg false は true になるので
--      neg (neg false) は false である。これは false と等しいため、この場合はOK
--
--    𝔹 の要素は true か false しか存在しないため、すべての場合を尽くしている。
--    したがって、証明終了である。
--
-- つづいて、Agda を使って (A) を証明します。まず、命題(=型)は次のように書けます
-- (∀ は \all などで入力)。
--
--    double-negate-elimination : ∀ (b : 𝔹) → neg (neg b) ≡ b
--    double-negate-elimination = ...
--
-- この命題(=型)は
--
--    任意の 𝔹 型の値 b について、neg (neg b) が b と等しい
--
-- ということを意味します。
--
-- この double-negate-elmination を例にして、Agda での証明の進め方を説明します。
--
--    1. 型を書き、関数本体は ? とします。
--
--       double-negate-elimination : ∀ (b : 𝔹) → neg (neg b) ≡ b
--       double-negate-elimination b = ?
--
--    2. ロードします。? の部分が { }0 に変化します(数字の部分は0じゃないかも)。
--
--       double-negate-elimination : ∀ (b : 𝔹) → neg (neg b) ≡ b
--       double-negate-elimination b = { }0
--
--    3. neg (neg b) はそれ以上計算できないので、このままでは証明が進みません。
--       計算できるようにするために、b について場合分けを行います。Agda では、
--       { }0 の穴の部分にカーソルを移動し、C-c C-c と打ったあと、場合分けしたい
--       対象(ここではb)を入力すると場合分けできます。
--     
--       動画: https://gyazo.com/34c1cf533ca9ea55d27dae82253c3c43
--
--       double-negate-elimination : ∀ (b : 𝔹) → neg (neg b) ≡ b
--       double-negate-elimination true = { }0
--       double-negate-elimination false = { }1
--
--    4. 1つ目の穴にカーソルを移動し、C-c C-, と打つと証明すべき命題が
--
--          Goal: true ≡ true
--
--       のように表示されます。この命題は ≡ の左辺と右辺が等しいので、
--       refl で証明することができます。カーソルの場所はそのままで
--       穴のなかに refl と書き、C-c C-r と打つと穴を埋めることができます。
--
--       動画: https://gyazo.com/e995c55f2dba81ed92f449d0e8560a98a TODO: fix
--
--       double-negate-elimination : ∀ (b : 𝔹) → neg (neg b) ≡ b
--       double-negate-elimination true = refl
--       double-negate-elimination false = { }1
--
--    5. 2つ目の穴も同様に refl で埋めることができます。すべての穴が埋まったら
--       証明終了です。
--
--       double-negate-elimination : ∀ (b : 𝔹) → neg (neg b) ≡ b
--       double-negate-elimination true = refl
--       double-negate-elimination false = refl
--
-- 上記 1. - 5. までの手順に従って、以下の穴を埋めてみてください。
--

double-negate-elimination : ∀ (b : 𝔹) → neg (neg b) ≡ b
double-negate-elimination b = {!!}

-- ======================================
-- Exercise: 1 star (and, or, xor, imply)
-- 論理積、論理和、排他的論理和、含意を計算する関数を書いてください。
-- ₁は\_1、₂は\_2 で入力できます。
-- ======================================

and : 𝔹 → 𝔹 → 𝔹
and b₁ b₂ = {!!}

or : 𝔹 → 𝔹 → 𝔹
or b₁ b₂ = {!!}

xor : 𝔹 → 𝔹 → 𝔹
xor b₁ b₂ = {!!}

imply : 𝔹 → 𝔹 → 𝔹
imply b₁ b₂ = {!!}

--
-- 関数が書けたら、確認として以下の定理を証明してください。
-- 証明が自明な場合は、穴にカーソルを移動して C-c C-a と打つと
-- Agda が自動で穴を埋めてくれます。
--

check-and₁ : and true false ≡ false
check-and₁ = {!!}

check-and₂ : and true true ≡ true
check-and₂ = {!!}

check-or₁ : or false true ≡ false
check-or₁ = {!!}

check-or₂ : or false false ≡ false
check-or₂ = {!!}

check-xor₁ : xor false true ≡ true
check-xor₁ = {!!}

check-xor₂ : xor false false ≡ false
check-xor₂ = {!!}

check-imply₁ : imply false true ≡ false
check-imply₁ = {!!}

check-imply₂ : imply false false ≡ true
check-imply₂ = {!!}

-- ===================================
-- Exercise: 2 star (ド・モルガンの法則)
-- ===================================

--
-- 型が推測可能な場合は型の記述(ここでは𝔹)を省略できます。
-- 型の記述を省略した場合、∀ は省略できません。
--

de-morgan-law₁ : ∀ b c → neg (or b c) ≡ and (neg b) (neg c)
de-morgan-law₁ b c = {!!}

de-morgan-law₂ : ∀ b c → neg (and b c) ≡ or (neg b) (neg c)
de-morgan-law₂ b c = {!!}

-- =========================
-- Exercise: 2 star (排中律)
-- =========================

excluded-middle : ∀ a → or a (neg a) ≡ true
excluded-middle a = {!!}

-- =============================
-- Exercise: 3 star (恒真命題の例)
-- =============================

tautology : ∀ a b c → imply (and (imply a b) (imply b c)) (imply a c) ≡ true
tautology a b c = {!!}

--
-- C-c C-c のコマンドは、場合分けの対象を複数受け付けることができます。
-- 動画: https://gyazo.com/0270c7e3653b0e3f8f9f28c753635aa1
-- 

--
--
-- § 2. 自然数
--
--
--
--
-- § 2.1. 自然数と足し算の定義
--
-- 自然数とは 0 以上の整数の集合です。Agda では次のようなデータ型として
-- 帰納的に定義することができます。
--

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ      -- 自然数 ℕ を受け取り、自然数 ℕ を返すコンストラクタ

--
-- zero はそのまま 0 ですが、suc とはなんでしょうか。この定義では、1, 2, 3 は
-- それぞれ以下のように表されます。
--

one : ℕ
one = suc zero

two : ℕ
two = suc (suc zero)

three : ℕ
three = suc (suc (suc zero))

--
-- suc x は x の次の自然数を意味します(suc は successor の略)。
-- 自然数 n は、zero の後に suc が n 個ついた値と対応します。
--

-- ====================
-- Exercise: 1 star (seven)
-- 7 を定義してください。
-- ====================

seven : ℕ
seven = {!!}

--
-- この定義のもとで、自然数同士の足し算は次のように定義されます。
--

_+_ : ℕ → ℕ → ℕ
zero    + m = m
(suc n) + m = suc (n + m)

-- #
-- # ちょっと寄り道: mixfix について
-- #    ここで定義した _+_ を mixifix と呼びます。mixifix のオペレータは、
-- #    _ の部分で引数を受け取ることができます。
-- #

four : ℕ
four = two + two -- C-c C-n で four を表示してみてください

-- #
-- #    mixfix でオペレータを定義した場合、結合性や優先順位を明示的に与えないと
-- #    Agda が構文解析に失敗する場合があります。
-- #    以下の命令は _+_ を左結合、優先順位 5 とすることを宣言します。
-- #

infixl 5 _+_

-- #
-- #    右結合の場合は infixr、結合性を明示しない場合は infix を使います。
-- #    優先順位の値は、大きい方が強く結合します。
-- #
-- #    mixfix は _ を3個以上使うことができます。例えば、Agda では if 式は
-- #    以下のように定義されます。
-- #

if_then_else_ : {A : Set} → 𝔹 → A → A → A
if true  then x else y = x
if false then x else y = y

--
-- _+_ の定義にしたがうと、2 + 1 は以下のように計算されます。
-- 2 がどのように変化しているかに注目してください。
-- 
--    suc (suc zero) + suc zero = suc (suc zero + suc zero)
--   ^^^^^^^^^^^^^                    ^^^^^^^^
--                              = suc (suc (zero + suc zero)
--                                         ^^^^
--                              = suc (suc (suc zero))
--
-- 計算が進むにつれて 2 についていた suc が外側に移り、最終的に 0 に
-- なっています。suc (suc (suc zero)) は 3 に対応するので、正しく
-- 計算できていることがわかります。
--
--
-- § 2.2 自然数に関する証明
--
--

-- ============================
-- Exercise: 2 star (0 + n = n)
-- 自然数 n に左から 0 を足した結果は n に等しいことを証明してください。
-- ============================

0+n≡n : ∀ n → zero + n ≡ n
0+n≡n n = {!!}

-- #
-- # ちょっと寄り道: 命題の名前について
-- #    Agda では命題の名前として 0+n≡n のように命題から空白を取り除いた文字列
-- #    を使うことがよくあります。名前が思いつかないときに便利です。
-- #

-- ============================
-- Exercise: 3 star (n + 0 = n)
-- 自然数 n に右から 0 を足した結果は n に等しいことを証明してください
-- (この節で説明するので、少し考えてみたあとで飛ばしてください)。
-- ============================

n+0≡n-first-attempt : ∀ n → n + zero ≡ n
n+0≡n-first-attempt n = {!!}

--
-- ここでは、ある自然数 n に右から 0 を足した結果は n に等しいことを証明します。
-- これはほとんど自明なことのように思えますが、実は左から 0 を足す場合に比べて
-- 自明ではありません。
--
-- _+_ の定義を思い出してください。_+_ は1つ目の引数に関してパターンマッチを
-- 行い、計算を進めます。zero + n の場合は、パターンマッチの1つ目のケースに
-- 該当するため、計算を進めることができました。ですが、n + zero の場合には、
-- どちらのケースに該当するか分からないため、計算を進めることができません。
-- したがって、このままでは証明ができないということになります。
--
-- n+0≡n の証明は、真偽値でおこなったのと同様に場合分けをすることでできます。
-- まず、自然言語による証明を考えてみましょう。
--
--    n + zero が n に等しいことを n に関する場合分けで証明する。
--   
--    n = zero の場合
--      zero + zero は zero と計算されるので、この場合はOK
--
--    ある自然数 m について n = suc m である場合
--      suc m + zero は suc (m + zero) と計算されるが、これは
--      suc m (= n) とは等しくない
--
--    n = suc m の場合に証明できなかったので、失敗
--
-- ナイーブな場合分けだと失敗してしまいます。失敗した n = suc m の場合を
-- 考えてみると、m + zero と m が等しいことがわかれば証明できそうです。
-- 自然数に関する帰納法の原理を用いると、この命題が証明できます。
--
--    n + zero が n に等しいことを n に関する帰納法で証明する。
-- 
--    n = zero の場合
--      zero + zero は zero と計算されるので、この場合はOK
--
--    ある自然数 m について n = suc m である場合
--      suc m + zero は suc (m + zero) と計算される。
--      帰納法の仮定より、m + zero と m は等しいため、suc (m + zero) と suc m
--      が等しいことが導かれる。よって、この場合もOK
--
--    以上より、任意の自然数 n について n + zero と n が等しいことが証明できた。
--
-- ところで、m + zero と m が等しいときに、suc (m + zero) と suc m
-- が等しいのはなぜでしょうか。なんとなく正しそうに思えますが、実はこれも
-- 証明が必要です。より一般に、任意の n と m について、n と m が等しい
-- ときに suc n と suc m が等しいことは、Agda では次のように証明できます。
--
-- まず、命題は次のように書けます。
--    
--    cong-suc : ∀ n m → n ≡ m → suc n ≡ suc m
--    cong-suc n m eq = {!!}
--
-- ここで、n と m について場合分けするのではなく、eq について場合分けします。
-- すると、次のように変化します。
--
--    cong-suc : ∀ n m → n ≡ m → suc n ≡ suc m
--    cong-suc n .n refl = {!!}
--
-- 突然 .n というものが現れましたが、これは何でしょうか。n ≡ m 型の値について
-- 場合分けすると、n ≡ m のコンストラクタは refl しか存在しないため、eq が
-- あった場所は refl で置き換わります。refl というコンストラクタが存在する場合、
-- n と m は同じものであることが要求されます。実際、次のプログラムをロード
-- すると型検査に失敗しエラーになります。
-- 
--    cong-suc : ∀ n m → n ≡ m → suc n ≡ suc m
--    cong-suc n m refl = {!!}
--
--    >> agda-handson/Day1/Basic.agda:520,14-18
--    >> n != m of type ℕ
--    >> when checking that the pattern refl has type n ≡ m
--
-- refl が n ≡ m という型を持つことができないため、エラーになっています。
-- (n と m は別々の値である可能性がある)
-- 型検査によってある引数の値が推論される場合、その値の前には . が付きます。
-- refl の型は ○ ≡ ○ という形をしているので、m は n と同じものと推論され、
-- 結果として m の場所には .n が来ることになります。
--
-- 以下の補題を証明してください。
-- 

cong-suc : ∀ n m → n ≡ m → suc n ≡ suc m
cong-suc n m eq = {!!}

--
-- Agda では、帰納法の仮定を用いることは再帰することに対応します。
-- n+0≡n は次のように証明できます。
--

n+0≡n : ∀ n → n + zero ≡ n
n+0≡n zero    = refl
n+0≡n (suc n) =
  cong-suc (n + zero) n (n+0≡n n) -- ここで帰納法の仮定を用い、
                                  -- n + zero ≡ n を証明を得ている。
                                  -- さらに cong-suc を用いることで、
                                  -- ≡ の両辺に suc を適用して
                                  -- suc (n + zero) ≡ suc n
                                  -- を得ている。

-- ========================================
-- Exercise: 3 star (_+_ の交換法則、結合法則)
-- ========================================

+-comm : ∀ n m → n + m ≡ m + n
+-comm = {!!}

+-assoc : ∀ n m o → n + m + o ≡ n + (m + o)
+-assoc = {!!}

--
-- § 2.3 関係の定義、及び関係に関する帰納法
--
-- m ≤ n という関係を定義してみましょう。この関係は、たとえば以下のように
-- 定義できます。
--
--    1. 任意の n について、0 ≤ n である
--    2. m ≤ n ならば、suc m ≤ suc n である
--

data _≤_ : ℕ → ℕ → Set where
  z≤n : (n : ℕ)                 → zero  ≤ n
  s≤s : (m n : ℕ) (m≤n : m ≤ n) → suc m ≤ suc n  -- (m n : ℕ) のように型をまとめて
                                                 -- 記述することもできる。

-- ===================================
-- Exercise: 1 star (_≤_ の練習)
-- 以下の命題を証明してください。
-- ===================================

0≤1 : zero ≤ one
0≤1 = {!!}

0≤2 : zero ≤ two
0≤2 = {!!}

1≤2 : one ≤ two
1≤2 = {!!}

4≤7 : four ≤ seven
4≤7 = {!!}

-- ==========================================================
-- Exercise: 3 star (n は n 以上)
-- 任意の自然数 n について、n が n 以上であることを証明してください。
-- ==========================================================

n≤n : ∀ n → n ≤ n
n≤n n = {!!}

--
-- 次の命題を考えてみましょう。
--
--    n≤m⇒n≤sm : ∀ n m → n ≤ m → n ≤ suc m
--    n≤m⇒n≤sm = ?
-- 
-- この命題に関しては、実は n (と m) に関する帰納法ではなく、n ≤ m に
-- 関する帰納法を使った方が簡単に証明できます。
--
--
--
--


-- y ≤ x + y    (s≤s ... s≤s (z≤n x))
-- ...
-- 2 ≤ x + 2    (s≤s (s≤s (z≤n x)))
-- 1 ≤ x + 1    (s≤s (z≤n x))
-- 0 ≤ x        (z≤n x)


n≤m⇒n≤sm : ∀ n m → n ≤ m → n ≤ suc m
n≤m⇒n≤sm .zero m (z≤n .m) = z≤n (suc m)
n≤m⇒n≤sm .(suc m) .(suc n) (s≤s m n n≤m) = s≤s m (suc n) (n≤m⇒n≤sm m n n≤m)

--
-- ところで、関係 _≤_ は次のようにも定義できます。以下の定義 _≤′_ と
-- _≤_ は実は等価な関係です。
--

data _≤′_ : ℕ → ℕ → Set where
  ≤′-refl : ∀ {m}                   → m ≤′ m
  ≤′-step : ∀ {m n} (m≤′n : m ≤′ n) → m ≤′ suc n

-- ===================================
-- Exercise: 1 star (_≤′_ の練習)
-- 以下の命題を証明してください。
-- ===================================

0≤′1 : zero ≤′ one
0≤′1 = {!!}

0≤′2 : zero ≤′ two
0≤′2 = {!!}

1≤′2 : one ≤′ two
1≤′2 = {!!}

4≤′7 : four ≤′ seven
4≤′7 = {!!}

-- ===========================================================
-- Exercise: 3 star (0 ≤′ n)
-- 任意の自然数 n について、_≤′_ の定義のもとで n が 0 以上であること
-- を証明してください。
-- ===========================================================

0≤′n : ∀ n → zero ≤′ n
0≤′n n = {!!}

n≤′m⇒sn≤′sm : ∀ n m → n ≤′ m → suc n ≤′ suc m
n≤′m⇒sn≤′sm n m n≤′m = {!!}

-- =============================================
-- Exercise: 4 star (_≤_ と _≤′_ が等価であること)
-- _≤_ と _≤′_ が等価であることを証明してください。
-- =============================================

n≤m⇒n≤′m : ∀ n m → n ≤ m → n ≤′ m
n≤m⇒n≤′m n m n≤m = {!!}

n≤′m⇒n≤m : ∀ n m → n ≤′ m → n ≤ m
n≤′m⇒n≤m n m n≤′m = {!!}

--
--
-- § 3. レコード TODO: write
--
--

record Point : Set where
  field
    x : ℕ
    y : ℕ

record Point-◸ : Set where
  field
    x : ℕ
    y : ℕ
    x≤y : x ≤ y

record _×_ {A : Set} {B : Set} : Set where
  constructor _,_
  field
    inj₁ : A
    inj₂ : B

-- with
-- ×
