module Day5 where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

--
-- Day5 では Odd や manhattan が必要なため Day4-answer を使います。
-- 自身の解答と異なるかもしれないのであらかじめ Day4-answer を確認しておくか、
-- あるいは Day4 を import するのをやめて自分の解答を使っても良いです。
--

open import Day4-answer

--
-- § 5. Absurd pattern
--

--
-- Even 1 という型を考えてみます。Even の定義から、Even 1 には e-zero も
-- e-suc もコンストラクタとして不適当であることが分かります。このように対応する
-- コンストラクタが存在しないような型を引数として受け取る場合、引数のところに ()
-- を記述し、右辺を省略する書き方ができます。これを absurd pattern と言います。
--

one-not-even : ∀ {A : Set} → Even 1 → A
one-not-even ()

--
-- Even 1 に対応する値は存在しないので、one-not-even を関数として使おうとしても
-- 引数を与えることができません。そのため、右辺を記述する必要はないのです。
--
-- 次に、コンストラクタを1つも持たないデータ型を考えます。
--

data ⊥ : Set where

--
-- ⊥ もコンストラクタが存在しないので、one-not-even と同様の命題が証明できます。
--

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

--
-- ある命題 P が真であることは、P という型をもつ値が定義できることと同値でした。
-- P が偽であることについてはどうでしょうか。直観主義論理(より正確には BHK 解釈)
-- では、P が偽であることは P → ⊥ という型に対応する命題として解釈されます。
-- P に証明が存在する場合、P → ⊥ という型をもつ関数は記述できません。⊥ には
-- コンストラクタがないため、返すべき値が存在しないからです。P が偽であることと、
-- P の証明が存在しないことはほぼ同じ意味になります。
--

¬_ : Set → Set
¬ P = P → ⊥

-- ==================================================================
-- Exercise: no-even (★★)
-- 任意の自然数 k について k * 2 + 1 が偶数ではないことを証明してください。
-- ==================================================================

no-even : ∀ k → ¬ Even (k * 2 + 1)
no-even zero ()
no-even (suc k) (e-suc x) = no-even k x

-- ==================================================================
-- Exercise: no-odd (★★)
-- 任意の自然数 k について k * 2 が奇数ではないことを証明してください。
-- ==================================================================

no-odd : ∀ k → ¬ Odd (k * 2)
no-odd zero ()
no-odd (suc k) (o-suc x) = no-odd k x

--
-- 2つの型の組を作るレコード型 _×_ は次のように定義されます。この _×_ は
-- 論理積として解釈され、A × B という型は A かつ B という命題を意味します。
--

infix 4 _,_
infix 2 _×_

record _×_ (A : Set) (B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

--
-- 簡単な命題の組を定義してみます。
--

1x2 : 1 ≡ 1 × 2 ≡ 2 -- 1 と 1 が等しいかつ、2 と 2 が等しいという命題
1x2 = refl , refl

--
-- 注意として、コンストラクタ _,_ は今まで定義してきたような _+_ などと同じ
-- ように、前後に空白が必要です。例えば次のように書くとエラーになります。
-- この場合は、2, が何らかの値であると解釈されてしまいます。
--
--   2x3 : ℕ × ℕ
--   2x3 = 2, 3
--
-- _×_ は標準ライブラリだと Data.Product で（似たような形で）定義されています。
--

-- ==================================================================
-- Exercise: no-odd (★★)
-- 任意の自然数 k について k が同時に偶数かつ奇数とはならないことを証明して
-- ください。
-- ==================================================================

no-eo : ∀ k → ¬ (Even k × Odd k)
no-eo zero (e-zero , ())
no-eo (suc zero) (() , _)
no-eo (suc (suc k)) (e-suc e , o-suc o) = no-eo k (e , o)

--
-- 引数をうまく使って ⊥ が作れるとき、absurd pattern と with pattern を
-- 組み合わせて元の命題を証明することができます。
--

pnnp : ∀ {P Q : Set} → P → (P → ⊥) → Q
pnnp p np with np p
... | ()

-- ==================================================================
-- Exercise: cp (★★)
-- 次の命題を証明してください。
-- ==================================================================

cp : ∀ {P Q R : Set} → (P → Q) → (Q → ⊥) → P → R
cp pq qb p with qb (pq p)
... | ()

-- ==================================================================
-- Exercise: dne (★★★)
-- 次の命題を証明してください。
-- ==================================================================

dne : ∀ {P Q : Set} → (((P → ⊥) → ⊥) → ⊥) → P → Q
dne a p with a (λ x → x p)
... | ()

-- a : ((P → ⊥) → ⊥) → ⊥
-- λx → ⋯ : (P → ⊥) → ⊥
-- x : P → ⊥
-- (((P → ⊥) → ⊥) → ⊥) ≡ ¬ (¬ (¬ P))

--
-- 論理積に対応する型は _×_ でしたが、一方論理和に対応する型は次のように
-- 定義される _⊎_ です（\uplus で入力）。
--

data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

--
-- A という命題もしくは B という命題のいずれかが証明できれば A ⊎ B という命題も
-- 証明できるということを意味しています。例えば、1 は偶数であるか奇数であるかの
-- いずれかなので、次の命題は成り立ちます。
--

eo-one : Even 1 ⊎ Odd 1
eo-one = inj₂ o-one

--
-- この場合 Even 1 は証明できませんが、Odd 1 が証明できるので Even 1 ⊎ Odd 1
-- は証明可能です。同様にして 2 が偶数あるいは奇数のいずれかであることも証明でき
-- ます。
--

eo-two : Even 2 ⊎ Odd 2
eo-two = inj₁ (e-suc e-zero)

--
-- この場合 Odd 2 は証明できませんが、Even 2 が証明できるので Even 2 ⊎ Odd 2
-- は証明可能です。
--

-- ==================================================================
-- Exercise: eo-k (★★)
-- 任意の自然数が偶数あるいは奇数であることを証明してください。
-- ==================================================================

eo-k : ∀ k → Even k ⊎ Odd k
eo-k zero = inj₁ e-zero
eo-k (suc zero) = inj₂ o-one
eo-k (suc (suc k)) = add2 (eo-k k)
  where
    add2 : ∀ {k} → Even k ⊎ Odd k → Even (suc (suc k)) ⊎ Odd (suc (suc k))
    add2 (inj₁ e) = inj₁ (e-suc e)
    add2 (inj₂ o) = inj₂ (o-suc o)

-- ==================================================================
-- Exercise: classic (★★)
-- 次の命題を証明してください。
-- ==================================================================

classic : ∀ {P : Set} → P ⊎ (P → ⊥) → ((P → ⊥) → ⊥) → P
classic (inj₁ p) not-not-p = p
classic (inj₂ not-p) not-not-p = ⊥-elim (not-not-p not-p)

-- ==================================================================
-- Exercise: loem (★★★)
-- 次の命題を証明してください。
-- ==================================================================

loem : ∀ {P Q : Set} → ((P ⊎ (P → ⊥)) → ⊥) → Q
loem x = ⊥-elim (x (inj₂ (λ x₁ → x (inj₁ x₁))))

-- ==================================================================
-- Exercise: mh-id (★★★)
-- 再びマンハッタン距離の例に戻ります。ある2点間のマンハッタン距離が 0 ならば
-- その2点は同一であることを示してください。
-- ==================================================================

+-zero : ∀ n m → n + m ≡ 0 → n ≡ 0 × m ≡ 0
+-zero = {!!}

mh₀-id : ∀ p q → manhattan₀ p q ≡ 0 → p ≡ q
mh₀-id zero zero _ = refl
mh₀-id zero (suc q) ()
mh₀-id (suc p) zero ()
mh₀-id (suc p) (suc q) e = cong suc (mh₀-id p q e)

px≡py×qx≡qy→p≡q : ∀ {p q} → Point.x p ≡ Point.x q × Point.y p ≡ Point.y q → p ≡ q
px≡py×qx≡qy→p≡q {record { x = _ ; y = _ }} {record { x = x ; y = y }} (refl , refl) = refl

mh-id : ∀ p q → manhattan p q ≡ 0 → p ≡ q
mh-id record { x = x₀ ; y = y₀ } record { x = x₁ ; y = y₁ } e =
  {!!}
  where
    foo : manhattan₀ x₀ x₁ ≡ 0 × manhattan₀ y₀ y₁ ≡ 0
    foo = +-zero (manhattan₀ x₀ x₁) (manhattan₀ y₀ y₁) e
    bar : x₀ ≡ x₁
    bar = mh₀-id x₀ x₁ (_×_.proj₁ foo)
    buzz : y₀ ≡ y₁
    buzz = mh₀-id y₀ y₁ (_×_.proj₂ foo)

{-
mh₀-id : ∀ p q → manhattan₀ p q ≡ 0 → p ≡ q
mh₀-id zero zero _ = refl
mh₀-id zero (suc q) ()
mh₀-id (suc p) zero ()
mh₀-id (suc p) (suc q) e = cong suc (mh₀-id p q e)

y≡0→mhₓ≡0 : ∀ x₀ x₁ → manhattan record { x = x₀ ; y = zero } record { x = x₁ ; y = zero } ≡ 0 → manhattan₀ x₀ x₁ ≡ 0
y≡0→mhₓ≡0 x₀ x₁ e = begin
    manhattan₀ x₀ x₁
  ≡⟨ {!x+0≡0→x≡0 e!} ⟩
    0
  ∎
  where
    open ≡-Reasoning
    x+0≡0→x≡0 : ∀ x → x + zero ≡ zero → x ≡ 0
    x+0≡0→x≡0 zero x₂ = refl
    x+0≡0→x≡0 (suc x) ()

mh0→mh₀0 : ∀ p q → manhattan p q ≡ 0 → manhattan₀ (Point.x p) (Point.x q) ≡ 0 × manhattan₀ (Point.y p) (Point.y q) ≡ 0
mh0→mh₀0 record { x = zero ; y = zero } record { x = zero ; y = zero } e = refl , refl
mh0→mh₀0 record { x = zero ; y = y₀ } record { x = zero ; y = y₁ } e = refl , e
mh0→mh₀0 record { x = x₀ ; y = zero } record { x = x₁ ; y = zero } e = y≡0→mhₓ≡0 x₀ x₁ e , refl
mh0→mh₀0 record { x = (suc x₀) ; y = (suc y₀) } record { x = (suc x₁) ; y = (suc y₁) } e = {!!}
mh0→mh₀0 _ _ ()
-}
