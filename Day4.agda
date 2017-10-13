module Day4 where

open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

--
-- § 4. レコード型
--

--
-- § 4.1. レコード型の基本
--

--
-- レコード型は複数の値を1つにまとめて扱うことのできるデータ型です。例えば
-- 2つの自然数の組は以下のように定義できます。
--

record Point : Set where
  field
    x : ℕ
    y : ℕ

--
-- この宣言では、Point というデータ型と、Point.x 及び Point.y という2つの
-- 射影関数を定義しています。射影関数は、Point 型の値から対応する field を
-- 取り出す関数です。Point 型の値は record 式を用いて以下のように定義できます。
--

p₀ : Point
p₀ = record { x = 1; y = 2 }

--
-- レコード型の値から各 field の値を取り出すには射影関数を使います。Point 型
-- を定義したときに同時に Point.x と Point.y という関数も定義されるので、
-- それらを用いることで値を取り出すことができます。
--

p₀-x : ℕ
p₀-x = Point.x p₀

p₀-y : ℕ
p₀-y = Point.y p₀

--
-- レコード型では constructor キーワードを使ってコンストラクタに使う
-- シンタックスを指定することができます。
--

record Point′ : Set where
  constructor _,_
  field
    x : ℕ
    y : ℕ

p₁ : Point′
p₁ = 1 , 2

-- ==================================================================
-- Exercise: manhattan (★★)
-- Point 型の値を二次元平面上の点とみなし、マンハッタン距離を計算する関数を
-- 定義してください。絶対値を使おうとすると面倒になるので、うまく回避してくだ
-- さい。
--
-- ヒント:
--   まず一次元のマンハッタン距離を求める関数を定義してください。
-- ==================================================================

mht1 : ℕ → ℕ → ℕ
mht1 zero y = y
mht1 (suc x) zero = suc x
mht1 (suc x) (suc y) = mht1 x y

manhattan : Point → Point → ℕ
manhattan p q = mht1 (Point.x p) (Point.x q) + mht1 (Point.y p) (Point.y q)

-- ==================================================================
-- exercise: manhattan (★★★)
-- マンハッタン距離が対称的であることを証明してください。
-- ==================================================================

x≡mht1x0 : ∀ x → x ≡ mht1 x zero
x≡mht1x0 zero = refl
x≡mht1x0 (suc x) = refl

mht1-sym : ∀ x y → mht1 x y ≡ mht1 y x
mht1-sym zero y = x≡mht1x0 y
mht1-sym (suc x) zero = refl
mht1-sym (suc x) (suc y) = mht1-sym x y

mh-sym : ∀ p q → manhattan p q ≡ manhattan q p
mh-sym p q = begin
  manhattan p q
    ≡⟨ refl ⟩
  mht1 (Point.x p) (Point.x q) + mht1 (Point.y p) (Point.y q)
    ≡⟨ cong (λ x → x + mht1 (Point.y p) (Point.y q)) (mht1-sym (Point.x p) (Point.x q)) ⟩
  mht1 (Point.x q) (Point.x p) + mht1 (Point.y p) (Point.y q)
    ≡⟨ cong (λ x → mht1 (Point.x q) (Point.x p) + x) (mht1-sym (Point.y p) (Point.y q)) ⟩
  mht1 (Point.x q) (Point.x p) + mht1 (Point.y q) (Point.y p)
    ≡⟨ refl ⟩
  manhattan q p
    ∎

-- ==================================================================
-- exercise: tri-ineq (★★★★)
-- マンハッタン距離が三角不等式を満たすことを証明してください。ただし、この
-- 問題は面倒な上にレコード型の理解にあまり寄与しないので、スキップすることを
-- 推奨します。
-- ==================================================================

tri-ineq : ∀ {p q r} → manhattan p q + manhattan q r ≥ manhattan p r
tri-ineq = {!!}

--
-- § 4.2. 依存型を伴うレコード型
--

--
-- Agda は依存型が使えるので、レコードの各フィールドの型が、別のフィールドの値
-- に依存することができます。
--
-- 次のデータ型 Even はある自然数が偶数であることを表すデータ型です。
--

data Even : ℕ → Set where
  e-zero : Even zero
  e-suc  : ∀ {n} → Even n → Even (suc (suc n))

--
-- この Even を用いて、偶数のデータ型 Even-number をレコード型として次のように
-- 定義します。
--

record Even-number : Set where
  constructor _even-by_
  field
    n      : ℕ
    n-even : Even n

--
-- Even-number は自然数 n と n が偶数であることの証明をフィールドととしてもつ
-- レコード型です。n が偶数でなければ Even n は示せないため、Even-number は
-- 偶数全体の集合を表す型となります。
--

-- ==================================================================
-- Exercise: twice-e (★★)
-- 自然数を受け取り、それを2倍にする関数 twice-e を定義してください。ただし、
-- 返り値の型は Even-number であるようにしてください。
-- ==================================================================

twice-e : ℕ → Even-number
twice-e zero = zero even-by e-zero
twice-e (suc x) = suc (suc (Even-number.n twice-x)) even-by e-suc (Even-number.n-even twice-x)
  where twice-x = twice-e x

-- ==================================================================
-- Exercise: add-ee (★★)
-- 偶数を2つ受け取り、それらの和を返す関数 add-ee を定義してください。ただし、
-- 返り値の型は Even-number であるようにしてください。
-- ==================================================================

add-even : ∀ {n m} → Even n → Even m → Even (n + m)
add-even e-zero evenₘ                = evenₘ
add-even (e-suc evenₙ) e-zero        = e-suc (add-even evenₙ e-zero)
add-even (e-suc evenₙ) (e-suc evenₘ) = e-suc (add-even evenₙ (e-suc evenₘ))

add-ee : Even-number → Even-number → Even-number
add-ee (n₁ even-by n-even₁) (n₂ even-by n-even₂) = (n₁ + n₂) even-by add-even n-even₁ n-even₂

-- ==================================================================
-- Exercise: add-eo (★★★)
-- Even, Even-number と同様にしてある自然数が奇数であることを表す型 Odd 及び
-- 奇数の型 Odd-number を定義し、偶数と奇数を足して奇数を返す関数 add-eo を
-- 定義してください。
-- ==================================================================

data Odd : ℕ → Set where
  o-one : Odd (suc zero)
  o-suc : ∀ {n} → Odd n → Odd (suc (suc n))

record Odd-number : Set where
  constructor _odd-by_
  field
    n     : ℕ
    n-odd : Odd n

add-even-odd : ∀ {n m} → Even n → Odd m → Odd (n + m)
add-even-odd e-zero m             = m
add-even-odd (e-suc n₁) o-one     = o-suc (add-even-odd n₁ o-one)
add-even-odd (e-suc n₂) (o-suc m) = o-suc (add-even-odd n₂ (o-suc m))

add-eo : Even-number → Odd-number → Odd-number
add-eo (n₁ even-by n-even₁) (n₂ odd-by n-odd₂) = (n₁ + n₂) odd-by add-even-odd n-even₁ n-odd₂
