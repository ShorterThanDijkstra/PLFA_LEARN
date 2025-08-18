module part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; subst)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ} → zero ≤ n

  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero

inv-z≤n z≤n = refl

{-
自然数上同余关系 : Reflexive, Transitive, not Anti-symmertric
自然数上的整除关系 : Reflexive, Transitive, not Total
-}

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n { zero }
≤-refl {suc n} = s≤s {n} {n} (≤-refl {n})

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans {zero} {n} {p} (z≤n {n}) _ = z≤n {p}
≤-trans {suc m} {suc n} {suc p} (s≤s {m} {n} m≤n) (s≤s {n} {p} n≤p) = s≤s {m} {p} (≤-trans {m} {n} {p} m≤n n≤p)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym (z≤n {zero}) (z≤n {zero}) = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where

  forward : m ≤ n → Total m n

  flipped : n ≤ m → Total m n

data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ} → m ≤ n → Total′ m n

  flipped′ : ∀ {m n : ℕ} → n ≤ m → Total′ m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward (z≤n {n})
≤-total (suc m) zero = flipped (z≤n {(suc m)})
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)

≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m       zero                      =  flipped z≤n
≤-total″ zero    (suc n)                   =  forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
...                         | forward m≤n  =  forward (s≤s m≤n)
...                         | flipped n≤m  =  flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ} → zero < suc n

  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data Tricho (m n : ℕ) : Set where

  lt : m < n → Tricho m n

  gt : n < m → Tricho m n

  eq : m ≡ n → Tricho m n

<-tricho : ∀ (m n : ℕ) → Tricho m n
<-tricho zero zero = eq refl
<-tricho zero (suc n) = lt z<s
<-tricho (suc m) zero = gt z<s
<-tricho (suc m) (suc n) with <-tricho m n
...                         | lt m<n = lt (s<s m<n)
...                         | eq m≡n = eq (cong suc m≡n)
...                         | gt n<m = gt (s<s n<m)

+-mono-<ʳ : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-mono-<ʳ zero p q p<q = p<q
+-mono-<ʳ (suc n) p q p<q = s<s (+-mono-<ʳ n p q p<q)

+-mono-<ˡ : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-mono-<ˡ m n p m<n rewrite (+-comm m p) | (+-comm n p) = +-mono-<ʳ p m n m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-mono-<ˡ m n p m<n) (+-mono-<ʳ n p q p<q)

≤→< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤→< 0 (suc n) (s≤s m≤n) = z<s
≤→< (suc m) (suc n) (s≤s m≤n) = s<s (≤→< m n m≤n)

<→≤ : ∀ (m n : ℕ) → m < n → suc m ≤ n
<→≤ 0 (suc n) z<s = s≤s (z≤n)
<→≤ (suc m) (suc n) (s<s m<n) = s≤s (<→≤ m n m<n)

sm<p→m<p : ∀ (m n : ℕ) → suc m < n → m < n
sm<p→m<p zero (suc n) _ = z<s
sm<p→m<p (suc m) (suc n) (s<s sm<n) = s<s (sm<p→m<p m n sm<n)

<-trans-revisited : ∀ (m n p : ℕ) → m < n → n < p → m < p
<-trans-revisited m n p m<n n<p =
  let sm≤n : suc m ≤ n
      sm≤n = <→≤ m n m<n

      sn≤p : suc n ≤ p
      sn≤p = <→≤ n p n<p

      ssm≤sn : suc (suc m) ≤ suc n
      ssm≤sn = s≤s sm≤n

      ssm≤p : suc (suc m) ≤ p
      ssm≤p = ≤-trans ssm≤sn sn≤p

      sm<p : (suc m) < p
      sm<p = ≤→< (suc m) p ssm≤p
   in sm<p→m<p m p sm<p

data even : ℕ → Set

data odd  : ℕ → Set

data even where

  zero : even zero

  suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where

  suc : ∀ {n : ℕ} → even n → odd (suc n)


e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero zero = zero
e+e≡e zero (suc o) = suc o
e+e≡e (suc o) e  =  suc (o+e≡o o e)

o+e≡o (suc e1) e2 = suc (e+e≡e e1 e2)


o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd (m + n)

o+o≡e (suc em) on = suc (e+o≡o em on)

e+o≡o zero (suc en) = suc en
e+o≡o (suc om) (suc en) = suc (o+o≡e om  (suc en))

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to   : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = (from b) * 2
from (b I) = (from b) * 2 + 1

data One : Bin → Set where
  one : One (⟨⟩ I)
  ones-zero : ∀ {b : Bin} → One b → One (b O)
  ones-one : ∀ {b : Bin} → One b → One (b I)

data Can : Bin → Set where
  can-zero : Can (⟨⟩ O)
  can : ∀ {b : Bin} → One b → Can b

inc-one : ∀ {b : Bin} → One b → One (inc b)
inc-one one = ones-zero one
inc-one (ones-zero ob) = ones-one ob
inc-one (ones-one ob) = ones-zero (inc-one ob)

can→can-inc : ∀ {b : Bin} → Can b → Can (inc b)
can→can-inc can-zero = can one
can→can-inc (can (one)) = can (ones-zero (one))
can→can-inc (can (ones-zero ob)) = can (ones-one ob)
can→can-inc (can (ones-one ob)) = can (ones-zero (inc-one ob))

can-to-n : ∀ {n : ℕ} → Can (to n)
can-to-n {zero} = can-zero
can-to-n {suc n} = can→can-inc (can-to-n {n})

n≤n*2 : ∀ {n : ℕ} → n ≤ n * 2
n≤n*2 {zero} = z≤n
n≤n*2 {(suc n)} = s≤s (+-mono-≤ 0 1 n (n * 2) z≤n n≤n*2)

one-b→1≤from-b : ∀ {b : Bin} → One b → 1 ≤ from b
one-b→1≤from-b one = (s≤s z≤n)
one-b→1≤from-b {b O}(ones-zero ob) = ≤-trans (one-b→1≤from-b ob) (n≤n*2 {from b})
one-b→1≤from-b {b I} (ones-one ob) rewrite (+-comm (from b * 2) 1) = let 1≤from-b : 1 ≤ from b
                                                                         1≤from-b = one-b→1≤from-b ob

                                                                         from-b≤from-b*2 : from b ≤ from b * 2
                                                                         from-b≤from-b*2 = n≤n*2

                                                                         1≤from-b*2 : 1 ≤ from b * 2
                                                                         1≤from-b*2 = ≤-trans (1≤from-b) (from-b≤from-b*2)

                                                                         0≤from-b*2 : 0 ≤ from b * 2
                                                                         0≤from-b*2 = ≤-trans z≤n 1≤from-b*2
                                                                     in s≤s 0≤from-b*2

1≤n→to-2n≡to-n-0 : ∀ {n : ℕ} → 1 ≤ n → to (n * 2) ≡ (to n) O
1≤n→to-2n≡to-n-0 {suc zero} _ = refl
1≤n→to-2n≡to-n-0 {suc (suc n)} (s≤s 1≤n) = {!!}

can-b→to-from-b≡b : ∀ {b : Bin} → Can b → to (from b) ≡ b
can-b→to-from-b≡b can-zero = refl
can-b→to-from-b≡b (can (one)) = refl
can-b→to-from-b≡b {b O} (can (ones-zero ob)) =
   begin
     to (from (b O))
   ≡⟨⟩
     to ((from b) * 2)
   ≡⟨ (1≤n→to-2n≡to-n-0 (one-b→1≤from-b ob)) ⟩
     (to (from b)) O
   ≡⟨ cong _O (can-b→to-from-b≡b (can ob)) ⟩
     b O
   ∎
can-b→to-from-b≡b {b I} (can (ones-one ob)) =
  begin
    to (from (b I))
  ≡⟨⟩
    to ((from b) * 2 + 1)
  ≡⟨ cong to (+-comm ((from b) * 2) 1) ⟩
    to (1 + (from b) * 2)
  ≡⟨⟩
    to (suc ((from b) * 2))
  ≡⟨⟩
    inc (to ((from b) * 2))
  ≡⟨ cong inc (1≤n→to-2n≡to-n-0 (one-b→1≤from-b ob)) ⟩
    inc ((to (from b)) O)
  ≡⟨⟩
    (to (from b)) I
  ≡⟨ cong _I (can-b→to-from-b≡b (can ob)) ⟩
    b I
  ∎
