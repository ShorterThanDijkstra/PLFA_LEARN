module part1.Induction where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m  n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ≡⟨⟩
    m + (n + p) + q
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc m) rewrite +-identity′ m = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

+-assoc″ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc″ zero n p = refl
+-assoc″ (suc m) n p rewrite +-assoc″ m n p = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p =
  begin
    (zero + n) * p
  ≡⟨⟩
    n * p
  ≡⟨⟩
    zero + n * p
  ≡⟨⟩
    zero * p + n * p
  ∎

*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    (suc (m + n)) * p
  ≡⟨⟩
    p + ((m + n) * p)
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    p + m * p + n * p
  ≡⟨⟩
    (suc m) * p + n * p
  ∎

*-zero : ∀ (n : ℕ) → n * zero ≡ zero
*-zero zero = refl
*-zero (suc n) =
  begin
    (suc n) * zero
  ≡⟨⟩
    zero + n * zero
  ≡⟨ cong (zero +_) (*-zero n) ⟩
    zero + zero
  ≡⟨⟩
    zero
  ∎

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p =
  begin
    (zero * n) * p
  ≡⟨⟩
    zero * p
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero * (n * p)
  ∎
*-assoc (suc m) n p =
  begin
    ((suc m) * n) * p
  ≡⟨⟩
    (n + (m * n)) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + (m * n) * p
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    n * p + m * (n * p)
  ≡⟨⟩
    (suc m) * (n * p)
  ∎

*-identityʳ : ∀ (m : ℕ) → m * 1 ≡ m
*-identityʳ zero = refl
*-identityʳ (suc m) =
  begin
    suc m * 1
  ≡⟨⟩
    1 + m * 1
  ≡⟨ cong (1 +_) (*-identityʳ m) ⟩
    1 + m
  ≡⟨⟩
    suc m
  ∎

*-identityˡ : ∀ (m : ℕ) → 1 * m ≡ m
*-identityˡ zero = refl
*-identityˡ (suc m) =
  begin
    1 * (suc m)
  ≡⟨⟩
    (suc zero) * (suc m)
  ≡⟨⟩
    (suc m) + (zero * suc m)
  ≡⟨⟩
    (suc m) + zero
  ≡⟨ +-comm (suc m) zero ⟩
    zero + (suc m)
  ≡⟨⟩
    suc m
  ∎

*-suc : ∀ (m n : ℕ) → m * (suc n) ≡ m * n + m
*-suc zero n =
  begin
    zero * (suc n)
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero * n
  ≡⟨⟩
    zero * n + zero
  ∎
*-suc (suc m) n =
  begin
    (suc m) * (suc n)
  ≡⟨⟩
    (suc n) + (m * (suc n))
  ≡⟨ +-comm (suc n) (m * (suc n)) ⟩
    (m * (suc n)) + (suc n)
  ≡⟨ cong (_+ (suc n)) (*-suc m n) ⟩
    (m * n + m) + (suc n)
  ≡⟨ +-assoc (m * n) m (suc n) ⟩
    (m * n) + (m + (suc n))
  ≡⟨ cong ((m * n) +_) (+-comm m (suc n)) ⟩
    (m * n) + ((suc n) + m)
  ≡⟨⟩
    (m * n) + (suc (n + m))
  ≡⟨ cong ((m * n) +_) (cong suc (+-comm n m)) ⟩
    (m * n) + (suc (m + n))
  ≡⟨⟩
    (m * n) + ((suc m) + n)
  ≡⟨ cong ((m * n) +_) (+-comm (suc m) n) ⟩
    (m * n) + (n + (suc m))
  ≡⟨ sym (+-assoc (m * n) n (suc m)) ⟩
    ((m * n) + n) + (suc m)
  ≡⟨ cong (_+ (suc m)) (+-comm (m * n) n) ⟩
    (n + (m * n)) + (suc m)
  ≡⟨⟩
    ((suc m) * n) + (suc m)
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n =
  begin
    zero * n
  ≡⟨⟩
    zero
  ≡⟨ sym (*-zero n) ⟩
    n * zero
  ∎
*-comm (suc m) n =
  begin
    (suc m) * n
  ≡⟨⟩
    n + (m * n)
  ≡⟨ +-comm n (m * n) ⟩
    (m * n) + n
  ≡⟨ cong (_+ n) (*-comm m n) ⟩
    (n * m) + n
  ≡⟨ sym (*-suc n m) ⟩
    n * (suc m)
  ∎

0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p =
  begin
    zero ∸ n ∸ p
  ≡⟨ cong (_∸ p) (0∸n≡0 n) ⟩
  zero ∸ p
  ≡⟨ 0∸n≡0 p ⟩
  zero
  ≡⟨ sym (0∸n≡0 (n + p)) ⟩
  zero ∸ (n + p)
  ∎

∸-+-assoc (suc m) zero p =
  begin
    (suc m) ∸ zero ∸ p
  ≡⟨⟩
  (suc m) ∸ p
  ≡⟨⟩
  (suc m) ∸ (zero + p)
  ∎

∸-+-assoc (suc m) (suc n) p =
  begin
    (suc m) ∸ (suc n) ∸ p
  ≡⟨⟩
    m ∸ n ∸ p
  ≡⟨ ∸-+-assoc m n p ⟩
    m ∸ (n + p)
  ≡⟨⟩
    (suc m) ∸ (suc (n + p))
  ≡⟨⟩
    (suc m) ∸ ((suc n) + p)
  ∎


^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m 0 p =
  begin
    m ^ (0 + p)
  ≡⟨⟩
    m ^ p
  ≡⟨ sym (*-identityˡ (m ^ p)) ⟩
    1 * (m ^ p)
  ≡⟨⟩
    (m ^ 0) * (m ^ p)
  ∎

^-distribˡ-+-* m (suc n) p =
  begin
    m ^ (suc n + p)
  ≡⟨⟩
    m ^ (suc (n + p))
  ≡⟨⟩
    m * (m ^ (n + p))
  ≡⟨ cong (m *_) (^-distribˡ-+-* m n p) ⟩
    m * ((m ^ n) * (m ^ p))
  ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    (m * (m ^ n)) * (m ^ p)
  ≡⟨⟩
    (m ^ suc n) * (m ^ p)
  ∎

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n 0 = refl
^-distribʳ-* m n (suc p) =
  begin
    (m * n) ^ (suc p)
  ≡⟨⟩
    (m * n) * ((m * n) ^ p)
  ≡⟨ cong ((m * n) *_) (^-distribʳ-* m n p) ⟩
    (m * n) * ((m ^ p) * (n ^ p))
  ≡⟨ sym (*-assoc (m * n) (m ^ p) (n ^ p)) ⟩
    ((m * n) * (m ^ p)) * (n ^ p)
  ≡⟨ cong (_* (n ^ p)) (*-comm (m * n) (m ^ p)) ⟩
    ((m ^ p) * (m * n)) * (n ^ p)
  ≡⟨ cong (_* (n ^ p)) (sym (*-assoc (m ^ p) m n)) ⟩
    (((m ^ p) * m) * n) * (n ^ p)
  ≡⟨ cong (_* (n ^ p)) (cong (_* n) (*-comm (m ^ p) m)) ⟩
    ((m * (m ^ p)) * n) * (n ^ p)
  ≡⟨⟩
    ((m ^ suc p) * n) * (n ^ p)
  ≡⟨ *-assoc (m ^ (suc p)) n (n ^ p) ⟩
    (m ^ suc p) * (n * (n ^ p))
  ≡⟨⟩
    (m ^ suc p) * (n ^ (suc p))
  ∎

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n 0 =
  begin
    (m ^ n) ^ 0
  ≡⟨⟩
    1
  ≡⟨⟩
    m ^ 0
  ≡⟨⟩
    m ^ (0 * n)
  ≡⟨ cong (m ^_) (*-comm 0 n) ⟩
    m ^ (n * 0)
  ∎

^-*-assoc m n (suc p) =
  begin
    (m ^ n) ^ (suc p)
  ≡⟨⟩
    (m ^ n) * ((m ^ n) ^ p)
  ≡⟨ cong ((m ^ n) *_) (^-*-assoc m n p) ⟩
    (m ^ n) * (m ^ (n * p))
  ≡⟨ sym (^-distribˡ-+-* m n (n * p)) ⟩
    m ^ (n + (n * p))
  ≡⟨ cong (m ^_) (cong (n +_) (*-comm n p)) ⟩
    m ^ (n + (p * n))
  ≡⟨⟩
    m ^ ((suc p) * n)
  ≡⟨ cong (m ^_) (*-comm (suc p) n) ⟩
    m ^ (n * (suc p))
  ∎

data Bin : Set where
 ⟨⟩ : Bin
 _O : Bin → Bin
 _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to   : ℕ → Bin
to zero = ⟨⟩
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = (from b) * 2
from (b I) = (from b) * 2 + 1

from_inc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from_inc ⟨⟩ =
  begin
    from (inc ⟨⟩)
  ≡⟨⟩
    from (⟨⟩ I)
  ≡⟨⟩
    1
  ≡⟨⟩
    suc zero
  ≡⟨⟩
    suc (from ⟨⟩)
  ∎
from_inc (b O) =
  begin
    from (inc (b O))
  ≡⟨⟩
    from (b I)
  ≡⟨⟩
    ((from b) * 2) + 1
  ≡⟨ +-comm ((from b) * 2) 1 ⟩
    1 + ((from b) * 2)
    ≡⟨⟩
    suc ((from b) * 2)
    ≡⟨⟩
    suc (from (b O))
    ∎

from_inc (b I) =
  begin
    from (inc (b I))
  ≡⟨⟩
    from ((inc b) O)
  ≡⟨⟩
    (from (inc b)) * 2
  ≡⟨ cong (_* 2) (from_inc b) ⟩
    (suc (from b)) * 2
  ≡⟨⟩
    (1 + (from b)) * 2
  ≡⟨ *-distrib-+ 1 (from b) 2 ⟩
    (1 * 2) + (from b) * 2
  ≡⟨⟩
    (1 + 1) + (from b) * 2
  ≡⟨ +-assoc 1 1 ((from b) * 2) ⟩
    1 + (1 + (from b) * 2)
  ≡⟨ cong (1 +_) (+-comm 1 ((from b) * 2)) ⟩
    suc ((from b) * 2 + 1)
  ≡⟨⟩
    suc (from (b I))
  ∎

from_to : ∀ (n : ℕ) → from (to n) ≡ n
from_to zero = refl
from_to (suc n) =
  begin
    from (to (suc n))
  ≡⟨⟩
    from (inc (to n))
  ≡⟨ from_inc (to n) ⟩
    suc (from (to n))
  ≡⟨ cong suc (from_to n) ⟩
    suc n
  ∎

to_from : ∀ (b : Bin) → to (from b) ≡ b
to_from b = {!!}
