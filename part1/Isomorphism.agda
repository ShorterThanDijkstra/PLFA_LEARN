module part1.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; sym)
open Eq.≡-Reasoning
open import Data.Nat.Properties using (+-comm)
open import Data.Nat using (ℕ; zero; suc;_+_; _*_)
open import Data.Nat.Properties using (+-assoc)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero    = refl
  helper m (suc n) = cong suc (helper m n)

same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

open _≃_

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl = record {
    to = λ a → a;
    from = λ b → b;
    from∘to = λ a → refl;
    to∘from = λ b → refl
  }

≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym (record {to = a→b; from = b→a; from∘to = from-to; to∘from = to-from}) =
       record {to = b→a; from = a→b; from∘to = to-from; to∘from = from-to}

≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans (record {to = a→b; from = b→a; from∘to = from-to-a≡a; to∘from = to-from-b≡b})
        (record {to = b→c; from = c→b; from∘to = from-to-b≡b; to∘from = to-from-c≡c}) =
         record {to = b→c ∘ a→b;
                 from = b→a ∘ c→b;
                 from∘to = λ { a →
                           begin
                             (b→a ∘ c→b)((b→c ∘ a→b) a)
                           ≡⟨⟩
                             b→a (c→b (b→c (a→b a)))
                           ≡⟨ cong b→a (from-to-b≡b (a→b a)) ⟩
                             b→a (a→b a)
                           ≡⟨ from-to-a≡a a ⟩
                             a
                           ∎
                             };
                 to∘from = λ {c →
                           begin
                             (b→c ∘ a→b) ((b→a ∘ c→b) c)
                           ≡⟨⟩
                             b→c (a→b (b→a (c→b c)))
                           ≡⟨ cong b→c (to-from-b≡b (c→b c)) ⟩
                             b→c (c→b c)
                           ≡⟨ to-from-c≡c c ⟩
                             c
                           ∎
                             }
                 }

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set} → A ≃ B → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≃ B → B ≃ C → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set) → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

infix 0 _≲_

record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl = record {
  to = λ a → a;
  from = λ b → b;
  from∘to = λ a → refl
 }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans (record {to = a→b; from = b→a; from∘to = b→a∘a→b≡id}) (record {to = b→c; from = c→b; from∘to = c→b∘b→c≡id}) =
  record {
   to = b→c ∘ a→b;
   from = b→a ∘ c→b;
   from∘to = λ {c →
             begin
               (b→a ∘ c→b) ((b→c ∘ a→b) c)
             ≡⟨⟩
               b→a (c→b (b→c (a→b c)))
             ≡⟨ cong b→a (c→b∘b→c≡id (a→b c)) ⟩
               b→a (a→b c)
             ≡⟨ b→a∘a→b≡id c ⟩
               c
             ∎
           }
   }

≲-antisym : ∀ {A B : Set} → (A≲B : A ≲ B) → (B≲A : B ≲ A) → (to A≲B ≡ from B≲A) → (from A≲B ≡ to B≲A) → A ≃ B
≲-antisym (record {to = a→b; from = b→a; from∘to = b→a∘a→b≡id})
          (record {to = b→a′; from = a→b′; from∘to = a→b′∘b→a′≡id})
          to≡from -- a→b ≡ a→b′
          from≡to -- b→a ≡ b→a′
          =
          record {to = a→b;
                  from = b→a;
                  from∘to = b→a∘a→b≡id;
                  to∘from = λ {b →
                            begin
                              (a→b (b→a b))
                            ≡⟨ cong a→b (cong (λ p → p b) from≡to) ⟩
                              (a→b (b→a′ b))
                            ≡⟨ cong (λ p → p (b→a′ b)) to≡from ⟩
                              (a→b′ (b→a′ b))
                            ≡⟨  a→b′∘b→a′≡id b ⟩
                              b
                            ∎}
                 }

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set} → A ≲ B → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≲ B → B ≲ C → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set) → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

≃-implies-≲ : ∀ {A B : Set} → A ≃ B → A ≲ B
≃-implies-≲ (record {to = a→b; from = b→a; from∘to = b→a∘a→b≡id; to∘from = a→b∘b→a≡id}) =
             record {to = a→b; from = b→a; from∘to = b→a∘a→b≡id}

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl = record { to = λ a → a; from = λ b → b}

⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym (record {to = a→b; from = b→a}) = record {to = b→a; from = a→b}

⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans (record {to = a→b; from = b→a}) (record {to = b→c; from = c→b}) = record {to = b→c ∘ a→b; from = b→a ∘ c→b}

data Bin : Set where
 ⟨⟩ : Bin
 _O : Bin → Bin
 _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

b-to   : ℕ → Bin
b-to zero = ⟨⟩
b-to (suc n) = inc (b-to n)

b-from : Bin → ℕ
b-from ⟨⟩ = 0
b-from (b O) = (b-from b) * 2
b-from (b I) = (b-from b) * 2 + 1

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


from_inc : ∀ (b : Bin) → b-from (inc b) ≡ suc (b-from b)
from_inc ⟨⟩ =
  begin
    b-from (inc ⟨⟩)
  ≡⟨⟩
    b-from (⟨⟩ I)
  ≡⟨⟩
    1
  ≡⟨⟩
    suc zero
  ≡⟨⟩
    suc (b-from ⟨⟩)
  ∎
from_inc (b O) =
  begin
    b-from (inc (b O))
  ≡⟨⟩
    b-from (b I)
  ≡⟨⟩
    ((b-from b) * 2) + 1
  ≡⟨ +-comm ((b-from b) * 2) 1 ⟩
    1 + ((b-from b) * 2)
  ≡⟨⟩
    suc ((b-from b) * 2)
  ≡⟨⟩
    suc (b-from (b O))
  ∎

from_inc (b I) =
  begin
    b-from (inc (b I))
  ≡⟨⟩
    b-from ((inc b) O)
  ≡⟨⟩
    (b-from (inc b)) * 2
  ≡⟨ cong (_* 2) (from_inc b) ⟩
    (suc (b-from b)) * 2
  ≡⟨⟩
    (1 + (b-from b)) * 2
    ≡⟨ *-distrib-+ 1 (b-from b) 2 ⟩
    (1 * 2) + (b-from b) * 2
  ≡⟨⟩
    (1 + 1) + (b-from b) * 2
  ≡⟨ +-assoc 1 1 ((b-from b) * 2) ⟩
    1 + (1 + (b-from b) * 2)
  ≡⟨ cong (1 +_) (+-comm 1 ((b-from b) * 2)) ⟩
    suc ((b-from b) * 2 + 1)
  ≡⟨⟩
    suc (b-from (b I))
  ∎

from_to : ∀ (n : ℕ) → b-from (b-to n) ≡ n
from_to zero = refl
from_to (suc n) =
  begin
    b-from (b-to (suc n))
  ≡⟨⟩
    b-from (inc (b-to n))
  ≡⟨ from_inc (b-to n) ⟩
    suc (b-from (b-to n))
  ≡⟨ cong suc (from_to n) ⟩
    suc n
  ∎

ℕ-≲-bin : ℕ ≲ Bin
ℕ-≲-bin = record {to = b-to; from = b-from; from∘to = from_to}

