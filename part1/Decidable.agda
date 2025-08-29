module part1.Decidable where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Negation using (¬_)
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.part1.Relations using (_<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_⇔_)
infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ} → zero ≤ n

  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤ᵇ_
_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n       =  true
suc m ≤ᵇ zero   =  false
suc m ≤ᵇ suc n  =  m ≤ᵇ n

_ : (2 ≤ᵇ 4) ≡ true
_ = begin
      2 ≤ᵇ 4
    ≡⟨⟩
      1 ≤ᵇ 3
    ≡⟨⟩
      0 ≤ᵇ 2
    ≡⟨⟩
      true
    ∎

_ : (4 ≤ᵇ 2) ≡ false
_ = begin
      4 ≤ᵇ 2
    ≡⟨⟩
      3 ≤ᵇ 1
    ≡⟨⟩
      2 ≤ᵇ 0
    ≡⟨⟩
      false
    ∎

T : Bool → Set
T true   =  ⊤
T false  =  ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt = refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T {true} refl = tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n tt = z≤n
≤ᵇ→≤ (suc m) zero ()
≤ᵇ→≤ (suc m) (suc n) T-m≤ᵇn = s≤s (≤ᵇ→≤ m n T-m≤ᵇn)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ {zero} {n} z≤n = tt
≤→≤ᵇ {suc m} {suc n} (s≤s m≤n) = ≤→≤ᵇ {m} {n} m≤n

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s m≤n→⊥ = λ {(s≤s m≤n) → m≤n→⊥ m≤n}

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no ¬s≤z
suc m ≤? suc n  with m ≤? n
...               | yes m≤n = yes (s≤s m≤n)
...               | no ¬m≤n = no (¬s≤s ¬m≤n)

_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl

¬s<z : ∀ {m : ℕ} → ¬ (suc m < zero)
¬s<z ()

¬z<z : ¬ zero < zero
¬z<z ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s m<n→⊥ = λ {(s<s m<n) → m<n→⊥ m<n}

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero = no ¬z<z
zero <? suc n = yes z<s
suc m <? zero = no ¬s<z
suc m <? suc n  with m <? n
...               | yes m<n = yes (s<s m<n)
...               | no ¬m<n = no (¬s<s ¬m<n)

¬m≡n-implies-¬sm≡sn : ∀ {m n : ℕ} → ¬ m ≡ n → ¬ (suc m ≡ suc n)
¬m≡n-implies-¬sm≡sn ¬m≡n refl = ¬m≡n refl

¬z≡s : ∀ {n : ℕ} → ¬ (zero ≡ (suc n))
¬z≡s ()

¬s≡z : ∀ {n : ℕ} → ¬ ((suc n) ≡ zero )
¬s≡z ()

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? (suc n) = no ¬z≡s
(suc n) ≡ℕ? zero = no ¬s≡z
(suc m) ≡ℕ? (suc n) with m ≡ℕ? n
...                   | yes refl = yes refl
...                   | no ¬m≡n = no (¬m≡n-implies-¬sm≡sn ¬m≡n)

_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = yes (p tt)
...        | false  | _        | ¬p           = no ¬p

⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋  =  true
⌊ no ¬x ⌋  =  false

_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n  =  ⌊ m ≤? n ⌋

toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt  =  x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _  =  tt
fromWitness {A} {no ¬x} x  =  ¬x x

≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤  =  toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }

_∨_ : Bool → Bool → Bool
true  ∨ _      = true
_     ∨ true   = true
false ∨ false  = false

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes a ⊎-dec _ = yes (inj₁ a)
_ ⊎-dec yes b = yes (inj₂ b)
no ¬a ⊎-dec no ¬b = no λ {(inj₁ a) → ¬a a; (inj₂ b) → ¬b b}

not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes a) =  no (¬¬-intro a)
¬? (no ¬a) = yes ¬a

_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_ →-dec (yes b) = yes (λ a → b)
(no ¬a) →-dec _ = yes (λ a → ⊥-elim (¬a a))
(yes a) →-dec (no ¬b) = no (λ {a→b → ¬b (a→b a)})

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes a) (yes b) = refl
∧-× (yes a) (no ¬b) = refl
∧-× (no ¬a) (yes b) = refl
∧-× (no ¬a) (no ¬b) = refl

∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ (yes a) (yes b) = refl
∨-⊎ (yes a) (no ¬b) = refl
∨-⊎ (no ¬a) (yes b) = refl
∨-⊎ (no ¬a) (no ¬b) = refl

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes a) = refl
not-¬ (no ¬a) = refl

_iff_ : Bool → Bool → Bool
true iff true = true
false iff false = true
_ iff _ = false

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
(yes a) ⇔-dec (yes b) = yes (record {to = λ _ → b; from = λ _ → a})
(yes a) ⇔-dec (no ¬b) = no (λ {(record {to = a→b ; from = b→a}) → ¬b (a→b a)})
(no ¬a) ⇔-dec (no ¬b) = yes (record {to = λ a → ⊥-elim (¬a a); from = λ b → ⊥-elim (¬b b)})
(no ¬a) ⇔-dec (yes b) = no (λ {(record {to = a→b ; from = b→a}) → ¬a (b→a b)})

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes a) (yes b) = refl
iff-⇔ (yes a) (no ¬b) = refl
iff-⇔ (no ¬a) (yes b) = refl
iff-⇔ (no ¬a) (no ¬b) = refl

minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m       zero    _         = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m

_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl

_-_ : (m n : ℕ) {n≤m : T ⌊ n ≤? m ⌋} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)
