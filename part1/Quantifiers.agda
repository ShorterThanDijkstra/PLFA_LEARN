module part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)

open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality; ∀-extensionality)

open import Function using (_∘_)

∀-elim : ∀ {A : Set} {B : A → Set} → (∀ (x : A) → B x) → (M : A) → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
              (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record {
   to = λ f → ⟨ (λ a → proj₁ (f a)), (λ a → proj₂ (f a)) ⟩ ;
   from = λ {⟨ fb , fc ⟩ → λ a → ⟨ fb a , fc a ⟩ } ;
   from∘to = λ _ → refl ;
   to∘from = λ _ → refl
  }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
                 (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) →
                 ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ fb) = λ a → inj₁ (fb a)
⊎∀-implies-∀⊎ (inj₂ fc) = λ a → inj₂ (fc a)

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

∀-× : ∀ {B : Tri → Set} →
       (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× = record {
    to   = λ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩ ;
    from = λ { ⟨ baa , ⟨ bbb , bcc ⟩ ⟩ →
                λ { aa → baa ; bb → bbb ; cc → bcc }} ;
    from∘to = λ f → ∀-extensionality (λ { aa → refl ; bb → refl ; cc → refl }) ;
    to∘from = λ _ → refl
  }

record Σ (A : Set) (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    proj₁ : A
    proj₂ : B proj₁

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → Bx) = Σ[ x ∈ A ] Bx

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set} →
          (∀ x → B x → C) → ∃[ x ] B x → C
∃-elim f (⟨ x , bx ⟩) = f x bx

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ} → even n → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero = ⟨ zero , refl ⟩
even-∃ (even-suc on) with odd-∃ on
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃ (odd-suc en) with even-∃ en
...                  |  ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨ zero , refl ⟩ = even-zero
∃-even ⟨ suc m , refl ⟩ =  even-suc (odd-suc (∃-even ⟨ m , refl ⟩))

∃-odd ⟨ m , refl ⟩ = odd-suc (∃-even ⟨ m , refl ⟩)

{-
∃-even′ : ∀ {n : ℕ} → ∃[ m ] ( 2 * m ≡ n) → even n
∃-odd′  : ∀ {n : ℕ} → ∃[ m ] ( m * 2 + 1 ≡ n) →  odd n

∃-even′ ⟨ zero , refl ⟩ = even-zero
∃-even′ ⟨ suc m , refl ⟩ = {!!}
-}

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n

  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

≡→≤ : ∀(m n : ℕ) → (m ≡ n) → m ≤ n
≡→≤ zero n refl = z≤n
≡→≤ (suc m) (suc n) refl = s≤s (≡→≤ m n refl)

m≤suc-m+n : ∀ (m n : ℕ) → m ≤ suc (n + m)
m≤suc-m+n zero n = z≤n
m≤suc-m+n (suc m) n rewrite (+-comm n (suc m)) | (+-comm m n) = s≤s (m≤suc-m+n m n)

∃-+-≤ : ∀ {y z : ℕ} → ∃[ x ] (x + y ≡ z) → y ≤ z
∃-+-≤ {y} {z} ⟨ zero , refl ⟩ = ≡→≤ y z refl
∃-+-≤ {y} {suc z} ⟨ (suc x), refl ⟩ = m≤suc-m+n y x

postulate
  +-identityʳ : ∀ (m : ℕ) → m + zero ≡ m

m+suc-n≡suc-m+n : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
m+suc-n≡suc-m+n zero n = refl
m+suc-n≡suc-m+n (suc m) n = cong suc (m+suc-n≡suc-m+n m n)

≤-+-∃ : ∀ {y z : ℕ} → y ≤ z → ∃[ x ] (x + y ≡ z)
≤-+-∃ {zero} {z} z≤n = ⟨ z , +-identityʳ z ⟩
≤-+-∃ {suc y} {suc z} (s≤s y≤z)  with ≤-+-∃ {y} {z} y≤z
...                                | ⟨ x , refl ⟩ = ⟨ x ,  m+suc-n≡suc-m+n x y ⟩

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set} → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ = record {
    to = λ {f → λ {x → λ {Bx → f ⟨ x , Bx ⟩}}};
    from = λ {g → λ {(⟨ x , Bx ⟩) → g x Bx}};
    from∘to = λ {f → refl};
    to∘from = λ {g → refl}
  }

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set} → ∃[ x ] (¬ B x) → ¬ (∀ x → B x)
∃¬-implies-¬∀ (⟨ x , ¬Bx ⟩) = λ {∀x→Bx → ¬Bx (∀x→Bx x)}

{-
¬∀-implies-∃¬ : ∀ {A : Set} {B : A → Set} → ¬ (∀ x → B x) → ∃[ x ] (¬ B x)
¬∀-implies-∃¬ f = {!!}
-}
