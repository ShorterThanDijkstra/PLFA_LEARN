import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning

record _×_ (A B : Set) : Set where
  constructor ⟨_,_⟩
  field
    proj₁ : A
    proj₂ : B
open _×_

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× w = refl

infixr 2 _×_
data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm = record {
    to = λ {⟨ a , b ⟩ → ⟨ b , a ⟩ };
    from = λ {⟨ b , a ⟩ → ⟨ a , b ⟩};
    from∘to = λ {⟨ a , b ⟩ → refl};
    to∘from = λ {⟨ b , a ⟩ → refl}
  }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = record {
    to = λ { ⟨ ⟨ a , b ⟩ , c ⟩ → ⟨ a , ⟨ b , c ⟩ ⟩ };
    from = λ { ⟨ a , ⟨ b , c ⟩ ⟩ → ⟨ ⟨ a , b ⟩ , c ⟩ };
    from∘to = λ w → refl;
    to∘from = λ w → refl
  }

⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ ((A → B) × (B → A))
⇔≃× = record {
    to = λ {(record {to = a→b; from = b→a}) → ⟨ a→b , b→a ⟩};
    from = λ {⟨ a→b , b→a ⟩ → record {to = a→b; from = b→a}};
    from∘to = λ x → refl;
    to∘from = λ x → refl
  }

record ⊤ : Set where
  constructor tt

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ w = refl

truth : ⊤
truth = _

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ = record {
     to = λ {⟨ tt , a ⟩ → a};
     from = λ {a → ⟨ tt , a ⟩};
     from∘to = λ x → refl ;
     to∘from = λ x → refl
  }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

data _⊎_ (A B : Set) : Set where

  inj₁ : A → A ⊎ B

  inj₂ : B → A ⊎ B

case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ a→c b→c (inj₁ a) = a→c a
case-⊎ a→c b→c (inj₂ b) = b→c b

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) → case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infixr 1 _⊎_

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = record {
    to = λ {(inj₁ a) → inj₂ a;
            (inj₂ b) → inj₁ b};
    from = λ {(inj₁ b) → inj₂ b;
              (inj₂ a) → inj₁ a};
    from∘to = λ {(inj₁ a) → refl;
                 (inj₂ b) → refl};
    to∘from = λ {(inj₁ b) → refl;
                 (inj₂ a) → refl}
  }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = record {
    to = λ {(inj₁ (inj₁ a)) → inj₁ a;
            (inj₁ (inj₂ b)) → inj₂ (inj₁ b);
            (inj₂ c) → inj₂ (inj₂ c)};
    from = λ {(inj₁ a) → (inj₁ (inj₁ a));
              (inj₂ (inj₁ b)) → inj₁ (inj₂ b);
              (inj₂ (inj₂ c)) → inj₂ c};

    from∘to = λ {(inj₁ (inj₁ a)) → refl;
                 (inj₁ (inj₂ b)) → refl;
                 (inj₂ c) → refl};
    to∘from =  λ {(inj₁ a) → refl;
                 (inj₂ (inj₁ b)) → refl;
                 (inj₂ (inj₂ c)) → refl}
  }


data ⊥ : Set where
-- no clauses!

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

⊥-identityˡ : ∀ {A : Set} → (A ⊎ ⊥) ≃ A
⊥-identityˡ = record {
  to = λ {(inj₁ a) → a;
           (inj₂ ())};
  from = λ {a → inj₁ a};
  from∘to = λ {(inj₁ a) → refl;
               (inj₂ ())};
  to∘from = λ x → refl
  }

⊥-identityʳ : ∀ {A : Set} → (⊥ ⊎ A) ≃ A
⊥-identityʳ {A} = ≃-begin
                    (⊥ ⊎ A)
                  ≃⟨ ⊎-comm ⟩
                    (A ⊎ ⊥)
                  ≃⟨ ⊥-identityˡ ⟩
                    A
                  ≃-∎
