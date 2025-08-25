module part1.Negation where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Negation using (contradiction)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x = λ ¬x →  ¬x x

¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x = λ x → (¬¬¬x (λ y → y x))

{-
想不出¬ A → A这个命题的构造。
不能证明无法给出构造？
¬¬-elim : ∀ {A : Set} → ¬ ¬ A → A
¬¬-elim = λ ¬¬x → ?
-}

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition a→b = λ ¬b → (λ a → ¬b (a→b a))

{-
想不出(¬ B → ¬ A) → (A → B)这个命题的构造。
不能证明无法给出构造？
contraposition-inverse : ∀ {A B : Set} → (¬ B → ¬ A) → (A → B)
contraposition-inverse ¬b→¬a = ?
-}

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → contradiction x ¬x)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n

  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive zero = λ ()
<-irreflexive (suc n) = λ {(s<s m<m) → <-irreflexive n m<m}

¬⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
¬⊎-dual-× = record {
       to = λ {¬a⊎b → ⟨ (λ a → (¬a⊎b (inj₁ a))) , (λ b → ( ¬a⊎b (inj₂ b))) ⟩};
       from = λ {⟨ ¬a , ¬b ⟩ → λ {(inj₁ a) → ¬a a; (inj₂ b) → ¬b b}};
       from∘to = λ {¬a⊎b → refl};
       to∘from = λ { ⟨ ¬a , ¬b ⟩ → refl}
   }


{-
¬x-dual-⊎ : ∀ {A B : Set} → ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
¬x-dual-⊎ = record {
       to = λ {¬a×b → inj₁ (λ a → ?)} ;
  }
-}

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ f → f (inj₂ (λ a → f (inj₁ a)))

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀ {A : Set} → Stable (¬ A)
¬-stable = ¬¬¬-elim

×-stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-stable sa sb = λ f → ⟨ (sa (λ a→f → f (λ a×b → a→f (proj₁ a×b)))),
                         (sb (λ b→f → f (λ a×b → b→f (proj₂ a×b)))) ⟩
