module part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityˡ; +-identityʳ; *-assoc; *-comm; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_; extensionality)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

data List′ : Set → Set₁ where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A

infixr 5 _∷′_
l1 : List ℕ
l1 = zero ∷ suc zero ∷ []

l2 : List′ ℕ
l2 = zero ∷′ (suc zero) ∷′ []′

nested1 : List (List ℕ)
nested1 = (zero ∷ suc zero ∷ []) ∷ []

{-
nested2 : List′ (List′ ℕ)
nested2 = (zero ∷′ suc zero ∷′ []) ∷′ []
-}

_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = begin
                            ((x ∷ xs) ++ ys) ++ zs
                          ≡⟨⟩
                            (x ∷ (xs ++ ys)) ++ zs
                          ≡⟨⟩
                            x ∷ ((xs ++ ys) ++ zs)
                          ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
                            x ∷ (xs ++ (ys ++ zs))
                          ≡⟨⟩
                            (x ∷ xs) ++ (ys ++ zs)
                          ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ [] = refl
++-identityˡ (x ∷ xs) = begin
                          [] ++ (x ∷ xs)
                        ≡⟨⟩
                          (x ∷ xs)
                        ∎

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = begin
                          (x ∷ xs) ++ []
                        ≡⟨⟩
                          x ∷ (xs ++ [])
                        ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
                          x ∷ xs
                        ∎

length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = begin
                          length ((x ∷ xs) ++ ys)
                        ≡⟨⟩
                          length (x ∷ (xs ++ ys))
                        ≡⟨⟩
                          suc (length (xs ++ ys))
                        ≡⟨ cong suc (length-++ xs ys) ⟩
                          suc (length xs + length ys)
                        ≡⟨⟩
                          suc (length xs) + length ys
                        ≡⟨⟩
                          length (x ∷ xs) + length ys
                        ∎

reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]

reverse-++-distrib : ∀ {A : Set} (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys = begin
                             reverse ([] ++ ys)
                           ≡⟨⟩
                             (reverse ys)
                           ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
                             (reverse ys) ++ []
                           ≡⟨⟩
                             (reverse ys) ++ (reverse [])
                           ∎
reverse-++-distrib (x ∷ xs) ys = begin
                                   reverse ((x ∷ xs) ++ ys)
                                 ≡⟨⟩
                                   reverse (x ∷ (xs ++ ys))
                                 ≡⟨⟩
                                   reverse (xs ++ ys) ++ [ x ]
                                 ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
                                   ((reverse ys) ++ (reverse xs)) ++ [ x ]
                                 ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
                                   (reverse ys) ++ ((reverse xs) ++ [ x ])
                                 ≡⟨⟩
                                   (reverse ys) ++ (reverse (x ∷ xs))
                                 ∎
involution-reverse : ∀ {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
involution-reverse [] = refl
involution-reverse (x ∷ xs) = begin
                                reverse (reverse (x ∷ xs))
                              ≡⟨⟩
                                reverse ((reverse xs) ++ [ x ])
                              ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
                                (reverse [ x ]) ++ (reverse (reverse xs))
                              ≡⟨ cong ((reverse [ x ]) ++_) (involution-reverse xs) ⟩
                                (reverse [ x ]) ++ xs
                              ≡⟨⟩
                                [ x ] ++ xs
                              ≡⟨⟩
                                ( x ∷ []) ++ xs
                              ≡⟨⟩
                                x ∷ ([] ++ xs)
                              ≡⟨⟩
                                x ∷ xs
                              ∎
shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A) → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x ∷ xs) ys = begin
                              shunt (x ∷ xs) ys
                            ≡⟨⟩
                              shunt xs (x ∷ ys)
                            ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
                              reverse xs ++ (x ∷ ys)
                            ≡⟨⟩
                              reverse xs ++ ([ x ] ++ ys)
                            ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
                              (reverse xs ++ [ x ]) ++ ys
                            ≡⟨⟩
                              reverse (x ∷ xs) ++ ys
                            ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A) → reverse′ xs ≡ reverse xs
reverses xs = begin
                reverse′ xs
              ≡⟨⟩
                shunt xs []
              ≡⟨ shunt-reverse xs [] ⟩
                reverse xs ++ []
              ≡⟨ ++-identityʳ (reverse xs) ⟩
                reverse xs
              ∎

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

map-compose′ : ∀ {A B C : Set} → (f : A → B) → (g : B → C) → ∀ (xs : List A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose′ f g [] = refl
map-compose′ f g (x ∷ xs) = begin
                             (g ∘ f) x ∷ map (g ∘ f) xs
                           ≡⟨ cong ((g ∘ f) x ∷_) (map-compose′ f g xs) ⟩
                             (g ∘ f) x ∷ ((map g ∘ map f) xs)
                           ≡⟨⟩
                             (g (f x)) ∷ (map g (map f xs))
                           ≡⟨⟩
                             map g (f x ∷ map f xs)
                           ≡⟨⟩
                               map g (map f (x ∷ xs))
                           ≡⟨⟩
                               (map g ∘ map f) (x ∷ xs)
                           ∎

map-compose : ∀ {A B C : Set} → (f : A → B) → (g : B → C) → map (g ∘ f) ≡ (map g ∘ map f)
map-compose f g = extensionality (λ xs → map-compose′ f g xs)

{- map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs -}

map-++-distribute : ∀ {A B : Set} → (f : A → B) → ∀ (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys = refl
map-++-distribute f (x ∷ xs) ys = begin
                                    map f ((x ∷ xs) ++ ys)
                                  ≡⟨⟩
                                    map f (x ∷ (xs ++ ys))
                                  ≡⟨⟩
                                    f x ∷ map f (xs ++ ys)
                                  ≡⟨ cong (f x ∷_) (map-++-distribute f xs ys) ⟩
                                    f x ∷ (map f xs ++ map f ys)
                                  ≡⟨⟩
                                    (f x ∷ (map f xs)) ++ map f ys
                                  ≡⟨⟩
                                    map f (x ∷ xs) ++ map f ys
                                  ∎

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree a→c b→d (leaf a) = leaf (a→c a)
map-Tree a→c b→d (node left b right) = node (map-Tree a→c b→d left) (b→d b) (map-Tree a→c b→d right)

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

product : List ℕ → ℕ
product = foldr _*_ 1

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys = begin
                               foldr _⊗_ e ((x ∷ xs) ++ ys)
                             ≡⟨⟩
                               foldr _⊗_ e (x ∷ (xs ++ ys))
                             ≡⟨⟩
                               x ⊗ foldr _⊗_ e (xs ++ ys)
                             ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys) ⟩
                               x ⊗ foldr _⊗_ (foldr _⊗_ e ys) xs
                             ≡⟨⟩
                               foldr _⊗_ (foldr _⊗_ e ys) (x ∷ xs)
                             ∎

foldr-∷ : ∀ {A : Set} → (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) = begin
                     foldr _∷_ [] (x ∷ xs)
                   ≡⟨⟩
                     x ∷ foldr _∷_ [] xs
                   ≡⟨ cong (x ∷_) (foldr-∷ xs) ⟩
                     x ∷ xs
                   ∎
foldr-∷++ : ∀ {A : Set} → (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
foldr-∷++ [] ys = begin
                    [] ++ ys
                  ≡⟨⟩
                    ys
                  ≡⟨⟩
                    foldr _∷_ ys []
                  ∎
foldr-∷++ (x ∷ xs) ys = begin
                          (x ∷ xs) ++ ys
                        ≡⟨⟩
                          x ∷ (xs ++ ys)
                        ≡⟨ cong (x ∷_) (foldr-∷++ xs ys) ⟩
                          x ∷ (foldr _∷_ ys xs)
                        ≡⟨⟩
                          foldr _∷_ ys (x ∷ xs)
                        ∎

map-is-foldr-lemma : ∀ {A B : Set} → (f : A → B) → (xs : List A) → map f xs ≡ foldr (λ y ys → f y ∷ ys) [] xs
map-is-foldr-lemma f [] = refl
map-is-foldr-lemma f (x ∷ xs) = begin
                                  map f (x ∷ xs)
                                ≡⟨⟩
                                  f x ∷ map f xs
                                ≡⟨ cong (f x ∷_) (map-is-foldr-lemma f xs) ⟩
                                  f x ∷ foldr (λ y ys → f y ∷ ys) [] xs
                                ≡⟨⟩
                                  foldr (λ y ys → f y ∷ ys) [] (x ∷ xs)
                                 ∎

map-is-foldr :  ∀ {A B : Set} → (f : A → B) → map f ≡ foldr (λ y ys → f y ∷ ys) []
map-is-foldr f = extensionality (map-is-foldr-lemma f)

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree a→c c→b→c→c (leaf a) = a→c a
fold-Tree a→c c→b→c→c (node left b right) = c→b→c→c (fold-Tree a→c c→b→c→c left) b (fold-Tree a→c c→b→c→c right)

map-is-fold-Tree-lemma : ∀ {A B C D : Set} → (a→c : A → C) → (b→d : B → D) → (tree : Tree A B) →
                           map-Tree a→c b→d tree ≡ fold-Tree (λ a → leaf (a→c a)) (λ left b right → node left (b→d b) right) tree
map-is-fold-Tree-lemma a→c b→d (leaf a) = refl
map-is-fold-Tree-lemma a→c b→d (node left b right) =
  begin
    node (map-Tree a→c b→d left) (b→d b) (map-Tree a→c b→d right)
  ≡⟨ cong (λ t → node t (b→d b) (map-Tree a→c b→d right)) (map-is-fold-Tree-lemma a→c b→d left) ⟩
    node (fold-Tree (λ a → leaf (a→c a)) (λ left b right → node left (b→d b) right) left) (b→d b) (map-Tree a→c b→d right)
  ≡⟨  cong (λ t → node (fold-Tree (λ a → leaf (a→c a)) (λ left b right → node left (b→d b) right) left)  (b→d b) t) (map-is-fold-Tree-lemma a→c b→d right) ⟩
    node (fold-Tree (λ a → leaf (a→c a)) (λ left b right → node left (b→d b) right) left)  (b→d b) (fold-Tree (λ a → leaf (a→c a)) (λ left b right → node left (b→d b) right) right)
  ∎


map-is-fold-Tree : ∀ {A B C D : Set} → (f : A → C) → (g : B → D) → map-Tree f g ≡ fold-Tree (λ a → leaf (f a)) (λ left b right → node left (g b) right)
map-is-fold-Tree f g = extensionality (λ t → map-is-fold-Tree-lemma f g t)

downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n

sum : List ℕ → ℕ
sum = foldr _+_ 0

n∸n≡zero : ∀ {n : ℕ} → n ∸ n ≡ zero
n∸n≡zero {zero} = refl
n∸n≡zero {suc n} = n∸n≡zero {n}

n+m∸n≡m : ∀ (m n : ℕ) → (n + m) ∸ n ≡ m
n+m∸n≡m zero n = begin
                   (n + zero) ∸ n
                 ≡⟨ cong (_∸ n) (+-comm n zero) ⟩
                   (zero + n) ∸ n
                 ≡⟨⟩
                   n ∸ n 
                 ≡⟨ n∸n≡zero {n} ⟩
                   zero
                 ∎
n+m∸n≡m (suc m) zero = refl
n+m∸n≡m (suc m) (suc n) = begin
                            (suc n + suc m) ∸ suc n
                          ≡⟨⟩
                            suc (n + suc m) ∸ suc n
                          ≡⟨⟩
                            n + suc m ∸ n 
                          ≡⟨ n+m∸n≡m (suc m) n ⟩
                            suc m
                          ∎

n*n∸n+n≡n*n : ∀ (n : ℕ) → (n * n ∸ n) + n ≡ n * n
n*n∸n+n≡n*n zero = refl
n*n∸n+n≡n*n (suc n) = begin
                        (suc n * suc n ∸ suc n) + suc n
                      ≡⟨⟩
                        (suc n + (n * suc n) ∸ suc n) + suc n
                      ≡⟨ cong (_+ (suc n)) (n+m∸n≡m (n * suc n) (suc n)) ⟩
                        (n * suc n) + suc n
                      ≡⟨ +-comm (n * suc n) (suc n) ⟩
                        suc n + (n * suc n)
                      ≡⟨⟩
                        (suc n) * (suc n)
                      ∎


n+n≡n*2 : ∀ (n : ℕ) → n + n ≡ n * 2
n+n≡n*2 zero = refl
n+n≡n*2 (suc n) = begin
                    suc n + suc n
                  ≡⟨ cong ((suc n) +_) (sym (*-identityˡ (suc n))) ⟩
                    suc n + (1 * suc n)
                  ≡⟨⟩
                    2 * (suc n)
                  ≡⟨ *-comm 2 (suc n) ⟩
                    (suc n) * 2
                  ∎

n*n∸n≡n*n∸1 : ∀ (n : ℕ) → n * n ∸ n ≡ n * (n ∸ 1)
n*n∸n≡n*n∸1 zero = refl
n*n∸n≡n*n∸1 (suc n) =  begin
                         (n + n * suc n) ∸ n
                       ≡⟨ n+m∸n≡m (n * suc n) n ⟩
                         n * suc n
                       ≡⟨ *-comm n (suc n) ⟩
                         suc n * n
                       ≡⟨⟩
                         n + n * n
                       ∎

sum-downFrom : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
--sum ( n :: downFrom n) * 2 == n + n * n
sum-downFrom (suc n) = begin
                         sum (n ∷ downFrom n) * 2
                       ≡⟨⟩
                         (foldr _+_ 0 (n ∷ downFrom n)) * 2
                       ≡⟨⟩
                         (n + (foldr _+_ 0 (downFrom n))) * 2
                       ≡⟨ *-distribʳ-+ 2 n (foldr _+_ 0 (downFrom n)) ⟩
                         (n * 2) + (foldr _+_ 0 (downFrom n) * 2)
                       ≡⟨⟩
                         (n * 2) + (sum (downFrom n) * 2)
                       ≡⟨ cong ((n * 2) +_) (sum-downFrom n) ⟩
                         (n * 2) + (n * (n ∸ 1))
                       ≡⟨ cong ((n * 2) +_) (sym (n*n∸n≡n*n∸1 n)) ⟩
                         (n * 2) + (n * n ∸ n)
                       ≡⟨ cong (_+ (n * n ∸ n)) (sym (n+n≡n*2 n)) ⟩
                         (n + n) + (n * n ∸ n)
                       ≡⟨ +-assoc n n (n * n ∸ n) ⟩
                         (n + (n + (n * n ∸ n)))
                       ≡⟨ cong (n +_) (+-comm n (n * n ∸ n)) ⟩
                         (n + ((n * n ∸ n) + n))
                       ≡⟨ cong (n +_) (n*n∸n+n≡n*n n) ⟩
                         (n + n * n)
                       ∎
record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid
  
+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y = begin
                                     foldr _⊗_ y []
                                   ≡⟨⟩
                                     y
                                   ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
                                     (e ⊗ y)
                                   ≡⟨⟩
                                     foldr _⊗_ e [] ⊗ y
                                   ∎
                                      
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y = begin
                                          foldr _⊗_ y (x ∷ xs)
                                         ≡⟨⟩
                                          x ⊗ foldr _⊗_ y xs
                                         ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
                                          x ⊗ (foldr _⊗_ e xs ⊗ y)
                                         ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
                                          (x ⊗ foldr _⊗_ e xs) ⊗ y
                                         ≡⟨⟩
                                          foldr _⊗_ e (x ∷ xs) ⊗ y
                                         ∎

--  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys) 
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    (foldr _⊗_ e xs) ⊗ (foldr _⊗_ e ys)
  ∎

foldl : ∀ {A B : Set} → (_⊗_ : B → A → B) → (y : B) → List A → B
foldl _⊗_ y [] = y
foldl _⊗_ y (x ∷ xs) = foldl _⊗_ (y ⊗ x) xs

foldl-⊗ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e → ∀ (xs : List A) →
 (y : A) → y ⊗ (foldl _⊗_ e xs) ≡ foldl _⊗_ y xs 
foldl-⊗ _⊗_ e monoid-⊗ [] y = 
  begin
    y ⊗ (foldl _⊗_ e [])
  ≡⟨⟩
    y ⊗ e
  ≡⟨ identityʳ monoid-⊗ y ⟩
    y
  ≡⟨⟩
    foldl _⊗_ y []
  ∎

foldl-⊗ _⊗_ e monoid-⊗ (x ∷ xs) y = 
  begin
    y ⊗ (foldl _⊗_ e (x ∷ xs))
  ≡⟨⟩
    y ⊗ (foldl _⊗_ (e ⊗ x) xs)
  ≡⟨ cong (λ t → y ⊗ (foldl _⊗_ t xs)) (identityˡ monoid-⊗ x) ⟩
    y ⊗ (foldl _⊗_ x xs)
  ≡⟨ cong (y ⊗_) (sym (foldl-⊗ _⊗_ e monoid-⊗ xs x)) ⟩
    y ⊗ (x ⊗ (foldl _⊗_ e xs))
  ≡⟨ sym (assoc monoid-⊗ y x (foldl _⊗_ e xs)) ⟩
    (y ⊗ x) ⊗ (foldl _⊗_ e xs)
  ≡⟨ foldl-⊗ _⊗_ e monoid-⊗ xs (y ⊗ x) ⟩
    foldl _⊗_ (y ⊗ x) xs
  ≡⟨⟩
    foldl _⊗_ y (x ∷ xs)
  ∎

foldr-monoid-foldl-lemma : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs 
foldr-monoid-foldl-lemma _⊗_ e monoid-⊗ [] = refl
foldr-monoid-foldl-lemma _⊗_ e monoid-⊗ (x ∷ xs) = 
  begin
    foldr _⊗_ e (x ∷ xs)
  ≡⟨⟩
    x ⊗ foldr _⊗_ e xs
  ≡⟨ cong (x ⊗_) (foldr-monoid-foldl-lemma _⊗_ e monoid-⊗ xs) ⟩
    x ⊗ foldl _⊗_ e xs
  ≡⟨ foldl-⊗ _⊗_ e monoid-⊗ xs x ⟩
    foldl _⊗_ x xs
  ≡⟨ cong (λ t → foldl _⊗_ t xs) (sym (identityˡ monoid-⊗ x)) ⟩
    foldl _⊗_ (e ⊗ x) xs
  ≡⟨⟩
    foldl _⊗_ e (x ∷ xs)
  ∎

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) → All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where
  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) → All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys = λ {all-P-ys → ⟨ [] , all-P-ys  ⟩}
  to (x ∷ xs) ys =  λ {(Px ∷ all-P-xs++ys) → 
                           ⟨ (Px ∷ (proj₁ (to xs ys all-P-xs++ys))) ,
                             (proj₂ (to xs ys all-P-xs++ys)) ⟩}
  
  from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →  (All P xs × All P ys) → All P (xs ++ ys) 
  from [] ys = λ { ⟨ [] , all-P-ys ⟩ → all-P-ys }
  from (x ∷ xs) ys = λ { ⟨ Px ∷ all-P-xs , all-P-ys ⟩ → Px ∷ (from xs ys ⟨ all-P-xs , all-P-ys ⟩)}
  
Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) → Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
    {
      to = to xs ys;
      from = from xs ys
    }
  where
  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) → Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
  to [] ys any-P-ys = inj₂ any-P-ys
  to (x ∷ xs) ys (there any-P-xs++ys) with to xs ys any-P-xs++ys  
  ...                                   | (inj₁ any-P-xs) = inj₁ (there any-P-xs)
  ...                                   | (inj₂ any-P-ys) = inj₂ any-P-ys
  to (x ∷ xs) ys (here Px) = inj₁ (here Px)
  
  from : ∀ {A : Set} {P : A → Set} (xs ys : List A) → (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
  from [] ys (inj₂ any-P-ys) = any-P-ys 
  from (x ∷ xs) ys (inj₁ (there any-P-xs)) = there (from xs ys (inj₁ any-P-xs))
  from (x ∷ xs) ys (inj₁ (here Px)) = here Px
  from (x ∷ xs) ys (inj₂ any-P-ys) = there (from xs ys (inj₂ any-P-ys))

∈-++ : ∀ {A : Set} → (xs ys : List A) → (z : A) → (z ∈ (xs ++ ys)) ⇔ ((z ∈ xs) ⊎ (z ∈ ys))
∈-++ xs ys z = Any-++-⇔ xs ys

postulate
  ×-η : ∀ {A B : Set} → (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) → All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    ; from∘to  =  from∘to xs ys
    ; to∘from  =  to∘from xs ys
    }
  where
  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) → All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys = λ {all-P-ys → ⟨ [] , all-P-ys  ⟩}
  to (x ∷ xs) ys =  λ {(Px ∷ all-P-xs++ys) → 
                           ⟨ (Px ∷ (proj₁ (to xs ys all-P-xs++ys))) ,
                             (proj₂ (to xs ys all-P-xs++ys)) ⟩}
  
  from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →  (All P xs × All P ys) → All P (xs ++ ys) 
  from [] ys = λ { ⟨ [] , all-P-ys ⟩ → all-P-ys }
  from (x ∷ xs) ys = λ { ⟨ Px ∷ all-P-xs , all-P-ys ⟩ → Px ∷ (from xs ys ⟨ all-P-xs , all-P-ys ⟩)}
  
  from∘to : ∀ {A : Set} {P : A → Set} (xs ys : List A) → (z : (All P (xs ++ ys))) → from xs ys (to xs ys z) ≡ z
  from∘to [] ys _ = refl
  from∘to (x ∷ xs) ys (Px ∷ all-P-xs++ys) = 
      begin
        Px ∷ from xs ys ⟨ proj₁ (to xs ys all-P-xs++ys) , proj₂ (to xs ys all-P-xs++ys) ⟩
      ≡⟨ cong (λ t → Px ∷ from xs ys t) (×-η (to xs ys all-P-xs++ys)) ⟩
        Px ∷ from xs ys (to xs ys all-P-xs++ys)
      ≡⟨ cong (Px ∷_) (from∘to xs ys all-P-xs++ys) ⟩
        Px ∷ all-P-xs++ys
      ∎
           
  to∘from : ∀ {A : Set} {P : A → Set} (xs ys : List A) → (z : (All P xs × All P ys)) → to xs ys (from xs ys z) ≡ z
  to∘from [] ys (⟨ [] , _ ⟩) = refl
  to∘from (x ∷ xs) ys (⟨ (Px ∷ all-P-xs) , all-P-ys ⟩) = 
    begin
      ⟨ Px ∷ proj₁ (to xs ys (from xs ys ⟨ all-P-xs , all-P-ys ⟩)) , proj₂ (to xs ys (from xs ys ⟨ all-P-xs , all-P-ys ⟩)) ⟩
    ≡⟨ cong (λ t → ⟨ Px ∷ proj₁ t , proj₂ t ⟩) (to∘from xs ys ⟨ all-P-xs , all-P-ys ⟩) ⟩
      ⟨ Px ∷ proj₁ ⟨ all-P-xs , all-P-ys ⟩ , proj₂ ⟨ all-P-xs , all-P-ys ⟩ ⟩
    ≡⟨⟩
      ⟨ Px ∷ all-P-xs , all-P-ys ⟩
    ∎

¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ xs =
  record
    {
      to = to xs;
      from = from xs
    }
  where
  to : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
  to [] _ = []
  to (x ∷ xs) any-P-x∷xs→⊥ = (λ Px → any-P-x∷xs→⊥ (here Px)) ∷ to xs (λ any-P-xs → any-P-x∷xs→⊥ (there any-P-xs))

  from : ∀ {A : Set} {P : A → Set} (xs : List A)  → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
  from [] [] = λ() 
  from (x ∷ xs) (¬Px ∷ all-¬P-xs) = λ {(here Px) → ¬Px Px; (there any-P-xs) → from xs all-¬P-xs any-P-xs}

  {- ¬_ is not a normal function, which type is : Set → Set.
     P is either not a normal function, which type is : P → Set
  -}

¬Any≃All¬ : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs ≃ All (¬_ ∘ P) xs
¬Any≃All¬ xs =
  record { to = to xs; from = from xs; from∘to = from∘to xs; to∘from = to∘from xs}
  where
  to : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
  to [] _ = []
  to (x ∷ xs) any-P-x∷xs→⊥ = (λ Px → any-P-x∷xs→⊥ (here Px)) ∷ to xs (λ any-P-xs → any-P-x∷xs→⊥ (there any-P-xs))

  from : ∀ {A : Set} {P : A → Set} (xs : List A)  → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
  from [] [] = λ() 
  from (x ∷ xs) (¬Px ∷ all-¬P-xs) = λ {(here Px) → ¬Px Px; (there any-P-xs) → from xs all-¬P-xs any-P-xs}
  
  from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) (y : (¬_ ∘ Any P) xs) → from xs (to xs y) ≡ y
  from∘to [] _ = refl
  from∘to (x ∷ xs) any-P-x∷xs→⊥ = 
    extensionality 
      (λ { (here Px) → refl;
           (there any-P-xs) →  begin
                                 from xs (to xs (λ any-P-xs → any-P-x∷xs→⊥ (there any-P-xs))) any-P-xs
                               ≡⟨ cong (λ t → t any-P-xs) (from∘to xs (λ any-P-xs → any-P-x∷xs→⊥ (there any-P-xs))) ⟩
                                 (λ any-P-xs → any-P-x∷xs→⊥ (there any-P-xs)) any-P-xs
                               ≡⟨⟩
                                 any-P-x∷xs→⊥ (there any-P-xs)
                               ∎ 
         })

  to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) (y : All (¬_ ∘ P) xs) → to xs (from xs y) ≡ y
  to∘from [] [] = refl
  to∘from (x ∷ xs) (¬Px ∷ all-¬P-xs) = 
    begin
      ¬Px ∷ to xs (from xs all-¬P-xs)
    ≡⟨ cong (¬Px ∷_) (to∘from xs all-¬P-xs) ⟩
      ¬Px ∷ all-¬P-xs
    ∎

All-∀ : ∀ {A : Set} {P : A → Set} (xs : List A) → (All P xs ≃ (∀ y → y ∈ xs → P y))
All-∀ xs = record {to = to xs; from = from xs; from∘to = from∘to xs; to∘from = to∘from xs}
  where 
  to : ∀ {A : Set} {P : A → Set} (xs : List A) → (All P xs → (∀ y → y ∈ xs → P y)) 
  to [] [] = λ x → λ()
  to (x ∷ xs) (Px ∷ all-P-xs) = λ {y → λ { (here refl) → Px ; (there any-P-xs) → to xs all-P-xs y any-P-xs}}
  
  from : ∀ {A : Set} {P : A → Set} (xs : List A) → ((∀ x → x ∈ xs → P x) → All P xs)
  from [] = λ f → []
  from (x ∷ xs) = λ { x→x∈x∷xs→Px → x→x∈x∷xs→Px x (here refl) ∷ (from xs λ {x → λ {x∈xs → x→x∈x∷xs→Px x (there x∈xs)}})}

  from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) → (z : All P xs) → from xs (to xs z) ≡ z
  from∘to [] [] = refl
  from∘to (x ∷ xs) (Px ∷ all-P-xs) = 
    begin
      Px ∷ from xs (to xs all-P-xs)     
    ≡⟨ cong (Px ∷_) (from∘to xs all-P-xs) ⟩
      Px ∷ all-P-xs
    ∎

  postulate  
    to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) → (z : (∀ y → y ∈ xs → P y)) → to xs (from xs z) ≡ z 
{-   to∘from (x ∷ xs) z = 
    begin
      (λ { y → λ { (here refl) → z x (here refl) ; (there any-P-xs) → to xs (from xs (λ { x → λ { x∈xs → z x (there x∈xs) } })) y any-P-xs } })
    ≡⟨ cong (λ t → (λ { y → λ { (here refl) → z x (here refl) ; (there any-P-xs) →  t y any-P-xs } })) (to∘from xs (λ { x → λ { x∈xs → z x (there x∈xs) } })) ⟩
      (λ { y → λ { (here refl) → z x (here refl) ; (there any-P-xs) →  (λ { x → λ { x∈xs → z x (there x∈xs) } }) y any-P-xs } })
    ≡⟨⟩
      (λ { y → λ { (here refl) → z x (here refl) ; (there any-P-xs) →  (λ { x∈xs → z y (there x∈xs) }) any-P-xs } })
    ≡⟨⟩
      (λ { y → λ { (here refl) → z x (here refl) ; (there any-P-xs) →  z y (there  any-P-xs) } })
    ≡⟨⟩
      (λ { y → λ { (here refl) → z y (here refl) ; (there any-P-xs) →  z y (there  any-P-xs) } })
    ≡⟨⟩
      (λ { y → λ { u → z y u } })
    ≡⟨⟩
      (λ { y →  z y })
    ≡⟨⟩
      z
    ∎ -}

Any-∃ : ∀ {A : Set} {P : A → Set} (xs : List A) → Any P xs ≃ ∃[ x ] (x ∈ xs × P x)
Any-∃ xs = record { to = to xs ; from = from xs ; from∘to = from∘to xs ; to∘from = to∘from xs }
  where
  to : ∀ {A : Set} {P : A → Set} (xs : List A) → Any P xs → ∃[ x ] (x ∈ xs × P x)
  to (x ∷ xs) (here Px) = ⟨ x , ⟨ here refl , Px ⟩ ⟩
  to (x ∷ xs) (there any-P-xs) = let ⟨ y , ⟨ y∈xs , Py ⟩ ⟩ = to xs any-P-xs
                                 in ⟨ y , ⟨ (there y∈xs) , Py ⟩ ⟩

  from : ∀ {A : Set} {P : A → Set} (xs : List A) → ∃[ x ] (x ∈ xs × P x) → Any P xs
  from (x ∷ xs) (⟨ y , ⟨ (here refl) , Py ⟩ ⟩) = here Py
  from (x ∷ xs) (⟨ y , ⟨ (there y∈xs) , Py ⟩ ⟩) = there (from xs (⟨ y , ⟨ y∈xs , Py ⟩ ⟩))
  
  from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) → (y : (Any P xs)) → (from xs (to xs y)) ≡ y
  from∘to (x ∷ xs) (here Px) = refl
  from∘to (x ∷ xs) (there any-P-xs) =
    begin
      from (x ∷ xs) (to (x ∷ xs) (there any-P-xs))
    ≡⟨ cong there (from∘to xs any-P-xs) ⟩
      there any-P-xs
    ∎

  to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) → (y : ∃[ x ] (x ∈ xs × P x)) → (to xs (from xs y)) ≡ y
  to∘from (x ∷ xs) (⟨ y , ⟨ (here refl) , Py ⟩ ⟩) = refl
  to∘from (x ∷ xs) (⟨ y , ⟨ (there y∈xs) , Py ⟩ ⟩) =
    begin
      to (x ∷ xs) (from (x ∷ xs) (⟨ y , ⟨ (there y∈xs) , Py ⟩ ⟩))
    -- ≡⟨⟩
    --  ⟨ to xs (from xs ⟨ y , ⟨ y∈xs , Py ⟩ ⟩) .proj₁ , ⟨ there (to xs (from xs ⟨ y , ⟨ y∈xs , Py ⟩ ⟩) .proj₂ .proj₁) , to xs (from xs ⟨ y , ⟨ y∈xs , Py ⟩ ⟩) .proj₂ .proj₂ ⟩ ⟩
    ≡⟨ cong (λ t → (⟨ t .proj₁ , ⟨ there (t .proj₂ .proj₁) , t .proj₂ .proj₂ ⟩ ⟩)) (to∘from xs ⟨ y , ⟨ y∈xs , Py ⟩ ⟩) ⟩
      ⟨ y , ⟨ there y∈xs , Py ⟩ ⟩
    ∎ 

{- 
data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A
 -}
Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }

any : ∀ { A : Set} → (A → Bool) → List A → Bool
any p = foldr _∨_ true ∘ map p

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? []                                 =  no (λ()) 
Any? P? (x ∷ xs) with P? x   | Any? P? xs
...                 | yes Px | _           =  yes (here Px)
...                 | _      | yes Pxs     =  yes (there Pxs)
...                 | no ¬Px | no ¬Pxs     =  no (λ {(here Px) → ¬Px Px;
                                                     (there any-P-xs) → ¬Pxs any-P-xs})

data merge {A : Set} : (xs ys zs : List A) → Set where

  [] : merge [] [] []

  left-∷ : ∀ {x xs ys zs} → merge xs ys zs → merge (x ∷ xs) ys (x ∷ zs)

  right-∷ : ∀ {y xs ys zs} → merge xs ys zs → merge xs (y ∷ ys) (y ∷ zs)

_ : merge [ 1 , 4 ] [ 2 , 3 ] [ 1 , 2 , 3 , 4 ]
_ = left-∷ (right-∷ (right-∷ (left-∷ [])))

split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A) → ∃[ xs ] ∃[ ys ] (merge xs ys zs × All P xs × All (¬_ ∘ P) ys)
split P? []                                                                 = ⟨ [] ,     ⟨ [] ,     ⟨ [] ,        ⟨ [] ,       [] ⟩ ⟩ ⟩ ⟩
split P? (z ∷ zs) with P? z   | split P? zs
...                  | yes Pz | ⟨ xs , ⟨ ys , ⟨ m , ⟨ Pxs , ¬Pys  ⟩  ⟩  ⟩ ⟩ = ⟨ z ∷ xs , ⟨ ys ,     ⟨ left-∷ m ,  ⟨ Pz ∷ Pxs , ¬Pys ⟩ ⟩ ⟩ ⟩
...                  | no ¬Pz | ⟨ xs , ⟨ ys , ⟨ m , ⟨ Pxs , ¬Pys  ⟩  ⟩  ⟩ ⟩ = ⟨ xs ,     ⟨ z ∷ ys , ⟨ right-∷ m , ⟨ Pxs ,      ¬Pz ∷ ¬Pys ⟩ ⟩ ⟩ ⟩