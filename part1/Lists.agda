module part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityˡ; +-identityʳ; *-assoc; *-comm; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
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

 