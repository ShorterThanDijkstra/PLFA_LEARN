module part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
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

