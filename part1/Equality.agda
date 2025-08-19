module part1.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl  =  refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B} → u ≡ x → v ≡ y → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl a = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst p refl px = px

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 step-≡-∣ step-≡-⟩
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y  =  x≡y

  step-≡-∣ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  step-≡-∣ x x≡y  =  x≡y

  step-≡-⟩ : ∀ (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡-⟩ x y≡z x≡y  =  trans x≡y y≡z

  syntax step-≡-∣ x x≡y      =  x ≡⟨⟩ x≡y
  syntax step-≡-⟩ x y≡z x≡y  =  x ≡⟨  x≡y ⟩ y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎  =  refl

open ≡-Reasoning

{-
trans′的定义用了_≡⟨_⟩_, _≡⟨_⟩_的定义用了trans
-}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
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

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ} → zero ≤ n

  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n { zero }
≤-refl {suc n} = s≤s {n} {n} (≤-refl {n})

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans {zero} {n} {p} (z≤n {n}) _ = z≤n {p}
≤-trans {suc m} {suc n} {suc p} (s≤s {m} {n} m≤n) (s≤s {n} {p} n≤p) = s≤s {m} {p} (≤-trans {m} {n} {p} m≤n n≤p)

module ≤-Reasoning where
  infix 1 begin≤_
  infixr 2 step-≤-| step-≤-⟩
  infix 3 _end≤

  begin≤_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
  begin≤_ x≤y = x≤y

  step-≤-| : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
  step-≤-| x x≤y = x≤y

  step-≤-⟩ : ∀ (x : ℕ) {y z : ℕ} → y ≤ z → x ≤ y → x ≤ z
  step-≤-⟩ x y≤z x≤y = ≤-trans x≤y y≤z

  syntax step-≤-| x x≤y = x ≤⟨⟩ x≤y
  syntax step-≤-⟩ x y≤z x≤y = x ≤⟨ x≤y ⟩ y≤z

  _end≤ : ∀ (x : ℕ) → x ≤ x
  x end≤ = ≤-refl

open ≤-Reasoning

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q =
  begin≤
    zero + p
  ≤⟨⟩
    p
  ≤⟨ p≤q ⟩
    q
  ≤⟨⟩
    zero + q
  end≤
+-monoʳ-≤ (suc n) p q p≤q =
  begin≤
    (suc n) + p
  ≤⟨⟩
    suc (n + p)
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    suc (n + q)
  ≤⟨⟩
    (suc n) + q
  end≤

≡-to-≤ : ∀ {m n : ℕ} → m ≡ n → m ≤ n
≡-to-≤ refl = ≤-refl

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n zero m≤n =
  begin≤
    m + zero
  ≤⟨  ≡-to-≤ (+-comm m zero) ⟩
    zero + m
  ≤⟨⟩
    m
  ≤⟨ m≤n ⟩
    n
  ≤⟨⟩
    zero + n
  ≤⟨ ≡-to-≤ (sym (+-identity n)) ⟩
    n + zero
  end≤
+-monoˡ-≤ m n (suc p) m≤n =
  begin≤
    m + (suc p)
  ≤⟨ ≡-to-≤ (+-comm m (suc p)) ⟩
    (suc p) + m
  ≤⟨⟩
    suc (p + m)
  ≤⟨ ≡-to-≤ (cong suc (+-comm p m)) ⟩
    suc (m + p)
  ≤⟨ s≤s (+-monoˡ-≤ m n p m≤n) ⟩
    suc (n + p)
  ≤⟨ ≡-to-≤ (cong suc (+-comm n p)) ⟩
    suc (p + n)
  ≤⟨⟩
    (suc p) + n
  ≤⟨ ≡-to-≤ (+-comm (suc p) n) ⟩
    n + (suc p)
  end≤

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q =
  begin≤
    m + p
  ≤⟨ +-monoˡ-≤ m n p m≤n ⟩
    n + p
  ≤⟨ +-monoʳ-≤ n p q p≤q ⟩
    n + q
  end≤

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where

  odd-suc : ∀ {n : ℕ} → even n → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm m n ev  rewrite +-comm n m  =  ev

even-comm′ : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm′ m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl       = ev

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
refl-≐ {A} {x} = λ P → λ Px → Px

trans-≐ : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
trans-≐ {A} {x} {y} {z} x≐y y≐z = λ P → λ Px → (y≐z P (x≐y P Px))

sym-≐ : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P  =  Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ {A} {x} {y} refl = λ P → λ Px → Px

≐-implies-≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y  =  Qy
  where
  Q : A → Set
  Q z = x ≡ z
  Qx : Q x
  Qx = refl
  Qy : Q y
  Qy = x≐y Q Qx
