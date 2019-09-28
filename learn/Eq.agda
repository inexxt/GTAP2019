module Eq where

variable
    A B : Set
    x y z : A
data _≡_ (x : A) : A -> Set where
    refl : x ≡ x

infix 4 _≡_

sym : x ≡ y -> y ≡ x
sym refl = refl

trans : x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

cong : (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

subst : (C : A -> Set) -> x ≡ y -> C x -> C y
subst C refl x = x


module ≡-Reasoning {A : Set} where

    infix  1 begin_
    infixr 2 _≡⟨_⟩_ _≡⟨⟩_
    infix  3 _∎

    begin_ : {x y : A} -> x ≡ y -> x ≡ y
    begin p = p

    _≡⟨⟩_ : (x : A) {y : A} -> x ≡ y -> x ≡ y
    x ≡⟨⟩ p = p

    _≡⟨_⟩_ : (x : A) {y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
    x ≡⟨ p ⟩ q = trans p q

    _∎ : (x : A) -> x ≡ x
    x ∎ = refl


open ≡-Reasoning

trans' : x ≡ y -> y ≡ z -> x ≡ z
trans' {x = x} {y = y} {z = z} p q =
        begin
            x
        ≡⟨ p ⟩
            y
        ≡⟨ q ⟩
            z
        ∎

data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
    +-identity : ∀ (m : ℕ) → m + zero ≡ m
    +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : (m n : ℕ) -> m + n ≡ n + m
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
