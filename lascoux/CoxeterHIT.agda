{-# OPTIONS --cubical #-}

module _ where

open import Cubical.Foundations.Everything
open import Cubical.Core.Everything
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin

infixr 20 _∷_

data L : Type₀ where
  [] : L
  _∷_ : ℕ → L → L
  cancel : ∀ n l → n ∷ n ∷ l ≡ l
  swap : ∀ {k n} l → suc k < n → n ∷ k ∷ l ≡ k ∷ n ∷ l
  braid : ∀ n l → ((suc n) ∷ n ∷ (suc n) ∷ l) ≡ (n ∷ (suc n) ∷ n ∷ l)
  trunc : isSet L

_++_ : L → L → L
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
cancel n xs i ++ ys = cancel n (xs ++ ys) i
swap xs x i ++ ys = swap (xs ++ ys) x i
braid n xs i ++ ys = braid n (xs ++ ys) i
trunc xs zs p q i j ++ ys = trunc (xs ++ ys) (zs ++ ys) (λ i → p i ++ ys) (λ i → q i ++ ys) i j

length : L → Fin 2
length [] = 0 , (1 , refl)
length (x ∷ xs) with length xs
length (x ∷ xs) | fst₁ , q = {!!}
length (cancel n xs i) = {!!}
length (swap xs x i) = {!!}
length (braid n xs i) = {!!}
length (trunc xs xs₁ x y i i₁) = {!!}

f : ∀ {x y} → Trichotomy x y → L → Type₀
f (lt x) xs = {!!}
f (eq x) xs = {!!}
f (gt x) xs = {!!}

code : L → Type₀
code [] = Unit
code (x ∷ []) = ⊥
code (x ∷ y ∷ xs) = ⊥
code (x ∷ cancel n xs i) = {!!}
code (x ∷ swap xs x₁ i) = {!!}
code (x ∷ braid n xs i) = {!!}
code (x ∷ trunc xs xs₁ x₁ y i i₁) = {!!}
code (cancel n xs i) = {!code xs!}
code (swap xs x i) = ⊥
code (braid n xs i) = ⊥
code (trunc xs xs₁ x y i i₁) = {!!}

lemma : ∀ n → ((n ∷ []) ≡ []) → ⊥
lemma n p = subst code (sym p) tt
