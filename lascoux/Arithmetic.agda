{-# OPTIONS --allow-unsolved-metas #-}

module Arithmetic where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

open import Relation.Nullary
open import Data.Empty
open Relation.Binary.PropositionalEquality.≡-Reasoning

open ≤-Reasoning renaming (_∎ to _≤∎; begin_ to begin-≤_) hiding (_≡⟨_⟩_)

variable
    n : ℕ

≤-up : {n m : ℕ} -> m ≤ n -> m ≤ suc n
≤-up {n} {.0} z≤n = z≤n
≤-up {.(suc _)} {.(suc _)} (s≤s q) = s≤s (≤-up q)

≤-down : {n m : ℕ} -> suc m ≤ n -> m ≤ n
≤-down {.(suc _)} {zero} (s≤s p) = z≤n
≤-down {.(suc _)} {suc n} (s≤s p) = s≤s (≤-down p)

≤-down2 : {n m : ℕ} -> suc m ≤ suc n -> m ≤ n
≤-down2 {m} {n} (s≤s p) = p

≤-abs : {A : Set} -> {n : ℕ} -> (suc n ≤ 0) -> A
≤-abs ()

postulate
    ∸-implies-≤ : {p q r : ℕ} -> (p ≡ q ∸ r) -> (p ≤ q)
    ≤-remove-+ : {p q r : ℕ} -> (p + q ≤ r) -> (q ≤ r)
    introduce-≤-from-+ : {p q r : ℕ} -> (p + q ≡ r) -> (p ≤ r)
    ≡-down2 : (p q : ℕ) -> suc p ≡ suc q -> p ≡ q
    +-three-assoc : {k i r : ℕ} -> k + (i + r) ≡ (i + k) + r
    introduce-∸ : {p q r : ℕ} -> (r ≤ q) -> (p + r ≡ q) -> (p ≡ q ∸ r)
    eliminate-∸ : {p q r : ℕ} -> (r ≤ q) -> (p ≡ q ∸ r) -> (p + r ≡ q)
    introduce-∸-≤ : {p q r : ℕ} -> (r ≤ q) -> (p + r ≤ q) -> (p ≤ q ∸ r)
    eliminate-∸-≤ : {p q r : ℕ} -> (r ≤ q) -> (p ≤ q ∸ r) -> (p + r ≤ q)
    introduce-∸-≤l : {p q r : ℕ} -> (r ≤ p) -> (p ≤ q + r) -> (p ∸ r ≤ q)
    eliminate-∸-≤l : {p q r : ℕ} -> (r ≤ p) -> (p ∸ r ≤ q) -> (p ≤ q + r)
    ∸-to-zero : {p q : ℕ} -> {p ≡ q} -> (p ∸ q ≡ 0)
    minus-plus : {p q : ℕ} -> {q ≤ p} -> p ∸ q + q ≡ p
    ∸-down2 : {n r : ℕ} -> {r ≤ n} -> ((suc n) ∸ (suc r)) ≡ n ∸ r
    ≤-up2-+ : {p q r : ℕ} -> (p ≤ q) -> (r + p ≤ r + q)
    ≤-up-+ : {p q r : ℕ} -> (p ≤ q) -> (p ≤ q + r)
    ≤-down-+ : {p q r : ℕ} -> (p + r ≤ q) -> (p ≤ q)
    ∸-anti-≤ : {p q r : ℕ} -> (q ≤ p) -> (p ≤ r) -> (r ∸ p) ≤ (r ∸ q)

∸-up : {n r : ℕ} -> (r < n) -> (n ∸ r) ≡ suc (n ∸ (suc r))
∸-up {suc zero} {zero} p = refl
∸-up {suc zero} {suc r} (s≤s p) = ≤-abs p
∸-up {suc (suc n)} {zero} p = refl
∸-up {suc (suc n)} {suc r} (s≤s p) = ∸-up {suc n} {r} p
