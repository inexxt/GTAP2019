{-# OPTIONS --without-K #-}

module Arithmetic where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)
open import Data.Product using (∃; _,_)

open import Relation.Nullary
open import Data.Empty
open Relation.Binary.PropositionalEquality.≡-Reasoning

open ≤-Reasoning renaming (_∎ to _≤∎; begin_ to begin-≤_)

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

abs-refl : {A : Set} -> n < n -> A
abs-refl p = ⊥-elim (1+n≰n p)

abs-suc : {A : Set} -> suc n < n -> A
abs-suc {n} p = ⊥-elim (1+n≰n (≤-down p))

postulate
    ∸-implies-≤ : {p q r : ℕ} -> (p ≡ q ∸ r) -> (p ≤ q)
    ≤-remove-+ : {p q r : ℕ} -> (p + q ≤ r) -> (q ≤ r)
    introduce-≤-from-+ : {p q r : ℕ} -> (p + q ≡ r) -> (p ≤ r)
    ≡-down2 : {p q : ℕ} -> suc p ≡ suc q -> p ≡ q
    +-three-assoc : {k i r : ℕ} -> k + (i + r) ≡ (i + k) + r
    introduce-∸ : {p q r : ℕ} -> (r ≤ q) -> (p + r ≡ q) -> (p ≡ q ∸ r)
    eliminate-∸ : {p q r : ℕ} -> (r ≤ q) -> (p ≡ q ∸ r) -> (p + r ≡ q)
    introduce-∸-≤ : {p q r : ℕ} -> (r ≤ q) -> (p + r ≤ q) -> (p ≤ q ∸ r)
    eliminate-∸-≤ : {p q r : ℕ} -> (r ≤ q) -> (p ≤ q ∸ r) -> (p + r ≤ q)
    introduce-∸-≤l : {p q r : ℕ} -> (r ≤ p) -> (p ≤ q + r) -> (p ∸ r ≤ q)
    eliminate-∸-≤l : {p q r : ℕ} -> (r ≤ p) -> (p ∸ r ≤ q) -> (p ≤ q + r)
    ∸-to-zero : {p q : ℕ} -> (p ≡ q) -> (p ∸ q ≡ 0)
    minus-plus : {p q : ℕ} -> {q ≤ p} -> p ∸ q + q ≡ p
    ∸-down2 : {n r : ℕ} -> {r ≤ n} -> ((suc n) ∸ (suc r)) ≡ n ∸ r
    ≤-up2-+ : {p q r : ℕ} -> (p ≤ q) -> (r + p ≤ r + q)
    ≤-up2-r-+ : {p q r : ℕ} -> (p ≤ q) -> (p + r ≤ q + r)
    ≤-up-r-+ : {p q r : ℕ} -> (p ≤ q) -> (p ≤ q + r)
    ≤-up-+ : {p q r : ℕ} -> (p ≤ q) -> (p ≤ r + q)
    ≤-down-+ : {p q r : ℕ} -> (p + r ≤ q) -> (p ≤ q)
    ≡-down-+ : {p q r : ℕ} -> (r + p ≡ r + q) -> (p ≡ q)
    ≡-down-r-+ : {p q r : ℕ} -> (p + r ≡ q + r) -> (p ≡ q)
    ∸-anti-≤ : {p q r : ℕ} -> (q ≤ p) -> (p ≤ r) -> (r ∸ p) ≤ (r ∸ q)
    +-unit : {n : ℕ} -> n + zero ≡ n
    ≤-≡ : {n k : ℕ} -> (n ≤ k) -> (k ≤ n) -> (n ≡ k)
    plus-minus : {p q : ℕ} -> (p ≤ q) -> p + (q ∸ p) ≡ q

zero-∸ : (n : ℕ) -> (zero ∸ n ≡ zero)
zero-∸ zero = refl
zero-∸ (suc n) = refl

∸-∸-+ : {p q r : ℕ} -> (r ≤ q) -> (q ≤ p + r) -> p ∸ (q ∸ r) ≡ (p + r) ∸ q
∸-∸-+ {p} {zero} {zero} rq qpr = +-comm zero p
∸-∸-+ {p} {suc q} {zero} rq qpr rewrite +-comm p 0 = refl
∸-∸-+ {p} {suc q} {suc r} (s≤s rq) qpr =
  let rec = ∸-∸-+ {p} {q} {r} rq (≤-down2 (≤-trans qpr (≤-reflexive (+-three-assoc {p} {1} {r}))))
      lemma : (p + r) ∸ q ≡ (p + suc r) ∸ suc q
      lemma = cong (λ x -> x ∸ suc q) (≡-sym (+-three-assoc {p} {1} {r}))
  in ≡-trans rec lemma

∸-up : {n r : ℕ} -> (r < n) -> (n ∸ r) ≡ suc (n ∸ (suc r))
∸-up {suc zero} {zero} p = refl
∸-up {suc zero} {suc r} (s≤s p) = ≤-abs p
∸-up {suc (suc n)} {zero} p = refl
∸-up {suc (suc n)} {suc r} (s≤s p) = ∸-up {suc n} {r} p

nowhere : {n k : ℕ} -> (¬ (n < k)) -> (¬ (n ≡ k)) -> (¬ (n ≡ 1 + k)) -> (¬ (1 + k < n)) -> ⊥
nowhere {zero} {zero} p1 p2 p3 p4 = p2 refl
nowhere {zero} {suc k} p1 p2 p3 p4 = p1 (s≤s z≤n)
nowhere {suc zero} {zero} p1 p2 p3 p4 = p3 refl
nowhere {suc (suc n)} {zero} p1 p2 p3 p4 = p4 (s≤s (s≤s z≤n))
nowhere {suc n} {suc k} p1 p2 p3 p4 = nowhere (λ x → p1 (s≤s x)) (λ x → p2 (cong suc x)) (λ x → p3 (cong suc x)) (λ x → p4 (s≤s x))

≤-≠-≤ : {n m : ℕ} -> (n ≤ suc m) -> ¬ (n ≡ suc m) -> (n ≤ m)
≤-≠-≤ {zero} {zero} p q = z≤n
≤-≠-≤ {zero} {suc m} p q = z≤n
≤-≠-≤ {suc zero} {zero} p q = ⊥-elim (q refl)
≤-≠-≤ {suc (suc n)} {zero} (s≤s ()) q
≤-≠-≤ {suc n} {suc m} (s≤s p) q = s≤s (≤-≠-≤ p λ x → q (cong suc x))

≤-∃ : (n m : ℕ) -> (n ≤ m) -> ∃ (λ t -> t + n ≡ m)
≤-∃ .0 m z≤n = m , +-unit
≤-∃ (suc n) (suc m) (s≤s p) =
  let rec-t , rec-p = ≤-∃ n m p
  in  rec-t , ≡-trans (+-three-assoc {rec-t} {1} {n}) (cong suc rec-p)

rrr : {k : ℕ} -> k ≤ k
rrr = ≤-reflexive refl
