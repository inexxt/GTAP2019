module Reduction where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; Σ; _×_; _,_; _,′_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

open import General
open import Relation.Nullary
open import Data.Empty
-- open import Relation.Binary.Reasoning.Setoid
open Relation.Binary.PropositionalEquality.≡-Reasoning


variable
    n : ℕ
    l : List ℕ

data _≃_ : List ℕ -> List ℕ -> Set where
    cancel : (n ∷ n ∷ []) ≃ []
    swap : {k : ℕ} -> (suc k < n) -> (n ∷ k ∷ []) ≃ (k ∷ n ∷ [])
    braid : (n ∷ (suc n) ∷ n ∷ []) ≃ ((suc n) ∷ n ∷ (suc n) ∷ [])
    prepend : (k : ℕ) -> {l l' : List ℕ} -> (l ≃ l') -> (k ∷ l) ≃ (k ∷ l')
    ++-respects : {l l' m m' : List ℕ} -> (l ≃ l') -> (m ≃ m') -> (l ++ m) ≃ (l' ++ m')
    refl : {l : List ℕ} -> l ≃ l
    comm : {l l' : List ℕ} -> (l ≃ l') -> l' ≃ l
    trans : {l l' l'' : List ℕ} -> (l ≃ l') -> (l' ≃ l'') -> l ≃ l''

data _∈_ : ℕ -> List ℕ -> Set where
    here : (n : ℕ) -> (l : List ℕ) -> n ∈ (n ∷ l)
    there : (k : ℕ) -> {n : ℕ} -> {l : List ℕ} -> (n ∈ l) -> n ∈ (k ∷ l)

data _∉_ : ℕ -> List ℕ -> Set where
    not-here : (n : ℕ) -> n ∉ []
    not-there : {k : ℕ} -> {n : ℕ} -> {¬ (k == n)} -> {l : List ℕ} -> (n ∉ l) -> n ∉ (k ∷ l)


_↓_ : (n : ℕ) -> (r : ℕ) -> List ℕ
n ↓ zero = []
zero ↓ suc zero = zero ∷ []
zero ↓ suc (suc r) = []
suc n ↓ suc r = n ∷ n ↓ r

↓-rec : {n k : ℕ} -> (k < n) -> (n ↓ suc k) ≡ (n ↓ k) ++ [ n ∸ (k + 1) ]
↓-rec {suc n} {zero} (s≤s z≤n) = refl
↓-rec {suc (suc n)} {suc k} (s≤s p) = cong (λ l -> suc n ∷ l) (↓-rec p)

abs : {A : Set} -> {k n : ℕ} -> (¬ (k ≤ n)) -> (k ≡ n) -> A
abs {_} {n} {k} p q = let r = ≤-reflexive q
                      in ⊥-elim (p r)

inv : (t : ℕ) -> {t ≤ 1} -> ℕ
inv .0 {z≤n} = 1
inv .1 {s≤s z≤n} = 0


-- for some reason, ≤-refl does not want to work
ext : {n m : ℕ} -> suc n ≡ suc m -> n ≡ m
ext {n} {.n} refl = refl

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

pa : {n i r : ℕ} -> suc (r + i) ≡ n -> suc i ≤ n
pa {zero} {i} {r} = λ ()
pa {suc n} {i} {zero} = ≤-reflexive
pa {suc n} {i} {suc r} = λ y -> ≤-up (pa {n} {i} {r} (ext y))

+-zero : n + zero ≡ n
+-zero {n} = +-comm n zero

<-zero : {n r : ℕ} -> suc r ≡ n -> zero < n
<-zero {.(suc r)} {r} refl = s≤s z≤n

<-down : {m n : ℕ} -> suc m < suc n -> m < n
<-down {m} {n} (s≤s p) = p

open Σ

postulate
    ≤-+-respects : {m n r p : ℕ} -> m ≤ n -> r ≤ p -> r + m ≤ p + n
    ∸-not-< : {n r : ℕ} -> (n > r) -> ¬ (zero ≡ n ∸ r)
    ∸-implies-≤ : {p q r : ℕ} -> (p ≡ q ∸ r) -> (p ≤ q)
    <-holes : {i n : ℕ} -> (1 + i + zero > n) -> (i < n) -> ⊥
    ∸-exact : {p q : ℕ} -> (q > p) -> (t : Σ ℕ (λ k -> k ≡ q ∸ p)) -> (proj₁ t + p ≡ q)
    +-cancel : {p q r : ℕ} -> (r + q ≡ r + p) -> (q ≡ p)
    ∸-up : {p q r : ℕ} -> (suc r ≤ q) -> (p ≡ q ∸ (suc r)) -> (suc p ≡ q ∸ r)
    ≤-remove-+ : {p q r : ℕ} -> (p + q ≤ r) -> (q ≤ r)

nnl=l : {l : List ℕ} -> {n : ℕ} -> (n ∷ n ∷ l) ≃ l
nnl=l = ++-respects cancel refl
l++nn=l : {l : List ℕ} -> {n : ℕ} -> (l ++ (n ∷ n ∷ [])) ≃ l
l++nn=l = trans (++-respects refl cancel) _

-- REMEMBER - i is (suc i)
canonize-p> : (n r1 r2 : ℕ)
              -> {i : ℕ}
              -> (zero < r1)
              -> (zero < r2)
              -> (r1 + r2 ≤ n)
              -> {i ≡ n ∸ (2 + r1)}
--              -> ((n ↓ (r2 + r1)) ++ [ suc i ]) ≃ (i ∷ n ↓ (r1 + r2))
              -> (((n ↓ r1) ++ [ 1 + i ] ++ (1 + i) ↓ r2) ++ [ 1 + i ]) ≃ (i ∷ (n ↓ (1 + r1 + r2)))
canonize-p> zero (suc r1) r2 {i} pr1 pr2 ()
canonize-p> (suc zero) (suc (suc r1)) (suc zero) pr1 pr2 (s≤s ())
canonize-p> (suc zero) (suc zero) (suc zero) {i} pr1 pr2 (s≤s ())
canonize-p> (suc (suc zero)) (suc zero) (suc zero) {i} pr1 pr2 prrn {pinr} rewrite pinr =
  trans (nnl=l {0 ∷ 1 ∷ []}) (comm l++nn=l)
canonize-p> (suc (suc (suc n))) (suc zero) (suc zero) {i} pr1 pr2 prrn {pinr} rewrite pinr =
  let x : ((2 +  n) ∷ 1 + n ∷ n ∷ 1 + n ∷ []) ≃ ((2 + n) ∷ n ∷ 1 + n ∷ n ∷ [])
      x = prepend (2 + n) (comm (braid {n}))
      y : {l : List ℕ} -> ((2 + n) ∷ n ∷ l) ≃ (n ∷ (2 + n) ∷ l)
      y = ++-respects (swap n<1+n) refl
  in trans x y
canonize-p> (suc (suc zero)) (suc (suc r1)) (suc zero) {i} pr1 pr2 (s≤s (s≤s prrn)) {pinr} =
  ≤-abs (≤-trans (≤-reflexive (+-comm 1 r1)) prrn)
canonize-p> (suc (suc (suc n))) (suc (suc r1)) (suc zero) {i} pr1 pr2 (s≤s prrn) {pinr} =
  let x = prepend (suc (suc n)) (canonize-p> (suc (suc n)) (suc r1) (suc zero) {i} (s≤s z≤n) pr2 (prrn) {pinr})
      y : (suc (suc n) ∷ [ i ]) ≃ (i ∷ [ suc (suc n) ])
      y = swap (s≤s (s≤s (∸-implies-≤ {i} {n} {suc r1} pinr)))
      z = ++-respects y (refl { (suc n) ∷ ((suc n) ↓ suc (r1 + 1))})
  in trans x z
canonize-p> (suc zero) (suc r1) (suc (suc r2)) {i} pr1 pr2 (s≤s prrn) {pirn} =
  ≤-abs (≤-remove-+ {r1} {suc (suc r2)} {zero} prrn)
canonize-p> (suc (suc zero)) (suc r1) (suc (suc r2)) {i} pr1 pr2 (s≤s prrn) {pirn} =
  let t = ≤-down2 (≤-remove-+ {r1} {suc (suc r2)} {1} prrn)
  in  ≤-abs t
canonize-p> (suc (suc (suc n))) (suc r1) (suc (suc r2)) {i} pr1 pr2 (s≤s prrn) {pirn} =
  let x = canonize-p> (3 + n) (1 + r1) (1 + r2) {i} pr1 (s≤s z≤n) (s≤s {!!}) {pirn}
      r2<i : r2 ≤ i
      r2<i = {!!}
  in  {!!}

reduction-lemma : {n ∈ l} -> ∃ (λ l' -> ∃ (λ r -> (n ∉ l) × (l ≃ (l' ++ (n ↓ r)))))
reduction-lemma = {!   !}
