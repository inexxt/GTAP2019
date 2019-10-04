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
    swap : {k : ℕ} -> {suc k < n} -> (n ∷ k ∷ []) ≃ (k ∷ n ∷ [])
    braid : (n ∷ (suc n) ∷ n ∷ []) ≃ ((suc n) ∷ n ∷ (suc n) ∷ [])
    prepend : (k : ℕ) -> {l l' : List ℕ} -> (l ≃ l') -> (k ∷ l) ≃ (k ∷ l')
--    ++-respects : {l l' m m' : List ℕ} -> {l ≃ l'} -> {m ≃ m'} -> (l ++ m) ≃ (l' ++ m')
    refl : {l : List ℕ} -> l ≃ l
    comm : {l l' : List ℕ} -> (l ≃ l') -> l' ≃ l
    trans : {l l' l'' : List ℕ} -> {l ≃ l'} -> {l' ≃ l''} -> l ≃ l''

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
    <-holes : {i n : ℕ} -> (1 + i + zero > n) -> (i < n) -> ⊥
    ∸-exact : {p q : ℕ} -> (q > p) -> (t : Σ ℕ (λ k -> k ≡ q ∸ p)) -> (proj₁ t + p ≡ q)
    +-cancel : {p q r : ℕ} -> (r + q ≡ r + p) -> (q ≡ p)

-- REMEMBER - i is (suc i)
canonize-p> : (n r i : ℕ) -> (i < n) -> (r < n) -> ((suc i) + r > n) -> (∃ (λ k -> k ≡ ((suc i) + r) ∸ n)) -> ((n ↓ r) ++ ((suc i) ∷ [])) ≃ (i ∷ (n ↓ r))
canonize-p> n r i pin prn pirn (zero , snd) = ⊥-elim ((∸-not-< pirn) snd)
canonize-p> n zero i pin prn pirn (suc zero , snd) = ⊥-elim (<-holes pirn pin)
canonize-p> n (suc zero) i pin prn pirn (suc zero , snd) = {!!}
canonize-p> (suc zero) (suc (suc zero)) i pin (s≤s ()) pirn (suc zero , snd)
canonize-p> (suc (suc n)) (suc (suc zero)) i pin prn pirn (suc zero , snd) =
  let 2+n=i+2 : suc (suc n) ≡ i + 2
      2+n=i+2 = ∸-exact (<-down pirn) (1 , snd)
      2+n=2+i = begin
          2 + n
        ≡⟨ 2+n=i+2 ⟩
          i + 2
        ≡⟨ +-comm i 2 ⟩
          2 + i
        ∎
      n=i : n ≡ i
      n=i = +-cancel 2+n=2+i
  in subst _ n=i (comm (braid {n})) -- true base case
canonize-p> (suc zero) (suc (suc (suc r))) i pin (s≤s ()) pirn (suc zero , snd)
canonize-p> (suc (suc n)) (suc (suc (suc r))) i pin prn pirn (suc zero , snd) = {!!}
canonize-p> n r i pin prn pirn (suc (suc fst) , snd) = {!!}

reduction-lemma : {n ∈ l} -> ∃ (λ l' -> ∃ (λ r -> (n ∉ l) × (l ≃ (l' ++ (n ↓ r)))))
reduction-lemma = {!   !}
