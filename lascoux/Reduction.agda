module Reduction where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_; _,′_)
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

postulate
    ≤-+-respects : {m n r p : ℕ} -> m ≤ n -> r ≤ p -> r + m ≤ p + n

lemma : {n i r : ℕ} -> suc (i + suc r) ≡ n -> suc i < n
lemma {.(suc (i + 1))} {i} {zero} refl = s≤s (≤-reflexive (+-comm 1 i))
lemma {.(suc (i + suc (suc r)))} {i} {suc r} refl =  s≤s (≤-trans {suc i} {suc (suc i)} (s≤s (<⇒≤ n<1+n)) (≤-trans {_} {i + suc (suc zero)} (≤-reflexive (+-comm 2 i)) (≤-+-respects (s≤s (s≤s z≤n)) (≤-refl {i}) )))


p1 : (n r i : ℕ) -> {i < n} -> {1 + i + r ≡ n} -> ((n ↓ r) ++ i ∷ []) ≃ ((i ↓ 0) ++ (n ↓ (suc r)))
p1 (suc n) zero i {pin} {pirn} =
    let pp : i ≡ n
        pp = ext ( ≡-trans (cong suc ( ≡-sym (+-zero {i}))) pirn)
        rl : (i ∷ []) ≃ (i ∷ [])
        rl = refl
    in subst _ pp rl
p1 (suc n) (suc r) zero {pin} {pirn} =
    let pp = ext pirn
        ll = p1 n r zero {<-zero pp} {pp}
    in prepend n ll
--- idea here : induction on n and r at the same time
p1 (suc n) (suc r) (suc i) {pin} {pirn} =
    let pp = ext pirn
        ll = p1 n r (suc i) {lemma pp} {_} -- skipped lemma is trivial too, as the previous one, but there has to be another way ...
    in prepend n ll

l++[] : {l : List ℕ} -> l ++ [] ≡ l
l++[] {l} = ++-identityʳ l

open ≤-Reasoning renaming (_∎ to _<∎)

<-tight : {m n : ℕ} -> m < n -> n < m + 2 -> n ≡ 1 + m
<-tight {m} {n} p q = {!   !}

braid-base-case : (k : ℕ) -> (((1 + k) ↓ 2) ++ k ∷ []) ≃ ((k ↓ 1) ++ ((1 + k) ↓ 2))
braid-base-case zero = refl
braid-base-case (suc k) = comm braid

p> : (n i r : ℕ) -> i < n -> n < i + r -> ((n ↓ r) ++ i ∷ []) ≃ ((i ↓ 1) ++ (n ↓ r))
-- Two ugly impossible cases
p> n i zero i<n n<i+r =
    let n<i : n < i
        n<i =
            begin-strict
                n
            <⟨ n<i+r ⟩
                i + zero
            ≤⟨ ≤-reflexive (+-comm i zero) ⟩
                i
            <∎
        n<n : (suc n) < suc n
        n<n = ≤-trans ( s≤s (s≤s (<⇒≤ n<i))) (s≤s i<n)
    in ⊥-elim (1+n≰n n<n)
-- Another one...
p> n i (suc zero) i<n n<i+r =
    let i<i : suc i < suc i
        i<i =
            begin-strict
                suc i
            ≤⟨ i<n ⟩
                n
            <⟨ n<i+r ⟩
                i + 1
            ≤⟨ ≤-reflexive (+-comm i 1) ⟩
                1 + i
            <∎
    in ⊥-elim (1+n≰n i<i)

-- The true base case : n ≡ i + 1
-- we use braid here
p> n i (suc (suc zero)) i<n n<i+r =
     let 1+i≡n : n ≡ 1 + i
         1+i≡n = <-tight i<n n<i+r

         pp = braid-base-case i
     in subst (λ k -> ((k ↓ 2) ++ i ∷ []) ≃ ((i ↓ 1) ++ (k ↓ 2)) ) (≡-sym 1+i≡n) pp -- this is stupid, subst should be able to guess the function
-- Inductive case is quite difficult
-- we have to swap until 1+i≡n
-- then do braid
-- and then once again exchange
p> n i (suc (suc (suc r))) i<n n<i+r = {!!}

p2 : (n i r : ℕ) -> i < n -> ¬ (1 + i + r) ≡ n -> ¬ (i + r) ≡ n -> ((n ↓ r) ++ i ∷ []) ≃ ((i ↓ 1) ++ (n ↓ r))
p2 n i r i<n 1+i+r≠n i+r≠n with (i + r) <? n
... | no 1+i+r≰n =
    let n<i+r : n < i + r
        n<i+r = {!   !}
    in p> _ _ _ i<n n<i+r
... | yes 1+i+r≤n = {!   !}


canonize : (n r i : ℕ) -> {i < n} -> ∃ (λ t -> ∃ (λ p -> ((n ↓ r) ++ (i ∷ [])) ≃ ((i ↓ t) ++ (n ↓ ((inv t {p}) + r)))))
canonize n r i with (1 + i + r ≟ n) ,′ (i + r ≟ n)
canonize n r i {pin} | yes p , yes q = absurd (≡-trans p (≡-sym q))
    where
        absurd : {A : Set} -> {n : ℕ} -> 1 + n ≡ n -> A
        absurd ()

canonize n r i {pin} | yes p , no ¬p = 0 , z≤n , p1 n r i {pin} {p} -- p1 from the paper
canonize n r i {pin} | no ¬p , yes p = {!!} -- here we will have to cancel, but might be hard, as the original paper doesnt take that into account...
canonize n r i {pin} | no ¬p , no ¬q = 1 , (s≤s z≤n) , p2 n i r pin ¬p ¬q


reduction-lemma : {n ∈ l} -> ∃ (λ l' -> ∃ (λ r -> (n ∉ l) × (l ≃ (l' ++ (n ↓ r)))))
reduction-lemma = {!   !}
