{-# OPTIONS --allow-unsolved-metas #-}

module ReductionStep where

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
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Canonization using (F-canonize-p>; F-canonize-p≡; F-canonize-p<; _≃_; _↓_ ; refl≡)

open _≃_

variable
  n : ℕ
  l : List ℕ

-- data _∈_ : ℕ -> List ℕ -> Set where
--     here : (n : ℕ) -> (l : List ℕ) -> n ∈ (n ∷ l)
--     there : (k : ℕ) -> {n : ℕ} -> {l : List ℕ} -> (n ∈ l) -> n ∈ (k ∷ l)

-- data _∉_ : ℕ -> List ℕ -> Set where
--     not-here : (n : ℕ) -> n ∉ []
--     not-there : {k : ℕ} -> {n : ℕ} -> {¬ (k == n)} -> {l : List ℕ} -> (n ∉ l) -> n ∉ (k ∷ l)

data _>=_ : ℕ -> List ℕ -> Set where
  [] : {n : ℕ} -> n >= []
  _:⟨_⟩:_ : {n : ℕ} -> {l : List ℕ} -> (k : ℕ) -> (k ≤ n) -> n >= l -> n >= (k ∷ l)

≤-≠-≤ : {n m : ℕ} -> (n ≤ suc m) -> ¬ (n ≡ suc m) -> (n ≤ m)
≤-≠-≤ z≤n q = z≤n
≤-≠-≤ (s≤s p) q = {!!}

n<i+r : (n : ℕ) -> (r : ℕ) -> (i : ℕ) -> (n < i + r) -> {!!}
n<i+r = {!!}

n=i+r : (n : ℕ) -> (r : ℕ) -> (i : ℕ) -> (n ≡ i + r) -> {!!}
n=i+r = {!!}

n=i+1+r : (n : ℕ) -> (r : ℕ) -> (i : ℕ) -> (n ≡ i + (1 + r)) -> {!!}
n=i+1+r = {!!}

n>i+1+r : (n : ℕ) -> (r : ℕ) -> (i : ℕ) -> (n > i + (1 + r)) -> {!!}
n>i+1+r = {!!}


++-unit : (l : List ℕ) -> (l ++ []) ≡ l
++-unit [] = refl
++-unit (x ∷ l) = cong (λ l -> x ∷ l) (++-unit l)

++-unit2 : (l1 l2 : List ℕ) -> (l1 ++ (l2 ++ [])) ≡ (l1 ++ l2)
++-unit2 l1 l2 = let xx = ++-assoc l1 l2 []
                     yy = ++-unit (l1 ++ l2)
                     in ≡-trans (≡-sym xx) yy

>=-++ : {l1 l2 : List ℕ} -> n >= l1 -> n >= l2 -> n >= (l1 ++ l2)
>=-++ {n} {[]} {l2} ll1 ll2 = ll2
>=-++ {n} {x ∷ l1} {l2} (.x :⟨ p ⟩: ll1) ll2 = x :⟨ p ⟩: (>=-++ ll1 ll2)

all-reduce : (w : List ℕ)
             -> (w' : List ℕ)
             -> (n : ℕ)
             -> (r : ℕ)
             -> (ww : n >= w)
             -> (ww' : (suc n) >= w')
             -> Σ (List ℕ × ℕ) (λ (w'' , r') -> (n >= w'') × (w'' ++ (n ↓ r')) ≃ (w ++ (n ↓ r) ++ w'))
all-reduce w [] n r ww [] = let tt = ++-assoc  in  (w , r) , (ww , refl≡ (≡-sym (++-unit2 w (n ↓ r))) )
all-reduce w (0 ∷ w') n r ww (.0 :⟨ p ⟩: ww') = {!!} , {!!}
all-reduce w ((suc i) ∷ w') n r ww (.(suc i) :⟨ (s≤s p) ⟩: ww') with (n <? i + r) with (n ≟ i + r) with (n ≟ i + (1 + r)) with (i + (1 + r) <? n)
... | yes q | _ | _ | _ = (w ++ [ i  ] , r) , (>=-++ ww (i :⟨ p ⟩: []) , {!!}) -- p>
... | _ | yes q | _ | _ = {!!} -- reduction
... | _ | _ | yes q | _ = {!!} -- p1
... | _ | _ | _ | yes q = {!!} -- p<
... | no p1 | no p2 | no p3 | no p4  = {!!}

step : (ll : (suc n) >= l) -> Σ (List ℕ × ℕ) (λ (l' , r) -> (n >= l') × (l' ++ ((suc (suc n)) ↓ r)) ≃ l)
step {n} {.[]} [] = ([] , 0) , ([] , refl)
step {n} {k ∷ l} (_ :⟨ x ⟩: ll) with k ≟ (suc n)
step {n} {k ∷ l} (.k :⟨ x ⟩: ll) | yes p =
  let xx = all-reduce {!!} {!!} {!!} {!!}
  in  {!!}
step {n} {k ∷ l} (.k :⟨ x ⟩: ll) | no ¬p =
  let k≤n : k ≤ n
      k≤n = ≤-≠-≤ x ¬p
      (l' , r) , (ll' , pp) = step ll
  in ((k ∷ l') , r) , ((k :⟨ k≤n ⟩: ll') , (prepend k pp))

data Canonical : (n : ℕ) -> Set where
  CanZ : Canonical 0
  CanS : {n : ℕ} -> (k r : ℕ) -> (n < k) -> (r ≤ k) -> (l : Canonical n) -> Canonical k

immersion : {n : ℕ} -> Canonical n -> List ℕ
immersion {zero} CanZ = []
immersion {suc n} (CanS k r n<k r≤k l) = (k ↓ r) ++ immersion l

open import Data.Fin

canonical-form-lemma : {n : ℕ} -> (l : List (Fin n)) -> ∃ (λ cl -> (map (λ x -> toℕ x) l) ≃ (immersion {n} cl))

canonical-form-lemma-Free : (l : List ℕ) -> ∃ (λ n -> ∃ (λ cl -> l ≃ (immersion {n} cl)))
