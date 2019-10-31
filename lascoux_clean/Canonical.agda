{-# OPTIONS --without-K #-}
module _ where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)

open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_; _≟_; _<?_)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans; _≟_; _<?_)
open import Function

open import Arithmetic hiding (n)
open import Lists
open import Compact hiding (n; l)
open import LongLemmas hiding (n; l)
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)


open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

open ≅*-Reasoning
open Relation.Binary.PropositionalEquality.≡-Reasoning

variable
  n : ℕ
  l : List ℕ

data Canonical : (n : ℕ) -> Set where
  CanZ : Canonical 0
  CanS : {n : ℕ} -> (l : Canonical n) -> {r : ℕ} -> (r ≤ suc n) -> Canonical (suc n)

immersion : {n : ℕ} -> Canonical n -> List ℕ
immersion {zero} CanZ = []
immersion {suc n} (CanS l {r} r≤1+n) = (immersion l) ++ ((suc n) ↓↓ r , r≤1+n)

postulate
  canonical-eta : {n : ℕ} -> {cl1 cl2 : Canonical n} -> {r1 r2 : ℕ} -> (rn1 : r1 ≤ (suc n)) -> (rn2 : r2 ≤ (suc n)) -> (cl1 ≡ cl2) -> (r1 ≡ r2) -> (CanS cl1 rn1) ≡ (CanS cl2 rn2)

data _>>_ : ℕ -> List ℕ -> Set where
  [] : {n : ℕ} -> n >> []
  _:⟨_⟩:_ : {n : ℕ} -> {l : List ℕ} -> (k : ℕ) -> (k < n) -> n >> l -> n >> (k ∷ l)

extract-proof : {a : ℕ} -> (n >> (a ∷ l)) -> (a < n)
extract-proof (_ :⟨ p ⟩: _) = p

>>-++ : {l1 l2 : List ℕ} -> n >> l1 -> n >> l2 -> n >> (l1 ++ l2)
>>-++ {n} {[]} {l2} ll1 ll2 = ll2
>>-++ {n} {x ∷ l1} {l2} (.x :⟨ p ⟩: ll1) ll2 = x :⟨ p ⟩: (>>-++ ll1 ll2)

>>-↓↓ : (n k r : ℕ) -> (p : r ≤ k) -> (q : k ≤ n) -> (n >> (k ↓↓ r , p))
>>-↓↓ n k zero z≤n p = []
>>-↓↓ (suc n) (suc k) (suc r) (s≤s q) (s≤s p) = k :⟨ s≤s p ⟩: (>>-↓↓ (suc n) k r q (≤-up p))

>>-suc : (n >> l) -> ((suc n) >> l)
>>-suc  [] = []
>>-suc  (k :⟨ p ⟩: l') = k :⟨ ≤-up p ⟩: >>-suc l'

immersion->> : (cl : Canonical n) -> n >> immersion cl
immersion->> {.0} CanZ = []
immersion->> {suc n} (CanS {n} cl {r} rn) =
  let p = immersion->> {n} cl
  in  >>-++ (>>-suc p) (>>-↓↓ _ _ _ rn rrr)

reverse->> : n >> l -> n >> reverse l
reverse->> {n} {[]} ll = ll
reverse->> {n} {x ∷ l} (.x :⟨ x₁ ⟩: ll) rewrite (reverse-++-commute [ x ] l) =
  let rec = reverse->> {n} {l} ll
  in  >>-++ {l1 = reverse l} {l2 = [ x ]} rec (x :⟨ x₁ ⟩: [])

abs-const-↓↓ : (n k a : ℕ) -> (p : k ≤ n) -> (l r : List ℕ) -> (n ↓↓ k , p) ≡ (l ++ a ∷ a ∷ r) -> ⊥
abs-const-↓↓ n k a p l r q = {!   !}

abs-inc-↓↓ : (n k a : ℕ) -> (p : k ≤ n) -> (l r : List ℕ) -> (n ↓↓ k , p) ≡ (l ++ a ∷ suc a ∷ r) -> ⊥
abs-inc-↓↓ n k a p l r q = {!!}

abs-jump-↓↓ : (n k a b : ℕ) -> (p : k ≤ n) -> (suc a < b) -> (l r : List ℕ) -> (n ↓↓ k , p) ≡ (l ++ b ∷ a ∷ r) -> ⊥
abs-jump-↓↓ n k a p l r q = {!!}

--- And versions for 2-⇣

abs-const2-↓ : (n1 k1 n2 k2 a : ℕ) -> (n1 < n2) -> (l r : List ℕ) -> (n1 ↓ k1) ++ (n2 ↓ k2) ≡ (l ++ a ∷ a ∷ r) -> ⊥
abs-const2-↓ n1 k1 n2 k2 a pnn l r p = {!   !}

abs-braid2-↓ : (n1 k1 n2 k2 a : ℕ) -> (n1 < n2) -> (l r : List ℕ) -> (n1 ↓ k1) ++ (n2 ↓ k2) ≡ (l ++ suc a ∷ a ∷ suc a ∷ r) -> ⊥
abs-braid2-↓ n1 k1 n2 k2 a pnn l r p = {!!}

abs-jump2-↓ : (n1 k1 n2 k2 a b : ℕ) -> (n1 < n2) -> (suc a < b) -> (l r : List ℕ) -> (n1 ↓ k1) ++ (n2 ↓ k2) ≡ (l ++ b ∷ a ∷ r) -> ⊥
abs-jump2-↓ n1 k1 n2 k2 a b pnn pab l r p = {!!}
