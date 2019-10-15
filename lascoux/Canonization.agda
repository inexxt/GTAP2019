module Canonization where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; Σ; _×_; _,_; _,′_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)
open import Function

open import General
open import Relation.Nullary
open import Data.Empty
open Relation.Binary.PropositionalEquality.≡-Reasoning

open ≤-Reasoning renaming (_∎ to _≤∎; begin_ to begin-≤_) hiding (_≡⟨_⟩_)
open import Arithmetic hiding (n)
open import Coxeter hiding (n; l)

open ≃-Reasoning

variable
    n : ℕ
    l : List ℕ

_↓_ : (n : ℕ) -> (r : ℕ) -> List ℕ
zero ↓ r = []
suc n ↓ zero = []
suc n ↓ suc r = n ∷ n ↓ r

↓-rec : {n k : ℕ} -> (k < n) -> (n ↓ suc k) ≡ (n ↓ k) ++ [ n ∸ (k + 1) ]
↓-rec {suc zero} {zero} (s≤s z≤n) = refl
↓-rec {suc (suc n)} {zero} (s≤s z≤n) = refl
↓-rec {suc (suc n)} {suc k} (s≤s p) = cong (λ l -> suc n ∷ l) (↓-rec p)

open Σ

nnl=l : {l : List ℕ} -> {n : ℕ} -> (n ∷ n ∷ l) ≃ l
nnl=l {l} = ++-respects-l cancel
l++nn=l : {l : List ℕ} -> {n : ℕ} -> (l ++ (n ∷ n ∷ [])) ≃ l
l++nn=l = trans (++-respects-r cancel) (refl≡ ++-unit)

canonize-swap : (n r i : ℕ)
                -> (r ≤ n)
                -> (n < i)
                -> ((n ↓ r) ++ [ i ]) ≃ (i ∷ (n ↓ r))
canonize-swap zero zero i prn pni = refl
canonize-swap (suc n) zero i prn pni = refl
canonize-swap (suc n) (suc r) i prn pni =
  let rec = canonize-swap n r i (≤-down2 prn) (≤-down pni)
  in  ≃begin
         n ∷ (n ↓ r) ++ i ∷ []
       ≃⟨ ++-respects-r {l = [ n ]} rec ⟩
         n ∷ i ∷ (n ↓ r)
       ≃⟨ ++-respects-l (comm (swap pni))  ⟩
         i ∷ n ∷ (n ↓ r)
       ≃∎

-- REMEMBER - i is (suc i)
canonize-p>' : (n r1 r2 : ℕ)
              -> {i : ℕ}
              -> ((suc zero) ≤ r2)
              -> (r1 + r2 < n)
              -> {i ≡ n ∸ (2 + r1)}
              -> (((n ↓ r1) ++ [ 1 + i ] ++ (1 + i) ↓ r2) ++ [ 1 + i ]) ≃ (i ∷ (n ↓ (1 + r1 + r2)))
-- again, weeding out small, impossible case
canonize-p>' (suc zero) r1 (suc r2) {i} pr2 prn = ≤-abs (≤-remove-+ {r1} (≤-down2 prn))
-- now, induction
-- base case on r1 and r2
canonize-p>' (suc (suc n)) zero (suc r2) {i} pr2 prn {pinr} rewrite pinr = -- induction on r2
  let rec = canonize-swap n r2 (1 + n) (≤-down2 (≤-down2 prn)) (s≤s (≤-reflexive refl))
  in  ≃begin
         (1 + n) ∷ n ∷ (n ↓ r2) ++ (1 + n) ∷ []
       ≃⟨ ++-respects-r {l = (1 + n) ∷ [ n ]} rec ⟩
         (1 + n) ∷ n ∷ (1 + n) ∷ (n ↓ r2)
       ≃⟨ ++-respects-l (comm braid)  ⟩
         n ∷ suc n ∷ n ∷ (n ↓ r2)
       ≃∎
canonize-p>' (suc (suc n)) (suc r1) (suc r2) {i} pr2 prn {pinr} = -- induction on r1
  let rec = canonize-p>' (suc n) r1 (suc r2) {i} pr2 (≤-down2 prn) {pinr}
      1+r1≤n : suc r1 ≤ n
      1+r1≤n = ≤-down2 (≤-down2 (
        begin-≤
          suc (suc (suc r1))
        ≤⟨ s≤s (s≤s (≤-reflexive (+-comm 1 r1))) ⟩
          suc (suc (r1 + 1))
        ≤⟨ s≤s (s≤s (≤-up2-+ {1} {suc r2} {r1} (s≤s z≤n))) ⟩
          suc (suc (r1 + (1 + r2)))
        ≤⟨ prn ⟩
          suc (suc n)
        ≤∎))

      lemma =
        begin
          (1 + i) + r1
        ≡⟨ +-three-assoc {1} {i} {r1} ⟩
          (i + 1) + r1
        ≡⟨ +-assoc i 1 r1 ⟩
          i + (1 + r1)
        ≡⟨ eliminate-∸ 1+r1≤n pinr ⟩
          n
        ∎
  in ≃begin
         (1 + n) ∷ (((1 + n) ↓ r1) ++ (1 + i) ∷ i ∷ (i ↓ r2)) ++ (1 + i) ∷ []
       ≃⟨ ++-respects-r {l = [ 1 + n ]} rec ⟩
         (1 + n) ∷ i ∷ n ∷ ( n ↓ (r1 + (1 + r2)))
       ≃⟨ ++-respects-l (swap (s≤s (introduce-≤-from-+ lemma)))  ⟩
         i ∷ (1 + n) ∷ n ∷ (n ↓ (r1 + (1 + r2)))
       ≃∎

canonize-p≡ : (n r i : ℕ)
              -> (r < n)
              -> (i ≡ n ∸ (1 + r))
              -> ((n ↓ r) ++ [ i ]) ≡ (n ↓ (1 + r))
canonize-p≡ (suc n) r i prn pirn =
  let tt = ≡-sym (↓-rec {suc n} {r} prn)
      i=n-r-1 : (suc n) ∸ (r + 1) ≡ i
      i=n-r-1 = begin
                    suc n ∸ (r + 1)
                  ≡⟨ cong (λ x -> (suc n) ∸ x) (+-comm r 1) ⟩
                    suc n ∸ (1 + r)
                  ≡⟨ refl ⟩
                    n ∸ r
                  ≡⟨ ≡-sym pirn ⟩
                    i
                  ∎
  in subst (λ k -> ((suc n) ↓ r) ++ [ k ] ≡ ((suc n) ↓ suc r)) i=n-r-1 tt


canonize-p>-lemma : (n r1 r2 : ℕ)
                    -> {i : ℕ}
                    -> ((suc zero) ≤ r2)
                    -> (r1 + r2 < n)
                    -> {i ≡ n ∸ (2 + r1)}
                    -> (n ↓ suc (r1 + r2)) ≡ (((n ↓ r1) ++ (suc (suc i)) ↓ (suc r2)))
-- impossible, small cases
canonize-p>-lemma (suc zero) zero (suc r2) {zero} pr2 (s≤s ()) {pirn}
canonize-p>-lemma (suc zero) (suc r1) r2 {zero} pr2 (s≤s ()) {pirn}
-- induction by n and r1
canonize-p>-lemma (suc (suc n)) zero r2 {i} pr2 prn {pirn} rewrite pirn = refl
-- induction step
canonize-p>-lemma (suc (suc n)) (suc r1) r2 {i} pr2 (s≤s prn) {pirn} =
  let rec =  canonize-p>-lemma (suc n) r1 r2 {i} pr2 prn {pirn}
  in  cong (λ l -> suc n ∷ l) rec


canonize-p> : (n r1 r2 : ℕ)
              -> {i : ℕ}
              -> ((suc zero) ≤ r2)
              -> (r1 + r2 < n)
              -> {i ≡ n ∸ (2 + r1)}
              -> ((n ↓ suc (r1 + r2)) ++ [ suc i ]) ≃ (i ∷ (n ↓ (1 + r1 + r2)))
canonize-p> n r1 r2 {i} pr2 prn {pirn} =
  ≃begin
    (n ↓ suc (r1 + r2)) ++ suc i ∷ []
  ≃⟨ refl≡ (cong (λ l -> l ++ [ suc i ]) (canonize-p>-lemma n r1 r2 {i} pr2 prn {pirn})) ⟩
    ((n ↓ r1) ++ suc i ∷ (suc i ↓ r2)) ++ suc i ∷ []
  ≃⟨ canonize-p>' n r1 r2 {i} pr2 prn {pirn} ⟩
    i ∷ (n ↓ suc (r1 + r2))
  ≃∎
