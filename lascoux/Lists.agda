{-# OPTIONS --allow-unsolved-metas --without-K #-}
module Lists where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)

open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_; ≤-trans)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans)
open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)


data nonempty : List ℕ -> Set where
  nonempty-l : (x : ℕ) -> (l : List ℕ) -> nonempty (x ∷ l)

_↓_ : (n : ℕ) -> (k : ℕ) -> List ℕ
n ↓ 0 = []
n ↓ (suc k) = (k + n) ∷ (n ↓ k)


++-unit : {l : List ℕ} -> l ++ [] ≡ l
++-unit = {!   !}

cut-head : {a1 a2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ l1 ≡ a2 ∷ l2) -> (l1 ≡ l2)
cut-head {a1} {.a1} {l1} {.l1} refl = refl

cut-tail : {a1 a2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ l1 ≡ a2 ∷ l2) -> (a1 ≡ a2)
cut-tail {a1} {.a1} {l1} {.l1} refl = refl

cut-t1 : {a1 a2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ l1 ≡ a2 ∷ l2) -> (a1 ≡ a2)
cut-t1 {a1} {.a1} {l1} {.l1} refl = refl

cut-t2 : {a1 a2 b1 b2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ b1 ∷ l1 ≡ a2 ∷ b2 ∷ l2) -> (b1 ≡ b2)
cut-t2 {l1 = l1} {l2 = .l1} refl = refl

cut-t3 : {a1 a2 b1 b2 c1 c2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ b1 ∷ c1 ∷ l1 ≡ a2 ∷ b2 ∷ c2 ∷ l2) -> (c1 ≡ c2)
cut-t3 {l1 = l1} {l2 = .l1} refl = refl

cut-t4 : {a1 a2 b1 b2 c1 c2 d1 d2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ b1 ∷ c1 ∷ d1 ∷ l1 ≡ a2 ∷ b2 ∷ c2 ∷ d2 ∷ l2) -> (d1 ≡ d2)
cut-t4 {l1 = l1} {l2 = .l1} refl = refl

cut-h2 : {a1 a2 b1 b2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ b1 ∷ l1 ≡ a2 ∷ b2 ∷ l2) -> (l1 ≡ l2)
cut-h2 {l1 = l1} {l2 = .l1} refl = refl

cut-h3 : {a1 a2 b1 b2 c1 c2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ b1 ∷ c1 ∷ l1 ≡ a2 ∷ b2 ∷ c2 ∷ l2) -> (l1 ≡ l2)
cut-h3 {l1 = l1} {l2 = .l1} refl = refl

cut-h4 : {a1 a2 b1 b2 c1 c2 d1 d2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ b1 ∷ c1 ∷ d1 ∷ l1 ≡ a2 ∷ b2 ∷ c2 ∷ d2 ∷ l2) -> (l1 ≡ l2)
cut-h4 {l1 = l1} {l2 = .l1} refl = refl

head+tail : {h1 h2 : ℕ} -> {t1 t2 : List ℕ} -> (h1 ≡ h2) -> (t1 ≡ t2) -> (h1 ∷ t1) ≡ (h2 ∷ t2)
head+tail p1 p2 = {!!}

start+end : {h1 h2 : List ℕ} -> {t1 t2 : List ℕ} -> (h1 ≡ h2) -> (t1 ≡ t2) -> (h1 ++ t1) ≡ (h2 ++ t2)
start+end p1 p2 = {!!}


↓-+ : (n k1 k2 : ℕ) -> n ↓ (k1 + k2) ≡ ((n + k2) ↓ k1) ++ (n ↓ k2)
↓-+ n zero k2 = refl
↓-+ n (suc k1) k2 rewrite (↓-+ n k1 k2) rewrite (+-comm n k2) = head+tail (+-assoc k1 k2 n) refl
