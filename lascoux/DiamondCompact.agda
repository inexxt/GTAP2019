{-# OPTIONS --allow-unsolved-metas #-}
module DiamondCompact where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)

open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_)
open import Data.Bool.Properties hiding (≤-reflexive)
open import Function

open import Arithmetic hiding (n)
open import Compact hiding (n; l)
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)


open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)


variable
    n : ℕ
    l : List ℕ

-- this should encode something like "m up to (irl m mf _) is unchanged"
irl : {m mf : List ℕ} -> (p : m ≅ mf) -> ℕ
irl (cancel≅ l r m mf defm defmf) = length l
irl (swap≅ x l r m mf defm defmf) = length l
irl (braid≅ l r m mf defm defmf) = length l

-- this should encode something like "m after (irr m mf _) is unchanged"
irr : {m mf : List ℕ} -> (p : m ≅ mf) -> ℕ
irr (cancel≅ l r m mf defm defmf) = 3 + length l
irr (swap≅ x l r m mf defm defmf) = 3 + length l
irr (braid≅ l r m mf defm defmf) = 4 + length l

-- these will be the two main technical lemmas
force-crit-pair : (m1 m2 m3 : List ℕ) -> (length m1 ≤ 5) -> (p1 : m1 ≅ m2) -> (p2 : m1 ≅ m3) -> ∃ (λ m -> (m2 ≅* m) × (m3 ≅* m))
force-crit-pair m1 m2 m3 lm p1 p2 = {!!}

force-not-crit-pair : (m1 m2 m3 : List ℕ) -> (p1 : m1 ≅ m2) -> (p2 : m1 ≅ m3) -> (irr p1 < irl p2) -> ∃ (λ m -> (m2 ≅* m) × (m3 ≅* m))
force-not-crit-pair m1 m2 m3 lm = {!!}


-- and this should do something like: if ir1 = (ir p1) and ir2 = (ir p2) are non-overlapping, use force-non-crit-pair
-- otherwise, take the ir1 ∪ ir2 , force it into one of the critical pairs and then reduce critical pair
diamond : (m1 m2 m3 : List ℕ) -> (m1 ≅ m2) -> (m1 ≅ m3) -> ∃ (λ m -> (m2 ≅* m) × (m3 ≅* m))
diamond m1 m2 m3 (cancel≅ l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
diamond m1 m2 m3 (cancel≅ l r .m1 .m2 defm defmf) (swap≅ x l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
diamond m1 m2 m3 (cancel≅ l r .m1 .m2 defm defmf) (braid≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
diamond m1 m2 m3 (swap≅ x l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
diamond m1 m2 m3 (swap≅ x l r .m1 .m2 defm defmf) (swap≅ x₁ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
diamond m1 m2 m3 (swap≅ x l r .m1 .m2 defm defmf) (braid≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
diamond m1 m2 m3 (braid≅ l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = ?
diamond m1 m2 m3 (braid≅ l r .m1 .m2 defm defmf) (swap≅ x l₁ r₁ .m1 .m3 defm₁ defmf₁) = ?
diamond m1 m2 m3 (braid≅ l r .m1 .m2 defm defmf) (braid≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = ?

diamond-full : {m1 m2 m3 : List ℕ} -> (m1 ≅* m2) -> (m1 ≅* m3) -> ∃ (λ m -> (m2 ≅* m) × (m3 ≅* m))
diamond-full p q = {!!}


data _≃_ : List ℕ -> List ℕ -> Set where
  R : {m1 m2 mf : List ℕ} -> (p1 : m1 ≅* mf) -> (p2 : m2 ≅* mf) -> m1 ≃ m2

refl≃ : (m : List ℕ) -> (m ≃ m)
refl≃ m = R refl refl

comm≃ : (m1 m2 : List ℕ) -> (m1 ≃ m2) -> (m2 ≃ m1)
comm≃ m1 m2 (R p1 p2) = R p2 p1

trans≃ : (m1 m2 m3 : List ℕ) -> (r1 : m1 ≃ m2) -> (r2 : m2 ≃ m3) -> (m1 ≃ m3)
trans≃ m1 m2 m3 (R p1 p2) (R p3 p4) =
  let lemma-m , lemma1 , lemma2 = diamond-full p2 p3
  in  R (trans p1 lemma1) (trans p4 lemma2)
