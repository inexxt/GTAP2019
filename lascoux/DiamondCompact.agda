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
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans)
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
--- crit-pair
diamond (x₁ ∷ .x₁ ∷ .x₁ ∷ m1) m2 m3 (cancel≅ [] .(x₁ ∷ m1) .(x₁ ∷ x₁ ∷ x₁ ∷ m1) .m2 refl defmf) (cancel≅ (.x₁ ∷ []) .m1 .(x₁ ∷ x₁ ∷ x₁ ∷ m1) .m3 refl defmf₁)
  rewrite defmf rewrite defmf₁ = (x₁ ∷ m1) , (refl , refl) -- cc
diamond (x₂ ∷ .x₂ ∷ x₄ ∷ m1) m2 m3 (cancel≅ [] .(x₄ ∷ m1) .(x₂ ∷ x₂ ∷ x₄ ∷ m1) .m2 refl defmf) (swap≅ x (.x₂ ∷ []) .m1 .(x₂ ∷ x₂ ∷ x₄ ∷ m1) .m3 refl defmf₁)
  rewrite defmf rewrite defmf₁ = (x₄ ∷ m1) , (refl , trans (swap x [] _) (cancel [ x₄ ] m1)) -- cs
diamond (.(suc x₃) ∷ .(suc x₃) ∷ x₃ ∷ .(suc x₃) ∷ m1) m2 m3 (cancel≅ [] .(x₃ ∷ suc x₃ ∷ m1) .(suc x₃ ∷ suc x₃ ∷ x₃ ∷ suc x₃ ∷ m1) .m2 refl defmf) (braid≅ (.(suc x₃) ∷ []) .m1 .(suc x₃ ∷ suc x₃ ∷ x₃ ∷ suc x₃ ∷ m1) .m3 refl defmf₁)
  rewrite defmf rewrite defmf₁ = (x₃ ∷ suc x₃ ∷ m1) , (refl , trans (braid [] ( x₃ ∷ m1 ) _ _ ) (cancel (x₃ ∷ suc x₃ ∷ []) m1)) -- cb
diamond (c ∷ b ∷ a ∷ m1) m2 m3 (swap≅ b<c [] .(a ∷ m1) .(c ∷ b ∷ a ∷ m1) .m2 refl defmf) (swap≅ a<b (.c ∷ []) .m1 .(c ∷ b ∷ a ∷ m1) .m3 refl defmf₁)
  rewrite defmf rewrite defmf₁ =
  let a<c : suc a < c
      a<c = ≤-down (≤-trans (s≤s a<b) (≤-down b<c))
      left = trans (swap a<c [ b ] m1) (swap a<b [] _)
      right = trans (swap a<c [] _) (swap b<c [ a ] _)
   in a ∷ b ∷ c ∷ m1 , left , right
diamond (a ∷ .(suc b) ∷ b ∷ .(suc b) ∷ m1) m2 m3 (swap≅ x [] .(b ∷ suc b ∷ m1) .(a ∷ suc b ∷ b ∷ suc b ∷ m1) .m2 refl defmf) (braid≅ (.a ∷ []) .m1 .(a ∷ suc b ∷ b ∷ suc b ∷ m1) .m3 refl defmf₁)
  rewrite defmf rewrite defmf₁ =
  let b<a : suc b < a
      b<a = ≤-down x
      left = trans (swap b<a [ suc b ] _) (trans (swap x (suc b ∷ b ∷ []) _) (braid [] (a ∷ m1) _ _))
      right = trans (swap b<a [] _) (trans (swap x [ b ] _) (swap b<a (b ∷ suc b ∷ []) _))
  in  b ∷ suc b ∷ b ∷ a ∷ m1 , (left , right)
diamond m1 m2 m3 (braid≅ [] r .m1 .m2 defm defmf) (braid≅ (x ∷ x₁ ∷ []) r₁ .m1 .m3 defm₁ defmf₁) = {!   !} -- bb

--- disjoint
diamond m1 m2 m3 (cancel≅ [] r .m1 .m2 defm defmf) (cancel≅ (x ∷ x₁ ∷ l) r₁ .m1 .m3 defm₁ defmf₁) = {!   !} -- cc-dis
diamond m1 m2 m3 (cancel≅ [] r .m1 .m2 defm defmf) (swap≅ x (x₁ ∷ x₂ ∷ l) r₁ .m1 .m3 defm₁ defmf₁) = {!   !} -- cs-dis
diamond m1 m2 m3 (cancel≅ [] r .m1 .m2 defm defmf) (braid≅ (x ∷ x₁ ∷ l) r₁ .m1 .m3 defm₁ defmf₁) = {!   !} -- cb-dis
diamond m1 m2 m3 (swap≅ x [] r .m1 .m2 defm defmf) (swap≅ x₁ (x₂ ∷ x₃ ∷ l) r₁ .m1 .m3 defm₁ defmf₁) = {!   !} -- ss-dis
diamond m1 m2 m3 (swap≅ x [] r .m1 .m2 defm defmf) (braid≅ (x₁ ∷ x₂ ∷ l) r₁ .m1 .m3 defm₁ defmf₁) = {!   !} -- sb-dis
diamond m1 m2 m3 (braid≅ [] r .m1 .m2 defm defmf) (braid≅ (x ∷ x₁ ∷ x₂ ∷ l) r₁ .m1 .m3 defm₁ defmf₁) = {!   !} -- bb-dis

--- identity
diamond m1 m2 m3 (cancel≅ [] r .m1 .m2 defm defmf) (cancel≅ [] r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
diamond m1 m2 m3 (swap≅ x [] r .m1 .m2 defm defmf) (swap≅ x₁ [] r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
diamond m1 m2 m3 (braid≅ [] r .m1 .m2 defm defmf) (braid≅ [] r₁ .m1 .m3 defm₁ defmf₁) = {!   !}

--- rec
diamond m1 m2 m3 (braid≅ l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
diamond m1 m2 m3 (braid≅ l r .m1 .m2 defm defmf) (swap≅ x l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
diamond m1 m2 m3 (swap≅ x l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}

--- abs
diamond m1 m2 m3 (cancel≅ [] r .m1 .m2 defm defmf) (swap≅ x [] r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
diamond m1 m2 m3 (cancel≅ [] r .m1 .m2 defm defmf) (braid≅ [] r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
diamond m1 m2 m3 (swap≅ x [] r .m1 .m2 defm defmf) (braid≅ [] r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
diamond m1 m2 m3 (braid≅ [] r .m1 .m2 defm defmf) (braid≅ (x ∷ []) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}

--- TODO
diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
diamond m1 m2 m3 (cancel≅ (x₁ ∷ l) r .m1 .m2 defm defmf) (swap≅ x l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf) (braid≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
diamond m1 m2 m3 (swap≅ x (x₂ ∷ l) r .m1 .m2 defm defmf) (swap≅ x₁ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
diamond m1 m2 m3 (swap≅ x (x₁ ∷ l) r .m1 .m2 defm defmf) (braid≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
diamond m1 m2 m3 (braid≅ (x ∷ l) r .m1 .m2 defm defmf) (braid≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}


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
