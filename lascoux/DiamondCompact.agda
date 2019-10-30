{-# OPTIONS --allow-unsolved-metas --without-K #-}
module DiamondCompact where

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


variable
    n : ℕ
    l : List ℕ

open ≅*-Reasoning
open Relation.Binary.PropositionalEquality.≡-Reasoning


-- and this should do something like: if ir1 = (ir p1) and ir2 = (ir p2) are non-overlapping, use force-non-crit-pair
-- otherwise, take the ir1 ∪ ir2 , force it into one of the critical pairs and then reduce critical pair
diamond : (m1 m2 m3 : List ℕ) -> (m1 ≅ m2) -> (m1 ≅ m3) -> ∃ (λ m -> (m2 ≅* m) × (m3 ≅* m))
-- -- crit-pair
-- diamond (x₁ ∷ .x₁ ∷ .x₁ ∷ m1) m2 m3 (cancel≅ [] .(x₁ ∷ m1) .(x₁ ∷ x₁ ∷ x₁ ∷ m1) .m2 refl defmf) (cancel≅ (.x₁ ∷ []) .m1 .(x₁ ∷ x₁ ∷ x₁ ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ = (x₁ ∷ m1) , (refl , refl) -- cc
-- diamond (x₂ ∷ .x₂ ∷ x₄ ∷ m1) m2 m3 (cancel≅ [] .(x₄ ∷ m1) .(x₂ ∷ x₂ ∷ x₄ ∷ m1) .m2 refl defmf) (swap≅ x (.x₂ ∷ []) .m1 .(x₂ ∷ x₂ ∷ x₄ ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ = (x₄ ∷ m1) , (refl , trans (swap x [] _) (cancel [ x₄ ] m1)) -- cs
-- diamond (c ∷ b ∷ a ∷ m1) m2 m3 (swap≅ b<c [] .(a ∷ m1) .(c ∷ b ∷ a ∷ m1) .m2 refl defmf) (swap≅ a<b (.c ∷ []) .m1 .(c ∷ b ∷ a ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ =
--   let a<c : suc a < c
--       a<c = ≤-down (≤-trans (s≤s a<b) (≤-down b<c))
--       left = trans (swap a<c [ b ] m1) (swap a<b [] _)
--       right = trans (swap a<c [] _) (swap b<c [ a ] _)
--    in a ∷ b ∷ c ∷ m1 , left , right -- ss
-- diamond (x₂ ∷ x₃ ∷ .x₃ ∷ m1) m2 m3 (cancel≅ (.x₂ ∷ []) .m1 .(x₂ ∷ x₃ ∷ x₃ ∷ m1) .m2 refl defmf) (swap≅ x [] .(x₃ ∷ m1) .(x₂ ∷ x₃ ∷ x₃ ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ = _ , (refl , trans (swap x [ x₃ ] _) (cancel [] _)) -- cs
-- diamond m1 m2 m3 (long≅ {n} k1 [] r m mf defm defmf) (long≅ {n₁} k2 [] r₁ m₁ mf₁ defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-t2 (≡-trans (≡-sym defm) defm₁)) =
--   let eq = ≡-trans (≡-sym defm) defm₁
--       eqn , eql , eqr = long-lemma n n₁ k1 k2 _ _ (s≤s (≤-up-+ (≤-reflexive refl))) (s≤s (≤-up-+ (≤-reflexive refl))) r r₁ eq
--   in  _ , (refl , refl≡ (head+tail refl (start+end (head+tail refl (head+tail refl (≡-sym (cut-h2 eql)))) (≡-sym eqr))))

diamond .(suc (k + _) ∷ suc (k + _) ∷ k + _ ∷ (_ ↓ k) ++ suc (k + _) ∷ r₁) m2 m3 (cancel≅ [] .(k + _ ∷ (_ ↓ k) ++ suc (k + _) ∷ r₁) .(suc (k + _) ∷ suc (k + _) ∷ k + _ ∷ (_ ↓ k) ++ suc (k + _) ∷ r₁) .m2 refl defmf) (long≅ {n} k (.(suc (k + _)) ∷ []) r₁ .(suc (k + _) ∷ suc (k + _) ∷ k + _ ∷ (_ ↓ k) ++ suc (k + _) ∷ r₁) .m3 refl defmf₁) rewrite defmf rewrite defmf₁ =
  let right =
        ≅*begin
          suc (k + n) ∷ k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ r₁
        ≅*⟨ braid [] _ ⟩
          k + n ∷ suc (k + n) ∷ k + n ∷ k + n ∷ (n ↓ k) ++ r₁
        ≅*⟨ cancel (k + n ∷ suc (k + n) ∷ []) ((n ↓ k) ++ r₁) ⟩
          k + n ∷ suc (k + n) ∷ (n ↓ k) ++ r₁
        ≅*⟨ long-swap-lr n (suc (k + n)) k [ _ ] r₁ rrr ⟩
          k + n ∷ (n ↓ k) ++ suc (k + n) ∷ r₁
        ≅*∎
  in  _ , (refl , right)
diamond .(x ∷ suc (k + _) ∷ k + _ ∷ (_ ↓ k) ++ suc (k + _) ∷ r₁) m2 m3 (swap≅ p [] .(k + _ ∷ (_ ↓ k) ++ suc (k + _) ∷ r₁) .(x ∷ suc (k + _) ∷ k + _ ∷ (_ ↓ k) ++ suc (k + _) ∷ r₁) .m2 refl defmf) (long≅ {n} k (x ∷ []) r₁ .(x ∷ suc (k + _) ∷ k + _ ∷ (_ ↓ k) ++ suc (k + _) ∷ r₁) .m3 refl defmf₁) rewrite defmf rewrite defmf₁ =
  let left =
        ≅*begin
          suc (k + n) ∷ x ∷ k + n ∷ (n ↓ k) ++ suc (k + n) ∷ r₁
        ≅*⟨ long-swap-lr n x (suc k) [ _ ] (suc (k + n) ∷ r₁) (≤-down p) ⟩
          suc (k + n) ∷ k + n ∷ (n ↓ k) ++ x ∷ suc (k + n) ∷ r₁
        ≅*⟨ swap p (suc (k + n) ∷ k + n ∷ (n ↓ k)) r₁ ⟩
          suc (k + n) ∷ k + n ∷ (n ↓ k) ++ suc (k + n) ∷ x ∷ r₁
        ≅*⟨ long k [] (x ∷ r₁) ⟩
          k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ x ∷ r₁
        ≅*∎
      right =
        ≅*begin
          x ∷ k + n ∷ (n ↓ (2 + k)) ++ r₁
        ≅*⟨ swap (≤-down p) [] ((n ↓ (2 + k)) ++ r₁) ⟩
         k + n ∷ x ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ r₁
        ≅*⟨ long-swap-lr n x (suc (suc k)) [ _ ] r₁ p ⟩
          k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ x ∷ r₁
        ≅*∎
  in  _ , (left , right)

-- -- -- -- - disjoint
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (cancel≅ {n = n} (x ∷ x₁ ∷ l) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--     rewrite (≡-trans defmf (cut-h2 d)) rewrite defmf₁ rewrite (≡-sym (cut-t1 d)) rewrite (≡-sym (cut-t2 d)) =
--     (l ++ r₁) ,  cancel l r₁ , (cancel [] (l ++ r₁)) --((cancel l r₁) ,  -- cc-dis
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (swap≅ x (x₁ ∷ x₂ ∷ l) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--     rewrite (≡-trans defmf (cut-h2 d)) rewrite defmf₁ rewrite (≡-sym (cut-t1 d)) rewrite (≡-sym (cut-t2 d)) =
--      ((l ++ _ ∷ _ ∷ r₁)) , (swap x l r₁ , cancel [] _) -- cs-dis
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (swap≅ x₁ (x₂ ∷ x₃ ∷ l) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--     rewrite defmf rewrite defmf₁ rewrite (≡-sym (cut-t1 d)) rewrite (≡-sym (cut-t2 d)) rewrite (cut-h2 d) =
--      _ , (swap x₁ _ r₁ , swap x [] _) -- ss-dis
-- diamond .(_ ∷ _ ∷ r₁) m2 m3 (cancel≅ (x₁ ∷ x₂ ∷ l) r .(_ ∷ _ ∷ r₁) .m2 defm defmf) (swap≅ x [] r₁ .(_ ∷ _ ∷ r₁) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 defm) rewrite ≡-sym (cut-t1 defm) rewrite ≡-sym (cut-t2 defm) =
--   _ , (swap x [] _ , cancel _ r)

-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (long≅ k (x ∷ x₁ ∷ l₁) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) =
--   _ , ((long k l₁ r₁) , (cancel [] _))
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (long≅ k (x₁ ∷ x₂ ∷ l₁) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) =
--   _ , ((long k (_ ∷ _ ∷ l₁) r₁) , (swap x [] _))

-- -- --- identity
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (cancel≅ [] r₁ .(_ ∷ _ ∷ r) .m3 defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 defm₁)  = r₁ , (refl , refl)
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (swap≅ x₁ [] r₁ .(_ ∷ _ ∷ r) .m3 defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 defm₁) rewrite (cut-t1 defm₁) rewrite (cut-t2 defm₁)  = _ , (refl , refl)

-- -- --- rec
-- diamond m1 m2 m3 (swap≅ x l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) =
--   let rec-m , rec-l , rec-r = diamond m1 m3 m2 (cancel≅ l₁ r₁ m1 m3 defm₁ defmf₁) (swap≅ x l r m1 m2 defm defmf)
--   in  rec-m , rec-r , rec-l
-- diamond m1 m2 m3 (long≅ k l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) =
--   let rec-m , rec-l , rec-r = diamond m1 m3 m2 (cancel≅ l₁ r₁ m1 m3 defm₁ defmf₁) (long≅ k l r m1 m2 defm defmf)
--   in  rec-m , rec-r , rec-l
-- diamond m1 m2 m3 (long≅ k l r .m1 .m2 defm defmf) (swap≅ x l₁ r₁ .m1 .m3 defm₁ defmf₁) =
--   let rec-m , rec-l , rec-r = diamond m1 m3 m2 (swap≅ x l₁ r₁ m1 m3 defm₁ defmf₁) (long≅ k l r m1 m2 defm defmf)
--   in  rec-m , rec-r , rec-l

-- diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf) (cancel≅ [] r₁ .m1 .m3 defm₁ defmf₁) =
--   let rec-m , rec-l , rec-r = diamond m1 m3 m2 (cancel≅ [] r₁ m1 m3 defm₁ defmf₁) (cancel≅ (x ∷ l) r m1 m2 defm defmf)
--   in  rec-m , rec-r , rec-l
-- diamond m1 m2 m3 (swap≅ x (x₂ ∷ l) r .m1 .m2 defm defmf) (swap≅ x₁ [] r₁ .m1 .m3 defm₁ defmf₁) =
--   let rec-m , rec-l , rec-r = diamond m1 m3 m2 (swap≅ x₁ [] r₁ m1 m3 defm₁ defmf₁) (swap≅ x (x₂ ∷ l) r m1 m2 defm defmf)
--   in  rec-m , rec-r , rec-l
-- diamond m1 m2 m3 (long≅ k (x ∷ l) r .m1 .m2 defm defmf) (long≅ k₁ [] r₁ .m1 .m3 defm₁ defmf₁) =
--   let rec-m , rec-l , rec-r = diamond m1 m3 m2 (long≅ k₁ [] r₁ m1 m3 defm₁ defmf₁) (long≅ k (x ∷ l) r m1 m2 defm defmf)
--   in  rec-m , rec-r , rec-l

-- -- rec - decreasing size
-- diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf)  (cancel≅ (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (cancel≅ (x₁ ∷ l) r .m1 .m2 defm defmf) (swap≅ x (x₂ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (swap≅ x (x₂ ∷ l) r .m1 .m2 defm defmf) (swap≅ x₁ (x₃ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf)  (long≅ k (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (swap≅ x (x₁ ∷ l) r .m1 .m2 defm defmf) (long≅ k (x₂ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (long≅ k (x ∷ l) r .m1 .m2 defm defmf)  (long≅ k₁ (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}

-- -- - abs
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (swap≅ x [] .r .(_ ∷ _ ∷ r) .m3 refl defmf₁) = abs-suc x

-- --- base cases when long is at the beginngin
-- diamond m1 m2 m3 (cancel≅ {n₁} l r .m1 .m2 defm defmf) (long≅ {n} k [] r₁ .m1 .m3 defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ =
--   let eq = ≡-trans (≡-sym defm₁) defm
--       rec-m , rec-r , rec-l = cancel-long-lemma n k n₁ r₁ l r eq
--   in  rec-m , rec-l , rec-r
-- diamond m1 m2 m3 (swap≅ x l r .m1 .m2 defm defmf) (long≅ {n} k [] r₁ .m1 .m3 defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ =
--   let eq = ≡-trans (≡-sym defm₁) defm
--       rec-m , rec-r , rec-l = swap-long-lemma n k _ _ x r₁ l r eq
--   in  rec-m , rec-l , rec-r
-- diamond m1 m2 m3 (long≅ {n} k [] r .m1 .m2 defm defmf) (long≅ {n₁} k₁ l₁ r₁ .m1 .m3 defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ =
--   let eq = ≡-trans (≡-sym defm₁) defm
--       rec-m , rec-l , rec-r = long-long-lemma n k n₁ k₁ r l₁ r₁ (≡-sym eq)
--   in  rec-m , rec-l , rec-r


-- diamond-full : {m1 m2 m3 : List ℕ} -> (m1 ≅* m2) -> (m1 ≅* m3) -> ∃ (λ m -> (m2 ≅* m) × (m3 ≅* m))
-- diamond-full refl q = _ , (q , refl)
-- diamond-full (trans≅ x p) refl = _ , refl , trans≅ x p
-- diamond-full (trans≅ x refl) (trans≅ y refl) = diamond _ _ _ x y
-- diamond-full {m1} {m2} {m3} (trans≅ x (trans≅ y p)) (trans≅ z refl) =
--   let one-m , one-l , one-r = diamond _ _ _ x z
--       rec-m , rec-l , rec-r = diamond-full {_} {m2} {one-m} (trans≅ y p) one-l
--   in  rec-m , rec-l , trans one-r rec-r
-- diamond-full {m1} {m2} {m3} (trans≅ x p) (trans≅ y (trans≅ {m4} z q)) =
--   let rec-m , rec-l , rec-r = diamond-full (trans≅ x p) (ext y)
--       rec-mm , rec-ll , rec-rr = diamond-full {m4} {rec-m} {_} rec-r (trans≅ z q)
--   in  rec-mm , trans rec-l rec-ll , rec-rr

--
-- data _≃_ : List ℕ -> List ℕ -> Set where
--   R : {m1 m2 mf : List ℕ} -> (p1 : m1 ≅* mf) -> (p2 : m2 ≅* mf) -> m1 ≃ m2
--
-- refl≃ : (m : List ℕ) -> (m ≃ m)
-- refl≃ m = R refl refl
--
-- comm≃ : (m1 m2 : List ℕ) -> (m1 ≃ m2) -> (m2 ≃ m1)
-- comm≃ m1 m2 (R p1 p2) = R p2 p1
--
-- trans≃ : (m1 m2 m3 : List ℕ) -> (r1 : m1 ≃ m2) -> (r2 : m2 ≃ m3) -> (m1 ≃ m3)
-- trans≃ m1 m2 m3 (R p1 p2) (R p3 p4) =
--   let lemma-m , lemma1 , lemma2 = diamond-full p2 p3
--   in  R (trans p1 lemma1) (trans p4 lemma2)
