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
open import Data.Bool hiding (_<_; _≤_; _≟_)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans; _≟_)
open import Function

open import Arithmetic hiding (n)
open import Compact hiding (n; l)
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)


open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)


variable
    n : ℕ
    l : List ℕ

open ≅*-Reasoning

abs-refl : {A : Set} -> n < n -> A
abs-refl p = ⊥-elim (1+n≰n p)

-- and this should do something like: if ir1 = (ir p1) and ir2 = (ir p2) are non-overlapping, use force-non-crit-pair
-- otherwise, take the ir1 ∪ ir2 , force it into one of the critical pairs and then reduce critical pair
diamond : (m1 m2 m3 : List ℕ) -> (m1 ≅ m2) -> (m1 ≅ m3) -> ∃ (λ m -> (m2 ≅* m) × (m3 ≅* m))
-- crit-pair
-- diamond (x₁ ∷ .x₁ ∷ .x₁ ∷ m1) m2 m3 (cancel≅ [] .(x₁ ∷ m1) .(x₁ ∷ x₁ ∷ x₁ ∷ m1) .m2 refl defmf) (cancel≅ (.x₁ ∷ []) .m1 .(x₁ ∷ x₁ ∷ x₁ ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ = (x₁ ∷ m1) , (refl , refl) -- cc
-- diamond (x₂ ∷ .x₂ ∷ x₄ ∷ m1) m2 m3 (cancel≅ [] .(x₄ ∷ m1) .(x₂ ∷ x₂ ∷ x₄ ∷ m1) .m2 refl defmf) (swap≅ x (.x₂ ∷ []) .m1 .(x₂ ∷ x₂ ∷ x₄ ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ = (x₄ ∷ m1) , (refl , trans (swap x [] _) (cancel [ x₄ ] m1)) -- cs
-- diamond (.(suc x₃) ∷ .(suc x₃) ∷ x₃ ∷ .(suc x₃) ∷ m1) m2 m3 (cancel≅ [] .(x₃ ∷ suc x₃ ∷ m1) .(suc x₃ ∷ suc x₃ ∷ x₃ ∷ suc x₃ ∷ m1) .m2 refl defmf) (braid≅ (.(suc x₃) ∷ []) .m1 .(suc x₃ ∷ suc x₃ ∷ x₃ ∷ suc x₃ ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ = (x₃ ∷ suc x₃ ∷ m1) , (refl , trans (braid [] ( x₃ ∷ m1 )) (cancel (x₃ ∷ suc x₃ ∷ []) m1)) -- cb
-- diamond (c ∷ b ∷ a ∷ m1) m2 m3 (swap≅ b<c [] .(a ∷ m1) .(c ∷ b ∷ a ∷ m1) .m2 refl defmf) (swap≅ a<b (.c ∷ []) .m1 .(c ∷ b ∷ a ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ =
--   let a<c : suc a < c
--       a<c = ≤-down (≤-trans (s≤s a<b) (≤-down b<c))
--       left = trans (swap a<c [ b ] m1) (swap a<b [] _)
--       right = trans (swap a<c [] _) (swap b<c [ a ] _)
--    in a ∷ b ∷ c ∷ m1 , left , right -- ss
-- diamond (a ∷ .(suc b) ∷ b ∷ .(suc b) ∷ m1) m2 m3 (swap≅ x [] .(b ∷ suc b ∷ m1) .(a ∷ suc b ∷ b ∷ suc b ∷ m1) .m2 refl defmf) (braid≅ (.a ∷ []) .m1 .(a ∷ suc b ∷ b ∷ suc b ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ =
--   let b<a : suc b < a
--       b<a = ≤-down x
--       left = trans (swap b<a [ suc b ] _) (trans (swap x (suc b ∷ b ∷ []) _) (braid [] (a ∷ m1)))
--       right = trans (swap b<a [] _) (trans (swap x [ b ] _) (swap b<a (b ∷ suc b ∷ []) _))
--   in  b ∷ suc b ∷ b ∷ a ∷ m1 , (left , right) -- sb
-- diamond (.(suc a) ∷ a ∷ .(suc a) ∷ .a ∷ .(suc a) ∷ m1) m2 m3 (braid≅ [] .(a ∷ suc a ∷ m1) .(suc a ∷ a ∷ suc a ∷ a ∷ suc a ∷ m1) .m2 refl defmf) (braid≅ (.(suc a) ∷ .a ∷ []) .m1 .(suc a ∷ a ∷ suc a ∷ a ∷ suc a ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ =
--   let left = trans (cancel (a ∷ suc a ∷ []) _) (cancel [ a ] _)
--       right = trans (cancel [ suc a ] _) (cancel [] _)
--   in  a ∷ m1 , left , right -- bb
-- diamond (x₂ ∷ x₃ ∷ .x₃ ∷ m1) m2 m3 (cancel≅ (.x₂ ∷ []) .m1 .(x₂ ∷ x₃ ∷ x₃ ∷ m1) .m2 refl defmf) (swap≅ x [] .(x₃ ∷ m1) .(x₂ ∷ x₃ ∷ x₃ ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ = _ , (refl , trans (swap x [ x₃ ] _) (cancel [] _)) -- cs
-- diamond (.(suc a) ∷ a ∷ .(suc a) ∷ .(suc a) ∷ m1) m2 m3 (cancel≅ (.(suc a) ∷ .a ∷ []) .m1 .(suc a ∷ a ∷ suc a ∷ suc a ∷ m1) .m2 refl defmf) (braid≅ [] .(suc a ∷ m1) .(suc a ∷ a ∷ suc a ∷ suc a ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ = suc a ∷ a ∷ m1 , (refl , trans (braid [ a ] _) (cancel [] _)) -- bc
-- diamond (.(suc a) ∷ a ∷ .(suc a) ∷ b ∷ m1) m2 m3 (swap≅ x (.(suc a) ∷ .a ∷ []) r .(suc a ∷ a ∷ suc a ∷ b ∷ m1) .m2 refl defmf) (braid≅ [] .(b ∷ m1) .(suc a ∷ a ∷ suc a ∷ b ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ with suc b ≟ a
-- ... | yes p rewrite (≡-sym p) = (1 + b) ∷ (2 + b) ∷ (1 + b) ∷ b ∷ m1  , bs [] m1 ,  refl
-- ... | no p =
--   let b<a : suc b < a
--       b<a = ≤-≠-≤ x (λ e → p (≡-down2 e))
--   in (b ∷ a ∷ (1 + a) ∷ a ∷ m1) , ((trans (swap b<a [ 1 + a ] _) (trans (swap x [] _) (braid [ b ] _))) , trans (swap b<a (a ∷ suc a ∷ []) m1) (trans (swap x (a ∷ []) (a ∷ m1)) (swap b<a [] (suc a ∷ a ∷ m1))))
-- diamond .(suc (suc _) ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) m2 m3 (cancel≅ {suc (suc n)} [] .(suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .(suc (suc _) ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m2 refl defmf) (bs≅ (.(suc (suc _)) ∷ []) r₁ .(suc (suc _) ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m3 refl defmf₁) rewrite defmf rewrite defmf₁ =
--    1 + n ∷ n ∷ 2 + n ∷ r₁   , ( refl , trans (braid [] _) (trans (cancel (_ ∷ _ ∷ []) (n ∷ r₁) ) (swap (s≤s (≤-reflexive refl)) [ suc n ] r₁)))
diamond .(x₁ ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) m2 m3 (swap≅ {k = suc (suc n)} x [] .(suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .(x₁ ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m2 refl defmf) (bs≅ (x₁ ∷ []) r₁ .(x₁ ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m3 refl defmf₁) rewrite defmf rewrite defmf₁ =
  let left =
        ≅*begin
          suc (suc n) ∷ x₁ ∷ suc n ∷ n ∷ suc (suc n) ∷ r₁
        ≅*⟨ swap (≤-down x) [ 2 + n ] (n ∷ suc (suc n) ∷ r₁)  ⟩
           suc (suc n) ∷ suc n ∷ x₁ ∷ n ∷ suc (suc n) ∷ r₁
        ≅*⟨ swap (≤-down (≤-down x)) (suc (suc n) ∷ suc n ∷ []) ((2 + n) ∷ r₁) ⟩
          suc (suc n) ∷ suc n ∷ n ∷ x₁ ∷ suc (suc n) ∷ r₁
        ≅*⟨ swap x (suc (suc n) ∷ suc n ∷ n ∷ []) r₁ ⟩
          suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ x₁ ∷ r₁
        ≅*⟨ bs [] (x₁ ∷ r₁) ⟩
          suc n ∷ suc (suc n) ∷ suc n ∷ n ∷ x₁ ∷ r₁
        ≅*∎
      right =
        ≅*begin
          x₁ ∷ suc n ∷ suc (suc n) ∷ suc n ∷ n ∷ r₁
        ≅*⟨ swap (≤-down x) [] (suc (suc n) ∷ suc n ∷ n ∷ r₁) ⟩
          suc n ∷ x₁ ∷ suc (suc n) ∷ suc n ∷ n ∷ r₁
        ≅*⟨ swap x (suc n ∷ []) ((1 + n) ∷ n ∷ r₁) ⟩
          suc n ∷ suc (suc n) ∷ x₁ ∷ suc n ∷ n ∷ r₁
        ≅*⟨ swap (≤-down x) (suc n ∷ suc (suc n) ∷ []) (n ∷ r₁) ⟩
          suc n ∷ suc (suc n) ∷ suc n ∷ x₁ ∷ n ∷ r₁
        ≅*⟨ swap (≤-down (≤-down x)) (suc n ∷ suc (suc n) ∷ suc n ∷ []) r₁ ⟩
          suc n ∷ suc (suc n) ∷ suc n ∷ n ∷ x₁ ∷ r₁
        ≅*∎
  in  _  , (left ,  right)
-- diamond .(suc (suc _) ∷ suc _ ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) m2 m3 (braid≅ [] .(suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .(suc (suc _) ∷ suc _ ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m2 refl defmf) (bs≅ {n} (.(suc (suc _)) ∷ .(suc _) ∷ []) r₁ .(suc (suc _) ∷ suc _ ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m3 refl defmf₁) rewrite defmf rewrite defmf₁ =
--   let left =
--         ≅*begin
--           suc n ∷ suc (suc n) ∷ suc n ∷ suc n ∷ n ∷ suc (suc n) ∷ r₁
--         ≅*⟨ cancel ((1 + n) ∷ (2 + n) ∷ []) (n ∷ (2 + n) ∷ r₁) ⟩
--           suc n ∷ suc (suc n) ∷ n ∷ suc (suc n) ∷ r₁
--         ≅*⟨ swap (s≤s (s≤s (≤-reflexive refl))) [ suc n ] ((2 + n) ∷ r₁) ⟩
--           suc n ∷ n ∷ suc (suc n) ∷ suc (suc n) ∷ r₁
--         ≅*⟨ cancel ((1 + n) ∷ n ∷ []) r₁ ⟩
--           suc n ∷ n ∷ r₁
--         ≅*∎
--       right =
--         ≅*begin
--           suc (suc n) ∷ suc n ∷ suc n ∷ suc (suc n) ∷ suc n ∷ n ∷ r₁
--         ≅*⟨ cancel [ 2 + n ] (suc (suc n) ∷ suc n ∷ n ∷ r₁) ⟩
--           suc (suc n) ∷ suc (suc n) ∷ suc n ∷ n ∷ r₁
--         ≅*⟨ cancel [] (suc n ∷ n ∷ r₁) ⟩
--           suc n ∷ n ∷ r₁
--         ≅*∎
--   in  _ , (left , right)
-- diamond .(suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ r₁) m2 m3 (bs≅ [] .(suc n ∷ n ∷ suc (suc n) ∷ r₁) .(suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ r₁) .m2 refl defmf) (bs≅ (.(suc (suc n)) ∷ .(suc n) ∷ n ∷ []) r₁ .(suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ r₁) .m3 refl defmf₁) rewrite defmf rewrite defmf₁ =
--   let left =
--         ≅*begin
--           suc n ∷ suc (suc n) ∷ suc n ∷ n ∷ suc n ∷ n ∷ suc (suc n) ∷ r₁
--         ≅*⟨ braid (suc n ∷ suc (suc n) ∷ []) (n ∷ suc (suc n) ∷ r₁) ⟩
--           suc n ∷ suc (suc n) ∷ n ∷ suc n ∷ n ∷ n ∷ suc (suc n) ∷ r₁
--         ≅*⟨ cancel (suc n ∷ suc (suc n) ∷ n ∷ suc n ∷ []) ((2 + n) ∷ r₁) ⟩
--           suc n ∷ suc (suc n) ∷ n ∷ suc n ∷ suc (suc n) ∷ r₁
--         ≅*⟨ swap (s≤s (≤-reflexive refl)) [ 1 + n ] (suc n ∷ suc (suc n) ∷ r₁)  ⟩
--           suc n ∷ n ∷ suc (suc n) ∷ suc n ∷ suc (suc n) ∷ r₁
--         ≅*⟨ braid (suc n ∷ n ∷ []) r₁ ⟩
--           suc n ∷ n ∷ suc n ∷ suc (suc n) ∷ suc n ∷ r₁
--         ≅*⟨ braid [] (suc (suc n) ∷ suc n ∷ r₁) ⟩
--           n ∷ suc n ∷ n ∷ suc (suc n) ∷ suc n ∷ r₁
--         ≅*∎
--       right =
--         ≅*begin
--           suc (suc n) ∷ suc n ∷ n ∷ suc n ∷ suc (suc n) ∷ suc n ∷ n ∷ r₁
--         ≅*⟨ braid [ 2 + n ] (suc (suc n) ∷ suc n ∷ n ∷ r₁) ⟩
--            suc (suc n) ∷ n ∷ suc n ∷ n ∷ suc (suc n) ∷ suc n ∷ n ∷ r₁
--         ≅*⟨ swap (s≤s (≤-reflexive refl)) [] (suc n ∷ n ∷ suc (suc n) ∷ suc n ∷ n ∷ r₁) ⟩
--           n ∷ suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ suc n ∷ n ∷ r₁
--         ≅*⟨ bs [ n ] ((1 + n) ∷ n ∷ r₁) ⟩
--           n ∷ suc n ∷ suc (suc n) ∷ suc n ∷ n ∷ suc n ∷ n ∷ r₁
--         ≅*⟨ braid (n ∷ suc n ∷ suc (suc n) ∷ []) (n ∷ r₁) ⟩
--           n ∷ suc n ∷ suc (suc n) ∷ n ∷ suc n ∷ n ∷ n ∷ r₁
--         ≅*⟨ cancel (n ∷ suc n ∷ suc (suc n) ∷ n ∷ suc n ∷ []) r₁ ⟩
--           n ∷ suc n ∷ suc (suc n) ∷ n ∷ suc n ∷ r₁
--         ≅*⟨ swap ((s≤s (≤-reflexive refl))) (n ∷ suc n ∷ []) ((1 + n) ∷ r₁)  ⟩
--           n ∷ suc n ∷ n ∷ suc (suc n) ∷ suc n ∷ r₁
--         ≅*∎
--   in  _ , left , right

-- diamond .(suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ suc (suc n) ∷ r) m2 m3 (cancel≅ (.(suc (suc n)) ∷ .(suc n) ∷ n ∷ []) r .(suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ suc (suc n) ∷ r) .m2 refl defmf) (bs≅ [] .(suc (suc n) ∷ r) .(suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ suc (suc n) ∷ r) .m3 refl defmf₁) rewrite defmf rewrite defmf₁ =
--   _ , (refl , (trans (bs [ suc n ]  r) (cancel [] (suc (suc n) ∷ suc n ∷ n ∷ r))))
diamond .(suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ _ ∷ r) m2 m3 (swap≅ {k = k} x (.(suc (suc n)) ∷ .(suc n) ∷ n ∷ []) r .(suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ _ ∷ r) .m2 refl defmf) (bs≅ [] .(_ ∷ r) .(suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ _ ∷ r) .m3 refl defmf₁) rewrite defmf rewrite defmf₁ with k ≟ n
... | yes p rewrite (≡-sym p) = _ , (trans (cancel ((2 + k) ∷ (1 + k) ∷ []) ((2 + k) ∷ r)) (braid [] r) , cancel _ r)
... | no p with suc k ≟ n
... | yes q rewrite (≡-sym q) = {!!} , ({!!} , {!!})
... | no q =
      let k<n : suc k < n
          k<n = ≤-≠-≤ (≤-≠-≤ x λ e → p (≡-down2 (≡-down2 e))) λ e → q (≡-down2 e)
          left =
            ≅*begin
              (suc (suc n) ∷ suc n ∷ n ∷ k ∷ suc (suc n) ∷ r)
            ≅*⟨ swap k<n (suc (suc n) ∷ suc n ∷ []) ((2 + n) ∷ r) ⟩
              suc (suc n) ∷ suc n ∷ k ∷ n ∷ suc (suc n) ∷ r
            ≅*⟨ swap (≤-up k<n) (suc (suc n) ∷ []) (n ∷ suc (suc n) ∷ r) ⟩
              suc (suc n) ∷ k ∷ suc n ∷ n ∷ suc (suc n) ∷ r
            ≅*⟨ swap (≤-up (≤-up k<n)) [] (suc n ∷ n ∷ suc (suc n) ∷ r) ⟩
              k ∷ suc (suc n) ∷ suc n ∷ n ∷ suc (suc n) ∷ r
            ≅*⟨ bs [ k ] r ⟩
              (k ∷ suc n ∷ suc (suc n) ∷ suc n ∷ n ∷ r)
            ≅*∎
          right =
            ≅*begin
              (suc n ∷ suc (suc n) ∷ suc n ∷ n ∷ k ∷ r)
            ≅*⟨ swap k<n (suc n ∷ suc (suc n) ∷ suc n ∷ []) r ⟩
              (suc n ∷ suc (suc n) ∷ suc n ∷ k ∷ n ∷ r)
            ≅*⟨ swap (≤-up k<n) ((suc n ∷ suc (suc n) ∷ [])) (n ∷ r) ⟩
              (suc n ∷ suc (suc n) ∷ k ∷ suc n ∷ n ∷ r)
            ≅*⟨ swap x (suc n ∷ []) (suc n ∷ n ∷ r) ⟩
              (suc n ∷ k ∷ suc (suc n) ∷ suc n ∷ n ∷ r)
            ≅*⟨ swap (≤-up k<n) [] (suc (suc n) ∷ suc n ∷ n ∷ r) ⟩
              (k ∷ suc n ∷ suc (suc n) ∷ suc n ∷ n ∷ r)
            ≅*∎
      in  _ , left , right

-- diamond m1 m2 m3 (braid≅ (x ∷ x₁ ∷ x₂ ∷ []) r .m1 .m2 defm defmf) (bs≅ [] r₁ .m1 .m3 defm₁ defmf₁) = {!  defm !}

-- -- - disjoint
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (cancel≅ {n = n} (x ∷ x₁ ∷ l) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--     rewrite (≡-trans defmf (cut-h2 d)) rewrite defmf₁ rewrite (≡-sym (cut-t1 d)) rewrite (≡-sym (cut-t2 d)) =
--     (l ++ r₁) ,  cancel l r₁ , (cancel [] (l ++ r₁)) --((cancel l r₁) ,  -- cc-dis
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (swap≅ x (x₁ ∷ x₂ ∷ l) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--     rewrite (≡-trans defmf (cut-h2 d)) rewrite defmf₁ rewrite (≡-sym (cut-t1 d)) rewrite (≡-sym (cut-t2 d)) =
--      ((l ++ _ ∷ _ ∷ r₁)) , (swap x l r₁ , cancel [] _) -- cs-dis
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (braid≅ (x ∷ x₁ ∷ l) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--     rewrite (≡-trans defmf (cut-h2 d)) rewrite defmf₁ rewrite (≡-sym (cut-t1 d)) rewrite (≡-sym (cut-t2 d)) =
--      (l ++ _ ∷ suc _ ∷ _ ∷ r₁) , ((braid l r₁) , (cancel [] _)) -- cb-dis
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (swap≅ x₁ (x₂ ∷ x₃ ∷ l) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--     rewrite defmf rewrite defmf₁ rewrite (≡-sym (cut-t1 d)) rewrite (≡-sym (cut-t2 d)) rewrite (cut-h2 d) =
--      _ , (swap x₁ _ r₁ , swap x [] _) -- ss-dis
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (braid≅ (x₁ ∷ x₂ ∷ l) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--     rewrite defmf rewrite defmf₁ rewrite (cut-h2 d) rewrite (cut-t1 d) rewrite (cut-t2 d) =
--      _  , ((braid (x₂ ∷ x₁ ∷ l) r₁ ) , (swap x [] _)) -- sb-dis
-- diamond .(suc _ ∷ _ ∷ suc _ ∷ r) m2 m3 (braid≅ [] r .(suc _ ∷ _ ∷ suc _ ∷ r) .m2 refl defmf) (braid≅ (x ∷ x₁ ∷ x₂ ∷ l) r₁ .(suc _ ∷ _ ∷ suc _ ∷ r) .m3 d defmf₁)
--     rewrite defmf rewrite defmf₁ rewrite (cut-h3 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) rewrite ≡-sym (cut-t3 d) =
--     _ , ((braid (_ ∷ suc _ ∷ _ ∷ l) r₁) , (braid [] (l ++ _ ∷ suc _ ∷ _ ∷ r₁))) -- bb-dis
-- diamond .(_ ∷ _ ∷ r₁) m2 m3 (cancel≅ (x₁ ∷ x₂ ∷ l) r .(_ ∷ _ ∷ r₁) .m2 defm defmf) (swap≅ x [] r₁ .(_ ∷ _ ∷ r₁) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 defm) rewrite ≡-sym (cut-t1 defm) rewrite ≡-sym (cut-t2 defm) =
--   _ , (swap x [] _ , cancel _ r)
-- diamond .(suc _ ∷ _ ∷ suc _ ∷ r₁) m2 m3 (cancel≅ (x ∷ x₁ ∷ x₂ ∷ l) r .(suc _ ∷ _ ∷ suc _ ∷ r₁) .m2 defm defmf) (braid≅ [] r₁ .(suc _ ∷ _ ∷ suc _ ∷ r₁) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h3 defm) rewrite ≡-sym (cut-t1 defm) rewrite ≡-sym (cut-t2 defm) rewrite ≡-sym (cut-t3 defm) =
--   _ , ((braid [] (l ++ r)) , (cancel _ r))
-- diamond .(suc _ ∷ _ ∷ suc _ ∷ r₁) m2 m3 (swap≅ x (x₁ ∷ x₂ ∷ x₃ ∷ l) r .(suc _ ∷ _ ∷ suc _ ∷ r₁) .m2 defm defmf) (braid≅ [] r₁ .(suc _ ∷ _ ∷ suc _ ∷ r₁) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h3 defm) rewrite ≡-sym (cut-t1 defm) rewrite ≡-sym (cut-t2 defm) rewrite ≡-sym (cut-t3 defm) =
--   _ , ((braid [] (l ++ _ ∷ _ ∷ r)) , (swap x (_ ∷ suc _ ∷ _ ∷ l) r))
--
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (bs≅ (x ∷ x₁ ∷ l) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) =
--   _ , ((bs l r₁ ) , (cancel [] _))
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (bs≅ (x₁ ∷ x₂ ∷ l) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) =
--   _ , (bs (_ ∷ _ ∷ l) r₁ , (swap x [] _))
-- diamond .(suc _ ∷ _ ∷ suc _ ∷ r) m2 m3 (braid≅ [] r .(suc _ ∷ _ ∷ suc _ ∷ r) .m2 refl defmf) (bs≅ (x ∷ x₁ ∷ x₂ ∷ l) r₁ .(suc _ ∷ _ ∷ suc _ ∷ r) .m3 d defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h3 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) rewrite ≡-sym (cut-t3 d) =
--   _ ∷ suc _ ∷ _ ∷ l ++ suc _ ∷ suc (suc _) ∷ suc _ ∷ _ ∷ r₁ , (bs (_ ∷ suc _ ∷ _ ∷ l) r₁ , braid [] _)
-- diamond .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) m2 m3 (bs≅ {n} [] r .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) .m2 refl defmf) (bs≅ {n₁} (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ l) r₁ .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) .m3 d defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h4 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) rewrite ≡-sym (cut-t3 d) rewrite ≡-sym (cut-t4 d) =
--   let left = bs (suc n ∷ suc (suc n) ∷ suc n ∷ n ∷ l) r₁
--       right = bs [] (l ++ suc n₁ ∷ suc (suc n₁) ∷ suc n₁ ∷ n₁ ∷ r₁)
--   in  (suc n ∷ suc (suc n) ∷ suc n ∷ n ∷ l ++ suc n₁ ∷ suc (suc n₁) ∷ suc n₁ ∷ n₁ ∷ r₁) , left , right
-- diamond .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) m2 m3 (cancel≅ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ l) r .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m2 d defmf) (bs≅ [] r₁ .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h4 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) rewrite ≡-sym (cut-t3 d) rewrite ≡-sym (cut-t4 d) =
--   _ , (bs [] (l ++ r) , cancel (suc _ ∷ suc (suc _) ∷ suc _ ∷ _ ∷ l) r)
-- diamond .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) m2 m3 (swap≅ x (x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ l) r .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m2 d defmf) (bs≅ [] r₁ .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h4 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) rewrite ≡-sym (cut-t3 d) rewrite ≡-sym (cut-t4 d) =
--    _ , (bs [] (l ++ (_ ∷ _ ∷ r)) , swap x (suc _ ∷ suc (suc _) ∷ suc _ ∷ _ ∷ l) r)
-- diamond .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) m2 m3 (braid≅ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ l) r .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m2 d defmf) (bs≅ [] r₁ .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h4 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) rewrite ≡-sym (cut-t3 d) rewrite ≡-sym (cut-t4 d) =
--   _ , ((bs [] (l ++ _ ∷ suc _ ∷ _ ∷ r)) , (braid (suc _ ∷ suc (suc _) ∷ suc _ ∷ _ ∷ l) r ))
-- diamond .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) m2 m3 (bs≅ {n} (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ l) r .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m2 d defmf) (bs≅ {n₁} [] r₁ .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h4 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) rewrite ≡-sym (cut-t3 d) rewrite ≡-sym (cut-t4 d) =
--   _ , (bs [] (l ++ suc n ∷ suc (suc n) ∷ suc n ∷ n ∷ r) , bs (suc n₁ ∷ suc (suc n₁) ∷ suc n₁ ∷ n₁ ∷ l) r)
--
-- -- --- identity
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (cancel≅ [] r₁ .(_ ∷ _ ∷ r) .m3 defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 defm₁)  = r₁ , (refl , refl)
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (swap≅ x₁ [] r₁ .(_ ∷ _ ∷ r) .m3 defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 defm₁) rewrite (cut-t1 defm₁) rewrite (cut-t2 defm₁)  = _ , (refl , refl)
-- diamond .(suc _ ∷ _ ∷ suc _ ∷ r) m2 m3 (braid≅ [] r .(suc _ ∷ _ ∷ suc _ ∷ r) .m2 refl defmf) (braid≅ [] r₁ .(suc _ ∷ _ ∷ suc _ ∷ r) .m3 defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h3 defm₁) rewrite (cut-t1 defm₁) rewrite (cut-t2 defm₁) rewrite (cut-t3 defm₁) = _ , (refl , refl)
-- diamond .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) m2 m3 (bs≅ [] r .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) .m2 refl defmf) (bs≅ [] r₁ .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) .m3 defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h4 defm₁) rewrite (cut-t1 defm₁) rewrite (cut-t2 defm₁) rewrite (cut-t3 defm₁) rewrite (cut-t4 defm₁) = _ , (refl , refl)

-- -- --- rec
-- diamond m1 m2 m3 (swap≅ x l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (braid≅ l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (braid≅ l r .m1 .m2 defm defmf) (swap≅ x l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (bs≅ l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (bs≅ l r .m1 .m2 defm defmf) (swap≅ x l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (bs≅ l r .m1 .m2 defm defmf) (braid≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
--
-- diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf) (cancel≅ [] r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (swap≅ x (x₂ ∷ l) r .m1 .m2 defm defmf) (swap≅ x₁ [] r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (braid≅ (x ∷ l) r .m1 .m2 defm defmf) (braid≅ [] r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (bs≅ (x ∷ x₁ ∷ x₂ ∷ []) r .m1 .m2 defm defmf) (bs≅ [] r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
--
-- diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf) (cancel≅ (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (cancel≅ (x₁ ∷ l) r .m1 .m2 defm defmf) (swap≅ x (x₂ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf) (braid≅ (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf) (bs≅ (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (swap≅ x (x₂ ∷ l) r .m1 .m2 defm defmf) (swap≅ x₁ (x₃ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (swap≅ x (x₁ ∷ l) r .m1 .m2 defm defmf) (braid≅ (x₂ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (swap≅ x (x₂ ∷ l) r .m1 .m2 defm defmf) (bs≅ (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (braid≅ (x ∷ l) r .m1 .m2 defm defmf) (braid≅ (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (braid≅ (x ∷ l) r .m1 .m2 defm defmf) (bs≅ (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (bs≅ (x ∷ l) r .m1 .m2 defm defmf) (bs≅ (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
--
-- -- - abs
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (swap≅ x [] .r .(_ ∷ _ ∷ r) .m3 refl defmf₁) = abs-suc x
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (braid≅ [] r₁ .(_ ∷ _ ∷ r) .m3 () defmf₁)
-- diamond .(suc _ ∷ _ ∷ suc _ ∷ r₁) m2 m3 (swap≅ x [] .(suc _ ∷ r₁) .(suc _ ∷ _ ∷ suc _ ∷ r₁) .m2 refl defmf) (braid≅ [] r₁ .(suc _ ∷ _ ∷ suc _ ∷ r₁) .m3 refl defmf₁) = abs-refl x
-- diamond .(suc _ ∷ _ ∷ suc _ ∷ r) m2 m3 (braid≅ [] r .(suc _ ∷ _ ∷ suc _ ∷ r) .m2 refl defmf) (braid≅ (x ∷ []) r₁ .(suc _ ∷ _ ∷ suc _ ∷ r) .m3 () defmf₁)
-- diamond .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) m2 m3 (bs≅ [] r .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) .m2 refl defmf) (bs≅ (x ∷ []) r₁ .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) .m3 () defmf₁)
-- diamond .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) m2 m3 (bs≅ [] r .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) .m2 refl defmf) (bs≅ (x ∷ x₁ ∷ []) r₁ .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) .m3 () defmf₁)
--
-- diamond (x₁ ∷ x₂ ∷ .x₂ ∷ []) m2 m3 (cancel≅ (.x₁ ∷ []) .[] .(x₁ ∷ x₂ ∷ x₂ ∷ []) .m2 refl defmf) (braid≅ [] r₁ .(x₁ ∷ x₂ ∷ x₂ ∷ []) .m3 () defmf₁)
-- diamond (.(suc x₃) ∷ x₃ ∷ .(suc x₃) ∷ []) m2 m3 (swap≅ x (.(suc x₃) ∷ []) .[] .(suc x₃ ∷ x₃ ∷ suc x₃ ∷ []) .m2 refl defmf) (braid≅ [] .[] .(suc x₃ ∷ x₃ ∷ suc x₃ ∷ []) .m3 refl defmf₁) = abs-suc (≤-down x)
-- diamond (.(suc x₃) ∷ x₃ ∷ .(suc x₃) ∷ x₅ ∷ m1) m2 m3 (swap≅ x (.(suc x₃) ∷ []) .(x₅ ∷ m1) .(suc x₃ ∷ x₃ ∷ suc x₃ ∷ x₅ ∷ m1) .m2 refl defmf) (braid≅ [] .(x₅ ∷ m1) .(suc x₃ ∷ x₃ ∷ suc x₃ ∷ x₅ ∷ m1) .m3 refl defmf₁) = abs-suc (≤-down x)
--
-- diamond .(x ∷ _ ∷ _ ∷ r) m2 m3 (cancel≅ (x ∷ []) r .(x ∷ _ ∷ _ ∷ r) .m2 refl defmf) (bs≅ [] r₁ .(x ∷ _ ∷ _ ∷ r) .m3 () defmf₁)
-- diamond .(x ∷ x₁ ∷ _ ∷ _ ∷ r) m2 m3 (cancel≅ (x ∷ x₁ ∷ []) r .(x ∷ x₁ ∷ _ ∷ _ ∷ r) .m2 refl defmf) (bs≅ [] r₁ .(x ∷ x₁ ∷ _ ∷ _ ∷ r) .m3 () defmf₁)
-- diamond .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) m2 m3 (swap≅ x (.(suc (suc _)) ∷ []) .(suc (suc _) ∷ r₁) .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m2 refl defmf) (bs≅ [] r₁ .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m3 refl defmf₁) = abs-refl x
--
-- diamond .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) m2 m3 (swap≅ x (.(suc (suc _)) ∷ .(suc _) ∷ []) r .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) .m2 refl defmf) (bs≅ [] .r .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) .m3 refl defmf₁) = abs-suc (≤-down (≤-down x))
-- diamond .(x ∷ suc _ ∷ _ ∷ suc _ ∷ r) m2 m3 (braid≅ (x ∷ []) r .(x ∷ suc _ ∷ _ ∷ suc _ ∷ r) .m2 refl defmf) (bs≅ [] r₁ .(x ∷ suc _ ∷ _ ∷ suc _ ∷ r) .m3 () defmf₁)
-- diamond .(x ∷ x₁ ∷ suc _ ∷ _ ∷ suc _ ∷ r) m2 m3 (braid≅ (x ∷ x₁ ∷ []) r .(x ∷ x₁ ∷ suc _ ∷ _ ∷ suc _ ∷ r) .m2 refl defmf) (bs≅ [] r₁ .(x ∷ x₁ ∷ suc _ ∷ _ ∷ suc _ ∷ r) .m3 () defmf₁)
--
-- diamond .(x ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) m2 m3 (bs≅ (x ∷ []) r .(x ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) .m2 refl defmf) (bs≅ [] r₁ .(x ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) .m3 () defmf₁)
-- diamond .(x ∷ x₁ ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) m2 m3 (bs≅ (x ∷ x₁ ∷ []) r .(x ∷ x₁ ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) .m2 refl defmf) (bs≅ [] r₁ .(x ∷ x₁ ∷ suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r) .m3 () defmf₁)
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (bs≅ [] r₁ .(_ ∷ _ ∷ r) .m3 () defmf₁)
-- diamond .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) m2 m3 (swap≅ x [] .(_ ∷ suc (suc _) ∷ r₁) .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m2 refl defmf) (bs≅ [] r₁ .(suc (suc _) ∷ suc _ ∷ _ ∷ suc (suc _) ∷ r₁) .m3 refl defmf₁) = abs-refl x
-- diamond .(suc _ ∷ _ ∷ suc _ ∷ r) m2 m3 (braid≅ [] r .(suc _ ∷ _ ∷ suc _ ∷ r) .m2 refl defmf) (bs≅ [] r₁ .(suc _ ∷ _ ∷ suc _ ∷ r) .m3 () defmf₁)
-- diamond .(suc _ ∷ _ ∷ suc _ ∷ r) m2 m3 (braid≅ [] r .(suc _ ∷ _ ∷ suc _ ∷ r) .m2 refl defmf) (bs≅ (x ∷ []) r₁ .(suc _ ∷ _ ∷ suc _ ∷ r) .m3 () defmf₁)



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
