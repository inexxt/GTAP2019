{-# OPTIONS --allow-unsolved-metas #-}

module CriticalPairs where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)
open import General
open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_)
open import Data.Bool.Properties hiding (≤-reflexive)

open import Arithmetic hiding (n)
open import Diamond hiding (n; l)
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)


open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

variable
  n : ℕ
  l : List ℕ

--- critical pairs

∷-≡1 : {n1 n2 : ℕ} -> {l1 l2 : List ℕ} -> (n1 ∷ l1 ≡ n2 ∷ l2) -> (n1 ≡ n2)
∷-≡1 refl = refl

∷-≡2 : {n1 n2 : ℕ} -> {l1 l2 : List ℕ} -> (n1 ∷ l1 ≡ n2 ∷ l2) -> (l1 ≡ l2)
∷-≡2 refl = refl


cc : (a : ℕ) -> (m m1 m2 : List ℕ) -> (m ≡ a ∷ a ∷ a ∷ []) -> (m ≅ m1) -> (m ≅ m2) -> ∃ (λ mm -> (m1 ≃ mm) × (m2 ≃ mm))
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (respects=r l x pm1 x₁ x₂) (respects=r l₁ x₃ pm2 x₄ x₅) = {!!}
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (respects=r (.a ∷ []) (nonempty-l .a .[]) cancel≅ refl x₂) (respects=l r x₃ pm2 x₄ x₅) rewrite x₂ rewrite x₅ =
  a ∷ [] , refl , trans {_ ++ r} {a ∷ a ∷ a ∷ []} {a ∷ []}  (trans {!!} {!refl≡ (≡-sym x₄)!}) (++-respects-r (nonempty-l a []) cancel)
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (respects=r .(x ∷ x₆ ∷ l) (nonempty-l x (x₆ ∷ l)) cancel≅ x₁ x₂) (respects=l r x₃ pm2 x₄ x₅) = {!!}
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (respects=r l x (swap≅ x₆) x₁ x₂) (respects=l r x₃ pm2 x₄ x₅) = {!!}
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (respects=r l x braid≅ x₁ x₂) (respects=l r x₃ pm2 x₄ x₅) = {!!}
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (respects=r l x (respects=r l₁ x₆ pm1 x₇ x₈) x₁ x₂) (respects=l r x₃ pm2 x₄ x₅) = {!!}
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (respects=r l x (respects=l r₁ x₆ pm1 x₇ x₈) x₁ x₂) (respects=l r x₃ pm2 x₄ x₅) = {!!}
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (respects=l r x pm1 x₁ x₂) (respects=r l x₃ pm2 x₄ x₅) = {!!}
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (respects=l r x pm1 x₁ x₂) (respects=l r₁ x₃ pm2 x₄ x₅) = {!!}


-- ss : (a b c : ℕ) -> (m m1 m2 : List ℕ) -> (a > suc b) -> (b > suc c) -> (m ≡ a ∷ b ∷ c ∷ []) -> (m ≅ m1) -> (m ≅ m2) -> ∃ (λ mm -> (m1 ≃ mm) × (m2 ≃ mm))
-- ss .(suc b) b .(suc b) .(suc b ∷ b ∷ suc b ∷ []) .(b ∷ suc b ∷ b ∷ []) m2 pab pbc refl braid≅ pm2 = ⊥-elim (1+n≰n pab)
-- ss .(suc b) b .(suc b) .(suc b ∷ b ∷ suc b ∷ []) m1 .(b ∷ suc b ∷ b ∷ []) pab pbc refl (respects=r l x pm1 x₁ x₂) braid≅ = ⊥-elim (1+n≰n pab)
-- ss a b c .(a ∷ b ∷ c ∷ []) m1 m2 pab pbc refl (respects=r .(a1 ∷ l1) (nonempty-l a1 l1) {r1} pm1 e1 e2) (respects=r .(a2 ∷ l2) (nonempty-l a2 l2) {r2} pm2 e3 e4) =
--   let a=a1 : a ≡ a1
--       a=a1 = ∷-≡1 e1
--       a=a2 : a ≡ a2
--       a=a2 = ∷-≡1 e3

--       l1++r1=bc : b ∷ c ∷ [] ≡ l1 ++ r1
--       l1++r1=bc = ∷-≡2 e1

--       l2++r2=bc : b ∷ c ∷ [] ≡ l2 ++ r2
--       l2++r2=bc = ∷-≡2 e3

--   in {!!} -- this is the easy case when two-two-reduction works
-- ss a b c .(a ∷ b ∷ c ∷ []) m1 m2 pab pbc refl (respects=r l x pm1 x₁ x₂) (respects=l r x₃ pm2 x₄ x₅) = {!!}
-- ss .(suc b) b .(suc b) .(suc b ∷ b ∷ suc b ∷ []) m1 .(b ∷ suc b ∷ b ∷ []) pab pbc refl (respects=l r x pm1 x₁ x₂) braid≅ = ⊥-elim (1+n≰n pab)
-- ss a b c .(a ∷ b ∷ c ∷ []) m1 m2 pab pbc refl (respects=l .(x ∷ l₁) (nonempty-l x l₁) pm1 e1 e2) (respects=r .(x₁ ∷ l) (nonempty-l x₁ l) pm2 e3 e4) = {!!}
-- ss a b c .(a ∷ b ∷ c ∷ []) m1 m2 pab pbc refl (respects=l .(a1 ∷ l1) (nonempty-l a1 l1) {r1} pm1 e1 e2) (respects=l .(a2 ∷ l2) (nonempty-l a2 l2) {r2} pm2 e3 e4) =
--   {!!} -- this is again the easy case when two-two-reduction worksw
