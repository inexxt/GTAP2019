{-# OPTIONS --allow-unsolved-metas #-}
module CriticalPairsCompact where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)
-- open import General
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

postulate
  3=2+2 : {a1 a2 a3 a4 a5 a6 a7 : ℕ} -> {m1 m2 : List ℕ} -> (a1 ∷ a2 ∷ a3 ∷ [] ≡ (a4 ∷ a5 ∷ m1) ++ a6 ∷ a7 ∷ m2) -> ⊥
  3=1+3 : {a1 a2 a3 a4 a5 a6 a7 : ℕ} -> {m1 m2 : List ℕ} -> (a1 ∷ a2 ∷ a3 ∷ [] ≡ (a4 ∷ m1) ++ a5 ∷ a6 ∷ a7 ∷ m2) -> ⊥
  2const-2const : {a a1 a2 : ℕ} -> {m1 m2 : List ℕ} -> (a ∷ a ∷ a ∷ [] ≡ m1 ++ a1 ∷ a2 ∷ m2) -> (a1 ≡ a) × (a2 ≡ a)
  1+a=a : {a : ℕ} -> (suc a ≡ a) -> ⊥

----------------------
--- critical pairs ---
----------------------

----------
--- CC ---
----------

cc : (a : ℕ) -> (m m1 m2 : List ℕ) -> (defm : m ≡ a ∷ a ∷ a ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≅* mm) × (m2 ≅* mm))
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ [] .(a ∷ []) .(a ∷ a ∷ a ∷ []) .m1 refl defmf) (cancel≅ [] .(a ∷ []) .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁ = [ a ] , (refl , refl)
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ [] .(a ∷ []) .(a ∷ a ∷ a ∷ []) .m1 refl defmf) (cancel≅ (.a ∷ []) .[] .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁ = [ a ] , (refl , refl)
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ (.a ∷ []) .[] .(a ∷ a ∷ a ∷ []) .m1 refl defmf) (cancel≅ [] .(a ∷ []) .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁ = [ a ] , (refl , refl)
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ (.a ∷ []) .[] .(a ∷ a ∷ a ∷ []) .m1 refl defmf) (cancel≅ (.a ∷ []) .[] .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁ = [ a ] , (refl , refl)
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ (x ∷ []) r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) (cancel≅ (x₁ ∷ x₂ ∷ l₁) r₁ .(a ∷ a ∷ a ∷ []) .m2 defm₁ defmf₁) = ⊥-elim (3=2+2 defm₁)
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ [] r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) (cancel≅ (x ∷ x₁ ∷ l₁) r₁ .(a ∷ a ∷ a ∷ []) .m2 defm₁ defmf₁) = ⊥-elim (3=2+2 defm₁)
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ (x ∷ x₁ ∷ l) r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) (cancel≅ l₁ r₁ .(a ∷ a ∷ a ∷ []) .m2 defm₁ defmf₁) = ⊥-elim (3=2+2 defm)

--- impossible
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ l r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) (swap≅ x l₁ r₁ .(a ∷ a ∷ a ∷ []) .m2 defm₁ defmf₁) =
  let ka , na = 2const-2const defm₁
  in  abs-suc (subst (λ e -> suc e < a ) na (subst (λ e -> _) ka  x))
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ l r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) (braid≅ l₁ r₁ .(a ∷ a ∷ a ∷ []) .m2 defm₁ defmf₁) =
  let ka , na = 2const-2const defm₁
  in  ⊥-elim (1+a=a (≡-trans ka (≡-sym na)))
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (swap≅ x l r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) p2 =
  let ka , na = 2const-2const defm
  in  abs-suc (subst (λ e -> suc e < a ) na (subst (λ e -> _) ka  x))
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (braid≅ l r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) p2 =
  let ka , na = 2const-2const defm
  in  ⊥-elim (1+a=a (≡-trans ka (≡-sym na)))

----------
--- CS ---
----------

cs : (a b : ℕ) -> (pab : suc b < a) -> (m m1 m2 : List ℕ) -> (defm : m ≡ a ∷ a ∷ b ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≅* mm) × (m2 ≅* mm))
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ [] .(b ∷ []) .(a ∷ a ∷ b ∷ []) .m1 refl defmf) (swap≅ x (.a ∷ []) .[] .(a ∷ a ∷ b ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁
  = [ b ] , refl , (trans (swap x [] (a ∷ [])) (cancel [ b ] []))

cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (swap≅ x (.a ∷ []) .[] .(a ∷ a ∷ b ∷ []) .m1 refl defmf) (cancel≅ [] .(b ∷ []) .(a ∷ a ∷ b ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁
  = [ b ] , (trans (swap x [] (a ∷ [])) (cancel [ b ] [])) , refl

--- abs
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ [] r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (swap≅ x (x₁ ∷ x₂ ∷ l₁) r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) = ⊥-elim (3=2+2 defm₁)
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ [] .(b ∷ []) .(a ∷ a ∷ b ∷ []) .m1 refl defmf) (swap≅ x [] .(b ∷ []) .(a ∷ a ∷ b ∷ []) .m2 refl defmf₁) = abs-suc x
cs a .a pab .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ (.a ∷ []) .[] .(a ∷ a ∷ a ∷ []) .m1 refl defmf) (swap≅ x l₁ r₁ .(a ∷ a ∷ a ∷ []) .m2 defm₁ defmf₁) = abs-suc pab
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ (x₁ ∷ x₂ ∷ l) r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (swap≅ x l₁ r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) = ⊥-elim (3=2+2 defm)
--trivial
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ [] .(b ∷ []) .(a ∷ a ∷ b ∷ []) .m1 refl defmf) (cancel≅ [] .(b ∷ []) .(a ∷ a ∷ b ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁ = [ b ] , (refl , refl)
cs a .a pab .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ [] r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) (cancel≅ (.a ∷ []) .[] .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁) = abs-suc pab
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ [] r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (cancel≅ (x ∷ x₁ ∷ l₁) r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) = ⊥-elim (3=2+2 defm₁)
cs a .a pab .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ (.a ∷ []) .[] .(a ∷ a ∷ a ∷ []) .m1 refl defmf) (cancel≅ [] r₁ .(a ∷ a ∷ a ∷ []) .m2 defm₁ defmf₁) = abs-suc pab
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ (x ∷ x₁ ∷ l) r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (cancel≅ [] r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) = ⊥-elim (3=2+2 defm)
cs a .a pab .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ (.a ∷ []) .[] .(a ∷ a ∷ a ∷ []) .m1 refl defmf) (cancel≅ (x₁ ∷ l₁) r₁ .(a ∷ a ∷ a ∷ []) .m2 defm₁ defmf₁) = abs-suc pab
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ (x ∷ x₂ ∷ l) r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (cancel≅ (x₁ ∷ l₁) r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) =  ⊥-elim (3=2+2 defm)
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (swap≅ x [] .(b ∷ []) .(a ∷ a ∷ b ∷ []) .m1 refl defmf) (swap≅ x₁ l₁ r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) = abs-suc x
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (swap≅ x (x₂ ∷ l) r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (swap≅ x₁ [] .(b ∷ []) .(a ∷ a ∷ b ∷ []) .m2 refl defmf₁) = abs-suc x₁
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (swap≅ x (.a ∷ []) .[] .(a ∷ a ∷ b ∷ []) .m1 refl defmf) (swap≅ x₁ (.a ∷ []) .[] .(a ∷ a ∷ b ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁
  = a ∷ b ∷ a ∷ [] , (refl , refl)
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (swap≅ x (x₂ ∷ []) r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (swap≅ x₁ (x₃ ∷ x₄ ∷ l₁) r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) = ⊥-elim (3=2+2 defm₁)
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (swap≅ x (x₂ ∷ x₄ ∷ l) r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (swap≅ x₁ (x₃ ∷ l₁) r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) = ⊥-elim (3=2+2 defm)
-- impossible
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ l r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (braid≅ (x ∷ l₁) r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) = ⊥-elim (3=1+3 defm₁)
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (swap≅ x [] .(b ∷ []) .(a ∷ a ∷ b ∷ []) .m1 refl defmf) (cancel≅ [] .(b ∷ []) .(a ∷ a ∷ b ∷ []) .m2 refl defmf₁) = abs-suc x
cs a .a pab .(a ∷ a ∷ a ∷ []) m1 m2 refl (swap≅ x [] r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) (cancel≅ (.a ∷ []) .[] .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁) = abs-suc pab
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (swap≅ x [] r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (cancel≅ (x₁ ∷ x₂ ∷ l₁) r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) = ⊥-elim (3=2+2 defm₁)

cs a .a pab .(a ∷ a ∷ a ∷ []) m1 m2 refl (swap≅ x (x₁ ∷ []) r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) (cancel≅ (.a ∷ []) .[] .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁) = abs-suc pab
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (swap≅ x (x₁ ∷ []) r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (cancel≅ (x₂ ∷ x₃ ∷ l₁) r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) = ⊥-elim (3=2+2 defm₁)
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (swap≅ x (x₁ ∷ x₂ ∷ l) r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (cancel≅ l₁ r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) = ⊥-elim (3=2+2 defm)
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (swap≅ x l r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (braid≅ (x₁ ∷ l₁) r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) = ⊥-elim (3=1+3 defm₁)
cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (braid≅ (x ∷ l) r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) p2 = ⊥-elim (3=1+3 defm)

----------
--- CB ---
----------
4=3+2 : {!!}
4=3+2 t = ⊥-elim (3=2+2 (cut-head t))
4=2+3 : {!!}
4=2+3 t = ⊥-elim (3=1+3 (cut-head t))

bc : (a : ℕ) -> (m m1 m2 : List ℕ) -> (defm : m ≡ suc a ∷ a ∷ suc a ∷ suc a ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≅* mm) × (m2 ≅* mm))
bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (cancel≅ (.(suc a) ∷ .a ∷ []) .[] .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 refl defmf) (braid≅ [] .(suc a ∷ []) .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁ = (suc a ∷ [ a ]) , (refl , (trans (braid [ a ] [] m1 m1) (cancel [] (suc a ∷ a ∷ []))))
bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (braid≅ [] .(suc a ∷ []) .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 refl defmf) (cancel≅ (.(suc a) ∷ .a ∷ []) .[] .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁ = (suc a ∷ [ a ]) , (((trans (braid [ a ] [] m1 m1 ) (cancel [] (suc a ∷ a ∷ [])))) , refl)

-- abs
bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (cancel≅ (x ∷ x₁ ∷ x₂ ∷ l) r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 defm defmf) (braid≅ l₁ r₁ .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 defm₁ defmf₁) = 4=3+2 defm
bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (braid≅ (x ∷ x₁ ∷ l) r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 defm defmf) (cancel≅ l₁ r₁ .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 defm₁ defmf₁) = 4=2+3 defm
bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (cancel≅ (x ∷ x₁ ∷ []) r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 defm defmf) (braid≅ (x₂ ∷ x₃ ∷ l₁) r₁ .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 defm₁ defmf₁) = 4=2+3 defm₁
bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (braid≅ [] r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 defm defmf) (cancel≅ (x ∷ x₁ ∷ x₂ ∷ l₁) r₁ .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 defm₁ defmf₁) = 4=3+2 defm₁

--- trivial
bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (braid≅ l r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 defm defmf) (braid≅ l₁ r₁ .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 defm₁ defmf₁) = {!!}
bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (cancel≅ l r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 defm defmf) (cancel≅ l₁ r₁ .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 defm₁ defmf₁) = {!!}

--- impossible
bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (swap≅ x l r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 defm defmf) p2 = {!!}
bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (braid≅ l r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 defm defmf) (swap≅ x l₁ r₁ .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 defm₁ defmf₁) = {!!}
bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (cancel≅ l r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 defm defmf) (swap≅ x l₁ r₁ .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 defm₁ defmf₁) = {!!}

postulate
  sc : (a b : ℕ) -> (suc b < a) -> (m m1 m2 : List ℕ) -> (defm : m ≡ a ∷ b ∷ b ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≅* mm) × (m2 ≅* mm))
  cb : (a : ℕ) -> (m m1 m2 : List ℕ) -> (defm : m ≡ suc a ∷ suc a ∷ a ∷ suc a ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≅* mm) × (m2 ≅* mm))
  sb : (a b : ℕ) -> (suc (suc b) < a) -> (m m1 m2 : List ℕ) -> (defm : m ≡ a ∷ (suc b) ∷ b ∷ suc b ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≅* mm) × (m2 ≅* mm))
  bs : (a b : ℕ) -> (suc b < a) -> (m m1 m2 : List ℕ) -> (defm : m ≡ (suc a) ∷ a ∷ (suc a) ∷ b ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≅* mm) × (m2 ≅* mm))
  bb : (a : ℕ) -> (m m1 m2 : List ℕ) -> (defm : m ≡ suc a ∷ a ∷ suc a ∷ a ∷ suc a ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≅* mm) × (m2 ≅* mm))
