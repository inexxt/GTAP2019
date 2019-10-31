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
open import DiamondCompact hiding (n; l)
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)
open _≅_

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)


variable
  n : ℕ
  l : List ℕ

data _≃_ : List ℕ -> List ℕ -> Set where
  comm≅ : {m1 m2 mf : List ℕ} -> (p1 : m1 ≅* mf) -> (p2 : m2 ≅* mf) -> m1 ≃ m2

refl≃ : (m : List ℕ) -> (m ≃ m)
refl≃ m = comm≅ refl refl

comm≃ : (m1 m2 : List ℕ) -> (m1 ≃ m2) -> (m2 ≃ m1)
comm≃ m1 m2 (comm≅ p1 p2) = comm≅ p2 p1

trans≃ : (m1 m2 m3 : List ℕ) -> (r1 : m1 ≃ m2) -> (r2 : m2 ≃ m3) -> (m1 ≃ m3)
trans≃ m1 m2 m3 (comm≅ p1 p2) (comm≅ p3 p4) =
  let lemma-m , lemma1 , lemma2 = diamond-full p2 p3
  in  comm≅ (trans p1 lemma1) (trans p4 lemma2)

-- True coxeter presentation
data _~_ : List ℕ -> List ℕ -> Set where
  cancel~ : (n ∷ n ∷ []) ~ []
  swap~ : {k : ℕ} -> (suc k < n) -> (n ∷ k ∷ []) ~ (k ∷ n ∷ [])
  braid~ : ((suc n) ∷ n ∷ (suc n) ∷ []) ~ (n ∷ (suc n) ∷ n ∷ [])
  respects-r~ : (l : List ℕ) -> {r r' lr lr' : List ℕ} -> (r ~ r') -> (lr ≡ l ++ r) -> (lr' ≡ l ++ r') -> lr ~ lr'
  respects-l~ : {l l' : List ℕ} -> (r : List ℕ) ->{lr l'r : List ℕ} -> (l ~ l') -> (lr ≡ l ++ r) -> (l'r ≡ l' ++ r) -> lr ~ l'r
  refl~ : {m : List ℕ} -> m ~ m
  comm~ : {m1 m2 : List ℕ} -> (m1 ~ m2) -> m2 ~ m1
  trans~ : {m1 m2 m3 : List ℕ} -> (m1 ~ m2) -> (m2 ~ m3) -> m1 ~ m3

compact≅->coxeter : (m1 m2 : List ℕ) -> (m1 ≅ m2) -> (m1 ~ m2)
compact≅->coxeter m1 m2 (cancel≅ l r .m1 .m2 defm defmf) = respects-r~ l (respects-l~ r cancel~ refl refl) defm defmf
compact≅->coxeter m1 m2 (swap≅ x l r .m1 .m2 defm defmf) = respects-r~ l (respects-l~ r (swap~ x) refl refl) defm defmf
compact≅->coxeter m1 m2 (long≅ {n} zero [] r .m1 .m2 defm defmf) =
  (respects-l~ r braid~ defm defmf)
compact≅->coxeter m1 m2 (long≅ (suc k) [] r .m1 .m2 defm defmf) = {!   !}
compact≅->coxeter (x₁ ∷ m1) (x₂ ∷ m2) (long≅ k (x ∷ l) r .(x₁ ∷ m1) .(x₂ ∷ m2) defm defmf) =
  let rec = compact≅->coxeter m1 m2 (long≅ k l r m1 m2 (cut-head defm) (cut-head defmf))
  in  respects-r~ [ x ] rec (head+tail (cut-tail defm) refl) (head+tail (cut-tail defmf) refl)


compact≅*->coxeter : (m1 m2 : List ℕ) -> (m1 ≅* m2) -> (m1 ~ m2)
compact≅*->coxeter m1 .m1 refl = refl~
compact≅*->coxeter m1 m2 (trans≅ x p) = trans~ ((compact≅->coxeter _ _ x)) ((compact≅*->coxeter _ _ p))

compact->coxeter : (m1 m2 : List ℕ) -> (m1 ≃ m2) -> (m1 ~ m2)
compact->coxeter m1 m2 (comm≅ p1 p2) = trans~ (compact≅*->coxeter _ _ p1) (comm~ ((compact≅*->coxeter _ _ p2)))
