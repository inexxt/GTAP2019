{-# OPTIONS --without-K #-}

module Coxeter where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)


variable
    n : ℕ
    l : List ℕ

∷-down2 : {m1 m2 : List ℕ} -> {x1 x2 : ℕ} -> x1 ∷ m1 ≡ x2 ∷ m2 -> (x1 ≡ x2) × (m1 ≡ m2)
∷-down2 {m1} {.m1} {x1} {.x1} refl = refl , refl

data _≅_ : List ℕ -> List ℕ -> Set where
    cancel≅ : (n ∷ n ∷ []) ≅ []
    swap≅ : {k : ℕ} -> (suc k < n) -> (n ∷ k ∷ []) ≅ (k ∷ n ∷ [])
    braid≅ : ((suc n) ∷ n ∷ (suc n) ∷ []) ≅ (n ∷ (suc n) ∷ n ∷ [])
    respects=r : (l : List ℕ) -> {r r' lr lr' : List ℕ} -> (r ≅ r') -> (lr ≡ l ++ r) -> (lr' ≡ l ++ r') -> lr ≅ lr'
    respects=l : {l l' : List ℕ} -> (r : List ℕ) ->{lr l'r : List ℕ} -> (l ≅ l') -> (lr ≡ l ++ r) -> (l'r ≡ l' ++ r) -> lr ≅ l'r
    comm≅ : {m1 m2 : List ℕ} -> (m1 ≅ m2) -> m2 ≅ m1

data _≃_ : List ℕ -> List ℕ -> Set where
    refl : {m : List ℕ} -> m ≃ m
    trans≅ : {m1 m2 m3 : List ℕ} -> (m1 ≅ m2) -> (m2 ≃ m3) -> m1 ≃ m3

ext : {l l' : List ℕ} -> l ≅ l' -> l ≃ l'
ext p = trans≅ p refl

cancel : (n ∷ n ∷ []) ≃ []
cancel = ext cancel≅

swap : {k : ℕ} -> (suc k < n) -> (n ∷ k ∷ []) ≃ (k ∷ n ∷ [])
swap p = ext (swap≅ p)

braid : ((suc n) ∷ n ∷ (suc n) ∷ []) ≃ (n ∷ (suc n) ∷ n ∷ [])
braid = ext braid≅

trans : {m1 m2 m3 : List ℕ} -> (m1 ≃ m2) -> (m2 ≃ m3) -> m1 ≃ m3
trans refl p  = p
trans (trans≅ x q) p = trans≅ x (trans q p)

comm : {m1 m2 : List ℕ} -> (m1 ≃ m2) -> (m2 ≃ m1)
comm refl = refl
comm (trans≅ p x) = trans (comm x) (ext (comm≅ p))

respects-r : (l : List ℕ) -> {r r' lr lr' : List ℕ} -> (r ≃ r') -> (lr ≡ l ++ r) -> (lr' ≡ l ++ r') -> lr ≃ lr'
respects-r l refl e1 e2 rewrite e1 rewrite e2 = refl
respects-r l (trans≅ {m2 = lhs} {m3 = rhs} rr' x) e1 e2 rewrite e1 rewrite e2 =
  let rec-l = respects=r l rr' e1 refl
      rec-r = respects-r l {lr = l ++ lhs} {lr' = l ++ rhs} x refl refl
  in  trans≅ (subst (λ y -> y ≅ (l ++ lhs)) e1 rec-l) rec-r

respects-l : {l l' : List ℕ} -> (r : List ℕ) ->{lr l'r : List ℕ} -> (l ≃ l') -> (lr ≡ l ++ r) -> (l'r ≡ l' ++ r) -> lr ≃ l'r
respects-l l refl e1 e2 rewrite e1 rewrite e2 = refl
respects-l r (trans≅ {m2 = lhs} {m3 = rhs} rr' x) e1 e2 rewrite e1 rewrite e2 =
  let rec-l = respects=l r rr' refl refl
      rec-r = respects-l r {lr = lhs ++ r} {l'r = rhs ++ r} x refl refl
  in  trans≅ rec-l rec-r

module ≃-Reasoning where
    infix  1 ≃begin_
    infixr 2 _≃⟨⟩_ _≃⟨_⟩_
    infix  3 _≃∎

    ≃begin_ : ∀ {x y : List ℕ}
             → x ≃ y
               -----
             → x ≃ y
    ≃begin x≃y  =  x≃y

    _≃⟨⟩_ : ∀ (x : List ℕ) {y : List ℕ}
            → x ≃ y
              -----
            → x ≃ y
    x ≃⟨⟩ x≃y  =  x≃y

    _≃⟨_⟩_ : ∀ (x : List ℕ) {y z : List ℕ}
             → x ≃ y
             → y ≃ z
               -----
             → x ≃ z
    x ≃⟨ x≃y ⟩ y≃z  = trans x≃y y≃z

    _≃∎ : ∀ (x : List ℕ)
           -----
          → x ≃ x
    x ≃∎  =  refl

open ≃-Reasoning


++-respects-r : {l r r' : List ℕ} -> (r ≃ r') -> (l ++ r) ≃ (l ++ r')
++-respects-r {l} {r} {r'} rr = respects-r l {r = r} {r' = r'} {lr = l ++ r} {lr' = l ++ r'} rr refl refl

++-respects-l : {l l' r : List ℕ} -> (l ≃ l') -> (l ++ r) ≃ (l' ++ r)
++-respects-l {l} {l'} {r} ll = respects-l {l = l} {l' = l'} r {lr = l ++ r} {l'r = l' ++ r} ll refl refl

++-respects : {l l' m m' : List ℕ} -> (l ≃ l') -> (m ≃ m') -> (l ++ m) ≃ (l' ++ m')
++-respects {l} {l'} {m} {m'} ll mm =
  ≃begin
    l ++ m
  ≃⟨ ++-respects-l ll ⟩
    l' ++ m
  ≃⟨ ++-respects-r mm ⟩
     l' ++ m'
  ≃∎

postulate
    ++-unit : l ++ [] ≡ l

refl≡ : {l l' : List ℕ} -> (l ≡ l') -> l ≃ l'
refl≡ refl = refl

++-unit2 : (l1 l2 : List ℕ) -> (l1 ++ (l2 ++ [])) ≡ (l1 ++ l2)
++-unit2 l1 l2 = let xx = ++-assoc l1 l2 []
                     yy = ++-unit {l1 ++ l2}
                 in ≡-trans (≡-sym xx) yy
