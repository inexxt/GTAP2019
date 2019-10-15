module Coxeter where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)


variable
    n : ℕ
    l : List ℕ

data _≃_ : List ℕ -> List ℕ -> Set where
    cancel : (n ∷ n ∷ []) ≃ []
    swap : {k : ℕ} -> (suc k < n) -> (n ∷ k ∷ []) ≃ (k ∷ n ∷ [])
    braid : (n ∷ (suc n) ∷ n ∷ []) ≃ ((suc n) ∷ n ∷ (suc n) ∷ [])
    respects-r : (l : List ℕ) -> {r r' lr lr' : List ℕ} -> (r ≃ r') -> (l ++ r ≡ lr) -> (l ++ r' ≡ lr') -> lr ≃ lr'
    respects-l : {l l' : List ℕ} -> (r : List ℕ) ->{lr l'r : List ℕ} -> (l ≃ l') -> (l ++ r ≡ lr) -> (l' ++ r ≡ l'r) -> lr ≃ l'r
    refl : {l : List ℕ} -> l ≃ l
    comm : {l l' : List ℕ} -> (l ≃ l') -> l' ≃ l
    trans : {l l' l'' : List ℕ} -> (l ≃ l') -> (l' ≃ l'') -> l ≃ l''

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
    x ≃⟨ x≃y ⟩ y≃z  =  trans x≃y y≃z

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
    ++-≃ : {l l' w w' : List ℕ} -> (l ≃ l') -> (w ≃ w') -> (l ++ w) ≃ (l' ++ w')


refl≡ : {l l' : List ℕ} -> (l ≡ l') -> l ≃ l'
refl≡ refl = refl


++-unit2 : (l1 l2 : List ℕ) -> (l1 ++ (l2 ++ [])) ≡ (l1 ++ l2)
++-unit2 l1 l2 = let xx = ++-assoc l1 l2 []
                     yy = ++-unit {l1 ++ l2}
                 in ≡-trans (≡-sym xx) yy
