-- source : https://gist.github.com/twanvl/5635740

{-# OPTIONS --without-K #-}

open import Level using () renaming (zero to ℓ₀;_⊔_ to lmax)
open import Data.List
open import Data.List.Properties
open import Data.Nat hiding (_≟_;_≤?_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.PropositionalEquality as PE
open PE using (_≡_)
open import Function
open import Induction.Nat

module SortedList
     {a r}
     {A   : Set a}
     {_≤_ : Rel A r}
     (isPartialOrder : IsPartialOrder _≡_ _≤_) where

  open IsPartialOrder isPartialOrder

  -- Less than all values in a list
  data _≤*_ (x : A) : List A → Set (lmax a r) where
    []  : x ≤* []
    _∷_ : ∀ {y ys} → (x ≤ y) → x ≤* ys → x ≤* (y ∷ ys)

  -- Proof that a list is sorted
  data IsSorted : List A → Set (lmax a r) where
    []  : IsSorted []
    _∷_ : ∀ {x xs} → x ≤* xs → IsSorted xs → IsSorted (x ∷ xs)

  trans* : ∀ {x u us} → x ≤ u → u ≤* us → x ≤* us
  trans* p []       = []
  trans* p (y ∷ ys) = trans p y ∷ trans* p ys


  -- relation to permutations
  open import Permutations A
  less-insert : ∀ {x y xs ys} → y ◂ ys ≡ xs → x ≤* xs → x ≤ y
  less-insert here      (l ∷ _)  = l
  less-insert (there p) (_ ∷ ls) = less-insert p ls

  less-remove : ∀ {x y xs ys} → y ◂ ys ≡ xs → x ≤* xs → x ≤* ys
  less-remove here      (l ∷ ls) = ls
  less-remove (there p) (l ∷ ls) = l ∷ less-remove p ls

  less-perm : ∀ {x xs ys} → IsPermutation xs ys → x ≤* ys → x ≤* xs
  less-perm [] [] = []
  less-perm (p ∷ ps) ss = less-insert p ss ∷ less-perm ps (less-remove p ss)

  -- alternative: insertion instead of selection
  insert-less : ∀ {x y xs ys} → y ◂ ys ≡ xs → x ≤ y → x ≤* ys → x ≤* xs
  insert-less here      l ks = l ∷ ks
  insert-less (there p) l (k ∷ ks) = k ∷ insert-less p l ks

  less-perm' : ∀ {x xs ys} → IsPermutation xs ys → x ≤* xs → x ≤* ys
  less-perm' [] [] = []
  less-perm' (p ∷ ps) (s ∷ ss) = insert-less p s (less-perm' ps ss)

  less-++ : ∀ {x xs ys} → x ≤* xs → x ≤* ys → x ≤* (xs ++ ys)
  less-++ [] ys = ys
  less-++ (x ∷ xs) ys = x ∷ less-++ xs ys

  -- Sorted permutations of xs
  data Sorted : List A → Set (lmax a r) where
    []   : Sorted []
    cons : ∀ x {xs xxs} → (p : x ◂ xs ≡ xxs) → (least : x ≤* xs) → (rest : Sorted xs) → Sorted xxs

  -- Alternative:
  record Sorted' (xs : List A) : Set (lmax a r) where
    constructor sorted'
    field
      list     : List A
      isSorted : IsSorted list
      isPerm   : IsPermutation list xs

  Sorted-to-Sorted' : ∀ {xs} → Sorted xs → Sorted' xs
  Sorted-to-Sorted' [] = sorted' [] [] []
  Sorted-to-Sorted' (cons x p l xs)
      = sorted' (x ∷ list) (IsSorted._∷_ (less-perm isPerm l) isSorted) (p ∷ isPerm)
    where open Sorted' (Sorted-to-Sorted' xs)

  Sorted'-to-Sorted : ∀ {xs} → Sorted' xs → Sorted xs
  Sorted'-to-Sorted (sorted' [] [] []) = []
  Sorted'-to-Sorted (sorted' (x ∷ xs) (l ∷ ls) (p ∷ ps))
    = cons x p (less-perm' ps l) (Sorted'-to-Sorted (sorted' xs ls ps))

  -- Sorted lists are unique
  Sorted-to-List : ∀ {xs} → Sorted xs → List A
  Sorted-to-List [] = []
  Sorted-to-List (cons x _ _ xs) = x ∷ Sorted-to-List xs

  -- Sorted-unique' : ∀ {xs xs'} → (IsPermutation xs xs') → (ys : Sorted xs) → (zs : Sorted xs')
  --                → Sorted-to-List ys ≡ Sorted-to-List zs
  -- Sorted-unique' [] [] [] = PE.refl
  -- Sorted-unique' [] (cons _ () _ _) _
  -- Sorted-unique' [] _ (cons _ () _ _)
  -- Sorted-unique' (() ∷ _) _ []
  -- Sorted-unique' ps (cons y yp yl ys) (cons z zp zl zs) = PE.cong₂ _∷_ y=z (Sorted-unique' ps' ys zs)
  --   where
  --   y=z : y ≡ z
  --   y=z = antisym (less-insert zp (less-perm' ps (insert-less yp refl yl)))
  --                 (less-insert yp (less-perm  ps (insert-less zp refl zl)))
  --   ps' = same-perm y=z ps yp zp

  -- Sorted-unique : ∀ {xs} → (ys zs : Sorted xs) → Sorted-to-List ys ≡ Sorted-to-List zs
  -- Sorted-unique = Sorted-unique' (id-permutation _)
