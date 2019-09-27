-- source : https://gist.github.com/twanvl/5635740

{-# OPTIONS --without-K #-}

open import Data.List
open import Data.List.Properties
open import Data.Nat hiding (_≟_;_≤?_)
open import Data.Product
open import Data.Sum
import Relation.Binary.PropositionalEquality as PE
open PE using (_≡_)
open import Function

module Permutations {a} (A : Set a) where

  -- x ◂ xs ≡ ys means that ys is equal to xs with x inserted somewhere
  data _◂_≡_ (x : A) : List A → List A → Set a where
    here  : ∀ {xs}           → x ◂ xs ≡ (x ∷ xs)
    there : ∀ {y} {xs} {xys} → (p : x ◂ xs ≡ xys) → x ◂ (y ∷ xs) ≡ (y ∷ xys)

  -- Proof that a list is a permutation of another one
  data IsPermutation : List A → List A → Set a where
    []  : IsPermutation [] []
    _∷_ : ∀ {x xs ys xys}
        → (p : x ◂ ys ≡ xys)
        → (ps : IsPermutation xs ys)
        → IsPermutation (x ∷ xs) xys

  -- Identity permutation
  id-permutation : (xs : List A) → IsPermutation xs xs
  id-permutation [] = []
  id-permutation (x ∷ xs) = here ∷ id-permutation xs

  -- cons on the other side
  insert-permutation : ∀ {x xs ys xys}
                     → x ◂ ys ≡ xys → IsPermutation ys xs → IsPermutation xys (x ∷ xs)
  insert-permutation here p = here ∷ p
  insert-permutation (there y) (p ∷ ps) = there p ∷ insert-permutation y ps

  -- inverse permutations
  inverse-permutation : ∀ {xs ys} -> IsPermutation xs ys → IsPermutation ys xs
  inverse-permutation [] = []
  inverse-permutation (p ∷ ps) = insert-permutation p (inverse-permutation ps)

  swap-inserts : ∀ {x y xs xxs yxxs}
               → (x ◂ xs ≡ xxs) → (y ◂ xxs ≡ yxxs) → ∃ \yxs → (y ◂ xs ≡ yxs) × (x ◂ yxs ≡ yxxs)
  swap-inserts p here = _ , here , there p
  swap-inserts here (there q) = _ , q , here
  swap-inserts (there p) (there q) with swap-inserts p q
  ... | _ , p' , q' = _ , there p' , there q'

  extract-permutation : ∀ {x ys zs zs'}
                      → x ◂ ys ≡ zs → IsPermutation zs zs'
                      → ∃ \ys' → (x ◂ ys' ≡ zs') × IsPermutation ys ys'
  extract-permutation here (q ∷ qs) = _ , q , qs
  extract-permutation (there p) (q ∷ qs) with extract-permutation p qs
  ... | ys' , r , rs with swap-inserts r q
  ...   | ys'' , s , t = ys'' , t , s ∷ rs

  -- composing permutations
  compose-permutation : ∀ {xs ys zs : List A}
                      → IsPermutation xs ys → IsPermutation ys zs → IsPermutation xs zs
  compose-permutation [] [] = []
  compose-permutation (p ∷ ps) qqs with extract-permutation p qqs
  ... | _ , q , qs = q ∷ compose-permutation ps qs

  insert-++₁ : ∀ {x xs ys xxs} → x ◂ xs ≡ xxs → x ◂ (xs ++ ys) ≡ (xxs ++ ys)
  insert-++₁ here = here
  insert-++₁ (there p) = there (insert-++₁ p)

  insert-++₂ : ∀ {y xs ys yys} → y ◂ ys ≡ yys → y ◂ (xs ++ ys) ≡ (xs ++ yys)
  insert-++₂ {xs = []} p = p
  insert-++₂ {xs = _ ∷ xs} p = there (insert-++₂ {xs = xs} p)

  -- Length of permutations
  length-insert : ∀ {x xs xxs} → x ◂ xs ≡ xxs → length xxs ≡ suc (length xs)
  length-insert here = PE.refl
  length-insert (there p) = PE.cong suc (length-insert p)

  length-permutation : ∀ {xs ys} → IsPermutation xs ys → length xs ≡ length ys
  length-permutation [] = PE.refl
  length-permutation (p ∷ ps) = PE.cong suc (length-permutation ps) ⟨ PE.trans ⟩ PE.sym (length-insert p)

  -- same-perm' : ∀ {x xs xxs ys} → x ◂ xs ≡ xxs → x ◂ ys ≡ xxs → IsPermutation xs ys
  -- same-perm' here here = id-permutation _
  -- same-perm' here (there q) = insert-permutation q (id-permutation _)
  -- same-perm' (there p) here = p ∷ id-permutation _
  -- same-perm' (there p) (there q) = here ∷ same-perm' p q

  -- same-perm : ∀ {x xs xxs y ys yys}
  --           → x ≡ y → IsPermutation xxs yys → x ◂ xs ≡ xxs → y ◂ ys ≡ yys → IsPermutation xs ys
  -- same-perm PE.refl ps q r with extract-permutation q ps
  -- ... | l' , q' , ps' = compose-permutation ps' (same-perm' q' r)
