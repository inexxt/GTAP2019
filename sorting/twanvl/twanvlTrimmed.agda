-- source : https://gist.github.com/twanvl/5635740

{-# OPTIONS --without-K #-}

module twanvlTrimmed where

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
-- open import Induction.WellFounded using (Acc;acc)

-- open import Data.Nat.Solver using (module +-*-Solver)
-- open +-*-Solver

-----------------------------------------------------------------------------------------
-- Permutations
-----------------------------------------------------------------------------------------

1+m+n=m+1+n : (m n : ℕ) → suc (m + n) ≡ m + suc n
1+m+n=m+1+n zero n = PE.refl
1+m+n=m+1+n (suc m) n = PE.cong suc (1+m+n=m+1+n m n)

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

-----------------------------------------------------------------------------------------
-- Sorted lists
-----------------------------------------------------------------------------------------

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
  open Permutations A
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



-----------------------------------------------------------------------------------------
-- Sorting algorithms
-----------------------------------------------------------------------------------------

module SortingAlgorithm
    {A : Set}
    {_≤_ : Rel A ℓ₀}
    (isPartialOrder : IsPartialOrder _≡_ _≤_)
    (_≤?_ : (x y : A) → (x ≤ y ⊎ y ≤ x)) where

  open Permutations A
  open SortedList isPartialOrder

  ---------------------------------------------------------------------------
  -- Insertion sort
  ---------------------------------------------------------------------------

  -- Insertion sort, O(n^2)
  insert : ∀ {xs} → (x : A) → Sorted xs → Sorted (x ∷ xs)
  insert x [] = cons x here [] []
  insert x (cons u p0 u≤*us us) with (x ≤? u)
  ... | (inj₁ p) = cons x here (insert-less p0 p (trans* p u≤*us)) $ cons u p0 u≤*us us
  ... | (inj₂ p) = cons u (there p0) (p ∷ u≤*us) (insert x us)

  insertion-sort : (xs : List A) → Sorted xs
  insertion-sort [] = []
  insertion-sort (x ∷ xs) = insert x (insertion-sort xs)


module SortingNat where
  open import Data.Empty

  absurd : {x y : ℕ} -> (¬ x ≤ y) -> (¬ y ≤ x) -> ⊥
  absurd {zero} {zero} p q = q z≤n
  absurd {zero} {suc y} p q = p z≤n
  absurd {suc x} {zero} p q = q z≤n
  absurd {suc x} {suc y} p q = absurd (λ z → p (s≤s z)) (λ z → q (s≤s z))

  _≤??_ : (x y : ℕ) → (x ≤ y ⊎ y ≤ x)
  x ≤?? y with (x ≤? y)
  (x ≤?? y) | yes p = inj₁ p
  (x ≤?? y) | no ¬p with (y ≤? x)
  (x ≤?? y) | no ¬p | yes p = inj₂ p
  (x ≤?? y) | no ¬p | no ¬p₁ =  ⊥-elim $ absurd ¬p ¬p₁

  open import Data.Nat.Properties using () renaming (≤-isPartialOrder to po)
  open SortingAlgorithm {ℕ} {Data.Nat._≤_} po _≤??_

  showSort : List ℕ -> List ℕ
  showSort xs = let ss = insertion-sort xs
                    ss' = SortedList.Sorted-to-Sorted' po ss in
                    SortedList.Sorted'.list ss'

  test : (showSort $ 5 ∷ 3 ∷ 2 ∷ 4 ∷ 1 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
  test = _≡_.refl

  ---------------------------------------------------------------------------
  -- Insertion sort with a list of swaps
  ---------------------------------------------------------------------------

  -- -- Insertion sort, O(n^2)
  -- insert : ∀ {xs} → (x : A) → Sorted xs → Sorted (x ∷ xs)
  -- insert x [] = cons x here [] []
  -- insert x (cons u p0 u≤*us us) with (x ≤? u)
  -- ... | (inj₁ p) = cons x here (insert-less p0 p (trans* p u≤*us)) $ cons u p0 u≤*us us
  -- ... | (inj₂ p) = cons u (there p0) (p ∷ u≤*us) (insert x us)
  --
  -- insertion-sort : (xs : List A) → Sorted xs
  -- insertion-sort [] = []
  -- insertion-sort (x ∷ xs) = insert x (insertion-sort xs)


  ---------------------------------------------------------------------------
  -- Selection sort
  ---------------------------------------------------------------------------

  -- import Data.Vec as Vec
  -- open Vec using (Vec;toList;fromList;_∷_;[])
  --
  -- -- select least element from a non-empty list x∷xs
  -- select1 : ∀ {n} (xs : Vec A (suc n))
  --         → (∃₂ \y ys → (y ◂ toList ys ≡ toList xs) × (y ≤* toList ys))
  -- select1 (x ∷ []) = x , [] , here , []
  -- select1 {suc n} (x ∷ xs)
  --   = bound-≡ (lem n) $
  --     select1 xs >>= \{ (z , zs , perm , least)
  --     → x ≤? z >>= \
  --       { (inj₁ p) → x , xs , here , insert-less perm p (trans* p least)
  --       ; (inj₂ p) → z , (x ∷ zs) , there perm , (p ∷ least)
  --       }}
  --   where
  --     lem : ∀ n → n + 1 ≡ 1 + n
  --     lem = solve 1 (\n → n :+ con 1 := con 1 :+ n) PE.refl
  --
  -- selection-sort1 : ∀ {n} (xs : Vec A n) → (Sorted (toList xs))
  -- selection-sort1 [] = return []
  -- selection-sort1 {suc n} xs
  --   = bound-+ (lem n) $
  --     select1 xs >>= \
  --     { (y , ys , perm , least)
  --     → cons y perm least <$> selection-sort1 ys }
  --   where
  --     lem : ∀ n → n + (n ^ 2) + (n + 1) ≡ (1 + n) ^ 2
  --     lem = solve 1 (\n → n :+ (n :^ 2) :+ (n :+ con 1)
  --                      := (con 1 :+ n) :^ 2) PE.refl
  --
  -- toList∘fromList : ∀ (xs : List A) → toList (fromList xs) ≡ xs
  -- toList∘fromList [] = PE.refl
  -- toList∘fromList (x ∷ xs) = PE.cong (_∷_ x) (toList∘fromList xs)
  --
  -- selection-sort2 : ∀ (xs : List A) → (Sorted xs)
  -- selection-sort2 xs = PE.subst Sorted (toList∘fromList xs)
  --                    <$> selection-sort1 (fromList xs)
