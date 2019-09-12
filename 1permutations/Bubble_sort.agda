{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Bubble_sort where
    --- First representation of swap: an element of the fin N

    open import FinTypes
    open import StandardFinTypes
    open import Agda.Builtin.Nat
    open import DecEquality
    open import Maybe
    open import StandardFinTypesOps
    open import Permutations
    open import Data.Product using (∃; Σ)
    open Σ

    ValuesTable : {T : Type} -> {StandardFinType T} -> (Member T -> Member T)

    TxT = λ T -> Member (getTypeFromStandardType (proj₁ (cnfp (T × T))))

    bubbleSortTerminating : {T : Type} -> {StandardFinType T} -> (f : (Member T) -> (Member T)) -> (TxT T) -> Permutation
    bubbleSortTerminating {T} {t} f n = {!   !}

    countInversions : {T : Type} -> {StandardFinType T} -> (f : (Member T) -> (Member T)) -> (Member T) -> TxT T
    countInversions {T} {t} f =

    bubble_sort : {T : Type} -> {StandardFinType T} -> (f : (Member T) -> (Member T)) -> Permutation
    bubble_sort {T} {t} f = bubbleSortTerminating f (countInversions f (max T))
