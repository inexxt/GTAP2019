{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Permutations where
    --- First representation of swap: an element of the fin N

    open import FinTypes
    open import StandardFinTypes
    open import Agda.Builtin.Nat
    open import DecEquality
    open import Maybe
    open import StandardFinTypesOps

    data Swap : {T : Type} -> (StandardFinType T) -> Set where
        swap : {T : Type} -> {t : StandardFinType T} -> (Member T) -> Swap t

    T𝟛 = FinS (FinS (FinS Fin0))

    swap01 : Swap T𝟛
    swap01 = swap (left (left (right *)))

    swap12 : Swap T𝟛
    swap12 = swap (left (right *))

    swap23 : Swap T𝟛
    swap23 = swap (right *)

    --- Adjecent swaps

    --- why cant I pattern match with true/false?
    apply-adjSwap : {T : Type} -> {t : StandardFinType T} -> (Swap t) -> (Member T) -> (Member T)
    apply-adjSwap {t + 𝟙} (swap (right *)) m = m
    apply-adjSwap {t + 𝟙} (swap (left x)) m with (areEqualT (left x) m) times (areEqualT (include x) m)
    ...                                    | left * times left * = m
    ...                                    | left * times right * = include+ x
    ...                                    | right * times left * = include x
    ...                                    | right * times right * = m -- this is not possible, I should change somethings

    --- why cant I pattern match with true/false?
    apply-zeroSwap : {T : Type} -> {t : StandardFinType T} -> (Swap t) -> (Member T) -> (Member T)
    apply-zeroSwap {t + 𝟙} (swap x) (right *) = right *
    apply-zeroSwap {t + 𝟙} (swap x) (left m) with (areEqualT x (left m))
    ...                                         | left * = (left m)
    ...                                         | right * = x


    --- Three generators

    Generator : Set
    Generator = Member (𝟙 Type.+ 𝟙)
    s : Generator
    s = left *
    t : Generator
    t = right *

    applyGenerator : {T : Type} -> {t : StandardFinType T} -> Generator -> (Member T) -> (Member T)
    applyGenerator {_} {t} (left *) (right *) = max t
    applyGenerator {_} {FinS t} (left *) (left m) with areEqualT (left m) (max (FinS t))
    ...                                               | left * = left m
    ...                                               | right * = right *
    applyGenerator {_} {FinS t} (right *) (left m) = include m --- why can't I remove implicits here?
    applyGenerator {_} {t} (right *) (right *) = max t


    -- data Permutation : {T : Type} -> {StandardFinType T} -> (cnfp (T × T)) -> Set
