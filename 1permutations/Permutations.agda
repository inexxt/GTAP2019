{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Permutations where
    --- First representation of swap: an element of the fin N

    open import FinTypes
    open import StandardFinTypes
    open import Agda.Builtin.Nat
    open import DecEquality

    data Swap : {T : Type} -> (StandardFinType T) -> Set where
        swap : {T : Type} -> {t : StandardFinType T} -> (Member T) -> Swap t

    T𝟛 = FinS (FinS (FinS Fin0))

    swap01 : Swap T𝟛
    swap01 = swap (left (left (right One)))

    swap12 : Swap T𝟛
    swap12 = swap (left (right One))

    swap23 : Swap T𝟛
    swap23 = swap (right One)

    applySwap : {T : Type} -> {t : StandardFinType T} -> (Swap t) -> (Member T) -> (Member T)
    applySwap (swap (right One)) = id
    applySwap (swap (left x)) m = {!   !}
    -- applySwap (swap (left x)) m with ((areEqual x m) times (areEqual (left x) m))
    -- ...                            | (left One) times (left One) = ?
    -- ...                            | (right _) times _ = ?
    -- ...                            | _ times (right _) = ?
