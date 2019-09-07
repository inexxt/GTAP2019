{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module DecEquality where

    open import FinTypes
    open import StandardFinTypes

    --- Non-dependent Product and Sum
    data Prod (T1 T2 : Set) : Set where
        _times_ : T1 -> T2 -> Prod T1 T2

    data Sum (T1 T2 : Set) : Set where
        left : T1 -> Sum T1 T2
        right : T2 -> Sum T1 T2

    --- Decidable equality

    Maybe : Set -> Set
    Maybe T = Sum (Member 𝟙) T
    --
    -- some : {T : Type} -> (Member T) -> Maybe (Member T)
    -- some = right
    -- none : {T : Type} -> Maybe (Member T)
    -- none = left One

    and : {T1 T2 : Set} -> Maybe T1 -> Maybe T2 -> Maybe (Prod T1 T2)
    and (right x) (right y) = right (x times y)
    and _ _ = left One
    --
    areEqual : {T : Type} -> (a b : Member T) -> Maybe (a ≣ b)
    areEqual One One = right (refl One)
    areEqual (a , b) (c , d) with (and (areEqual a c) (areEqual b d))
    areEqual (a , b) (c , d)    | (left One) = left One
    areEqual (a , b) (c , d)    | (right (x times y)) = right (reflₓ x y)

    areEqual (left x) (left y) with (areEqual x y)
    areEqual (left x) (left y)    | (left One) = left One
    areEqual (left x) (left y)    | (right p) = right (reflₗ p)

    areEqual (right x) (right y) with (areEqual x y)
    areEqual (right x) (right y)    | (left One) = left One
    areEqual (right x) (right y)    | (right p) = right (reflᵣ p)

    areEqual _ _ = left One
