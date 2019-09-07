{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module DecEquality where

    open import FinTypes
    open import StandardFinTypes
    open import Maybe

    areEqual : {T : Type} -> (a b : Member T) -> Maybe (a ≣ b)
    areEqual * * = right (refl *)
    areEqual (a , b) (c , d) with (and (areEqual a c) (areEqual b d))
    areEqual (a , b) (c , d)    | (left *) = left *
    areEqual (a , b) (c , d)    | (right (x times y)) = right (reflₓ x y)

    areEqual (left x) (left y) with (areEqual x y)
    areEqual (left x) (left y)    | (left *) = left *
    areEqual (left x) (left y)    | (right p) = right (reflₗ p)

    areEqual (right x) (right y) with (areEqual x y)
    areEqual (right x) (right y)    | (left *) = left *
    areEqual (right x) (right y)    | (right p) = right (reflᵣ p)

    areEqual _ _ = left *

    Bool : Set
    Bool = Maybe (Member 𝟙)

    true : Bool
    true = right *

    false : Bool
    false = left *
    --
    areEqualT : {T1 T2 : Type} -> {t1 : StandardFinType T1} -> {t2 : StandardFinType T2} -> (a : Member T1) -> (b : Member T2) -> Bool
    areEqualT (left x) (left y) = areEqualT x y
    areEqualT (right x) (right y) = areEqualT x y
    areEqualT _ _ = false
