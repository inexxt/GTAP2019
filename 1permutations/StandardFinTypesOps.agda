{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module StandardFinTypesOps where

    open import FinTypes
    open import StandardFinTypes
    open import Agda.Builtin.Sigma
    open import Data.Product using (∃)
    open import Maybe
    open import DecEquality

    include : {T : Type} -> {t : StandardFinType T} -> (Member T) -> Member (T + 𝟙)
    include {t + 𝟙} (left x) = left (include {t} x)
    include {t + 𝟙} (right *) = right *

    include+ : {T : Type} -> {t : StandardFinType T} -> (Member T) -> Member (T + 𝟙)
    include+ x = left x

    max : {T : Type} -> (t : StandardFinType (T + 𝟙)) -> (Member (T + 𝟙))
    max (FinS Fin0) = right *
    max (FinS (FinS t)) = left (max (FinS t))

    --- a++ operation
    -- _-^ : {T : Type} -> {t : StandardFinType T} -> (a : Member T) -> Maybe (Member T)
    -- _-^ {T} {t} a with areEqualT a (max t)
    -- ...              | true = left *
    -- ...              | false = {!   !}
    -- _-^ {_} {t} a with areEqualT a (max (T))
    -- ...              | true = left *
    -- ...              | false = include+ a
    -- --- a-- operation
    -- _-v : {T : Type} -> {t : StandardFinType T} -> (a : Member T) -> Maybe (Member T)
    -- left a -v = {! right a  !}
    -- right a -v = left *
