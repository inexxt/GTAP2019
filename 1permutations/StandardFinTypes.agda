{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module StandardFinTypes where

    open import Agda.Builtin.Sigma
    open import Data.Product using (∃)
    open import FinTypes

    data StandardFinType : Type -> Set where
        Fin0 : StandardFinType 𝟘
        FinS : {S : Type} -> StandardFinType S -> StandardFinType (S + 𝟙)


    getTypeFromStandardType : {T : Type} -> (StandardFinType T) -> Type
    getTypeFromStandardType {T} _ = T

    _++_ : {A B : Type} -> StandardFinType A -> StandardFinType B -> ∃ (λ x -> getTypeFromStandardType x ≈ (A + B))
    Fin0 ++ y = y , +-unit
    _++_ {A + 𝟙} {B} (FinS x) y =
        let (t , p) = x ++ y
            tt = getTypeFromStandardType t
            tt1 = Equiv-+respects p (Equiv-reflex {𝟙})

            1+a=a+1 = +-commut {𝟙} {A}
            [1+a]+b=[a+1]+b = Equiv-+respects 1+a=a+1 (Equiv-reflex {B})
            [a+b]+1=1+[a+b] = +-commut {A + B} {𝟙}
            1+[a+b]=[1+a]+b = +-assoc {𝟙} {A} {B}
            [a+b]+1=[1+a]+b = Equiv-composition [a+b]+1=1+[a+b] 1+[a+b]=[1+a]+b
            [a+b]+1=[a+1]+b = Equiv-composition [a+b]+1=[1+a]+b [1+a]+b=[a+1]+b

            goal = Equiv-composition tt1 [a+b]+1=[a+1]+b
        in  (FinS t) , goal

    normalizePlus : (A : Type) -> Type
    normalizePlus a = a

    -- cnf : (A : Type) -> Σ Type (λ T -> (T ≈ A))
    -- cnf 𝟘 = (𝟘 , Equiv-reflex)
    -- cnf 𝟙 = (𝟘 + 𝟙 , +-unit)
    -- cnf (A + B) = let (ta , pa) = cnf A
    --                   (tb , pb) = cnf B
    --               in  (ta + tb) , (Equiv-+respects pa pb)
    -- cnf (𝟘 × A) =  𝟘 , ×𝟘
    -- cnf (𝟙 × A) = let (ta , pa) = cnf A
    --               in  ta , (Equiv-composition pa (Equiv-symmetry ×-unit))
    -- cnf ((A × B) × C) = let (t , p) = cnf (A × (B × C))
    --                     in  t , (Equiv-composition p ×-assoc)
    -- cnf ((A + B) × C) = let (tac , pac) = cnf (A × C)
    --                         (tbc , pbc) = cnf (B × C)
    --                         pabc = Equiv-+respects pac pbc
    --                         distrib = Equiv-symmetry (×+-distrib {C} {A} {B})
    --                     in  tac + tbc , Equiv-composition pabc distrib

    cnfp : (A : Type) -> ∃ (λ x -> (getTypeFromStandardType x ≈ A))
    cnfp 𝟘 = Fin0 , Equiv-reflex
    cnfp 𝟙 = (FinS Fin0) , Equiv-reflex
    cnfp (A × B) = {!   !}
    cnfp (A + B) = let (ta , pa) = cnfp A
                       (tb , pb) = cnfp B
                   in  {!   !} , {!   !} -- (Equiv-+respects pa pb)
    -- cnfp 𝟘 = (Fin0 , Equiv-reflex)
    -- cnfp 𝟙 = (FinS Fin0 , +-unit)

    -- cnfp (𝟘 × A) =  𝟘 , ×𝟘
    -- cnfp (𝟙 × A) = let (ta , pa) = cnfp A
    --               in  ta , (Equiv-composition pa (Equiv-symmetry ×-unit))
    -- cnfp ((A × B) × C) = let (t , p) = cnfp (A × (B × C))
    --                     in  t , (Equiv-composition p ×-assoc)
    -- cnfp ((A + B) × C) = let (tac , pac) = cnf (A × C)
    --                         (tbc , pbc) = cnf (B × C)
    --                         pabc = Equiv-+respects pac pbc
    --                         distrib = Equiv-symmetry (×+-distrib {C} {A} {B})
    --                     in  tac + tbc , Equiv-composition pabc distrib


    --- Every type is ≈ to a StandardFinType
    --- TODO how do I write that???
    -- allTypesEquivToStandard : (A : Type) -> Σ {T} (StandardFinType T) (λ x -> (getTypeFromStandardType x) ≈ A)
    -- allTypesEquivToStandard A = ?

    allTypesEquivToStandard : (A : Type) -> ∃ (λ x -> (getTypeFromStandardType x) ≈ A)
    allTypesEquivToStandard A = {!   !}

    --- First representation of swap: an element of the
