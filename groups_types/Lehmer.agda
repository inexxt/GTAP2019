{-# OPTIONS --without-K #-}

module Lehmer where

open import Data.Nat
open import Data.Fin
open import General
open import Relation.Nullary

data S (n : ℕ): Set where
    Perm : ((k : Fin n) -> (Fin (suc (toℕ k)))) -> S n

howManySmaller : {n m : ℕ} -> (Fin (suc n) -> Fin m) -> Fin m -> Fin (suc n)
howManySmaller {0F} {m} f my = 0F
howManySmaller {suc n} {m} f my with my Data.Fin.<? f 0F
...  | yes _ = suc (howManySmaller {n} {m} (λ k ->  f (suc k)) my)
...  | Dec.no _ = inject₁ (howManySmaller {n} {m} (λ k ->  f (suc k)) my)

encode : {n : ℕ} -> (Fin n ≈ Fin n) -> S n
encode {0F} (Equiv f g x y) = Perm (λ ())
encode {suc n} (Equiv f g x y) = Perm (λ k → howManySmaller (λ l → f (inject! l)) k)

addTo : {n : ℕ} -> (Fin n -> Fin n) -> (k : Fin n) ->

decode' : {n : ℕ} -> S n -> (k : Fin n) -> Fin n
decode' {suc n} (Perm p) acc 0F = addTo acc k (p 0F)
decode' {suc n} (Perm p) acc (suc k) = {!   !}
    where
    pp : (k : Fin n) -> Fin (suc (toℕ k))
    pp k = {! p (inject₁ k) !}
    f' = decode' {n} (Perm (λ l → pp l)) acc k
