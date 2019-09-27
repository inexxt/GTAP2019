{-# OPTIONS --without-K #-}

module Lehmer where

open import Data.Nat
open import Data.Fin
open import General
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Vec hiding (insert)
open import Function
open import Data.Nat.Properties
open import Data.List
open import Data.Product using (∃)
open import Permutations ℕ

FinN : {n : ℕ} -> (k : Fin n) -> Set
FinN k = Fin (suc (toℕ k))

data Code (n : ℕ): Set where
    Perm : ((k : Fin n) -> (FinN k)) -> Code n

n-list : (n : ℕ) -> List ℕ
n-list 0F = []
n-list (suc n) = n ∷ n-list n

N-Permutation : (n : ℕ) -> List ℕ -> Set
N-Permutation n = λ l -> IsPermutation (n-list n) l

howManySmaller : {n m : ℕ} -> (Fin (suc n) -> Fin m) -> Fin m -> Fin (suc n)
howManySmaller {0F} {m} f my = 0F
howManySmaller {suc n} {m} f my with my Data.Fin.<? f 0F
...  | yes _ = suc (howManySmaller {n} {m} (λ k ->  f (suc k)) my)
...  | Dec.no _ = inject₁ (howManySmaller {n} {m} (λ k ->  f (suc k)) my)

encode : {n : ℕ} -> (Fin n ≈ Fin n) -> Code n
encode {0F} (Equiv f g x y) = Perm (λ ())
encode {suc n} (Equiv f g x y) = Perm (λ k → howManySmaller (λ l → f (inject! l)) k)

injection-eq : {n : ℕ} -> {k : Fin n} -> toℕ k == toℕ (inject₁ k)
injection-eq {suc n} {0F} = idp
injection-eq {suc n} {suc k} = let p =  injection-eq {k = k} in ap suc p

injection-type-eq : {n : ℕ} -> {k : Fin n} -> {C : ℕ -> Set} -> C (toℕ k) == C (toℕ (inject₁ k))
injection-type-eq {C = C} = ap C injection-eq

coe-inject : {n : ℕ} -> {k : Fin n} -> {C : ℕ -> Set} -> C (toℕ k) -> C (toℕ (inject₁ k))
coe-inject {C = C} = coe (injection-type-eq {C = C})

toℕ-fromℕ : {n : ℕ} -> toℕ (fromℕ n) == n
toℕ-fromℕ {0F} = idp
toℕ-fromℕ {suc n} = let p = toℕ-fromℕ {n}
                    in ap suc p

toℕ-suc : {n : ℕ} -> {k : Fin n} -> suc (toℕ k) == toℕ (suc k)
toℕ-suc {suc n} {0F} = idp
toℕ-suc {suc n} {suc k} = let p = toℕ-suc
                          in ap suc p

-- insert' : {n : ℕ} -> {k : ℕ} -> {p : k Data.Nat.≤ n} -> Vec (Fin n) k -> (Fin (suc k)) -> (Fin (suc n)) -> Vec (Fin (suc n)) (suc k)
-- insert' {0F} {0F} [] pos e = e ∷ []
-- insert' {suc n} v 0F e = e ∷ (Data.Vec.map inject₁ v)
-- insert' {suc n} {suc k} {s≤s p} (x ∷ v) (suc place) e = inject₁ x ∷ (insert' {p = ≤-step p} v place e)

insert : {n : ℕ} -> Vec (Fin n) n -> Fin (suc n) ->  Vec (Fin (suc n)) (suc n)
insert {0F} [] 0F = 0F ∷ []
insert {suc n} v place = insert' {p = ≤-refl} v place (fromℕ (suc n))

decrease-fin : {n : ℕ} -> (i : Fin n) -> Fin (suc (toℕ i))
decrease-fin {suc n} 0F = 0F
decrease-fin {suc n} (suc i) = suc (decrease-fin i)


decode' : {n : ℕ} -> Code n -> Vec (Fin n) n
decode' {0F} (Perm p) = []
decode' {suc n} (Perm p) = let C = (λ x → Vec (Fin (toℕ x)) (toℕ x))
                               f = λ i x → let px : Vec (Fin (toℕ (inject₁ i))) (toℕ (inject₁ i)) == Vec (Fin (toℕ i)) (toℕ i)
                                               px = ap (λ x → Vec (Fin x) x) (rev injection-eq)
                                               x' = coe px x
                                          in insert x' (p i)
                               x = fold′ {suc n} C f []
                               xl = x (fromℕ (suc n))

                               pxl : Vec (Fin (suc (toℕ (fromℕ n)))) (suc (toℕ (fromℕ n))) == Vec (Fin (suc n)) (suc n)
                               pxl = ap (λ x → Vec (Fin (suc x)) (suc x)) toℕ-fromℕ
                               xl' = coe pxl xl
                           in xl'

decode : {n : ℕ} -> Code n -> (Fin n ≈ Fin n)
decode {n} (Perm p) = let d = decode' (Perm p)
                      in Equiv {!!} {!!} {!!} {!!}


encode-decode : {n : ℕ} -> (e : Fin n ≈ Fin n) -> decode (encode e) == e
encode-decode {n} e = {!!}

decode-encode : {n : ℕ} -> (c : Code n) -> encode (decode c) == c
decode-encode {n} p = {!!}

Code-Perm : {n : ℕ} -> (Fin n ≈ Fin n) ≈ Code n
Code-Perm = Equiv encode decode encode-decode decode-encode
