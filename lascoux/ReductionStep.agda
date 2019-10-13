{-# OPTIONS --allow-unsolved-metas #-}

module ReductionStep where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; Σ; _×_; _,_; _,′_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

open import General
open import Relation.Nullary
open import Data.Empty
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Coxeter hiding (n; l)
open import Arithmetic hiding (n; l)
open import Canonization hiding (n; l)
open import CanonizationInterface hiding (n; l)

open _≃_
open ≃-Reasoning
open Σ


variable
  n : ℕ
  l : List ℕ

data _>>_ : ℕ -> List ℕ -> Set where
  [] : {n : ℕ} -> n >> []
  _:⟨_⟩:_ : {n : ℕ} -> {l : List ℕ} -> (k : ℕ) -> (k < n) -> n >> l -> n >> (k ∷ l)

>>-++ : {l1 l2 : List ℕ} -> n >> l1 -> n >> l2 -> n >> (l1 ++ l2)
>>-++ {n} {[]} {l2} ll1 ll2 = ll2
>>-++ {n} {x ∷ l1} {l2} (.x :⟨ p ⟩: ll1) ll2 = x :⟨ p ⟩: (>>-++ ll1 ll2)


all-reduce : {w : List ℕ}
           -> {w' : List ℕ}
           -> {n : ℕ}
           -> (zero < n)
           -> {r : ℕ}
           -> (r ≤ (suc n))
           -> (ww : n >> w)
           -> (ww' : (suc n) >> w')
           -> Σ ((List ℕ) × ℕ) (λ (w'' , r') -> (n >> w'') × (r' ≤ suc n) × (w'' ++ ((suc n) ↓ r')) ≃ (w ++ ((suc n) ↓ r) ++ w'))

n=i+r : {w : List ℕ}
          -> {w' : List ℕ}
          -> {n : ℕ}
          -> (zero < n)
          -> {r : ℕ}
          -> (r ≤ (suc n))
          -> {i : ℕ}
          -> (i < (suc n))
          -> (ww : n >> w)
          -> (ww' : (suc n) >> w')
          -> ((suc n) ≡ i + r)
          -> Σ ((List ℕ) × ℕ) (λ (w'' , r') -> (n >> w'') × (r' ≤ suc n) × (w'' ++ ((suc n) ↓ r')) ≃ (w ++ ((suc n) ↓ r) ++ (i ∷ w')))

n=i+1+r : {w : List ℕ}
          -> {w' : List ℕ}
          -> {n : ℕ}
          -> (zero < n)
          -> {r : ℕ}
          -> (r ≤ (suc n))
          -> {i : ℕ}
          -> (i < (suc n))
          -> (ww : n >> w)
          -> (ww' : (suc n) >> w')
          -> ((suc n) ≡ i + (suc r))
          -> Σ ((List ℕ) × ℕ) (λ (w'' , r') -> (n >> w'') × (r' ≤ suc n) × (w'' ++ ((suc n) ↓ r')) ≃ (w ++ ((suc n) ↓ r) ++ (i ∷ w')))

i+1+r<n : {w : List ℕ}
          -> {w' : List ℕ}
          -> {n : ℕ}
          -> (zero < n)
          -> {r : ℕ}
          -> (r ≤ (suc n))
          -> {i : ℕ}
          -> (i < (suc n))
          -> (ww : n >> w)
          -> (ww' : (suc n) >> w')
          -> (i + (suc r) < (suc n))
          -> Σ ((List ℕ) × ℕ) (λ (w'' , r') -> (n >> w'') × (r' ≤ suc n) × (w'' ++ ((suc n) ↓ r')) ≃ (w ++ ((suc n) ↓ r) ++ (i ∷ w')))

n<i+r : {w : List ℕ}
        -> {w' : List ℕ}
        -> {n : ℕ}
        -> (zero < n)
        -> {r : ℕ}
        -> (r ≤ (suc n))
        -> {i : ℕ}
        -> (i < (suc n))
        -> (ww : n >> w)
        -> (ww' : (suc n) >> w')
        -> ((suc n) < i + r)
        -> Σ ((List ℕ) × ℕ) (λ (w'' , r') -> (n >> w'') × (r' ≤ suc n) × (w'' ++ ((suc n) ↓ r')) ≃ (w ++ ((suc n) ↓ r) ++ (i ∷ w')))

absurd-nowhere : {n r i : ℕ}
                 -> ¬ (n < i + r)
                 -> ¬ (n ≡ i + r)
                 -> ¬ (n ≡ i + (1 + r))
                 -> ¬ (i + (1 + r) < n)
                 -> ⊥

n=i+1+r {w} {w'} {n} pn {r} prn {i} pi ww ww' q =
  let r+i=n : r + i ≡ n
      r+i=n = ≡-down2 (≡-sym (≡-trans q (+-comm i (suc r))))

      r≤n : r ≤ n
      r≤n = introduce-≤-from-+ r+i=n

      (w'' , r') , (ww'' , pr' , pp) = all-reduce {w} {w'} {n} pn {suc r} (s≤s r≤n) ww ww'

      pp' = F-canonize-p≡ (suc n) r i (s≤s r≤n) (≡-trans (+-assoc i 1 r) (≡-sym q))
      pp'' = ≡-sym (cong (λ l -> w ++ l ++ w') pp')
  in (w'' , r') , ww'' , pr' , trans pp (refl≡ (≡-trans pp'' (cong (λ l → w ++ l) (++-assoc (suc n ↓ r) (i ∷ []) w')))) -- p≡


n=i+r {w} {w'} {suc n} pn {zero} prn {i} pi ww ww' q =
  -- impossible
  {!!}
n=i+r {w} {w'} {suc n} pn {suc r} prn {i} pi ww ww' q =
  let (w'' , r') , (ww'' , pr' , pp) = all-reduce {w} {w'} {suc n} pn {r} (≤-down prn) ww ww'
      can = F-canonize-red (suc (suc n)) r i prn (≡-sym q)
      lemma =
        ≃begin
          (suc (suc n) ↓ r) ++ w'
        ≃⟨ ++-≃ (comm can) (refl {w'})  ⟩
          suc n ∷ ((suc n ↓ r) ++ i ∷ []) ++ w'
        ≃⟨ refl≡ (++-assoc (suc n ∷ (suc n ↓ r)) (i ∷ []) w') ⟩
          suc n ∷ (suc n ↓ r) ++ i ∷ w'
        ≃∎

      in  (w'' , r') , (ww'' , pr' , trans pp (++-≃ (refl {w}) lemma))


i+1+r<n {w} {w'} {n} pn {r} prn {i} pi ww ww' q =
  let 1+i+r=i+1+r : 1 + (i + r) ≡ i + (1 + r)
      1+i+r=i+1+r = ≡-sym (+-three-assoc {i} {1} {r})

      i<n : i < n
      i<n = ≤-down2 (≤-down-+ (≤-trans (s≤s (≤-reflexive 1+i+r=i+1+r)) q))

      (w'' , r') , (ww'' , pr' , pp) = all-reduce {w ++ [ i ]} {w'} {n} pn {r} prn (>>-++ ww (i :⟨ i<n ⟩: [])) ww'
      pp' = F-canonize-p< (suc n) r i prn (≤-trans (s≤s (≤-reflexive 1+i+r=i+1+r)) q)

      lemma =
        ≃begin
          (w ++ [ i ]) ++ ((suc n ↓ r) ++ w')
        ≃⟨ refl≡ (++-assoc w (i ∷ []) ((suc n ↓ r) ++ w')) ⟩
          w ++ (([ i ] ++ (suc n ↓ r)) ++ w')
        ≃⟨ ++-≃ refl (++-≃ (comm pp') refl)   ⟩
          w ++ (((suc n ↓ r) ++ [ i ]) ++ w')
        ≃⟨ refl≡ (cong (λ l → w ++ l) (++-assoc (suc n ↓ r) (i ∷ []) w')) ⟩
          w ++ ((suc n ↓ r) ++ ([ i ] ++  w'))
        ≃∎
  in (w'' , r') , (ww'' , pr' , trans pp lemma)


n<i+r {w} {w'} {n} pn {suc r} (s≤s prn) {zero} pi ww ww' (s≤s q) = ⊥-elim (1+n≰n (≤-trans q prn))
n<i+r {w} {w'} {n} pn {r} prn {suc i} pi ww ww' q =
  let lemma0 : ((i ∷ []) ++ ((suc n) ↓ r)) ≃ (((suc n) ↓ r) ++ [ suc i ])
      lemma0 = comm (F-canonize-p> (suc n) r i prn pi q)

      lemma1 =
         ≃begin
          ((w ++ i ∷ []) ++ ((suc n) ↓ r) ++ w')
        ≃⟨ refl≡ (++-assoc w (i ∷ []) _)  ⟩
          (w ++ (i ∷ [] ++ ((suc n) ↓ r) ++ w'))
        ≃⟨ refl ⟩
          (w ++ (i ∷ [] ++ ((suc n) ↓ r)) ++ w')
        ≃⟨ ++-≃ refl (++-≃ lemma0 refl) ⟩
          (w ++ (((suc n) ↓ r) ++ [ suc i ]) ++ w')
        ≃⟨ ++-≃ {w} {w} refl (refl≡ (++-assoc ((suc n) ↓ r) _ _)) ⟩
          (w ++ ((suc n) ↓ r) ++ suc i ∷ w')
        ≃∎

      (w'' , r') , (ww'' , pr' , pp) = all-reduce {w ++ [ i ]} {w'} {n} pn {r} prn (>>-++ ww (i :⟨ ≤-down2 pi ⟩: [])) ww'
  in  (w'' , r') , (ww'' , pr' , trans pp lemma1)


absurd-nowhere {n} {r} {i} p1 p2 p3 p4 =
  let lemma : i + suc r ≡ suc i + r
      lemma = +-three-assoc {i} {1} {r}
      t1 = p1
      t2 = p2
      t3 = (λ x → p3 (≡-trans x (≡-sym lemma)))
      t4 = (λ x → p4 (≤-trans (≤-reflexive (cong suc lemma)) x))
  in  nowhere t1 t2 t3 t4


all-reduce {w} {[]} {n} pn {r} prn ww [] = (w , r) , (ww , prn , refl≡ (≡-sym (++-unit2 w ((suc n) ↓ r))) ) -- base of induction
all-reduce {w} {i ∷ w'} {n} pn {r} prn ww (.i :⟨ pi ⟩: ww') with ((suc n) <? i + r) with ((suc n) ≟ i + r) with ((suc n) ≟ i + (1 + r)) with (i + (1 + r) <? (suc n))
... | yes q | _ | _ | _ = n<i+r {w} {w'} {n} pn {r} prn {i} pi ww ww' q
... | _ | yes q | _ | _ = n=i+r {w} {w'} {n} pn {r} prn {i} pi ww ww' q
... | _ | _ | yes q | _ = n=i+1+r {w} {w'} {n} pn {r} prn {i} pi ww ww' q
... | _ | _ | _ | yes q = i+1+r<n {w} {w'} {n} pn {r} prn {i} pi ww ww' q
... | no p1 | no p2 | no p3 | no p4  = ⊥-elim (absurd-nowhere p1 p2 p3 p4)


-- step : (ll : (suc n) >> l) -> Σ (List ℕ × ℕ) (λ (l' , r) -> (n >> l') × (l' ++ ((suc (suc n)) ↓ r)) ≃ l)
-- step {n} {.[]} [] = ([] , 0) , ([] , refl)
-- step {n} {k ∷ l} (_ :⟨ x ⟩: ll) with (suc k) ≟ (suc n)
-- step {n} {k ∷ l} (.k :⟨ x ⟩: ll) | yes p =
--   let xx = all-reduce {!!}  {!!} {!!} {!!} {!!} {!!}
--   in  {!!}
-- step {n} {k ∷ l} (.k :⟨ x ⟩: ll) | no ¬p =
--   let k≤n : k < n
--       k≤n = ≤-≠-≤ x ¬p
--       (l' , r) , (ll' , pp) = step ll
--   in ((k ∷ l') , r) , ((k :⟨ k≤n ⟩: ll') , (prepend k pp))
--
-- data Canonical : (n : ℕ) -> Set where
--   CanZ : Canonical 0
--   CanS : {n : ℕ} -> (k r : ℕ) -> (n < k) -> (r ≤ k) -> (l : Canonical n) -> Canonical k
--
-- immersion : {n : ℕ} -> Canonical n -> List ℕ
-- immersion {zero} CanZ = []
-- immersion {suc n} (CanS k r n<k r≤k l) = (k ↓ r) ++ immersion l
--
-- open import Data.Fin
--
-- canonical-form-lemma : {n : ℕ} -> (l : List (Fin n)) -> ∃ (λ cl -> (map (λ x -> toℕ x) l) ≃ (immersion {n} cl))
--
-- canonical-form-lemma-Free : (l : List ℕ) -> ∃ (λ n -> ∃ (λ cl -> l ≃ (immersion {n} cl)))
