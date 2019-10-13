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
           -> Σ ((List ℕ) × ℕ) (λ (w'' , r') -> (n >> w'') × (w'' ++ ((suc n) ↓ r')) ≃ (w ++ ((suc n) ↓ r) ++ w'))

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
          -> Σ ((List ℕ) × ℕ) (λ (w'' , r') -> (n >> w'') × (w'' ++ ((suc n) ↓ r')) ≃ (w ++ ((suc n) ↓ r) ++ (i ∷ w')))

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
          -> Σ ((List ℕ) × ℕ) (λ (w'' , r') -> (n >> w'') × (w'' ++ ((suc n) ↓ r')) ≃ (w ++ ((suc n) ↓ r) ++ (i ∷ w')))

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
          -> Σ ((List ℕ) × ℕ) (λ (w'' , r') -> (n >> w'') × (w'' ++ ((suc n) ↓ r')) ≃ (w ++ ((suc n) ↓ r) ++ (i ∷ w')))

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
        -> Σ ((List ℕ) × ℕ) (λ (w'' , r') -> (n >> w'') × (w'' ++ ((suc n) ↓ r')) ≃ (w ++ ((suc n) ↓ r) ++ (i ∷ w')))

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

      (w'' , r') , (ww'' , pp) = all-reduce {w} {w'} {n} pn {suc r} (s≤s r≤n) ww ww'

      pp' = F-canonize-p≡ (suc n) r i (s≤s r≤n) (≡-trans (+-assoc i 1 r) (≡-sym q))
      pp'' = ≡-sym (cong (λ l -> w ++ l ++ w') pp')
  in (w'' , r') , (ww'' , trans pp (refl≡ (≡-trans pp'' (cong (λ l → w ++ l) (++-assoc (suc n ↓ r) (i ∷ []) w'))))) -- p≡


n=i+r {w} {w'} {suc n} pn {zero} prn {i} pi ww ww' q =
  -- impossible
  {!!}
n=i+r {w} {w'} {suc n} pn {suc zero} prn {i} pi ww ww' q =
  -- reduction
  let i=n : i ≡ suc n
      i=n = ≡-down2 (≡-trans (+-comm 1 i) (≡-sym q))

      (w'' , r') , (ww'' , pp) = all-reduce {w} {w'} {suc n} pn {zero} z≤n ww ww'

      lemma =
        ≃begin
          w'
        ≃⟨ ++-respects (comm (cancel {i})) refl ⟩
          i ∷ i ∷ w'
        ≃⟨ refl≡ (cong (λ x → x ∷ i ∷ w') i=n) ⟩
          suc n ∷ i ∷ w'
        ≃∎
  in  (w'' , r') , ww'' , (trans pp (++-≃ refl lemma))

-- n=i+r {w} {w'} {suc n} pn {suc zero} prn {i} pi ww ww' q =
--   -- reduction
--   let i=n : i ≡ suc n
--       i=n = ≡-down2 (≡-trans (+-comm 1 i) (≡-sym q))

--       (w'' , r') , (ww'' , pp) = all-reduce {w} {w'} {suc n} pn {zero} z≤n ww ww'

--       lemma =
--         ≃begin
--           w'
--         ≃⟨ ++-respects (comm (cancel {i})) refl ⟩
--           i ∷ i ∷ w'
--         ≃⟨ refl≡ (cong (λ x → x ∷ i ∷ w') i=n) ⟩
--           suc n ∷ i ∷ w'
--         ≃∎
--   in  (w'' , r') , ww'' , (trans pp (++-≃ refl lemma))


-- ... | no q = -- the case when there's no n and it doesn't appear on the right
--   let (w'' , r') , (ww'' , pp) = all-reduce (w ++ [ i ])  w' (suc n) pn zero prn ((>>-++ ww (i :⟨ (≤-≠-≤ p λ x → q (≡-down2 _ _ x)) ⟩: []))) ww'
--   in (w'' , r') , ww'' , trans pp (refl≡ ( ++-assoc w (i ∷ []) w'))


i+1+r<n {w} {w'} {n} pn {r} prn {i} pi ww ww' q =
  let 1+i+r=i+1+r : 1 + (i + r) ≡ i + (1 + r)
      1+i+r=i+1+r = ≡-sym (+-three-assoc {i} {1} {r})

      i<n : i < n
      i<n = ≤-down2 (≤-down-+ (≤-trans (s≤s (≤-reflexive 1+i+r=i+1+r)) q))

      (w'' , r') , (ww'' , pp) = all-reduce {w ++ [ i ]} {w'} {n} pn {r} prn (>>-++ ww (i :⟨ i<n ⟩: [])) ww'
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

  in (w'' , r') , (ww'' , trans pp lemma)


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

      (w'' , r') , (ww'' , pp) = all-reduce {w ++ [ i ]} {w'} {n} pn {r} prn (>>-++ ww (i :⟨ ≤-down2 pi ⟩: [])) ww'
  in  (w'' , r') , (ww'' , trans pp lemma1)


absurd-nowhere {n} {r} {i} p1 p2 p3 p4 =
  let lemma : i + suc r ≡ suc i + r
      lemma = +-three-assoc {i} {1} {r}
      t1 = p1
      t2 = p2
      t3 = (λ x → p3 (≡-trans x (≡-sym lemma)))
      t4 = (λ x → p4 (≤-trans (≤-reflexive (cong suc lemma)) x))
  in  nowhere t1 t2 t3 t4


all-reduce {w} {[]} {n} pn {r} prn ww [] = (w , r) , (ww , refl≡ (≡-sym (++-unit2 w ((suc n) ↓ r))) ) -- base of induction
all-reduce {w} {i ∷ w'} {n} pn {r} prn ww (.i :⟨ pi ⟩: ww') with ((suc n) <? i + r) with ((suc n) ≟ i + r) with ((suc n) ≟ i + (1 + r)) with (i + (1 + r) <? (suc n))
... | yes q | _ | _ | _ = n<i+r {w} {w'} {n} pn {r} prn {i} pi ww ww' q
... | _ | yes q | _ | _ = n=i+r {w} {w'} {n} pn {r} prn {i} pi ww ww' q
... | _ | _ | yes q | _ = n=i+1+r {w} {w'} {n} pn {r} prn {i} pi ww ww' q
... | _ | _ | _ | yes q = i+1+r<n {w} {w'} {n} pn {r} prn {i} pi ww ww' q
... | no p1 | no p2 | no p3 | no p4  = ⊥-elim (absurd-nowhere p1 p2 p3 p4)



-- all-reduce w [] n pn r prn ww [] = (w , r) , (ww , refl≡ (≡-sym (++-unit2 w ((suc n) ↓ r))) ) -- base of induction
-- all-reduce w (i ∷ w') (suc n) pn zero prn ww (.i :⟨ p ⟩: ww') with i ≟ (suc n)
-- ... | yes q = -- the case when there's no n, but now it appears on the right
--   let (w'' , r') , (ww'' , pp) = all-reduce w  w' (suc n) pn (suc zero) (s≤s z≤n) ww ww'
--   in (w'' , r') , ww'' , trans pp (refl≡ (cong (λ k -> w ++ k ∷ w') (≡-sym q)) )
-- ... | no q = -- the case when there's no n and it doesn't appear on the right
--   let (w'' , r') , (ww'' , pp) = all-reduce (w ++ [ i ])  w' (suc n) pn zero prn ((>>-++ ww (i :⟨ (≤-≠-≤ p λ x → q (≡-down2 _ _ x)) ⟩: []))) ww'
--   in (w'' , r') , ww'' , trans pp (refl≡ ( ++-assoc w (i ∷ []) w'))
-- all-reduce w (0 ∷ w') n pn r prn ww (.0 :⟨ p ⟩: ww') = {!!}
-- all-reduce w ((suc i) ∷ w') n pn r prn ww (.(suc i) :⟨ p ⟩: ww') with ((suc n) <? (suc i) + r) with ((suc n) ≟ (suc i) + r) with ((suc n) ≟ (suc i) + (1 + r)) with ((suc i) + (1 + r) <? (suc n))
-- ... | yes q | _ | _ | _ =
--   let (w'' , r') , (ww'' , pp) = all-reduce (w ++ [ i ]) w' n pn r prn (>>-++ ww (i :⟨ ≤-down2 p ⟩: [])) ww'
--   in (w'' , r') , (ww'' , trans pp (n<i+r w w' (suc n) r i (s≤s (≤-down2 p)) prn q)) -- p>
-- ... | _ | yes q | _ | _ = {!!} -- reduction
-- ... | _ | _ | yes q | _ =
--   let xx : 1 + r ≤ n
--       xx = (≤-remove-+ {i} {1 + r} (≤-reflexive (≡-down2 (i + suc r) n (≡-sym q))))
--
--       r≤n : r ≤ n
--       r≤n = ≤-≠-≤ prn (λ x → 1+n≰n (≤-down (≤-trans (s≤s xx) (≤-reflexive (≡-sym x)))))
--
--       (w'' , r') , (ww'' , pp) = all-reduce w w' n pn (suc r) (s≤s r≤n) ww ww'
--
--       pp' = F-canonize-p≡ (suc n) r i (s≤s r≤n) (s≤s (≤-down2 p)) (≡-sym (≡-trans q (cong suc (≡-sym (+-assoc i 1 r)))))
--       pp'' = ≡-sym (cong (λ l -> w ++ l ++ w') pp')
--   in (w'' , r') , (ww'' , trans pp (refl≡ (≡-trans pp'' (cong (λ l -> w ++ l) (++-assoc (suc n ↓ r) (suc i ∷ []) w'))))) -- p≡
-- ... | _ | _ | _ | yes q =  -- p<
--   let i+1+r≡1+i+r : i + suc r ≡ suc i + r
--       i+1+r≡1+i+r = +-three-assoc {i} {1} {r}
--       2+i≤n : 2 + i ≤ n
--       2+i≤n = ≤-down2 (≤-trans (s≤s (s≤s (≤-trans (≤-up-+ {r = r} (≤-reflexive refl)) (≤-reflexive (≡-sym i+1+r≡1+i+r))))) q)
--       (w'' , r') , (ww'' , pp) = all-reduce (w ++ [ suc i ]) w' n pn r prn (>>-++ ww ((suc i) :⟨ 2+i≤n ⟩: [])) ww'
--       pp' = F-canonize-p< (suc n) r (suc i) prn (s≤s (≤-trans (≤-reflexive (cong suc (≡-sym i+1+r≡1+i+r))) (≤-down2 q)))
--
--       lemma =
--         ≃begin
--           (w ++ [ suc i ]) ++ ((suc n ↓ r) ++ w')
--         ≃⟨ refl≡ (++-assoc w (suc i ∷ []) ((suc n ↓ r) ++ w')) ⟩
--           w ++ (([ suc i ] ++ (suc n ↓ r)) ++ w')
--         ≃⟨ ++-≃ refl (++-≃ (comm pp') refl)   ⟩
--           w ++ (((suc n ↓ r) ++ [ suc i ]) ++ w')
--         ≃⟨ refl≡ (cong (λ l → w ++ l) (++-assoc (suc n ↓ r) (suc i ∷ []) w')) ⟩
--           w ++ ((suc n ↓ r) ++ ([ suc i ] ++  w'))
--         ≃∎
--
--   in (w'' , r') , (ww'' , trans pp lemma) -- p<
-- ... | no p1 | no p2 | no p3 | no p4  =
--   let lemma : i + suc r ≡ suc i + r
--       lemma = +-three-assoc {i} {1} {r}
--       t1 = p1
--       t2 = p2
--       t3 = (λ x → p3 (≡-trans x (cong suc (≡-sym lemma)) ))
--       t4 = (λ x → p4 (≤-trans (≤-reflexive (cong suc (cong suc lemma))) x))
--   in  ⊥-elim (nowhere t1 t2 t3 t4) -- absurd

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
