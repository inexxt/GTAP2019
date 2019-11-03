{-# OPTIONS --allow-unsolved-metas --without-K #-}
module _ where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (Σ; ∃; _×_; _,_)

open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_; _≟_; _<?_; _≤?_)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans; _≟_; _<?_; _≤?_)
open import Function

open import Arithmetic hiding (n)
open import Lists
open import Compact hiding (n; l)
open import ImpossibleLemmas
open import SwapLemmas
open import Canonical
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)


open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

open ≅*-Reasoning
open Relation.Binary.PropositionalEquality.≡-Reasoning
open _⊎_


-- Canonical proper represents canonicals with a non-empty last sequence
data CanonicalProper : (n : ℕ) -> Set where
  CanZ : CanonicalProper 0
  CanS : {n : ℕ} -> {nf : ℕ} -> (n < nf) -> (l : CanonicalProper n) -> {r : ℕ} -> (r < nf) -> CanonicalProper nf


immersionProper : {n : ℕ} -> CanonicalProper n -> List ℕ
immersionProper {zero} CanZ = []
immersionProper {suc n} (CanS _ l {r} _) = (immersionProper l) ++ ((n ∸ r) ↓ (1 + r))

properize : (cl : Canonical n) -> ∃ (λ nf -> ∃ (λ clf -> immersion {n} cl ≡ immersionProper {nf} clf))
properize cl = {!!}

unproperize : (cl : CanonicalProper n) -> ∃ (λ nf -> ∃ (λ clf -> immersionProper {n} cl ≡ immersion {nf} clf))
unproperize cl = {!!}

canonical-proper-append : {n : ℕ} -> (cl : CanonicalProper n) -> (x : ℕ) -> (n ≤ x) -> ∃ (λ clx -> immersionProper {suc x} clx ≡ immersionProper {n} cl ++ [ x ])
canonical-proper-append cl x px =
  let _ , upl , upl-p = unproperize cl
      clx , clx-p = canonical-append upl x px
  in  {!!}

canonical-proper-append-smaller : {n nf r : ℕ} -> {pn : suc n ≤ suc nf} -> {pr : suc r ≤ suc nf} -> {cl : CanonicalProper n} -> (x : ℕ) -> (clf : CanonicalProper (suc nf)) -> (defclf : clf ≡ CanS pn cl pr)
                                  -> (defx : suc x ≡ (nf ∸ r)) -> Σ (suc r < suc nf) (λ prr -> immersionProper {suc nf} (CanS pn cl prr) ≡ (immersionProper {suc nf} clf) ++ [ x ])
canonical-proper-append-smaller {n} {nf} {r} {pn} {pr} {cl} x clf defclf defx = {!!}


always-reduces : (n k x : ℕ) -> (x ≤ k + n) -> (∃ (λ mf -> (n ↓ (1 + k) ++ [ x ]) ≅* mf)) ⊎ (suc x ≡ n)
always-reduces n k x px with suc x <? n
... | yes r = inj₁ (_ , (long-swap<-lr x n (1 + k) [] [] r))
... | no r with suc x ≟ n
... | yes rr = inj₂ rr
... | no rr with x ≟ n
... | no rrr = {!!}
always-reduces n zero x px | no r | no rr | yes rr2 rewrite rr2 = inj₁ (_ , (cancel [] []))
always-reduces n (suc k) x px | no r | no rr | yes rr2 with (always-reduces n k x (≤-trans (≤-reflexive rr2) (≤-up-+ rrr)))
always-reduces n (suc k) x px | no r | no rr | yes rr2 | inj₁ (rec-m , rec-p) = inj₁ (_ , l++ [ suc (k + n) ] rec-p)
always-reduces n (suc k) x px | no r | no rr | yes rr2 | inj₂ y = inj₂ y

lemma : (n r x : ℕ) -> (r ≤ n) -> (cl : Canonical n) -> (f : (mf : List ℕ) -> ((immersion {n} cl ++ ((n ∸ r) ↓ (1 + r))) ++ x ∷ []) ≅* mf -> ⊥) -> (n < x) ⊎ ((x ≡ n ∸ (1 + r)) × (suc r ≤ n))
lemma n r x pnr cl f with n <? x
... | yes q = inj₁ q
... | no q with  always-reduces (n ∸ r) r x (≤-trans (≤-down2 (≰⇒> q)) (≤-reflexive (≡-sym (plus-minus pnr))))
... | inj₁ (ar-m , ar-p) =
  let red =
        ≅*begin
          (immersion cl ++ ((n ∸ r) ↓ (1 + r))) ++ x ∷ []
        ≅*⟨ refl≡ (++-assoc (immersion cl) _ _) ⟩
          immersion cl ++ ((n ∸ r) ↓ (1 + r)) ++ x ∷ []
        ≅*⟨ l++ (immersion cl) ar-p ⟩
          _
        ≅*∎
  in  ⊥-elim (f _ red)
... | inj₂ qq = inj₂ ({!!} , {!!})

-- canonical-final≅ : (m : List ℕ) -> (f : (mf : List ℕ) -> (rev m ≅* mf) -> ⊥) -> ∃ (λ n -> ∃ (λ cl -> immersion {n} cl ≡ rev m))
-- canonical-final≅ [] f = zero , CanZ , refl
-- canonical-final≅ (x ∷ m) f with (canonical-final≅ m (λ mf red → f (mf ++ [ x ]) (++r [ x ] red)))
-- canonical-final≅ (x ∷ m) f | zero , CanZ , snd rewrite (≡-sym snd) = _ , canonical-append CanZ x z≤n
-- canonical-final≅ (x ∷ m) f | _ , CanS fst {zero} x₁ , snd = {!!} -- TODO this requires changing the signature to return canonicalProper instead of just canonical - then it will be impossible
-- canonical-final≅ (x ∷ m) f | _ , CanS {n₁} fst {suc r} x₁ , snd  with lemma n₁ r x (≤-down2 x₁) fst (λ mf mf-abs → f mf (subst (λ e -> (e ++ [ x ]) ≅* mf) snd mf-abs))
-- canonical-final≅ (x ∷ m) f | _ , CanS fst {suc r} x₁ , snd | inj₁ x₂ =
--   let rec-m , rec-p = canonical-append (CanS fst {suc r} x₁) x x₂
--   in  _ , rec-m , (≡-trans rec-p (start+end snd refl))
-- canonical-final≅ (x ∷ m) f | _ , CanS {n} fst {suc r} x₁ , snd | inj₂ (fst₁ , snd₁) =
--   let tt =
--         begin
--           immersion fst ++ suc (r + (n ∸ suc r)) ∷ ((n ∸ suc r) ↓ (1 + r))
--         ≡⟨ start+end (refl {x = immersion fst}) (head+tail (≡-trans (plus-minus snd₁) (≡-sym (plus-minus (≤-down snd₁)))) (≡-sym (++-↓ (n ∸ suc r) r))) ⟩
--           immersion fst ++ r + (n ∸ r) ∷ (suc (n ∸ suc r) ↓ r) ++ n ∸ suc r ∷ []
--         ≡⟨ start+end (refl {x = immersion fst}) (head+tail refl (start+end (cong (λ e -> e ↓ r) {!!}) (cong [_]  (≡-sym fst₁)))) ⟩
--           immersion fst ++ r + (n ∸ r) ∷ ((n ∸ r) ↓ r) ++ x ∷ []
--         ≡⟨ ≡-sym (++-assoc (immersion fst) _ [ x ]) ⟩
--           (immersion fst ++ r + (n ∸ r) ∷ ((n ∸ r) ↓ r)) ++ x ∷ []
--         ≡⟨ start+end snd (refl {x = [ x ]}) ⟩
--           rev m ++ x ∷ []
--         ∎
--   in _ , ((CanS fst {suc (suc r)} (s≤s snd₁)) , tt)

canonical-final≅ : (m : List ℕ) -> (f : (mf : List ℕ) -> (rev m ≅* mf) -> ⊥) -> ∃ (λ n -> ∃ (λ cl -> immersionProper {n} cl ≡ rev m))
canonical-final≅ m pf = {!!}

abs-list : {r : List ℕ} -> ([] ≡ l ++ n ∷ r) -> ⊥
abs-list {[]} ()
abs-list {x ∷ l} ()

cut-last : {l1 l2 : List ℕ} -> {x1 x2 : ℕ} -> (l1 ++ [ x1 ] ≡ l2 ++ [ x2 ]) -> (l1 ≡ l2)
cut-last {[]} {[]} p = refl
cut-last {[]} {x ∷ []} ()
cut-last {[]} {x ∷ x₁ ∷ l2} ()
cut-last {x ∷ []} {[]} ()
cut-last {x ∷ x₁ ∷ l1} {[]} ()
cut-last {x ∷ l1} {x₁ ∷ l2} p = head+tail (cut-tail p) (cut-last (cut-head p))

cut-last-canonical : (x : ℕ) -> (cl : CanonicalProper n) -> (immersionProper cl ≡ l ++ [ x ]) -> ∃ (λ nf -> ∃ (λ clf -> immersionProper {nf} clf ≡ l))
cut-last-canonical {zero} {l} x CanZ pp = ⊥-elim (abs-list pp)
cut-last-canonical {suc n} {l} x (CanS pn cl {zero} pr) pp = _ , (cl , cut-last pp)
cut-last-canonical {suc n} {l} x (CanS pn cl {suc r} pr) pp =
  let p1 =
        begin
          (immersionProper cl ++ ((1 + (n ∸ suc r)) ↓ (1 + r))) ++ [ _ ]
        ≡⟨ ++-assoc (immersionProper cl) (suc (n ∸ suc r) ↓ (1 + r)) _ ⟩
          _
        ≡⟨ start+end (refl {x = immersionProper cl}) (++-↓ (n ∸ suc r) (suc r)) ⟩
          immersionProper cl ++ ((n ∸ suc r) ↓ (2 + r))
        ≡⟨ pp ⟩
          l ++ [ x ]
        ∎
      p2 =
        begin
          _
        ≡⟨ start+end (refl {x = immersionProper cl}) (head+tail (cong (λ e -> r + e) {!!}) (cong (λ e -> e ↓ r) {!!})) ⟩
          immersionProper cl ++ r + suc (n ∸ suc r) ∷ (suc (n ∸ suc r) ↓ r)
        ≡⟨ cut-last p1 ⟩
          l
        ∎
  in  _ , (CanS pn cl (≤-down pr)) , p2

is-canonical? : (m : List ℕ) -> Dec (∃ (λ nf -> ∃ (λ cl -> immersionProper {nf} cl ≡ rev m)))
is-canonical? [] = yes (_ , (CanZ , refl))
is-canonical? (x ∷ m) with is-canonical? m
... | no  p = no λ {(_ , cl , pp) → p (cut-last-canonical x cl pp) }
... | yes (_ , CanZ , pp) rewrite (≡-sym pp) = yes (_ , canonical-proper-append CanZ x z≤n)
... | yes (suc nn , CanS {n} {suc nn} qn cl {r} qr , pp) with nn <? x
... | yes q =
  let clx , clp = canonical-proper-append (CanS qn cl qr) x q
  in  yes (_ , clx , (≡-trans clp (start+end pp refl)))
... | no q with suc x ≟ (nn ∸ r)
... | yes qq rewrite (≡-sym pp) =
  let  prr , app = canonical-proper-append-smaller x (CanS qn cl qr) refl qq
  in  yes (_ , ((CanS qn cl prr) , app))
... | no qq = no λ {
  (_ , CanZ , pp) → abs-list pp ;
  (_ , CanS (s≤s x) CanZ {zero} (s≤s z≤n) , ppp) →
    let m-empty = cut-last {[]} ppp
    in  abs-list (≡-trans m-empty (≡-sym pp)) ;
  (_ , CanS x (CanS x₂ cl pr) {zero} x₁ , ppp) → {!!} ;
  (_ , CanS x cl {suc r} pr , ppp) → {!!} }

canonical-proper-NF : {n : ℕ} -> (cl : CanonicalProper n) -> (∃ (λ m -> immersionProper {n} cl ≅ m)) -> ⊥
canonical-proper-NF cl (m , p) =
  let _ , unproper , unproper-p = unproperize cl
  in  final≅-canonical unproper _ m refl (subst (λ e -> e ≅ m) unproper-p p)

not-canonical-not-NF : (m : List ℕ) -> ¬ ∃ (λ n -> ∃ (λ cl -> immersionProper {n} cl ≡ (rev m))) -> ∃ (λ mf -> (rev m) ≅* mf)
not-canonical-not-NF [] p = ⊥-elim (p (_ , (CanZ , refl)))
not-canonical-not-NF (x ∷ m) p with is-canonical? m
-- first, the case when m is not canonical
... | no  q =
  let rec-m , rec-p = not-canonical-not-NF m q
  in  _ , (++r [ x ] rec-p)
-- under this line, we know that m is canonical
-- now, lets check if m is empty
... | yes (_ , CanZ , qp) rewrite (≡-sym qp) =
  let app = canonical-proper-append CanZ x z≤n
  in  ⊥-elim (p (_ , app))
-- under this line, we know that m is not empty
-- now check if x is not too big, which will make a canonical out of m ++ [ x ]
... | yes ((suc nf) , CanS {nf = suc nf} pn cl {r} pr , qp) with x ≤? nf
... | no q2 rewrite (≡-sym qp) =
  let app = canonical-proper-append (CanS pn cl pr) x (≰⇒> q2)
  in  ⊥-elim (p (_ , app))
-- under this line, we know that x is not too big
-- now we can finally use the always-reduces
... | yes  q2 with (always-reduces (nf ∸ r) r x (≤-trans q2 (≤-reflexive (≡-sym (plus-minus (≤-down2 pr))))))
 -- the case when there is a reduction
... | inj₁ (red-m , red-p) rewrite (≡-sym qp) rewrite (plus-minus (≤-down pr)) rewrite (plus-minus (≤-down2 pr)) = _ , trans (refl≡ (++-assoc (immersionProper cl) _ _)) (l++ (immersionProper cl) red-p)
-- the case when x completes the sequence
... | inj₂ q3 rewrite (≡-sym qp) =
  let prr , app = canonical-proper-append-smaller x (CanS pn cl pr) refl q3
  in  ⊥-elim (p (_ , (CanS pn cl prr) , app))

{-# NON_TERMINATING #-}
everything-to-canonical : (m : List ℕ) -> ∃ (λ n -> ∃ (λ cl -> rev m ≅* immersionProper {n} cl))
everything-to-canonical m with is-canonical? m
... | yes (_ , cl , cl-p) = _ , (cl , (refl≡ (≡-sym cl-p)))
... | no  p =
  let step-m , step-p = not-canonical-not-NF m p
      nn , rec-m , rec-p = everything-to-canonical (rev step-m)
  in  nn , rec-m , (trans step-p (trans (refl≡ rev-rev) rec-p))
