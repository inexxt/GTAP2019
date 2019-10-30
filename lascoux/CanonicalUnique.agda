{-# OPTIONS --no-termination-check #-}
module _ where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (Σ; ∃; _×_; _,_)
open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans)
open import Function

open import Arithmetic hiding (n)
open import Compact hiding (n; l)
open import Lists
open import DiamondCompact hiding (n ; l)

open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)

variable
  n : ℕ
  l : List ℕ

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

data Canonical : (n : ℕ) -> Set where
  CanZ : Canonical 0
  CanS : {n : ℕ} -> (l : Canonical n) -> {r : ℕ} -> (r ≤ suc n) -> Canonical (suc n)

immersion : {n : ℕ} -> Canonical n -> List ℕ
immersion {zero} CanZ = []
immersion {suc n} (CanS l {r} r≤1+n) = (immersion l) ++ ((suc n) ↓ r)

postulate
  canonical-eta : {cl1 cl2 : Canonical n} -> {r1 r2 : ℕ} -> (rn1 : r1 ≤ (suc n)) -> (rn2 : r2 ≤ (suc n)) -> (cl1 ≡ cl2) -> (r1 ≡ r2) -> (CanS cl1 rn1) ≡ (CanS cl2 rn2)

data _>>_ : ℕ -> List ℕ -> Set where
  [] : {n : ℕ} -> n >> []
  _:⟨_⟩:_ : {n : ℕ} -> {l : List ℕ} -> (k : ℕ) -> (k < n) -> n >> l -> n >> (k ∷ l)

extract-proof : {a : ℕ} -> (n >> (a ∷ l)) -> (a < n)
extract-proof (_ :⟨ p ⟩: _) = p

>>-++ : {l1 l2 : List ℕ} -> n >> l1 -> n >> l2 -> n >> (l1 ++ l2)
>>-++ {n} {[]} {l2} ll1 ll2 = ll2
>>-++ {n} {x ∷ l1} {l2} (.x :⟨ p ⟩: ll1) ll2 = x :⟨ p ⟩: (>>-++ ll1 ll2)

>>-↓ : (n k r : ℕ) -> (r + k ≤ n) -> (n >> (k ↓ r))
>>-↓ n k zero p = []
>>-↓ n k (suc r) p = (r + k) :⟨ p ⟩: (>>-↓ n k r (≤-down p))

>>-suc : (n >> l) -> ((suc n) >> l)
>>-suc  [] = []
>>-suc  (k :⟨ p ⟩: l') = k :⟨ ≤-up p ⟩: >>-suc l'

immersion->> : {n : ℕ} -> (cl : Canonical n) -> n >> immersion cl
immersion->> {.0} CanZ = []
immersion->> {suc n} (CanS {n} cl {r} rn) =
  let p = immersion->> {n} cl
  in  >>-++ (>>-suc p) (>>-↓ _ _ _ {!!})

-- reverse->> : n >> l -> n >> reverse l
-- reverse->> {n} {[]} ll = ll
-- reverse->> {n} {x ∷ l} (.x :⟨ x₁ ⟩: ll) rewrite (reverse-++-commute [ x ] l) =
--   let rec = reverse->> {n} {l} ll
--   in  >>-++ {l1 = reverse l} {l2 = [ x ]} rec (x :⟨ x₁ ⟩: [])

-- abs-const-↓ : (n k a : ℕ) -> (l r : List ℕ) -> (n ↓ k) ≡ (l ++ a ∷ a ∷ r) -> ⊥
-- -- abs-const-↓ zero k a (x ∷ l) r ()
-- -- abs-const-↓ (suc zero) (suc k) a [] r ()
-- -- abs-const-↓ (suc (suc n)) (suc zero) a [] r ()
-- -- abs-const-↓ (suc (suc n)) (suc (suc k)) a [] r ()
-- -- abs-const-↓ (suc n) (suc k) a (x ∷ l) r p  = abs-const-↓ n k a l r (cut-head p)

-- abs-inc-↓ : (n k a : ℕ) -> (l r : List ℕ) -> (n ↓ k) ≡ (l ++ a ∷ suc a ∷ r) -> ⊥
-- abs-inc-↓ n k a l r p = {!!}

-- abs-jump-↓ : (n k a b : ℕ) -> (suc a < b) -> (l r : List ℕ) -> (n ↓ k) ≡ (l ++ b ∷ a ∷ r) -> ⊥
-- abs-jump-↓ n k a l r p = {!!}

-- --- And versions for 2-⇣

-- abs-const2-↓ : (n1 k1 n2 k2 a : ℕ) -> (n1 < n2) -> (l r : List ℕ) -> (n1 ↓ k1) ++ (n2 ↓ k2) ≡ (l ++ a ∷ a ∷ r) -> ⊥
-- -- abs-const2-↓ zero k1 n2 k2 a pnn l r p = abs-const-↓ _ _ _ l r p
-- -- abs-const2-↓ (suc n1) zero n2 k2 a pnn l r p = abs-const-↓ _ _ _ l r p
-- -- abs-const2-↓ (suc zero) (suc k1) (suc .0) (suc k2) .0 (s≤s ()) [] .[] refl
-- -- abs-const2-↓ (suc (suc n1)) (suc zero) (suc .(suc n1)) (suc k2) .(suc n1) pnn [] .(suc n1 ↓ k2) refl = (⊥-elim (1+n≰n pnn))
-- -- abs-const2-↓ (suc n1) (suc k1) n2 k2 a pnn (x ∷ l) r p = abs-const2-↓ n1 k1 n2 k2 a (≤-down pnn) l r (cut-head p)

-- abs-braid2-↓ : (n1 k1 n2 k2 a : ℕ) -> (n1 < n2) -> (l r : List ℕ) -> (n1 ↓ k1) ++ (n2 ↓ k2) ≡ (l ++ suc a ∷ a ∷ suc a ∷ r) -> ⊥
-- abs-braid2-↓ n1 k1 n2 k2 a pnn l r p = {!!}

-- abs-jump2-↓ : (n1 k1 n2 k2 a b : ℕ) -> (n1 < n2) -> (suc a < b) -> (l r : List ℕ) -> (n1 ↓ k1) ++ (n2 ↓ k2) ≡ (l ++ b ∷ a ∷ r) -> ⊥
-- abs-jump2-↓ n1 k1 n2 k2 a b pnn pab l r p = {!!}

-- data _||_||_ (A : Set) (B : Set) (C : Set) : Set where
--   R1 : A -> A || B || C
--   R2 : B -> A || B || C
--   R3 : C -> A || B || C

-- -- some technical lemmas about lists
-- lemma-l++2++r : (a : ℕ) -> (l1 r1 l2 r2 : List ℕ) -> (l1 ++ r1 ≡ l2 ++ a ∷ a ∷ r2)
--                 -> (Σ (List ℕ × List ℕ) (λ (rl2 , rr2) -> (r2 ≡ rl2 ++ rr2) × (l1 ≡ l2 ++ a ∷ a ∷ rl2) × (r1 ≡ rr2))) || -- the case when both a ∷ a are in left
--                    (Σ (List ℕ × List ℕ) (λ (ll2 , lr2) -> (l2 ≡ ll2 ++ lr2) × (l1 ≡ ll2) × (r1 ≡ lr2 ++ a ∷ a ∷ r2))) || -- the case when both a ∷ a are in right
--                    ((l1 ≡ l2 ++ [ a ]) × (r1 ≡ a ∷ r2)) -- the case when one a is in left, and one in right
-- lemma-l++2++r a [] r1 l2 r2 p = R2 (([] , l2) , (refl , (refl , p)))
-- lemma-l++2++r a (x ∷ []) r1 [] r2 p =
--   let h = cut-tail p
--   in  R3 ((cong [_] h) , (cut-head p))
-- lemma-l++2++r a (x ∷ x₁ ∷ l1) r1 [] r2 p =
--   let h1 = cut-tail p
--       h2 = cut-tail (cut-head p)
--   in  R1 ((l1 , r1) , (cut-head (cut-head (≡-sym p)) , (head+tail h1 (head+tail h2 refl)) , refl))
-- lemma-l++2++r a (x ∷ l1) r1 (x₁ ∷ l2) r2 p with lemma-l++2++r a l1 r1 l2 r2 (cut-head p)
-- ... | R1 ((fst , snd) , fst₁ , fst₂ , snd₁) = R1 ((fst , snd) , (fst₁ , ((head+tail (cut-tail p) fst₂) , snd₁)))
-- ... | R2 ((fst , snd) , fst₁ , fst₂ , snd₁) = R2 (((x₁ ∷ fst) , snd) , ((cong (λ e -> x₁ ∷ e) fst₁) , ((head+tail (cut-tail p) fst₂) , snd₁)))
-- ... | R3 (fst , snd) = R3 (head+tail (cut-tail p) fst , snd)

-- --- and versions for many-↓
-- abs-const-many-↓ : (n a : ℕ) -> (l r : List ℕ) -> (cl : Canonical n) -> (immersion {n} cl) ≡ (l ++ a ∷ a ∷ r) -> ⊥
-- abs-const-many-↓ .0 a [] r CanZ ()
-- abs-const-many-↓ .0 a (x ∷ l) r CanZ ()
-- abs-const-many-↓ (suc n) a l r (CanS cl x) p with lemma-l++2++r _ (immersion cl) (suc n ↓ _) _ _ p
-- ... | R1 ((fst , snd) , fst₁ , fst₂ , snd₁) = abs-const-many-↓ _ _ _ fst cl fst₂
-- ... | R2 ((fst , snd) , fst₁ , fst₂ , snd₁) = abs-const-↓ _ _ _ snd r snd₁
-- abs-const-many-↓ (suc n) a l r (CanS cl {suc r₁} x) p | R3 (fst , snd) =
--   let h = cut-tail snd
--       n>cl = immersion->> cl
--       n>a = subst (λ e -> n >> e) (reverse-++-commute l [ a ]) (reverse->> (subst (λ e -> n >> e) fst n>cl))
--   in  ⊥-elim (1+n≰n (≤-trans (≤-reflexive (cong suc h)) {!!}))

-- abs-braid-many-↓ : (n a : ℕ) -> (l r : List ℕ) -> (cl : Canonical n) -> (immersion {n} cl) ≡ (l ++ suc a ∷ a ∷ suc a ∷ r) -> ⊥
-- abs-braid-many-↓ .0 a [] r CanZ ()
-- abs-braid-many-↓ .0 a (x ∷ l) r CanZ ()
-- abs-braid-many-↓ .(suc _) a l r (CanS cl x) p = {!!}

-- abs-jump-many-↓ : (n a b : ℕ) -> (suc a < b) -> (l r : List ℕ) -> (cl : Canonical n) -> (immersion {n} cl) ≡ (l ++ b ∷ a ∷ r) -> ⊥
-- abs-jump-many-↓ .0 a b pab [] r CanZ ()
-- abs-jump-many-↓ .0 a b pab (x ∷ l) r CanZ ()
-- abs-jump-many-↓ .(suc _) a b pab l r (CanS cl x) p = {!!}

-- only-one≅-↓ : (n k1 k2 : ℕ)  -> (k1 ≤ n) -> (k2 ≤ n) -> (n ↓ k1) ≅ (n ↓ k2) -> ⊥
-- -- only-one≅-↓ n k1 k2 pk1 pk2 (cancel≅ l r .(n ↓ k1) .(n ↓ k2) defm defmf) = abs-const-↓ _ _ _ l r defm
-- -- only-one≅-↓ n k1 k2 pk1 pk2 (swap≅ x l r .(n ↓ k1) .(n ↓ k2) defm defmf) = abs-jump-↓ _ _ _ _ x l r defm
-- -- only-one≅-↓ n k1 k2 pk1 pk2 (braid≅ l r .(n ↓ k1) .(n ↓ k2) defm defmf) = abs-inc-↓ _ _ _ l (_ ∷ r) defmf

-- ++-∷ : {l r : List ℕ} -> l ++ n ∷ r ≡ (l ++ [ n ]) ++ r
-- ++-∷ {n} {l} {r} = ≡-sym (++-assoc l (n ∷ []) r)

-- abs≅-↓ : (n k : ℕ) -> (k ≤ n) -> (m : List ℕ) -> ((n ↓ k) ≅ m) -> ⊥
-- -- abs≅-↓ n k pk m (cancel≅ l r .(n ↓ k) .m defm defmf) = abs-const-↓ _ _ _ l r defm
-- -- abs≅-↓ n k pk m (swap≅ x l r .(n ↓ k) .m defm defmf) = abs-jump-↓ _ _ _ _ x l r defm
-- -- abs≅-↓ n k pk m (braid≅ {n₁} l r .(n ↓ k) .m defm defmf) =
-- --   let lemma = ≡-trans defm ++-∷
-- --   in  abs-inc-↓ n k n₁ (l ++ [ suc n₁ ]) r lemma

-- abs2≅-↓ : (n1 k1 n2 k2 : ℕ) -> (k1 ≤ n1) -> (k2 ≤ n2) -> (n1 < n2) -> (m : List ℕ) -> ((n1 ↓ k1) ++ (n2 ↓ k2)) ≅ m -> ⊥
-- -- abs2≅-↓ n1 k1 n2 k2 pkn1 pkn2 pnn m (cancel≅ l r .((n1 ↓ k1) ++ (n2 ↓ k2)) .m defm defmf) = abs-const2-↓ n1 k1 n2 k2 _ pnn l r defm
-- -- abs2≅-↓ n1 k1 n2 k2 pkn1 pkn2 pnn m (swap≅ x l r .((n1 ↓ k1) ++ (n2 ↓ k2)) .m defm defmf) = abs-jump2-↓ n1 k1 n2 k2 _ _ pnn x l r defm
-- -- abs2≅-↓ n1 k1 n2 k2 pkn1 pkn2 pnn m (braid≅ l r .((n1 ↓ k1) ++ (n2 ↓ k2)) .m defm defmf) = abs-braid2-↓ n1 k1 n2 k2 _ pnn l r defm

-- only-one-canonical≅ : (cl : Canonical n) -> (m : List ℕ) -> (immersion {n} cl) ≅ m -> ⊥
-- -- only-one-canonical≅ cl m (cancel≅ l r .(immersion cl) .m defm defmf) = abs-const-many-↓ _ _ _ r cl defm
-- -- only-one-canonical≅ cl m (swap≅ x l r .(immersion cl) .m defm defmf) = abs-jump-many-↓ _ _ _ x l r cl defm
-- -- only-one-canonical≅ cl m (braid≅ l r .(immersion cl) .m defm defmf) = abs-braid-many-↓ _ _ _ r cl defm

-- ≡-↓ : (n k1 k2 : ℕ) -> (k1 ≤ n) -> (k2 ≤ n) -> ((n ↓ k1) ≡ (n ↓ k2)) -> (k1 ≡ k2)
-- ≡-↓ zero .0 .0 z≤n z≤n p = refl
-- ≡-↓ (suc n) zero zero pk1 pk2 p = refl
-- ≡-↓ (suc n) (suc k1) (suc k2) pk1 pk2 p =
--   let lemma = (cut-head p)
--       rec = ≡-↓ _ _ _ (≤-down2 pk1) (≤-down2 pk2) {!!}
--   in  cong suc rec

-- ≡-++↓ : (m1 m2 : List ℕ) -> (n k1 k2 : ℕ) -> (ml1 : n >> m1) -> (ml2 : n >> m2) -> (k1 ≤ suc n) -> (k2 ≤ suc n) -> (m1 ++ ((suc n) ↓ k1) ≡ m2 ++ ((suc n) ↓ k2)) -> (k1 ≡ k2) × (m1 ≡ m2)
-- -- ≡-++↓ [] [] n k1 k2 ml1 ml2 pk1 pk2 p = (≡-↓ _ _ _ pk1 pk2 p) , refl
-- -- ≡-++↓ [] (x ∷ m2) (suc n) (suc k1) k2 ml1 (.x :⟨ x₁ ⟩: ml2) pk1 pk2 p =
-- --   let r = cut-tail  p
-- --   in  ⊥-elim (1+n≰n (≤-trans ? (≤-down2 x₁)))
-- -- ≡-++↓ (x ∷ m1) [] (suc n) k1 (suc k2) (.x :⟨ x₁ ⟩: ml1) ml2 pk1 pk2 p =
-- --   let r = cut-tail  p
-- --   in  ⊥-elim (1+n≰n (≤-trans (≤-reflexive (≡-sym r)) (≤-down2 x₁)))
-- -- ≡-++↓ (x ∷ m1) (x₁ ∷ m2) n k1 k2 (.x :⟨ x₂ ⟩: ml1) (.x₁ :⟨ x₃ ⟩: ml2) pk1 pk2 p =
-- --   let t = cut-head  p
-- --       h = cut-tail  p
-- --       hh , tt = ≡-++↓ m1 m2 n k1 k2 ml1 ml2 pk1 pk2 t
-- --   in  hh , subst (λ z → x ∷ m1 ≡ z ∷ m2) h (cong (λ e -> x ∷ e) tt)


-- ≡immersion : (cl1 cl2 : Canonical n) -> (immersion {n} cl1 ≡ immersion {n} cl2) -> cl1 ≡ cl2
-- ≡immersion CanZ CanZ refl = refl
-- ≡immersion {n} (CanS cl1 {r = r} x) (CanS cl2 {r = r₁} x₁) p =
--   let n>>cl1 = immersion->> cl1
--       n>>cl2 = immersion->> cl2
--       lemma-r , lemma-cl = ≡-++↓ _ _ _ _ _ n>>cl1 n>>cl2 x x₁ p
--       rec = ≡immersion cl1 cl2 lemma-cl
--   in  canonical-eta x x₁ rec lemma-r

-- only-one-canonical≅* : (cl1 cl2 : Canonical n) -> (m1 m2 : List ℕ) -> (immersion {n} cl1 ≡ m1) -> (immersion {n} cl2 ≡ m2) -> (m1 ≅* m2)-> cl1 ≡ cl2
-- only-one-canonical≅* cl1 cl2 m1 .m1 pm1 pm2 refl = ≡immersion _ _ (≡-trans pm1 (≡-sym pm2))
-- only-one-canonical≅* cl1 cl2 m1 m2 pm1 pm2 (trans≅ x p) =
--   let ss = subst (λ t → t ≅ _) (≡-sym pm1) x
--   in  ⊥-elim (only-one-canonical≅ cl1 _ ss)

-- only-one-canonical≃ : (cl1 cl2 : Canonical n) -> (m1 m2 : List ℕ) -> (immersion {n} cl1 ≡ m1) -> (immersion {n} cl2 ≡ m2) -> (m1 ≃ m2) -> cl1 ≡ cl2
-- only-one-canonical≃ cl1 cl2 m1 .m1 pm1 pm2 (R refl refl) = ≡immersion _ _ (≡-trans pm1 (≡-sym pm2))
-- only-one-canonical≃ cl1 cl2 m1 m2 pm1 pm2 (R refl (trans≅ x p2)) =
--   let ss = subst (λ t → t ≅ _) (≡-sym pm2) x
--   in  ⊥-elim (only-one-canonical≅ cl2 _ ss)
-- only-one-canonical≃ cl1 cl2 m1 m2 pm1 pm2 (R (trans≅ x p1) p2) =
--   let ss = subst (λ t → t ≅ _) (≡-sym pm1) x
--   in  ⊥-elim (only-one-canonical≅ cl1 _ ss)
