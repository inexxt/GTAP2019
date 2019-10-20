{-# OPTIONS --allow-unsolved-metas #-}
module Diamond where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)
open import General
open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_)
open import Data.Bool.Properties hiding (≤-reflexive)

open import Arithmetic hiding (n)
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)


open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)


variable
    n : ℕ
    l : List ℕ

data nonempty : List ℕ -> Set where
  nonempty-l : (x : ℕ) -> (l : List ℕ) -> nonempty (x ∷ l)

data _≅_ : List ℕ -> List ℕ -> Set where
    cancel≅ : (n ∷ n ∷ []) ≅ []
    swap≅ : {k : ℕ} -> (suc k < n) -> (n ∷ k ∷ []) ≅ (k ∷ n ∷ [])
    braid≅ : ((suc n) ∷ n ∷ (suc n) ∷ []) ≅ (n ∷ (suc n) ∷ n ∷ [])
    respects=r : (l : List ℕ) -> (nl : nonempty l) -> {r r' lr lr' : List ℕ} -> (rr : r ≅ r') -> (deflr : lr ≡ l ++ r) -> (deflr' : lr' ≡ l ++ r') -> lr ≅ lr'
    respects=l : {l l' : List ℕ} -> (r : List ℕ) -> (nr : nonempty r) -> {lr l'r : List ℕ} -> (ll : l ≅ l') -> (deflr : lr ≡ l ++ r) -> (defl'r : l'r ≡ l' ++ r) -> lr ≅ l'r

data _≃_ : List ℕ -> List ℕ -> Set where
    refl : {m : List ℕ} -> m ≃ m
    trans≅ : {m1 m2 m3 : List ℕ} -> (m1 ≅ m2) -> (m2 ≃ m3) -> m1 ≃ m3

ext : {l l' : List ℕ} -> l ≅ l' -> l ≃ l'
ext p = trans≅ p refl

cancel : (n ∷ n ∷ []) ≃ []
cancel = ext cancel≅

swap : {k : ℕ} -> (suc k < n) -> (n ∷ k ∷ []) ≃ (k ∷ n ∷ [])
swap p = ext (swap≅ p)

braid : ((suc n) ∷ n ∷ (suc n) ∷ []) ≃ (n ∷ (suc n) ∷ n ∷ [])
braid = ext braid≅

trans : {m1 m2 m3 : List ℕ} -> (m1 ≃ m2) -> (m2 ≃ m3) -> m1 ≃ m3
trans refl p  = p
trans (trans≅ x q) p = trans≅ x (trans q p)

-- comm : {m1 m2 : List ℕ} -> (m1 ≃ m2) -> (m2 ≃ m1)
-- comm refl = refl
-- comm (trans≅ p x) = trans (comm x) (ext (comm≅ p))

respects-r : (l : List ℕ) -> (nonempty l) -> {r r' lr lr' : List ℕ} -> (r ≃ r') -> (lr ≡ l ++ r) -> (lr' ≡ l ++ r') -> lr ≃ lr'
respects-r l nl refl e1 e2 rewrite e1 rewrite e2 = refl
respects-r l nl (trans≅ {m2 = lhs} {m3 = rhs} rr' x) e1 e2 rewrite e1 rewrite e2 =
  let rec-l = respects=r l nl rr' e1 refl
      rec-r = respects-r l nl {lr = l ++ lhs} {lr' = l ++ rhs} x refl refl
  in  trans≅ (subst (λ y -> y ≅ (l ++ lhs)) e1 rec-l) rec-r

respects-l : {l l' : List ℕ} -> (r : List ℕ) -> (nonempty r) -> {lr l'r : List ℕ} -> (l ≃ l') -> (lr ≡ l ++ r) -> (l'r ≡ l' ++ r) -> lr ≃ l'r
respects-l r nr refl e1 e2 rewrite e1 rewrite e2 = refl
respects-l r nr (trans≅ {m2 = lhs} {m3 = rhs} rr' x) e1 e2 rewrite e1 rewrite e2 =
  let rec-l = respects=l r nr rr' refl refl
      rec-r = respects-l r nr {lr = lhs ++ r} {l'r = rhs ++ r} x refl refl
  in  trans≅ rec-l rec-r

module ≃-Reasoning where
    infix  1 ≃begin_
    infixr 2 _≃⟨⟩_ _≃⟨_⟩_
    infix  3 _≃∎

    ≃begin_ : ∀ {x y : List ℕ}
             → x ≃ y
               -----
             → x ≃ y
    ≃begin x≃y  =  x≃y

    _≃⟨⟩_ : ∀ (x : List ℕ) {y : List ℕ}
            → x ≃ y
              -----
            → x ≃ y
    x ≃⟨⟩ x≃y  =  x≃y

    _≃⟨_⟩_ : ∀ (x : List ℕ) {y z : List ℕ}
             → x ≃ y
             → y ≃ z
               -----
             → x ≃ z
    x ≃⟨ x≃y ⟩ y≃z  = trans x≃y y≃z

    _≃∎ : ∀ (x : List ℕ)
           -----
          → x ≃ x
    x ≃∎  =  refl

open ≃-Reasoning


++-respects-r : {l r r' : List ℕ} -> (nonempty l) -> (r ≃ r') -> (l ++ r) ≃ (l ++ r')
++-respects-r {l} {r} {r'} nl rr = respects-r l nl {r = r} {r' = r'} {lr = l ++ r} {lr' = l ++ r'} rr refl refl

++-respects-l : {l l' r : List ℕ} -> (nonempty r) -> (l ≃ l') -> (l ++ r) ≃ (l' ++ r)
++-respects-l {l} {l'} {r} nr ll = respects-l {l = l} {l' = l'} r nr {lr = l ++ r} {l'r = l' ++ r} ll refl refl

-- ++-respects : {l l' m m' : List ℕ} -> (l ≃ l') -> (m ≃ m') -> (l ++ m) ≃ (l' ++ m')
-- ++-respects {l} {l'} {m} {m'} ll mm =
--   ≃begin
--     l ++ m
--   ≃⟨ ++-respects-l ll ⟩
--     l' ++ m
--   ≃⟨ ++-respects-r mm ⟩
--      l' ++ m'
--   ≃∎

postulate
    ++-unit : l ++ [] ≡ l

refl≡ : {l l' : List ℕ} -> (l ≡ l') -> l ≃ l'
refl≡ refl = refl

++-unit2 : (l1 l2 : List ℕ) -> (l1 ++ (l2 ++ [])) ≡ (l1 ++ l2)
++-unit2 l1 l2 = let xx = ++-assoc l1 l2 []
                     yy = ++-unit {l1 ++ l2}
                 in ≡-trans (≡-sym xx) yy

∷-abs : (n ∷ l ≡ []) -> ⊥
∷-abs ()

∷-≡ : {n1 n2 : ℕ} -> {l1 l2 : List ℕ} -> (n1 ∷ l1 ≡ n2 ∷ l2) -> (n1 ≡ n2) × (l1 ≡ l2)
∷-≡ refl = refl , refl

∷-abs2 : {n1 n2 n3 : ℕ} -> {m1 m2 : List ℕ} -> (n1 ∷ m1 ++ n2 ∷ m2 ≡ n3 ∷ []) -> ⊥
∷-abs2 {n1} {n2} {n3} {m1} {m2} p =
  let nm1 = n1 ∷ m1
      nm2 = n2 ∷ m2
      lemma = length-++ nm1 {nm2}

      tx = ≤-reflexive (cong length p)
      tt : 2 ≤ 1
      tt = ≤-begin
             1 + 1
           ≤⟨ ≤-up2-r-+ {p = 1} {q = (length nm1)} {r = 1} (s≤s z≤n) ⟩
             (length nm1) + 1
           ≤⟨ ≤-up2-+ { 1 } {length nm2} { length nm1} (s≤s z≤n) ⟩
             (length nm1) + (length nm2)
           ≤⟨ ≤-reflexive (≡-sym lemma) ⟩
             length (n1 ∷ m1 ++ n2 ∷ m2)
           ≤⟨ ≤-reflexive (cong length p) ⟩
             {!!}
           ≤∎
  in ⊥-elim (1+n≰n tt)

≅-abs-l : {x : ℕ} -> (x ∷ []) ≅ [] -> ⊥
≅-abs-l (respects=r .(x ∷ l) (nonempty-l x l) p x₁ ())
≅-abs-l (respects=l {l' = []} .(x ∷ l) (nonempty-l x l) p x₁ ())
≅-abs-l (respects=l {l' = x₃ ∷ l'} .(x ∷ l) (nonempty-l x l) p x₁ ())

≅-abs-r : {x : ℕ} -> [] ≅ (x ∷ []) -> ⊥
≅-abs-r (respects=r .(x ∷ l) (nonempty-l x l) p () x₂)
≅-abs-r (respects=l {[]} .(x ∷ l) (nonempty-l x l) p () x₂)
≅-abs-r (respects=l {x₃ ∷ l₁} .(x ∷ l) (nonempty-l x l) p () x₂)


empty-reduction : (m : List ℕ) -> ([] ≅ m) -> ⊥
empty-reduction .(x ∷ l ++ _) (respects=r .(x ∷ l) (nonempty-l x l) p () refl)
empty-reduction .(_ ++ x ∷ l) (respects=l {[]} .(x ∷ l) (nonempty-l x l) p () refl)
empty-reduction .(_ ++ x ∷ l) (respects=l {x₂ ∷ l₁} .(x ∷ l) (nonempty-l x l) p () refl)

len-nonincreasing : (m1 m2 : List ℕ) -> (m1 ≅ m2) -> (length m2 ≤ length m1)
len-nonincreasing .(_ ∷ _ ∷ []) .[] cancel≅ = z≤n
len-nonincreasing .(_ ∷ _ ∷ []) .(_ ∷ _ ∷ []) (swap≅ x) = s≤s (s≤s z≤n)
len-nonincreasing .(suc _ ∷ _ ∷ suc _ ∷ []) .(_ ∷ suc _ ∷ _ ∷ []) braid≅ = s≤s (s≤s (s≤s z≤n))
len-nonincreasing m1 m2 (respects=r l nl {r} {r'} p e1 e2) rewrite e1 rewrite e2 rewrite ((length-++ l {r})) rewrite ((length-++ l {r'})) =
  let rec = (len-nonincreasing _ _ p)
  in  ≤-up2-+ rec
len-nonincreasing m1 m2 (respects=l {l} {l'} r nr p e1 e2) rewrite e1 rewrite e2 rewrite ((length-++ l {r})) rewrite (length-++ l' {r}) =
  let rec = (len-nonincreasing _ _ p)
  in  ≤-up2-r-+ rec

mod2 : ℕ -> Bool
mod2 0 = true
mod2 (suc n) with mod2 n
... | true = false
... | false = true

abs-bool : (true ≡ false) -> ⊥
abs-bool ()

mod2-+ : (n1 n2 : ℕ) -> mod2 (n1 + n2) ≡ not ((mod2 n1) xor (mod2 n2))
mod2-+ zero n2 = {!not-involutive!}
mod2-+ (suc n1) n2 = {!!}

len-mod2 : (m1 m2 : List ℕ) -> (m1 ≅ m2) -> (mod2 (length m1) ≡ mod2 (length m2))
len-mod2 .(_ ∷ _ ∷ []) .[] cancel≅ = refl
len-mod2 .(_ ∷ _ ∷ []) .(_ ∷ _ ∷ []) (swap≅ x) = refl
len-mod2 .(suc _ ∷ _ ∷ suc _ ∷ []) .(_ ∷ suc _ ∷ _ ∷ []) braid≅ = refl
len-mod2 m1 m2 (respects=r l nl {r} {r'} p e1 e2) rewrite e1 rewrite e2 rewrite ((length-++ l {r})) rewrite (length-++ l {r'}) =
  let rec = len-mod2 _ _ p
      q1 = mod2-+ (length l) (length r)
      q2 = mod2-+ (length l) (length r')
  in  ≡-trans q1 (≡-trans (cong (λ t -> not (mod2 (length l) xor t)) rec) (≡-sym q2))
len-mod2 m1 m2 (respects=l {l} {l'} r nr p e1 e2) rewrite e1 rewrite e2 rewrite ((length-++ l {r})) rewrite (length-++ l' {r}) =
  let rec = len-mod2 _ _ p
      q1 = mod2-+ (length l) (length r)
      q2 = mod2-+ (length l') (length r)
  in  ≡-trans q1 (≡-trans (cong (λ t → not (t xor (mod2 (length r)))) rec) (≡-sym q2))

-- length-3 : {n1 n2 n3 : ℕ} -> {m1 m2 : List ℕ} -> 3 ≤ length (n1 ∷ n2 ∷ m1 ++ n3 ∷ m2)
-- length-3 = {!!}

one-one-reduction : (n1 n2 : ℕ) -> ((n1 ∷ []) ≅ (n2 ∷ [])) -> n1 ≡ n2
one-one-reduction n1 n2 (respects=r [] nl p refl refl) = one-one-reduction _ _ p
one-one-reduction n1 .n1 (respects=r (.n1 ∷ []) nl p refl refl) = refl
one-one-reduction n1 n2 (respects=l {x₂ ∷ []} {x₃ ∷ []} [] nr p e1 e2) =
  let p1 , _ = ∷-≡ e1
      p2 , _ = ∷-≡ e2
      rec = one-one-reduction _ _ p
  in ≡-trans p1 (≡-trans rec (≡-sym p2))
one-one-reduction n1 n2 (respects=l {[]} (.n1 ∷ .[]) nl  p refl e) =
  let rec = empty-reduction _ p
  in  ⊥-elim rec
one-one-reduction n1 n2 (respects=l {x₃ ∷ l} (x₂ ∷ r) nr p e1 e2) = ⊥-elim (∷-abs2 (≡-sym e1))


-- two-two-reduction : (a b1 b2 : ℕ) -> ((a ∷ a ∷ []) ≅ (b1 ∷ b2 ∷ [])) -> (b1 ≡ b2) × (a ≡ b1)
-- two-two-reduction a .a .a (swap≅ x) = ⊥-elim (1+n≰n (≤-down x))
-- two-two-reduction a b1 b2 (respects=r [] p refl refl) = two-two-reduction _ _ _ p
-- two-two-reduction a .a b2 (respects=r (.a ∷ []) p refl refl) =
--   let rec = one-one-reduction _ _ p
--   in  rec , refl
-- two-two-reduction a .a .a (respects=r (.a ∷ .a ∷ []) p refl refl) = refl , refl
-- two-two-reduction a .a .a (respects=l {[]} {[]} .(a ∷ a ∷ []) p refl refl) = refl , refl
-- two-two-reduction a b1 b2 (respects=l {[]} {x ∷ x₁ ∷ []} .(a ∷ a ∷ []) p refl ())
-- two-two-reduction a b1 b2 (respects=l {[]} {x ∷ x₁ ∷ x₂ ∷ l'} .(a ∷ a ∷ []) p refl ())
-- two-two-reduction a b1 .a (respects=l {.a ∷ []} {.b1 ∷ []} .(a ∷ []) p refl refl) =
--   let rec = one-one-reduction _ _ p
--   in  ≡-sym rec , rec
-- two-two-reduction a b1 b2 (respects=l {.a ∷ []} {x ∷ x₁ ∷ []} .(a ∷ []) p refl ())
-- two-two-reduction a b1 b2 (respects=l {.a ∷ []} {x ∷ x₁ ∷ x₂ ∷ l'} .(a ∷ []) p refl ())
-- two-two-reduction a b1 b2 (respects=l {.a ∷ .a ∷ []} {.b1 ∷ .b2 ∷ []} .[] p refl refl) = two-two-reduction _ _ _ p


-- one-reduction : (m : List ℕ) -> ((n ∷ []) ≅ m) -> m ≡ (n ∷ [])
-- one-reduction [] (respects=r [] p refl refl) = one-reduction _ p
-- one-reduction {n} [] (respects=l {x₂ ∷ []} {[]} [] p e1 e2) = ⊥-elim (≅-abs-l p)
-- one-reduction [] (respects=l {l' = []} (x₂ ∷ r) p x ())
-- one-reduction [] (respects=l {l' = x₃ ∷ l'} (x₂ ∷ r) p x ())
-- one-reduction (.x₃ ∷ []) (respects=r (x₃ ∷ []) {[]} p refl refl) = refl
-- one-reduction (x ∷ []) (respects=r [] {x₃ ∷ .[]} p refl refl) = (one-reduction _ p)
-- one-reduction (x ∷ []) (respects=r (x₄ ∷ l) {x₃ ∷ r} p e1 e2) = ⊥-elim (∷-abs2 (≡-sym e1))
-- one-reduction {.x₂} (x ∷ []) (respects=l {x₂ ∷ []} {l' = .x ∷ []} [] p refl refl) = one-reduction _ p
-- one-reduction (.x₁ ∷ []) (respects=l {[]} {[]} (x₁ ∷ .[]) p refl refl) = refl
-- one-reduction (x ∷ []) (respects=l {[]} {x₂ ∷ l'} (x₁ ∷ .[]) p refl e2) = ⊥-elim (∷-abs2 (≡-sym e2))
-- one-reduction (x ∷ []) (respects=l {x₂ ∷ l} (x₁ ∷ r) p e1 e2) = ⊥-elim (∷-abs2 (≡-sym e1))
-- one-reduction (x ∷ x₁ ∷ m) p =
--   let rec = len-nonincreasing _ _ p
--   in  ⊥-elim (1+n≰n (≤-down-+ {2} {1} {length m} rec))


-- cancel-reduction : (m : List ℕ) -> ((n ∷ n ∷ []) ≅ m) -> (m ≡ []) ⊎ (m ≡ (n ∷ n ∷ []))
-- cancel-reduction [] p = inj₁ refl
-- cancel-reduction (x ∷ []) (respects=r [] p refl refl) = cancel-reduction _ p
-- cancel-reduction (x ∷ []) (respects=r (.x ∷ []) p refl refl) =
--   let r = one-reduction _ p
--   in  inj₁ (≡-sym r)
-- cancel-reduction (x ∷ []) (respects=l {[]} {x₁ ∷ []} .(_ ∷ _ ∷ []) p refl ())
-- cancel-reduction (x ∷ []) (respects=l {[]} {x₁ ∷ x₃ ∷ l'} .(_ ∷ _ ∷ []) p refl ())
-- cancel-reduction (x ∷ []) (respects=l {x₃ ∷ []} {[]} .(x₃ ∷ []) p refl e1) =
--   let r = one-reduction _ p
--   in  inj₁ (≡-sym (≡-trans r (≡-sym e1)))
-- cancel-reduction (x ∷ []) (respects=l {x₃ ∷ []} {x₁ ∷ l'} .(x₃ ∷ []) p refl e2) = ⊥-elim (∷-abs2 (≡-sym e2))
-- cancel-reduction (x ∷ []) (respects=l {x₃ ∷ .x₃ ∷ []} {.x ∷ []} .[] p refl refl) =
--   let rec = len-mod2 (x₃ ∷ x₃ ∷ []) (x ∷ []) p
--   in  ⊥-elim (abs-bool rec)
-- cancel-reduction (x ∷ .x ∷ []) (swap≅ q) = ⊥-elim (1+n≰n (≤-down q))
-- cancel-reduction (x ∷ x₁ ∷ []) (respects=r [] p refl refl) = cancel-reduction _ p
-- cancel-reduction (.x₄ ∷ x₁ ∷ []) (respects=r (x₄ ∷ []) p refl refl) rewrite one-one-reduction _ _ p = inj₂ refl
-- cancel-reduction (.x₄ ∷ .x₄ ∷ []) (respects=r (x₄ ∷ .x₄ ∷ []) p refl refl) = inj₂ refl
-- cancel-reduction (x ∷ x₁ ∷ []) (respects=l {x₂ ∷ .x₂ ∷ []} {.x ∷ .x₁ ∷ []} [] p refl refl) =
--   let rec1 , rec2 = two-two-reduction _ _ _ p

--       tt = x ∷ x ∷ [] ≡ x ∷ x ∷ []
--       tt = refl

--       step1 : x ∷ x₁ ∷ [] ≡ x ∷ x ∷ []
--       step1 = subst (λ t -> x ∷ t ∷ [] ≡ x ∷ x ∷ []) rec1 tt

--       step2 : x ∷ x₁ ∷ [] ≡ x₂ ∷ x₂ ∷ []
--       step2 = subst (λ t -> x ∷ x₁ ∷ [] ≡ t ∷ t ∷ []) (≡-sym rec2) step1
--   in  inj₂ step2
-- cancel-reduction (x ∷ x₁ ∷ []) (respects=l {[]} (x₄ ∷ .(x₄ ∷ [])) p refl e2) =
--   let rec = empty-reduction _ p
--       lemma = subst (λ t -> x ∷ x₁ ∷ [] ≡ t ++ x₄ ∷ x₄ ∷ []) rec e2
--   in  inj₂ lemma
-- cancel-reduction (x ∷ .x₅ ∷ []) (respects=l {x₅ ∷ []} {.x ∷ []} (.x₅ ∷ .[]) p refl refl) =
--   let rec = one-one-reduction _ _ p
--   in  inj₂ ((cong (λ t -> t ∷ x₅ ∷ []) (≡-sym rec)))
-- cancel-reduction (x ∷ x₁ ∷ []) (respects=l {x₅ ∷ []} {x₂ ∷ x₄ ∷ l'} (.x₅ ∷ .[]) p refl x₃) = ⊥-elim {!!} -- lengths are wrong, tedious
-- cancel-reduction (x ∷ x₁ ∷ []) (respects=l {x₅ ∷ x₆ ∷ l} {l'} (x₄ ∷ r) p x₂ x₃) = ⊥-elim {!!} -- lengths are wrong, tedious
-- cancel-reduction (x ∷ x₁ ∷ x₂ ∷ m) p =
--   let rec = len-nonincreasing _ _ p
--   in  ⊥-elim (1+n≰n (≤-down-+ rec))


-- diamond-separate : {l r l' r' ml mr : List ℕ} -> (ml ≡ l' ++ r) -> (mr ≡ l ++ r') -> (l ≅ l') -> (r ≅ r') -> (ml ≅ (l' ++ r')) × (mr ≅ (l' ++ r'))
-- diamond-separate {l' = l'} {r' = r'} mle mre lp rp rewrite mle rewrite mre = respects=r l' rp refl refl , respects=l r' lp refl refl

-- -- diamond-separate : {l r l' r' ml mr : List ℕ} -> (ml ≡ l' ++ r) -> (mr ≡ l ++ r') -> (l ≅ l') -> (r ≅ r') -> (ml ≅ (l' ++ r')) × (mr ≅ (l' ++ r'))
-- -- diamond-separate {l' = l'} {r' = r'} mle mre lp rp rewrite mle rewrite mre = respects=r l' rp refl refl , respects=l r' lp refl refl


-- diamond : (m1 m2 m3 : List ℕ) -> (m1 ≅ m2) -> (m1 ≅ m3) -> ∃ (λ m -> (m2 ≃ m) × (m3 ≃ m))
-- diamond m1 m2 m3 p q = {!!}
