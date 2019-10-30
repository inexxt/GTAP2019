{-# OPTIONS --without-K #-}
module Compact where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)

open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans)
open import Function

open import Arithmetic hiding (n)
open import Lists
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)


variable
  n : ℕ
  l : List ℕ

data _≅_ : List ℕ -> List ℕ -> Set where
    cancel≅ : (l r m mf : List ℕ) -> (defm : m ≡ l ++ n ∷ n ∷ r) -> (defmf : mf ≡ l ++ r) -> (m ≅ mf)
    swap≅ : {k : ℕ} -> (suc k < n) ->  (l r m mf : List ℕ) -> (defm : m ≡ l ++ n ∷ k ∷ r) -> (defmf : mf ≡ l ++ k ∷ n ∷ r) -> (m ≅ mf)
    long≅ : (k : ℕ) -> (l r m mf : List ℕ) -> (defm : m ≡ l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) -> (defmf : mf ≡ l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r) -> (m ≅ mf)

data _≅*_ : List ℕ -> List ℕ -> Set where
    refl : {m : List ℕ} -> m ≅* m
    trans≅ : {m1 m2 m3 : List ℕ} -> (m1 ≅ m2) -> (m2 ≅* m3) -> m1 ≅* m3

cancel-c : (l r : List ℕ) -> (l ++ n ∷ n ∷ r) ≅ (l ++ r)
cancel-c {n} = λ l r → cancel≅ l r (l ++ n ∷ n ∷ r) (l ++ r) refl refl

swap-c : {k : ℕ} -> (pk : suc k < n) ->  (l r : List ℕ) -> (l ++ n ∷ k ∷ r) ≅ (l ++ k ∷ n ∷ r)
swap-c {k} pk l r = swap≅ pk l r (l ++ k ∷ _ ∷ r) (l ++ _ ∷ k ∷ r) refl refl

long-c : (k : ℕ) -> (l r : List ℕ) -> (l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) ≅ (l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r)
long-c k l r = long≅ k l r _ _ refl refl

ext : {l l' : List ℕ} -> l ≅ l' -> l ≅* l'
ext p = trans≅ p refl

cancel : (l r : List ℕ) -> (l ++ n ∷ n ∷ r) ≅* (l ++ r)
cancel {n} = λ l r →
             trans≅ (cancel≅ l r (l ++ n ∷ n ∷ r) (l ++ r) refl refl) refl

swap : {k : ℕ} -> (pk : suc k < n) ->  (l r : List ℕ) -> (l ++ n ∷ k ∷ r) ≅* (l ++ k ∷ n ∷ r)
swap {k} pk l r = trans≅ (swap≅ pk l r (l ++ k ∷ _ ∷ r) (l ++ _ ∷ k ∷ r) refl refl)
                    refl

long : (k : ℕ) -> (l r : List ℕ) -> (l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) ≅* (l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r)
long k l r = ext (long≅ k l r _ _ refl refl)

braid : (l r : List ℕ) -> (l ++ suc n ∷ n ∷ suc n ∷ r) ≅* (l ++ n ∷ suc n ∷ n ∷ r)
braid {n} l r = long {n} 0 l r

trans : {m1 m2 m3 : List ℕ} -> (m1 ≅* m2) -> (m2 ≅* m3) -> m1 ≅* m3
trans refl p  = p
trans (trans≅ x q) p = trans≅ x (trans q p)

l++≅ : (m1 m2 l : List ℕ) -> (m1 ≅ m2) -> ((l ++ m1) ≅ (l ++ m2))
l++≅ m1 m2 l (cancel≅ l₁ r .m1 .m2 defm defmf) =  cancel≅ (l ++ l₁) r _ _ (≡-trans (start+end refl defm) (≡-sym (++-assoc l l₁ _))) ((≡-trans (start+end refl defmf) (≡-sym (++-assoc l l₁ _))))
l++≅ m1 m2 l (swap≅ x l₁ r .m1 .m2 defm defmf) =  swap≅ x (l ++ l₁) r _ _ (≡-trans (start+end refl defm) (≡-sym (++-assoc l l₁ _))) ((≡-trans (start+end refl defmf) (≡-sym (++-assoc l l₁ _))))
l++≅ m1 m2 l (long≅ k l₁ r .m1 .m2 defm defmf) =  long≅ k (l ++ l₁) r _ _ (≡-trans (start+end refl defm) (≡-sym (++-assoc l l₁ _))) ((≡-trans (start+end refl defmf) (≡-sym (++-assoc l l₁ _))))

l++ : (l : List ℕ) -> {m1 m2 : List ℕ} -> (m1 ≅* m2) -> ((l ++ m1) ≅* (l ++ m2))
l++ l refl = refl
l++ l (trans≅ x p) = trans≅ (l++≅ _ _ l x) ((l++ l p))

++r≅ : (m1 m2 r : List ℕ) -> (m1 ≅ m2) -> ((m1 ++ r) ≅ (m2 ++ r))
++r≅ m1 m2 r (cancel≅ l r₁ .m1 .m2 defm defmf) = cancel≅ l (r₁ ++ r)  _ _  (≡-trans (start+end defm refl) (++-assoc l _ r)) ((≡-trans (start+end defmf refl) (++-assoc l _ r)))
++r≅ m1 m2 r (swap≅ x l r₁ .m1 .m2 defm defmf) = swap≅ x l (r₁ ++ r)  _ _  (≡-trans (start+end defm refl) (++-assoc l _ r)) ((≡-trans (start+end defmf refl) (++-assoc l _ r)))
++r≅ m1 m2 r (long≅ k l r₁ .m1 .m2 defm defmf) = long≅ k l (r₁ ++ r)  _ _
  (≡-trans (start+end defm refl) (≡-trans (++-assoc l _ r) (start+end (refl {x = l}) (head+tail refl (head+tail refl (++-assoc (_ ↓ k) _ r))))))
  ((≡-trans (start+end defmf refl) (≡-trans (++-assoc l _ r) (start+end (refl {x = l}) (head+tail refl (head+tail refl (head+tail refl (++-assoc _ r₁ r))))))))

++r : {m1 m2 : List ℕ} -> (r : List ℕ) -> (m1 ≅* m2) -> ((m1 ++ r) ≅* (m2 ++ r))
++r r refl = refl
++r r (trans≅ x p) = trans≅ (++r≅ _ _ r x) (++r r p)

refl≡ : {l l' : List ℕ} -> (l ≡ l') -> l ≅* l'
refl≡ refl = refl

abs-suc : {A : Set} -> suc n < n -> A
abs-suc {n} p = ⊥-elim (1+n≰n (≤-down p))

module ≅*-Reasoning where
    infix  1 ≅*begin_
    infixr 2 _≅*⟨⟩_ _≅*⟨_⟩_
    infix  3 _≅*∎

    ≅*begin_ : ∀ {x y : List ℕ}
             → x ≅* y
               -----
             → x ≅* y
    ≅*begin x≅*y  =  x≅*y

    _≅*⟨⟩_ : ∀ (x : List ℕ) {y : List ℕ}
            → x ≅* y
              -----
            → x ≅* y
    x ≅*⟨⟩ x≅*y  =  x≅*y

    _≅*⟨_⟩_ : ∀ (x : List ℕ) {y z : List ℕ}
             → x ≅* y
             → y ≅* z
               -----
             → x ≅* z
    x ≅*⟨ x≅*y ⟩ y≅*z  = trans x≅*y y≅*z

    _≅*∎ : ∀ (x : List ℕ)
           -----
          → x ≅* x
    x ≅*∎  =  refl

open ≅*-Reasoning

≅-abs-l : {x : ℕ} -> (x ∷ []) ≅ [] -> ⊥
≅-abs-l (cancel≅ [] r .(_ ∷ []) .[] () defmf)
≅-abs-l (cancel≅ (x ∷ []) r .(_ ∷ []) .[] () defmf)
≅-abs-l (cancel≅ (x ∷ x₁ ∷ l) r .(_ ∷ []) .[] () defmf)
≅-abs-l (swap≅ x [] r .(_ ∷ []) .[] () defmf)
≅-abs-l (swap≅ x (x₁ ∷ []) r .(_ ∷ []) .[] () defmf)
≅-abs-l (swap≅ x (x₁ ∷ x₂ ∷ l) r .(_ ∷ []) .[] () defmf)
≅-abs-l (long≅ k [] r .(_ ∷ []) .[] defm ())
≅-abs-l (long≅ k (x ∷ l) r .(_ ∷ []) .[] defm ())

≅-abs-r : {x : ℕ} -> [] ≅ (x ∷ []) -> ⊥
≅-abs-r (cancel≅ [] r .[] .(_ ∷ []) () defmf)
≅-abs-r (cancel≅ (x ∷ l) r .[] .(_ ∷ []) () defmf)
≅-abs-r (swap≅ x [] r .[] .(_ ∷ []) () defmf)
≅-abs-r (swap≅ x (x₁ ∷ l) r .[] .(_ ∷ []) () defmf)
≅-abs-r (long≅ k [] r .[] .(_ ∷ []) () defmf)
≅-abs-r (long≅ k (x ∷ l) r .[] .(_ ∷ []) () defmf)
--
empty-reduction : {m : List ℕ} -> ([] ≅ m) -> ⊥
empty-reduction (cancel≅ [] r .[] _ () defmf)
empty-reduction (cancel≅ (x ∷ l) r .[] _ () defmf)
empty-reduction (swap≅ x [] r .[] _ () defmf)
empty-reduction (swap≅ x (x₁ ∷ l) r .[] _ () defmf)
empty-reduction (long≅ k [] r .[] mf () defmf)
empty-reduction (long≅ k (x ∷ l) r .[] mf () defmf)

one-reduction : {x : ℕ} -> {m : List ℕ} -> ([ x ] ≅ m) -> ⊥
one-reduction {x} (cancel≅ (x₁ ∷ []) r .(x ∷ []) mf () defmf)
one-reduction {x} (cancel≅ (x₁ ∷ x₂ ∷ l) r .(x ∷ []) mf () defmf)
one-reduction {x} (swap≅ x₁ (x₂ ∷ []) r .(x ∷ []) mf () defmf)
one-reduction {x} (swap≅ x₁ (x₂ ∷ x₃ ∷ l) r .(x ∷ []) mf () defmf)
one-reduction {x} (long≅ k (x₁ ∷ []) r .(x ∷ []) mf () defmf)
one-reduction {x} (long≅ k (x₁ ∷ x₂ ∷ l) r .(x ∷ []) mf () defmf)

mod2 : ℕ -> Bool
mod2 0 = true
mod2 (suc n) with mod2 n
... | true = false
... | false = true

abs-bool : (true ≡ false) -> ⊥
abs-bool ()

-- postulate
--   -- these are proved for the previous representation, it's possible to transport them to here
--   mod2-+ : (n1 n2 : ℕ) -> mod2 (n1 + n2) ≡ not ((mod2 n1) xor (mod2 n2))
--   len-mod2≅ : (m1 m2 : List ℕ) -> (m1 ≅ m2) -> (mod2 (length m1) ≡ mod2 (length m2))
--   len-nonincreasing≅ : (m1 m2 : List ℕ) -> (m1 ≅ m2) -> (length m2 ≤ length m1)
--   diamond-separate : {l r l' r' ml mr : List ℕ} -> (ml ≡ l' ++ r) -> (mr ≡ l ++ r') -> (l ≅ l') -> (r ≅ r') -> (ml ≅ (l' ++ r')) × (mr ≅ (l' ++ r'))
--
--   -- this ones are a little different (just because the new ≅ doesnt have reflexivity)
--   one-one-reduction : (n1 n2 : ℕ) -> ((n1 ∷ []) ≅* (n2 ∷ [])) -> n1 ≡ n2
--   two-two-reduction : (a b1 b2 : ℕ) -> ((a ∷ a ∷ []) ≅* (b1 ∷ b2 ∷ [])) -> (b1 ≡ b2) × (a ≡ b1)
--   cancel-reduction : (m : List ℕ) -> ((n ∷ n ∷ []) ≅* m) -> (m ≡ []) ⊎ (m ≡ (n ∷ n ∷ []))
--   -- one-reduction : (m : List ℕ) -> ((n ∷ []) ≅* m) -> m ≡ (n ∷ [])
--
--   -- these ones are extension to ≅*
--   len-mod2 : (m1 m2 : List ℕ) -> (m1 ≅* m2) -> (mod2 (length m1) ≡ mod2 (length m2))
--   len-nonincreasing : (m1 m2 : List ℕ) -> (m1 ≅* m2) -> (length m2 ≤ length m1)


long-swap : (n1 n2 : ℕ) -> (k : ℕ) -> (k + n1 < n2) -> (n2 ∷ (n1 ↓ k)) ≅* ((n1 ↓ k) ++ [ n2 ])
long-swap n1 n2 zero p = refl
long-swap n1 n2 (suc k) p =
  let rec = long-swap n1 n2 k (≤-down p)
  in  trans (swap p [] _) (l++ [ k + n1 ] rec)

long-swap< : (n1 n2 : ℕ) -> (k : ℕ) -> (suc n1 < n2) -> ((n2 ↓ k) ++ [ n1 ]) ≅* (n1 ∷ (n2 ↓ k))
long-swap< n1 n2 zero p = refl
long-swap< n1 n2 (suc k) p =
  let rec = long-swap< n1 n2 k p
  in  trans (l++ (k + n2 ∷ []) rec) (swap (≤-up-+ p) [] _)

long-swap-lr : (n1 n2 k : ℕ) -> (l r : List ℕ) -> (k + n1 < n2) -> (l ++ (n2 ∷ (n1 ↓ k)) ++ r) ≅* (l ++ (n1 ↓ k) ++ n2 ∷ r)
long-swap-lr n1 n2 k l r p =
  let lemma = (++r r (long-swap n1 n2 k p))
  in  l++ l (trans lemma (refl≡ (++-assoc _ [ _ ] r)))

long-swap<-lr : (n1 n2 k : ℕ) -> (l r : List ℕ) -> (suc n1 < n2) -> (l ++ (n2 ↓ k) ++ n1 ∷ r) ≅* (l ++ n1 ∷ (n2 ↓ k) ++ r)
long-swap<-lr n1 n2 k l r p =
  let lemma = (++r r (long-swap< n1 n2 k p))
  in  l++ l (trans (refl≡ (≡-sym (++-assoc (n2 ↓ k) (n1 ∷ []) r))) lemma)

short-swap : {n k t tl tr : ℕ} -> (tr + n ≡ t) -> ((tl + suc t) ≡ suc (k + n)) -> (n ↓ (2 + k) ++ [ suc t ]) ≅* (t ∷ (n ↓ (2 + k)))
short-swap {n} {k} {t} {tl} {tr} ptn ptkn rewrite (≡-sym ptn) =
  let pp = ≡-down-r-+ {r = n} (≡-trans (+-assoc tl (1 + tr) n) (≡-trans ptkn (≡-sym (+-assoc 1 k n))))
      k=tl+tr : 2 + k ≡ tl + (2 + tr)
      k=tl+tr = ≡-trans (≡-sym (cong suc pp)) (≡-sym (+-three-assoc {tl} {1} {1 + tr}))

      lemma : n ↓ (2 + k) ≡ (n + (2 + tr)) ↓ tl ++ (n ↓ (2 + tr))
      lemma = ≡-trans (cong (λ e -> n ↓ e) k=tl+tr) (↓-+ n tl (2 + tr))

      red =
        ≅*begin
          suc (k + n) ∷ k + n ∷ (n ↓ k) ++ suc (tr + n) ∷ []
        ≅*⟨ refl≡ (start+end lemma refl) ⟩
          (((n + (2 + tr)) ↓ tl) ++ (n ↓ (2 + tr))) ++ suc (tr + n) ∷ []
        ≅*⟨ refl≡ (++-assoc ((n + suc (suc tr)) ↓ tl) _ (suc (tr + n) ∷ []) ) ⟩
          ((n + (2 + tr)) ↓ tl) ++ (n ↓ (2 + tr)) ++ suc (tr + n) ∷ []
        ≅*⟨ long _ (((n + (2 + tr)) ↓ tl)) [] ⟩
          ((n + (2 + tr)) ↓ tl) ++ (tr + n) ∷ (n ↓ (2 + tr)) ++ []
        ≅*⟨ long-swap<-lr (tr + n) (n + (2 + tr)) tl [] (suc (tr + n) ∷ tr + n ∷ (n ↓ tr) ++ []) (≤-reflexive (≡-trans (≡-sym (+-assoc 2 tr n)) (+-comm (suc (suc tr)) n))) ⟩
          (tr + n) ∷ ((n + (2 + tr)) ↓ tl) ++ (n ↓ (2 + tr)) ++ []
        ≅*⟨ refl≡ (start+end (refl {x = (tr + n) ∷ ((n + (2 + tr)) ↓ tl)}) (++-unit {(n ↓ (2 + tr))})) ⟩
          (tr + n) ∷ ((n + (2 + tr)) ↓ tl) ++ (n ↓ (2 + tr))
        ≅*⟨ refl≡ (head+tail refl (≡-sym (↓-+ n tl (2 + tr)))) ⟩
          tr + n ∷ (n ↓ (tl + suc (suc tr)))
        ≅*⟨ refl≡ (head+tail refl (cong (λ e -> n ↓ e) (≡-sym k=tl+tr))) ⟩
          tr + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)
        ≅*∎
  in  red

short-swap-l : {n k t : ℕ} -> (l : List ℕ) -> (n ≤ t) -> (suc t ≤ suc (k + n)) -> (l ++ n ↓ (2 + k) ++ [ suc t ]) ≅* (l ++ t ∷ (n ↓ (2 + k)))
short-swap-l {n} {k} {t} l pnt ptkn =
  let tr , tr-p = ≤-∃ n t pnt
      tl , tl-p = ≤-∃ (suc t) (suc k + n) ptkn
      lemma = (short-swap {n} {k} {t} {tl} {tr} tr-p tl-p)
  in  l++ l lemma

short-swap-lr : {n k t : ℕ} -> (l r : List ℕ) -> (n ≤ t) -> (suc t ≤ suc (k + n)) -> ((l ++ n ↓ (2 + k)) ++ suc t ∷ r) ≅* ((l ++ t ∷ (n ↓ (2 + k))) ++ r)
short-swap-lr {n} {k} {t} l r pnt ptkn =
  let tr , tr-p = ≤-∃ n t pnt
      tl , tl-p = ≤-∃ (suc t) (suc k + n) ptkn
      lemma = ++r r (l++ l (short-swap {n} {k} {t} {tl} {tr} tr-p tl-p))
  in  trans (refl≡ (≡-sym (≡-trans (start+end (≡-sym (++-assoc l _ [ _ ])) (refl {x = r})) (++-assoc _ [ _ ] r)))) lemma

long->-long : (n k n1 k1 : ℕ) -> (k + n ≡ suc (k1 + n1)) -> (k1 < k) -> ((n ↓ (2 + k)) ++ ((1 + n1) ↓ (2 + k1))) ≅* ((n1 ↓ (2 + k1)) ++ (n ↓ (2 + k)))
long->-long n zero n1 k1 pp ()
long->-long n (suc k) n1 zero pp pk rewrite (≡-sym pp)  =
  ≅*begin
    (n ↓ (3 + k)) ++ (2 + (k + n)) ∷ (1 + (k + n)) ∷ []
  ≅*⟨ long (1 + k) [] [ _ ] ⟩
    (1 + (k + n)) ∷ (n ↓ (3 + k)) ++ (1 + (k + n)) ∷ []
  ≅*⟨ short-swap-lr {n = n} {k = (1 + k)} [ _ ] [] (≤-up-+ (≤-reflexive refl)) (≤-up (≤-reflexive refl)) ⟩
    _
  ≅*⟨ refl≡ ++-unit ⟩
    _
  ≅*⟨ refl≡ (head+tail refl (head+tail (≡-down2 pp) refl)) ⟩
    _
  ≅*∎
long->-long n (suc k) n1 (suc k1) pp pk =
  let rec = long->-long n k n1 k1 (≡-down2 pp) (≤-down2 pk)
  in
    ≅*begin
      (n ↓ (3 + k)) ++ ((1 + n1) ↓ (3 + k1))
    ≅*⟨ short-swap-lr {n = n} {k = (1 + k)} [] (((1 + n1) ↓ (2 + k1))) (≤-trans (≤-trans (≤-up (≤-up-+ rrr)) (≤-reflexive pp)) (≤-reflexive (≡-sym (+-three-assoc {1 + k1} {1} {_})))) (≤-reflexive (cong suc (≡-trans (+-three-assoc {1 + k1} {1} {_}) (≡-sym pp)))) ⟩
      _ ∷ _ ∷ (n ↓ (2 + k)) ++ ((1 + n1) ↓ (2 + k1))
    ≅*⟨ l++ (_ ∷ _ ∷ []) rec ⟩
      _ ∷ _ ∷ (n1 ↓ (2 + k1)) ++ (n ↓ (2 + k))
    ≅*⟨ long-swap-lr n1 (suc (suc (k + n))) (suc (suc k1)) [ _ ] ((n ↓ (2 + k))) (≤-reflexive (cong suc (≡-sym pp))) ⟩
      _ ∷ (n1 ↓ (2 + k1)) ++ _ ∷ (n ↓ (2 + k))
    ≅*⟨ refl≡ (head+tail (+-three-assoc {1 + k1} {1} {n1}) refl) ⟩
      (n1 ↓ (3 + k1)) ++ (n ↓ (3 + k))
    ≅*∎

long-≤-long : (n k n1 k1 : ℕ) -> (k + n ≡ k1 + n1) -> (k ≤ k1) -> ((n ↓ (2 + k)) ++ (n1 ↓ (2 + k1))) ≅* ((n1 ↓ (1 + k1)) ++ ((1 + n) ↓ (1 + k)))
long-≤-long n zero n1 k1 pp pk rewrite pp rewrite (+-three-assoc {k1} {1} {n1}) =
  ≅*begin
    _
  ≅*⟨ braid [] _ ⟩
    _
  ≅*⟨ cancel (_ ∷ _ ∷ [])  _ ⟩
    _
  ≅*⟨ refl≡ (≡-sym (++-unit)) ⟩
    _
  ≅*⟨ long-swap-lr n1 (1 + k1 + n1) k1 [ _ ] [] (≤-reflexive refl) ⟩
    _
  ≅*∎
long-≤-long n (suc k) n1 zero pp ()
long-≤-long n (suc k) n1 (suc k1) pp pk =
  let rec = long-≤-long n k n1 k1 (≡-down2 pp) (≤-down2 pk)
      lemma = (≡-sym (cong (λ e -> 2 + e) (≡-trans (+-three-assoc {k} {1} {n}) (≡-trans pp (≡-sym (+-three-assoc {k1} {1} {n1}))))))
  in
    ≅*begin
      (n ↓ (3 + k)) ++ 2 + k1 + n1 ∷ (n1 ↓ (2 + k1))
    ≅*⟨ short-swap-lr {n = n} [] ((n1 ↓ (2 + k1))) (≤-trans (≤-up (≤-up-+ (≤-reflexive refl))) (≤-reflexive pp)) (s≤s (≤-reflexive (≡-sym pp))) ⟩
       1 + k1 + n1 ∷ (2 + k + n) ∷ (n ↓ (2 + k)) ++ (n1 ↓ (2 + k1))
    ≅*⟨ refl≡ (++-assoc (_ ∷ _ ∷ []) ((n ↓ (2 + k))) _) ⟩
      1 + k1 + n1 ∷ (2 + k + n) ∷ [] ++ (((n ↓ (2 + k)) ++ (n1 ↓ (2 + k1))))
    ≅*⟨ l++ (_ ∷ _ ∷ []) rec ⟩
      1 + k1 + n1 ∷ (2 + k + n) ∷ [] ++ (((n1 ↓ (1 + k1)) ++ ((1 + n) ↓ (1 + k))))
    ≅*⟨ refl≡ (≡-sym (++-assoc (_ ∷ _ ∷ []) (n1 ↓ (1 + k1)) _)) ⟩
      _
    ≅*⟨ long-swap-lr n1 (suc (suc (k + n))) (suc k1) [ _ ] ((1 + n) ↓ (1 + k)) (≤-reflexive (cong suc (≡-sym pp))) ⟩
      1 + k1 + n1 ∷ (n1 ↓ (1 + k1)) ++ (2 + k + n) ∷ ((1 + n) ↓ (1 + k))
    ≅*⟨ refl≡ (start+end (refl {x = 1 + k1 + n1 ∷ (n1 ↓ (1 + k1))})  (head+tail (≡-sym (+-three-assoc {1 + k} {1} {n})) refl)) ⟩
      _
    ≅*∎
