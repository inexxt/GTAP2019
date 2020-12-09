module _ where

open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Fin using (Fin)
open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

---------------
--- Pi lang ---
---------------

data Pi-type : Set where
  -- Here we define Pi types
  
data _<->_ : Pi-type -> Pi-type -> Set where
  -- Here we define Pi 1-combinators
 
data _<=>_ : {A B C D : Pi-type} -> (A <-> B) -> (C <-> D) -> Set where
  -- Here we define Pi 2-combinators


---------------
--- Stage 1 ---
---------------
PiFin : ℕ -> Pi-type

data Normed1comb : {n : ℕ} -> (PiFin n) <-> (PiFin n) -> Set where
  -- this is a (technical) property of 1-combinators that tells us that it is composed only from swaps, assocs and identities
  -- for us to be able to represent it as an abstract "list of swaps"

Pi-norm  : {A B : Pi-type} -> (c : A <-> B) -> Σ ℕ (λ n -> Σ ((PiFin n) <-> (PiFin n)) (λ cc -> (Normed1comb cc) × (c <=> cc)))

---------------
--- Stage 2 ---
---------------
Pi-sseq : {n : ℕ} -> (c : PiFin n <-> PiFin n) -> List (Fin n)
sseq-Pi : {n : ℕ} -> List (Fin n) -> (PiFin n <-> PiFin n)

Pi-sseq-Pi : {n : ℕ} -> (Pi-sseq {n}) ∘ (sseq-Pi {n}) ≡ id
sseq-Pi-sseq : {n : ℕ} -> (sseq-Pi {n}) ∘ (Pi-sseq {n}) ≡ id


---------------
--- Stage 3 ---
---------------

data _≃_ : {n : ℕ} -> List (Fin n) -> List (Fin n) -> Set where
  -- This is the main part - the equivalence relation over lists of swaps that tells us if they represent the same permutation
  -- It is implemented as a reduction of such lists to a canonical form

data _≈_ : Set -> Set -> Set where
  -- this is just functions equivalence
  bijection : {A B : Set} -> (f : A -> B) -> (g : B -> A) -> (f ∘ g ≡ id) -> (g ∘ f ≡ id) -> (A ≈ B)

data Lehmer : ℕ -> Set where
  LZ : Lehmer 0
  LS : {n : ℕ} -> (l : Lehmer n) -> {r : ℕ} -> (r ≤ suc n) -> Lehmer (suc n)

immerse : {n : ℕ} -> Lehmer n -> List (Fin n)
immerse-inj : {n : ℕ} -> (l1 l2 : Lehmer n) -> immerse l1 ≡ immerse l2 -> l1 ≡ l2

sseq-norm : {n : ℕ} -> (l : List (Fin n)) -> Σ (Lehmer n) (λ cl -> l ≃ immerse cl)


---------------
--- Stage 4 ---
---------------

eval  : {n : ℕ} -> (Lehmer n) -> (Fin n ≈ Fin n)
fquote : {n : ℕ} -> (Fin n ≈ Fin n) -> (Lehmer n)

eval∘fquote : {n : ℕ} -> (eval {n}) ∘ (fquote {n}) ≡ id
fquote∘eval : {n : ℕ} -> (fquote {n}) ∘ (eval {n}) ≡ id

---------------
---   All   ---
---------------

Pi-eval : Σ (Pi-type × Pi-type) (λ (A , B) -> (A <-> B)) -> Σ ℕ (λ n -> (Fin n) ≈ (Fin n))
Pi-eval (a , c) =
  let x = proj₁ (proj₂ (Pi-norm c))
      nx = proj₁ (Pi-norm c)
  in  (nx , eval (proj₁ (sseq-norm (Pi-sseq x))))

fquote-Pi : Σ ℕ (λ n -> (Fin n) ≈ (Fin n)) -> Σ (Pi-type × Pi-type) (λ (A , B) -> (A <-> B))
fquote-Pi (n , b) =
  let x = sseq-Pi (immerse (fquote b))
  in  (PiFin n , PiFin n) , x

fquote-eval : Pi-eval ∘ fquote-Pi ≡ id
eval-fquote : {A B : Pi-type} -> (c : A <-> B) -> (proj₂ ∘ fquote-Pi ∘ Pi-eval) ((A , B) , c) <=> c
