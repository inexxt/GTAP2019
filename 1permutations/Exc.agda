module Exc where
    data _×_ : Set -> Set -> Set where
        _,_ : {A : Set} -> {B : Set} -> (a : A) -> (b : B) -> (A × B)

    swap : {A : Set} -> {B : Set} -> (A × B) -> (B × A)
    swap (a , b) = (b , a)

    swap_lemma : {A : Set} -> {B : Set} -> ()

    order : {n : Nat} -> (eq : (fin n) ≈ (fin n)) -> Σ Nat (λ n -> ((comp n (eq .f)) ≣ id)) 
    order n = order' (fact n) n

    order' k n = if (eq .f
