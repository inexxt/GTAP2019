module Exc where
    data _×_ : Set -> Set -> Set where
        _,_ : {A : Set} -> {B : Set} -> (a : A) -> (b : B) -> (A × B)

    swap : {A : Set} -> {B : Set} -> (A × B) -> (B × A)
    swap (a , b) = (b , a)

    swap_lemma : {A : Set} -> {B : Set} -> ()
