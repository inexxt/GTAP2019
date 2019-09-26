Agda standard library:

 - agda-stdlib/src/Data/Fin/Permutation.agda
  - Definition as invertible functions Fin n -> Fin m
  - Defined transpositions, compositions, reverses
  - Defined remove : Perm n+1 m+1 -> k -> Perm n m
 
 - agda-stdlib/src/Data/List/Relation/Binary/Permutation/Homogeneous.agda
  - Definition as relation on Setoid, as in Coq:
  ```agda
  data Permutation {A : Set a} (R : Rel A r) : Rel (List A) (a ⊔ r) where
    refl : Permutation x x
    prep : x == y  -> Permutation xs ys -> Permutation (x:xs) (y:ys)
  swap : x == x' -> y == y' -> Permutation xs ys -> Permutation x :: y :: xs   -> Permutation y' :: x' :: ys
    trans : Permutation xs ys -> Permutation ys zs -> Permutation xs zs
  ```
  - proof that it is an equivalence relation (isEquivalence)
 
 - agda-stdlib/src/Data/List/Relation/Binary/Permutation/Setoid.agda
  - Imports from the above
  - introduces nice arrows
  - does some strange stuff(TODO?) with equality reasoning
   - explained in README/Data/List.agda , useful for easier proofs
 
 - agda-stdlib/src/Data/List/Relation/Binary/Permutation/Propositional.agda
  - the same as in setoid, but without considering setoid relation
  - apparently easier to work, if one doesn't need to operate on a setoid
 
 - agda-stdlib/src/Data/List/Relation/Binary/Permutation/Setoid/Properties.agda
  - Some useful properties of <-> and ++
  - strange stuff with "respecting predicates" (TODO?)

  - left and right identities of ++ wrt ↭
  - ↭ commutes with ++ 
  - ↭ is associative with ++ 
  - IsCommutativeMonoid _↭_ _++_ []
  
  - mapping preserves permutations
  - shift  : xs ++ [ v ] ++ ys ↭ w ∷ xs ++ ys 
  
  - inject : ws ++ [ v ] ++ xs ↭ ys ++ [ v ] ++ zs
  - shifts : xs ++ ys ++ zs ↭ ys ++ xs ++ zs
  - zoom :  xs ↭ ys → h ++ xs ++ t ↭ h ++ ys ++ t

 - agda-stdlib/src/Data/List/Relation/Binary/Permutation/Propositional/Properties.agda
  - the same as in Setoid properties, but with additional ones
  - drop-mid:  ws ++ [ x ] ++ ys ≡ xs ++ [ x ] ++ zs → ws ++ ys ↭ xs ++ zs
  - shift, inject, zoom
  - relation with "bag"
 
 - Generally, there's nothing in the mailing lists that concerns Fin permutations and Relation.Binary.Permutation
  - I should ask them (but first ask prof. Sabry)

 - http://lacim.uqam.ca/wp-content/uploads/Publications/29.pdf
  - This describes the algorithm
  - In particular, claims that the normal form is like the ones given by the insertion sort (1.1.5)
  - (Theorem 1.1.2) We may pass from any reduced factorization to any other of a given permutation σ by a sequence of applications of identities 1.1.7 2) & 3). The inclusion of 1.1.7 1) (ie s^2 == 1) is only necessary to pass from a non-reduced factorization of σ to a reduced one.
  - 