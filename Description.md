# Technical explanation

## Introduction

We are working with Pi language. Pi is a language for describing (syntactically) invertible functions between types. It consists of three parts:
  - First part is about types. It consists of type constants `0, 1` and type constructors `_+_ , _*_`
  - Second part is about invertible functions between these types. It consists of so-called 1-combinators: constants (like `id: A <-> A`, `+-comm: A + B <-> B + A`, etc.) and 1-combinators constructors (like sequential composition, parallel composition etc).
  - Third part is about the equivalences between the 1-combinators, so called 2-combinators (like `id-left: id.x <=> x`, etc).

To define the semantics of Pi, we have to map Pi types to appropriate concrete types, where 1-combinators will be mapped to bijections between (concrete) types, and if two 1-combinators are related by some 2-combinator, then appropriate (concrete) bijections should be equivalent.

We'd also like this language to be complete in this context, e.g. for the family of concrete types that we can get from interpreting Pi types, every possible bijection can be acquired by interpreting some 1-combinator, and if two bijections are equivalent, there is a way of constructing 2-combinator between them.

To do that, the choice was made to have the semantics grounded in (... - this depends on where does Robert Rose work - in HoTT? in pure Agda? in cubical?)

## Outline

  1. First step is doing an internal normalization in Pi.
      - Types normalization: informally speaking, every type in Pi should be "equivalent" to a type in the family:
    ` {0, 0 + 1, (0 + 1) + 1, ((0 + 1) + 1) + 1, ...}`
      We'll call this family of types `PiFin`.
      - Along with types normalization, there comes (internal to Pi) 1-combinator normalization. We want to express all normalized functions solely by a combination of `id, assoc, swap` constants and sequential and parallel composition.
      - Ultimately, what we want to get is a following commuting square:
      (square picture)
      where "commuting" in this case means "related by 2-combinator"
      - In the end, we should have a function

          ```agda
          Pi-norm  : {A B : Pi-type} -> (c : A <-> B) -> Σ ℕ (λ n -> Σ ( PiFin n <-> PiFin n) (λ cc -> c <=> cn))
          ```

  2. Then, we want to switch away from Pi, and talk about the combinators more abstractly - informally, as seqences of adjecent swaps (we'll talk about it in the next section). Such sequences are represented as elements of the `List (Fin n)` type.
  So, we'd like to have two functions

      ```agda
      Pi-sseq : {n : ℕ} -> (c : PiFin n <-> PiFin n) -> List (Fin n)
      sseq-Pi : {n : ℕ} -> List ℕ -> (PiFin n <-> PiFin n)
      ```

      along with the proofs that `Pi-sseq ∘ sseq-Pi ≡ id` and `sseq-Pi ∘ Pi-sseq ≡ id`.

  3. We're in the realm of permutations represented as `List (Fin n)` now - in other words, what we have is a word in the free group of `n` generators. We introduce a relation `_≃_`, based on Coxeter presentation of full symmetric group `S_n`, and we'd like to show that the type `List (Fin n)` divided by this equivalence relation is isomorphic to yet another form of permutation representation - Lehmer codes.
  We do that by defining a function

      ```agda
      immerse : {n : ℕ} -> Lehmer n -> List (Fin n)
      ```

      (together with a proof that it is an injection), and a proof

      ```agda
      sseq-norm : {n : ℕ} -> (l : List (Fin n)) -> Σ (Lehmer n) (λ cl -> l ≃ cl)
      ```

      (an image showing the embedding)

  4. Now we do the final isomorphism, between Lehmer codes and real bijections. Having the type of bijections as `_~_`, what we want are two functions

      ```agda
      eval  : {n : ℕ} -> (Lehmer n) -> (Fin n ~ Fin n)
      quote : {n : ℕ} -> (Fin n ~ Fin n) -> (Lehmer n)
      ```

  along with the proofs that `eval ∘ quote ≡ id` and `quote ∘ eval ≡ id`.

---

We can then finally define

```agda
Pi-eval = eval ∘ sseq-norm ∘ Pi-sseq ∘ Pi-norm
quote-Pi : sseq-Pi ∘ immerse ∘ quote`
```

and two proofs
 - that turning an bijection into Pi 1-combinator and executing it gives us the same bijection back:
   `quote-eval : Pi-eval ∘ quote-Pi ≡ id`
 - that executing a Pi 1-combinator and then quoting the result gives us the same (with respect to 2-combinators) combinator back:
   `eval-quote : {A B : PiType} -> (c : A <-> B) -> ((quote-Pi ∘ Pi-eval) c) <=> c`

The picture below hopefully shows it more clearly
(picture)

## Discussion of the specifics

### Outline

The reason the proof is structured in a way it is, is to bring down the complexity of idividual steps.
First, as Pi is a fairly complicated language, with many features built-in, we want to scale it down to the bare minimum. This minimum consists specifically of the standard types `(0 + 1 + 1 + ...)` and functions defined by `id, assoc, swap` together with parallel and sequential composition.

Then, we go to even more bare-bones, abstract language for describing permutations syntactically - lists of numbers denoting adjecent swaps - based on Coxeter presentation of a full symmetric group `S_n`. It is in this setting we isolate the task of word normalization (e.g. reducing all words to a subset of them).

This step takes us from the countable to the finite world (intuitively, from "operational" to "denotational" world). In the first one, each permutation is written as a sequence of operations, and so the type representing the permutations (on some particular type) is infinite - in the second one, we have some finite representation of this set of permutations, and permutations having the same "outcome" are identified.

The choice of introducing this intermediate representation in terms of Lehmer codes stems from the fact that working with the permutations type in Agda is a little cumbersome - they are defined as invertible functions, having the proofs of compositions with inversions being identity and so on. The Lehmer codes do not come with any of that - in a way, they are the simplest possible way of talking about the type of bijections on a finite type.

Having the Lehmer encoding of the bijection, we can isolate the complexity of dealing with bijection types in the last stage of the proof.

Since every step comes with it's own proofs of being an isomorphism (in case of step 3 - injection), the whole proof can be made by composition of all parts.

### First stage
Info from prof. Sabry.

### Second stage
Info from prof. Sabry.

### Third stage
Normalization is done using a collection of rewriting rules.
  - cancel, where `l ++ n ∷ n ∷ r` goes to `l ++ r`
  - swap, where `l ++ k ∷ n ∷ r` goes to `l ++ n ∷ k ∷ r`, provided that `1 + k < n`
  - lbraid, where  `l ++ n ∷ n - 1 ∷ n - 2 ∷ ... ∷ n - k ∷ n ∷ r` goes to `l ++ n - 1 ∷ n ∷ n - 2 ∷ ... ∷ n - k ∷ r`, provided that `0 < k`
These three rules come from Coxeter presentation, and the first two of them appear as they are. The third rule is different - it replaces the standard `braid` rule.
Using these rewriting rules, after taking reflexive-transitive closure, the diamond lemma, and, consequently, Church-Rosser property for the system.

Strong normalization for the system stems from the fact that each transformation either reduces the length of the list or its lexicographical order.

This whole procedure is done to define the relation
```agda
data _≃_ : List ℕ -> List ℕ -> Set where
  comm : (l1 l2 l : List ℕ) -> (l1 →* l) -> (l2 →* l) -> l1 ≃ l2
```

Contrast this with the usual definition of Coexeter relations for a full symmetric group, where the reduction rules (having `braid` instad of `lbraid`) go in both directions, but so there is no normalization property.
The reason we're using this admittedly more complicated machinery is because it is very hard (or maybe even impossible) to prove certain things about the relation when using non-directed version. For example, suppose that what we need to prove is that `[] ≄ [ 0 ]`. Using the standard Coxeter presentation, we quickly run into a problem with transitive property: we have to prove, that there is no (arbitrary list) `l`, such that `[] ≃ l` and `l ≃ [ x ]`. Thus, we can't do usual induction over reduction rules, and the only way to prove that is to use some kind of invariant. And even though in this particular case, the invariant saying that if `l ≃ l'`, then their lengths are equal `mod 2` would suffice, it should be clear that in general case, proving things about this relation is going to be very difficult.

## Third stage - alternative approach
In the case above, we prove that any way of reducing a word, using provided rules, is equivalent.
A somewhat easier way to define reduction is to focus on some standard reduction method, and prove properties only for that. This is what Alain Lascoux in (THE SYMMETRIC GROUP, 2002, unpublished) does, in `Lemma 1`, and what is (partially) replicated in the coq proof of the equivalence between Coxeter presentation of `S_n` and bijections between sets.

Lascoux method works by induction over the generators. (TODO should I describe it there?)

We started by implementing this method first, but then run into technical problems described at the end of the previous section. Although Lascoux method does not require the use of full Coxeter relations, and works with reduction rules described above, we thought it is better to prove the more general case, since we had the machinery set up anyway.

The implementation closely follows the decription in the book (text included?) and is availble in the `lascoux` directory.

### Fourth stage
Info from Robert Rose.

### Fourth stage - alternative approach
An alternative approach to defining isomorphism between Lehmer codes and bijections would be to work directly with lists of swaps. Then, `eval` is trivially defined as a composition of `eval` on each element, and the proof that it gives a bijection is quite easily done (by induction).
On the other hand, `quote` can be defined as insertion sort of tabulated function values. That this is specifically the **insertion** sort is important - this is because normalized words in Coxeter group are precisely the sequences of swaps coming from insertion sort running on some data!

Then, to complete the proof, one would have to show that `eval` respects Coxeter equations - but this is again quite simple to do so.

## The meaning

As the space of 1-combinators is much bigger than the space of bijections, we cannot hope for getting the same thing back - but this is a good thing! What we are actually getting is a normalized version of the program defined by 1-combinator.

What we would like would be of course an "optimized" version of such a program. The procedure outlined cannot guarantee that at this moment - the reason for this is that we lack the `un-norm-Pi` function, that would serve as a counterpart of `Pi-norm` function. However, this is actually the only missing element of the puzzle!
What we have now is the optimizer for the low-level language describing the permutations (lists of adjecent transpositions) (TODO think more about that)
And, of course, it is possible that such a function will be developed in the future, giving us the ultimate optimizer for the whole stack.

## TODO
Define adjecent swaps
