# Technical explanation

## Introduction

We are working with Pi language. Pi is a language for describing (syntactically) invertible functions between types. It consists of three parts:
  - First part is about types. It consists of type constants (0, 1) and type constructors (_+_ , _*_)
  - Second part is about the invertible functions between these types. It consists of so-called 1-combinators: constants (like id: A <-> A, +-comm: A + B <-> B + A) and 1-combinators constructors (like sequential composition, parallel composition etc).
  - Third part is about the equivalences between the 1-combinators, so called 2-combinators (like id-left: id.x <=> x, etc).

The intended semantics for this language is of course to map Pi types to appropriate concrete types, for 1-combinators to describe bijections between (concrete) types, and for 2-combinators to describe equivalences between (concrete) bijections. We'd also like this language to be complete in this context, e.g. that, for the family of concrete types that we can get from interpreting Pi types, every possible bijection can be acquired by interpreting some 1-combinator, and if two bijections are equivalent, there is a way of constructing 2-combinator between them.

To prove that, the choice was made to have the semantics grounded in (... - this section depends on where does Robert Rose work - in HoTT? in pure Agda? in cubical?)

\subsection{Outline}

The proof goes through four stages.
  1. First step is doing an internal normalization in Pi.
    - Types normalization: informally speaking, every type in Pi should be "equivalent" to a type in the family:
    $ \{0, 0 + 1, (0 + 1) + 1, ((0 + 1) + 1) + 1, ...\} $
    We'll call this family of types PiFin.
    - Along with types normalization, there comes (internal to Pi) 1-combinator normalization. We have a
    - Ultimately, what we want to get is a following commuting square:
    (square picture)
    where "commuting" in this case means "related by 2-combinator"
  In the end, we should have a function
  `Pi-norm  : {A B : Pi-type} -> (c : A <-> B) -> Σ ℕ (λ n -> Σ (PiFin n <-> PiFin n) (λ cc -> c <=> cn))`

  2. Then, we want to switch away from Pi, and talk about the combinators more abstractly - informally, as seqences of adjecent swaps. We represent such sequences as elements of the `List (Fin n)` type. We'll talk about it in the next section.
  So, we'd like to have two functions
  ```
  Pi-sseq : {n : ℕ} -> (c : PiFin n <-> PiFin n) -> List (Fin n)
  sseq-Pi : {n : ℕ} -> List ℕ -> (PiFin n <-> PiFin n)
  ```
  along with the proofs that `Pi-sseq ∘ sseq-Pi ≡ id` and `sseq-Pi ∘ Pi-sseq ≡ id`.
  The idea in this part is to prepare the ground for the next step.

  3. We're in the realm of permutations represented as `List (Fin n)` now - in other words, what we have is a word in the free group of $n$ generators. In the type `List (Fin n)` we introduce a relation `_≃_`, based on Coxeter presentation of full symmetric group $S_n$. We'd like to show that the type `List (Fin n)` divided by this equivalence relation is isomorphic to yet another form of permutation representation - Lehmer codes. To do that, we have a function
  `immerse : {n : ℕ} -> Lehmer n -> List (Fin n)` (together with a proof that it is an injection), and a proof
  `sseq-norm : {n : ℕ} -> (l : List (Fin n)) -> Σ (Lehmer n) (λ cl -> l ≃ cl)`.
  (an image showing the embedding)
  The idea here is that this step takes us from the countable to finite world (intuitively, from "operational" to "denotational" world). In the first case, each permutation is written as a sequence of operations, and so the type representing the permutations (on some particular type) is infinite - in the second case, we have some finite representation of this set of permutations.

  4. Now we do the final isomorphism, between Lehmer codes and real bijections. We have the type of bijections `_~_`, and what we want are two functions
  ```
  eval  : {n : ℕ} -> (Lehmer n) -> (Fin n ~ Fin n)
  quote : {n : ℕ} -> (Fin n ~ Fin n) -> (Lehmer n)
  ```
  along with the proofs that `eval ∘ quote ≡ id` and `quote ∘ eval ≡ id`.

We can then finally define
```
Pi-eval = eval ∘ sseq-norm ∘ Pi-sseq ∘ Pi-norm
quote-Pi : sseq-Pi ∘ immerse ∘ quote`
```
and two proofs
 - that turing an bijection into Pi 1-combinator and executing it gives us the same bijection back:
   `quote-eval : Pi-eval ∘ quote-Pi ≡ id`
 - that executing a Pi 1-combinator and then quoting the result gives us the same (with respect to 2-combinators) combinator back:
   `eval-quote : {A B : PiType} -> (c : A <-> B) -> ((quote-Pi ∘ Pi-eval) c) <=> c`

## The discussion of specifics

### Outline

The reason the proof is structured in a way it is, is to get down the complexity of idividual steps.
First, as Pi is a fairly complicated language, with many features built-in, we want to scale it down to the bare minimum. This minimum consists specifically of the standard types (0 + 1 + 1 + ...) and functions defined by (id, assoc, swap) and parallel and sequential composition.

Then, we go to even more bare-bones, abstract language for describing permutations syntactically - lists of numbers denoting adjecent swaps - Coxeter presentation of a full symmetric group $S_n$. It is in this setting we isolate the task of word normalization.

The choice of introducing this intermediate representation in terms of Lehmer codes stems from the fact that working with permutations in Agda is a little cumbersome - they are defined as invertible functions, having the proofs of compositions with inversions being identity and so on. The Lehmer codes do not come with any of that - in a way, they are the simplest possible way of talking about the type of bijections on a finite type.

Having some (Lehmer) encoding of the bijection, we can isolate the complexity of dealing with bijection types in the last stage of the proof.

Since every step comes with it's own proofs of being an isomorphism (in case of step 3 - injection), the whole proof can be made by composition of all parts.

### First stage
Info from prof. Sabry.

### Second stage
Info from prof. Sabry.

### Third stage


### Fourth stage
Info from Robert Rose.

### Fourth stage - alternative approach
An alternative approach to defining isomorphism between Lehmer codes and bijections would be to work directly with lists of swaps. Then, `eval` is trivially defined as a composition of `eval` on each element, and the proof that it gives a bijection is quite easily done (by induction).
On the other hand, `quote` can be defined as insertion sort of tabulated function values. That this is specifically the **insertion** sort is important - this is because normalized words in Coxeter group are precisely the sequences of swaps coming from insertion sort running on some data!

Then, to complete the proof, one would have to show that `eval` respects Coxeter equations - but this is again quite simple to do so.

## The meaning

As the space of 1-combinators is much bigger than the space of bijections, we cannot hope for getting the same thing back - but this is a good thing! Because what we are actually getting is a normalized version of the program defined by 1-combinator.

What we would like would be of course an "optimized" version of such a program. The procedure outlined cannot guarantee that at this moment - the reason for this is that we lack the `un-norm-Pi` function, that would serve as a counterpart of `Pi-norm` function. However, this is actually the only missing element of the puzzle!
What we have now is the optimizer for the low-level language describing the permutations (lists of adjecent transpositions) (TODO think more about that)
And, of course, it is possible that such a function will be developed in the future, giving us the ultimate optimizer for the whole stack.

## TODO
Define adjecent swaps
