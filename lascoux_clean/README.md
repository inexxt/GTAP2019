## Structure

General:
  - `Arithmetic.agda` - general arithmetical lemmas and proofs
  - `Lists.agda` - general lemmas for lists, mainly concerned with `_↓_` function (TODO think about some good name for down-arrow)
    - I use my own `rev` function instead of library `reverse`, because `reverse` doesn't compute
  - `Compact.agda` - defines relations in full symmetric group, concerned mainly with `_≅*_` data type (TODO think of a good name for this relation)
  - `SwapLemmas.agda` - defines lemmas concerning exchanging the order of singletons and down-arrows (TODO rename them to exchange-lemmas)
  - `Canonical.agda` - defines canonical data type
  - `CoxeterCompact.agda` - defines Coxeter presentation and proves that Compact presentation is weaker than Coxeter presentation
    - (ie when two things are related by Compact, then they are related by Coxeter)

Diamond:
  - `LongLemmas.agda` - defines very specific lemmas for critical pairs involving `long` constructor
  - `DiamondCompact.agda` - proves diamond and diamond-full lemmas (diamond-full operates on transitive closure of MYREL)
    - TODO take care of termination checker in diamond
    - TODO take care of termination checker in diamond-full

Uniqueness:
  - `CanonicalUnique.agda` - proves that if two canonical elements have immersions related by Compact, then they are the same element

Reduction:
  - ?? - proves that every element in the free group is related by Compact to some canonical element
    (actually, maybe I can try to prove that it is only canonical elements that do not reduce?)
