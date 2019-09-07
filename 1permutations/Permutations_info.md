Presentations of Sn, reducing words, order of elements

Algorithm for Coxeter presentation (references)
https://mathoverflow.net/questions/109071/algorithm-for-reducing-words-in-a-coxeter-group

algorithm which finds the Landau Function fast
https://arxiv.org/pdf/0803.2160.pdf

Paper on presentations of Sn
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.76.6192&rep=rep1&type=pdf
https://www.math.auckland.ac.nz/~obrien/research/an-sn-present.pdf

On Sn as a Coxeter group
https://arxiv.org/pdf/1503.05205.pdf

Another one
http://www.math.utah.edu/~ciubo/6310/Sn.pdf

Calculating Coxeter length from number of inversions
Converting permutation to a reduced word
https://math.stackexchange.com/questions/175652/converting-a-signed-permutation-to-a-reduced-word

A word is reduced iff its length is equal to the number of inversions in the resulting permutation. I don't know if there is a nice quick way to do this by hand, but there is a fairly simple O(nlogn) algorithm for counting inversions

Generally
https://en.wikipedia.org/wiki/Coxeter_group


Novikov–Boone theorem
The negative solution to the word problem for groups states that there is a finite presentation <S | R> for which there is no algorithm which, given two words u, v, decides whether u and v describe the same element in the group. This was shown by Pyotr Novikov in 1955[3] and a different proof was obtained by William Boone in 1958.


Lecture notes on Coxeter
https://www.win.tue.nl/~amc/pub/CoxNotes.pdf


On other presentations of Sn
paper_archives/moore1896.pdf


Algorithm for finding monoid presentation (this is exactly my problem)
https://math.stackexchange.com/questions/1001243/words-of-the-normal-form-of-the-presentation-of-a-finite-monoid

(Burnside problem)

(Tarski Monster groups)


Complexity of word problem in Sn is O(n * (l1 + l2))
https://mathoverflow.net/questions/294557/time-complexity-of-the-word-problem-for-finite-permutation-groups


String rewriting system is a presentation of a monoid
https://en.wikipedia.org/wiki/Semi-Thue_system

List of possible Sn presentations
 - adjoint transpositions - Coxeter presentation
 - transpositions with zero (if n > 2) - STAR TRANSPOSITIONS
 - prefix cycles - nowhere to be found
 - (1n) (2...n) (if n > 2)
 - (ab) (1...n) if (b-a, n) = 1
 - prefix reversals - Pancake sorting
https://kconrad.math.uconn.edu/blurbs/grouptheory/genset.pdf

How many (arbitrary) transpositions?
If you're only dealing with permutations of n elements, then you will need exactly n−c(π) swaps, where c(π) is the number of cycles in the disjoint cycle decomposition of π. Since this distance is bi-invariant, transforming π into σ (or A into B, or conversely) requires n−c(σ−1∘π) such moves.


Multiplication in Coxeter groups (long)
https://www.math.ubc.ca/~cass/research/pdf/cm.pdf


