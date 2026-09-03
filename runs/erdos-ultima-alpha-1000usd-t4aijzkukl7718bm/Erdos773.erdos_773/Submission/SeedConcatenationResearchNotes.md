# Concatenating the genuinely Sidon checksum seed

This does NOT settle Erdős 773. The main Spec.lean file is unchanged and
still has its sole sorry for 0 < epsilon <= 1/3. No proof was submitted.

## New verified module

Submission/SeedConcatenation.lean imports the clean CubicChecksumExample.
All six main axiom audits use only propext, Classical.choice, Quot.sound.
The file builds without warnings or admissions and has a built olean.
Log: /tmp/seed-concatenation-final.log.

For a digit alphabet A, define words(A,B,0)={0} and

    words(A,B,k+1) = {a+B*n : a in A, n in words(A,B,k)}.

The generic lemmas words_card and words_lt prove, for canonical digits a<B
and B>0, that there are exactly |A|^k words and every word is below B^k.

## A good seed need not give a good two-block code

Take A=CubicChecksumExample.roots, the VERIFIED square-Sidon set of 27 roots
at height 80. Its base-81 two-block code nevertheless contains

    334 = 10 + 81*4,
    537 = 51 + 81*6,
    345 = 21 + 81*4,
    530 = 44 + 81*6,

and

    334^2 + 537^2 = 345^2 + 530^2 = 399925.

All six digits 4,6,10,21,44,51 belong to the verified seed. In particular this
is not merely propagation from a seed that was already nonsidon.

## Failure at every positive even block length

Set G(B,k)=sum_{j<k}(B^2)^j. The lemma repeat_mem proves that

    (a+B*b)*G(B,k) belongs to words(A,B,2k)

whenever a,b belong to A. The multiplier is positive when k>0. Scaling the
four roots of the displayed collision by G(81,k) preserves the equality
and nontriviality. Thus every_positive_even_length_fails proves:

    for every k>0, the squares of words(A,81,2k) are NOT Sidon.

At the same time seed_code_card and seed_code_height prove the exact count
27^j and root height less than 81^j at EVERY length j. These numerical data
would have the desired 3/4 exponent if the code were Sidon, but it is not.

The result says nothing comparable about a Sidon SUBSET of this language,
about a more selective recursive code, or about all possible amplification
schemes. It is not an upper bound on the original Sidon maximum.

## Further review and main gap

The subsequent affine-shift review did not produce a new implication to
the existing universal-affine upper bound. The extracted shifts and sparse
base sets still do not supply Sidonness for all needed affine parameters.
No near-linear selector or fixed-power upper bound for arbitrary square-
Sidon subsets was found. No asymptotic exponent improved in this continuation.

The strongest actual lower bound remains eventual M(N)>=N^(2/3)/500.
Spec.lean retains its statement, import, and hash:
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
