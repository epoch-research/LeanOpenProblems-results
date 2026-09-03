# Prime outputs removed from the block main term — not a settlement

Submission/Spec.lean remains unchanged with its original sorry. No proof
of the conjecture, negation, or sufficient prime-pair lower bound was found.

## New verified file

Submission/CompositeBlockMain.lean
Namespace: Erdos972CompositeBlockMain.

For the existing prime-input weight primeWeight(p), define

    nonPrimeOutputWeight(alpha,p)
      = 0                     if floor(alpha*p) is prime,
      = primeWeight(p)         otherwise.

Nonzero weights in the restricted sum have prime inputs and composite
outputs when alpha>=1: the output is at least the input prime, hence >=2.

The prime-output block contribution is

    P(alpha,N,D) = sum_{0<p<=N,
                        floor(alpha*p) prime,
                        D<floor(alpha*p)<=2D} primeWeight(p).

### Exact identity and uniform upper bound

For D>0, block_firstMoment_prime_removal proves

    sum_{D<d<=2D} row_d(primeWeight)
      - sum_{D<d<=2D} row_d(nonPrimeOutputWeight)
      = P(alpha,N,D).

A prime output has only one divisor above D>=1, namely itself. The
identity retains that contribution exactly, rather than estimating a
prime output by a generic divisor-count bound.

For alpha>=1, primeOutputBlockMass_le proves

    0 <= P(alpha,N,D) <= 14D,

where nonnegativity is also available as primeOutputBlockMass_nonneg.
The upper bound is uniform in N and follows because every contributing
input prime satisfies p<=floor(alpha*p)<=2D, and theta(2D)<=14D.

### Same main term after removing all prime outputs

exists_nonPrimeOutput_block_firstMoment_log_two proves that for every
alpha>1 irrational, epsilon>0, and initial bound B, there exist u>B and

    N=u^6, v=root64(u), D=blockStart(alpha,N,v),
    0<D<N,

such that BOTH of the following hold at that SAME scale:

    |sum_{D<d<=2D} row_d(primeWeight) - N log 2| <= epsilon N,

    |sum_{D<d<=2D} row_d(nonPrimeOutputWeight) - N log 2|
        <= epsilon N.

Also P(alpha,N,D)<=epsilon N. The argument uses the existing selected-scale
first moment with tolerance epsilon/2 and ensures 14D<=epsilon N/2 using
Dv<=(alpha+1)N and a sufficiently large v. It does not intersect unrelated
existential good-scale sets.

## Verification and limitation

The file compiles to
.lake/build/lib/lean/Submission/CompositeBlockMain.olean.
All three principal declarations audit with only propext, Classical.choice,
and Quot.sound. The new file contains no sorry declarations.

This shows that the already-proved order-N first-moment asymptotic survives
removal of every prime output. It is NOT a theorem that prime outputs are
absent, nor does it exclude a more precise use of these rows. It supplies
neither a signed centered four-factor gap nor the weaker prime-pair lower
bound needed by the original task.

The misplaced follow-up review in ProgressLargeDivisorBlockMain.md was also
moved below its completed centering and remaining-gap sections. No original
conjecture statement or imports were modified. No proof was submitted.
