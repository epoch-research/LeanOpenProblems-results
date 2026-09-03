# Conditional use of the odd descending congruence in the actual carry

Verified auxiliary progress, NOT a settlement of Erdos 68. Spec.lean is
unchanged with its original sorry. No complete proof or disproof was found
or submitted in this continuation.

`Submission/CarriedOddDescendingCriterion.lean` compiles without warnings
and has a built olean. All four printed principal axiom audits use only
propext, Classical.choice, and Quot.sound. The file has no proof holes.

## A valid conditional application

Let c_n and h_n be the exact coefficients and integer carries of
CongruencePreservingCarry, whose sum is the original target alpha. Its
scaled tails are positive and are strictly less than n at EVERY composite
index. This distinction is essential: the rational descending-congruence
comparison has this linear bound only at even indices.

The new file proves that if alpha=q is rational, then for every odd
composite n with n>=2*q.den+11,

    (n-1)*(n-2) does NOT divide c_n-1.

Thus arbitrarily late odd composite indices at which this congruence DOES
hold suffice to prove the original irrationality conjecture. This is
`irrational_of_frequent_odd_composite_congruence`.

The existence of those arbitrarily late indices remains UNPROVED.

## Proof of the conditional exclusion

Bertrand's theorem and a finite maximum give a last prime p<n with

    p>=5, p+1<n, n+3<=2*p,

and every index from p+1 through n composite. The existing rational
prime-successor identity and descending-block lemma then give

    T_(n-1)=2*p-n,
    T_n=2*p-n-1,
    c_n=1+(n-1)*(2*p-n).

Here 0<2*p-n<n-2. Divisibility of c_n-1 by (n-1)*(n-2) would consequently
force n-2 to divide a strictly positive integer smaller than n-2, impossible.
All casts, denominator conditions, and finite-index bounds are checked in
Lean; the proof does not assume a quantitative prime number theorem.

## Exact inheritance condition and finite failure

The original Lambert coefficients a_n satisfy a_n=1 modulo (n-1)*(n-2)
for every odd n>=3, by LambertDescendingCongruence. For n>=5 odd, the new
file verifies the exact equivalence

    (n-1)*(n-2) divides c_n-1
      iff
    (n-1)*(n-2) divides h_n-n*h_(n-1).

The Lean indices for the two carries are n-3 and n-4. This equivalence
is only an arithmetic reformulation; no infinitely-often divisibility of
the displayed carry combination has been proved.

A finite kernel-checked computation gives

    a_9=1681, c_9=49, 56 does not divide c_9-1.

Thus the original congruence is not automatic for the actual carry. This
is not a counterexample to the irrationality of their common real sum.

Principal declarations:

* last_prime_before_odd_composite
* rational_coeff_in_composite_run
* rational_odd_composite_not_congruent
* odd_congruence_iff_carry_transfer
* irrational_of_frequent_odd_composite_congruence
* finite_inheritance_failure

## Other work in this continuation

The exact boundary-lattice projection and image formulas were reviewed,
but no uniform useful-lift estimate or nonzero small integral-form family
was obtained. Full pair image and short weight vectors still do not establish
nonvanishing of the resulting value. Positive kernels, polynomial-part
kernels, finite-column approximation, and carry dynamics were also checked
against their existing notes; no complete new construction resulted.

No new numerical search was run. All compilation and axiom checks are
complete; nothing is running or pending. The original conjecture remains
unproved and undisproved in this workspace.
