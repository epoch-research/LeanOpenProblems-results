# Direct simultaneous Padé forms with full-target corrections

This is an external exact finite construction test, NOT a Lean theorem and
NOT a settlement of Erdős 68. Spec.lean is unchanged with its original sorry.
No complete proof or disproof has been obtained or submitted.

## Construction distinct from the earlier rescaled-column test

Use direct factorial-power functions

    E_(j,r)(z)=sum_(n>=0) n^r*z^n/(n!)^j.

For r=0, the constant coefficient is one. The earlier joint test instead
used z^(j*n). Two direct variants are tested here:

* r=0 only, j=1,...,J;
* r=0,...,j-1, j=1,...,J (the full derivative set).

If there are d functions, set L=d*m and choose a nonzero polynomial Q of
degree at most L so that, for each selected function, Q*E has zero
coefficients in degrees L+1,...,L+m. All 43 tested systems had a
one-dimensional rational kernel and Q(1)!=0. Let P_j be the degree-L
truncation of Q*E_(j,0), and set

    R=(sum_j P_j(1))/Q(1)-2J.

This is an approximation to the finite column sum beta_J, not to alpha.
For each cutoff K>=1, correct it by the exact rational quantity

    R_K=R+sum_(n=2)^K 1/[(n!)^J*(n!-1)].

The full original target decomposes as

    alpha=beta_J+sum_(n=2)^K 1/[(n!)^J*(n!-1)]
                 +sum_(n>K) 1/[(n!)^J*(n!-1)].

Thus the final positive omitted-row tail remains part of the error; it is
not discarded or inferred small solely from the Padé order. Each R_K is
fully reduced to a/b, b>0, before checking the integer form b*alpha-a.

## Completed exact test

J=1,...,6, m=1,...,4, both variants, omitting the redundant full J=1
variant and cases L>65. There are 43 parameter groups. For each group,
K=1,...,max(8,2L), giving 1372 corrected forms in total.

Exact interval classifications:

* 4 forms have error in (0,1);
* 1 form has error in (-1,0);
* 856 forms have error greater than 1;
* 511 forms have error less than -1;
* no classification is ambiguous.

All five small forms occur in the r=0-only variant:

    J  m  K   a    b   sign
    1  1  1   1    1    +
    1  1  2   3    2    -
    1  2  2  17   14    +
    1  2  3 131  105    +
    2  1  2   6    5    +

For each group the JSON also records the form with the smallest certified
absolute-error upper endpoint. This selection is made by exact rational
comparison, not by the diagnostic floating-point logarithms. It is only a
minimum over the tested cutoffs and that one-dimensional Padé family.

Selected diagnostic results for this best tested cutoff:

    variant  J  m   L   K   denominator bits   log10 |b*alpha-a| upper
    r=0      3  1   3   2          14                1.504
    r=0      3  4  12   6         388              101.755
    full     4  1  10   4         230               59.137
    full     5  4  60  11       13653             4057.658
    full     6  3  63  11       18059             5375.382

These finite failures prove no asymptotic impossibility theorem and do not
exclude other degrees, corrections, or auxiliary constructions.

## Exact enclosure and independent audit

Set N=2000, W=N!, and

    L0=sum_(n=2)^N floor(W/(n!-1)).

The already established elementary enclosure is

    L0/W < alpha < (L0+N+2)/W.

All signs and comparisons with one use exact rational multiplication of
this enclosure. No floating-point decision is used as a proof premise.

The construction uses Sage rational matrix kernels and GMP rationals. An
independent audit uses Python Fraction arithmetic and direct polynomial
convolutions, without matrix algorithms. It rechecks every Padé equation,
Q(1), all truncated numerators, every rational correction, all reduced
pairs, every recorded interval and classification, and each selected best
cutoff. All 43 groups and 1372 forms passed the audit.

Artifacts:

* /tmp/direct_joint_full_target.py
* /tmp/direct_joint_full_target.log
* /tmp/direct_joint_full_target.json
* /tmp/direct_joint_full_target_audit.py
* /tmp/direct_joint_full_target_audit.log

Both computations have completed. Nothing remains running. No complete
informal solution or new original-conjecture Lean proof was obtained.
