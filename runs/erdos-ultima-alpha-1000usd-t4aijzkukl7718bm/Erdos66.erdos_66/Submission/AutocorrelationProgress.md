# Natural autocorrelation stability

## Original task status

Erdos66.erdos_66 remains unproved and undisproved. Spec.lean is unchanged
with its original sorry. Nothing here is a proof of its negation.

## Verified files

* AutocorrelationStabilityExplore.lean
* NaturalAutocorrelationExplore.lean
* AutocorrelationAbelExplore.lean
* WitnessAutocorrelationExplore.lean

All four compile with current oleans. AutocorrelationAudit.log audits eleven
principal declarations with only propext, Classical.choice, Quot.sound.
The two *Checks.lean files are name-search scratch files, not dependencies.

## Finite algebra

For real f,g on any finite abelian group,

    sum_h (corr(f)(h)-corr(g)(h))^2
       <= sum_n (conv(f,f)(n)-conv(g,g)(n))^2.

Set F=f+g and G=f-g. The autocorrelation difference is the symmetric part
of conv(F,reflect G). Symmetrization does not increase squared norm, and
reflection preserves convolution energy. No Fourier theorem is required.

Periodizing weighted sequences gives the same inequality with explicit
upper bound

    (1-r^m)^(-1) sum_n (sumConv(f,f)(n)-sumConv(g,g)(n))^2 r^n.

## Natural half-line transfer

Define

    weightedCorr(f,r,h) = sum_n f(n) f(n+h) r^(2n+h),  h>=0.

The cyclic correlation of the pushforward of a summable sequence is a
summable double series over (i,j), with indicator j=i+h mod m. For each
fixed (i,j,h), as m tends to infinity this indicator becomes exactly
j=i+h. Dominated convergence is justified by the summable product
|f(i) f(j)|. Hence cyclic correlations converge to natural correlations.

Finite lists of natural shifts inject into sufficiently large cyclic
periods. Pass to the limit for each finite list, then use the uniform
nonnegative partial-sum bound to obtain summability and

    sum_(h>=0) (weightedCorr(f,r,h)-weightedCorr(g,r,h))^2
       <= sum_n (sumConv(f,f)(n)-sumConv(g,g)(n))^2 r^n.

The theorem uses a ONE-SIDED shift norm. It does not claim a sharp constant
or count the positive shifts twice. No modular wraparound is retained in
its final statement. Signed real f,g are permitted with the explicit
summability hypotheses.

## Specialization and unrestricted necessary condition

Let p be the already checked fractional profile, with p*p(n)=H_(n+1).
For ANY natural set A, c>=0, and 0<r<1,

    E_corr(A,c,r)
      := sum_(h>=0) (weightedCorr(1_A,r,h)-c weightedCorr(p,r,h))^2
      <= sum_n (r_A(n)-c H_(n+1))^2 r^n.

This also proves summability of the full one-sided correlation-error norm.

A generic Abel ratio lemma shows that u_n/v_n->0, u_n>=0, v_n>=1, with
the stated geometric summability, implies series(u,r)/series(v,r)->0.
Apply it to squared representation errors and squared harmonic numbers.
The explicit harmonic-square bound is

    sum_n H_(n+1)^2 r^n <= 6[-log(1-r)]^2/(1-r)

when -log(1-r)>=1. Its proof uses
H_(n+1)<=-log(1-r)+(1-r)(n+1) and the second binomial geometric series.

Thus every hypothetical witness, including any finite limit c=0, satisfies

    [(1-r)/(-log(1-r))^2] E_corr(A,c,r) -> 0.

Main declaration:
Erdos66WitnessAutocorrelation.witness_normalized_corr_error_zero.

## Scope

This is an unrestricted necessary condition, not a pointwise statement
about individual shifts or individual sum targets. It remains compatible
with squared representation-error energy of order log(1/(1-r))/(1-r),
which is forced by the earlier sharp fluctuation theorem. It does not
force the larger order log^2(1/(1-r))/(1-r) needed for a contradiction.
No compatible construction or universal logarithmic-order fluctuation
obstruction has been established.

The nonlinear digit route was reviewed before this work. Existing
DfaCountingExplore and AutomaticCoreExplore already exclude finite-state
cores, beyond the binary linear-code obstruction. No new compatible
unbounded-memory digit construction was found; those reviews are not
additional formal theorems.
