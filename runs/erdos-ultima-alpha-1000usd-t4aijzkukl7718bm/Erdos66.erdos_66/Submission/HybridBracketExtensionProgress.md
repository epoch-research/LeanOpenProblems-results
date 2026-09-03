# Hybrid prediction and bracket-preserving prescribed-prefix extensions

## Task status

The original conjecture remains unproved and undisproved. Spec.lean is
unchanged with its original sorry. No proof has been submitted.

## Checked sources and audit

* HybridPrefixPredictionExplore.lean
* ClampedPrefixContinuationExplore.lean
* BracketPreservingExtensionExplore.lean

All compile and have current oleans. HybridBracketExtensionAudit.lean audits
52 declarations; HybridBracketExtensionAudit.log reports only propext,
Classical.choice, and Quot.sound. The three production files contain no
sorries or new axioms.

## Uncorrected hybrid: exact lookahead decomposition

Let p be the exact harmonic profile, p*p(n)=H_(n+1). Fix old membership
below N, and define e_N(i)=(1_A(i)-p(i)) for i<N and zero otherwise.
The hybrid q keeps these old bits and uses p beyond N. Exactly:

    q*q(n)=H_(n+1)+2(e_N*p)(n)+(e_N*e_N)(n).

If every old prefix discrepancy is at most D, then for N<=n:

    |(e_N*p)(n)|<=2D p(n-N).

For 2N<=n+1 the truncated quadratic term is exactly zero. Thus, for 2N<=n:

    |q*q(n)-H_(n+1)|<=4D p(floor(n/2)),
    |repMean(q;n)-H_(n+1)|<=(4D+1)p(floor(n/2)).

Because p tends to zero, these are absolutely vanishing bounds, uniformly
over ALL old sets and cutoffs with the same discrepancy allowance and
2N<=n. The finite Bernoulli bound is also uniform in the final cutoff L>=n.

For N<=n<2N the Bernoulli diagonal correction is exactly zero, and:

    |(repMean(q;n)-H_(n+1))-(e_N*e_N)(n)|<=4D p(n-N).

The truncated quadratic error is not discarded or bounded by past accuracy.

## Correcting the discrepancy-invariant accumulation

The raw hybrid need not lie in the original profile's prefix brackets, so
rounding it could increase an absolute allowance D to D+1. This has now
been avoided.

For ANY fractional p in [0,1], write P(k)=sum_(i<k) p(i), and let s be the
old integer mass below N. Assume every old prefix lies in
[floor(P(k)),ceil(P(k))]. Define a corrected cumulative mass C by retaining
the exact old cumulative mass up to N, and for k>=N setting:

    C(k)=max(s,min(s+k-N,P(k))).

The fractional continuation is x(i)=C(i+1)-C(i). Checked properties:

* 0<=x(i)<=1;
* x(i)=1_A(i) for EVERY i<N;
* EVERY new prefix remains in the ORIGINAL brackets for P;
* the total l1 change from the raw hybrid is at most |s-P(N)|<=1,
  uniformly in the final cutoff.

The correction has one sign: if s>=P(N) it only deletes fractional mass;
if s<=P(N) it only adds fractional mass.

For arbitrary probability profiles p,q, the matching structure of each
representation target gives the checked Lipschitz bound:

    |repMean(p;n)-repMean(q;n)|<=2 sum_i |p(i)-q(i)|.

Consequently the bracket correction changes every finite mean by at most
TWO, independent of L, N, n, or the old set size.

## Exact Boolean extension, conditional on the tail budget

The existing compensated pipage selector is applied to the corrected
continuation. Its bracket condition forces every integral old prefix mass
EXACTLY. Consecutive differences then force every old bit EXACTLY.
Transitivity of brackets preserves the same original brackets after rounding.
Thus no D+1 or accumulated stagewise discrepancy is needed.

The general endpoint exists_bracket_preserving_extension returns a finite
C subset [0,L] with:

* exact old membership below N;
* exact old representation counts below N;
* the original profile's brackets through L+1;
* requested errors about the corrected Bernoulli mean <epsilon V(n)+2,

provided V bounds the variance proxies and the explicit budget

    sum_(n in S) 2 exp(-epsilon^2 V(n)/8)<1

holds. The old set is prescribed BEFORE this extension is chosen.

For the harmonic profile, every far-future request 2N<=n<=L has corrected
mean bias at most 2+5p(n/2). With

    V(n)=H_(n+1)+2+5p(n/2),

exists_harmonic_far_extension therefore gives, under the same budget:

    |r_C(n)-H_(n+1)|<epsilon V(n)+4+5p(n/2).

In the first transition window the corrected mean still satisfies only:

    |(repMean(x;n)-H_(n+1))-(e_N*e_N)(n)|<=2+4p(n-N).

## Remaining gaps

Bracket-invariant regeneration is now proved. It is no longer a gap for
this corrected continuation. Two genuinely separate gaps remain:

1. Uniform sublogarithmic control of the truncated quadratic error in the
   transition window (or another way to bridge every transition).
2. Selecting Boolean extensions at vanishing relative tolerance without
   relying on a full-window summed-Chernoff budget that fails at one fixed
   logarithmic coefficient.

The finite extension theorem does not solve either issue, does not supply
cutoff-independent finite feasibility, and cannot yet be iterated to obtain
the original all-tail limit. No disproof of arbitrary witnesses is claimed.
