# Cutoff and factor-range review — no new sufficient estimate

The conjecture remains UNSOLVED. Spec.lean is unchanged with its original
sorry. This continuation adds no new Lean theorem and no irrational
counterexample. No incomplete proof was submitted.

The verified development remains as described in ProgressPrimeFactorRemoval.md
and ProgressPrimeRemainderProfile.md.

The following directions were reviewed, without obtaining a sufficient
signed bound:

1. Varying or averaging the Vaughan cutoffs. The actual-remainder variance
   bounds already rule out treating the available remainder as o(N) in L2.
   No smaller cross-covariance bound was derived by varying the cutoffs.
2. Separating rough semiprime configurations, which have a favourable
   product sign. This does not control the mixed-sign configurations of
   the complete remainder or its mean-product centering correction.
3. Replacing the Type-I approximation by a genuine nonnegative majorant.
   At the level of the available normalized moment identities, majorant
   means M,L give only the lower expression M+L-M*L. If M=L>=2 this is
   nonpositive. No smaller-majorant construction with the necessary row
   estimates, or sufficient extra residual-product lower bound, was proved.
4. Averaging over cofactor ratios and thin-strip lattice counting. No
   signed discrepancy estimate was obtained; counting the distinct prime
   factors or controlling multiplicities cannot be substituted for it.
5. Bounding a weaker, sublinear prime-pair correlation rather than its full
   asymptotic. No frequently positive N^s lower bound for s>1/2 or unbounded
   excess over the prime-power error was found.

These are limitations of the estimates used in this development, not
proofs that every possible variant of these methods must fail. In
particular, no new general impossibility theorem is being asserted.

The decisive remaining task is unchanged: establish a genuinely sufficient
signed off-diagonal lower bound, obtain another prime-pair lower bound, or
construct an actual irrational counterexample. The existing conditional
criteria cannot replace that task.
