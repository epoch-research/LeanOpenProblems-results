# Higher even Abel moments: checked Jensen consequence

## Original task status

The conjecture remains neither proved nor disproved. Submission/Spec.lean
is unchanged, including its original sorry. No proof was submitted.

## Verified files

AbelHigherMomentExplore.lean compiles with a current olean.
AbelHigherMomentAudit.lean audits all eight declarations, and the saved
AbelHigherMomentAudit.log uses only propext, Classical.choice, and
Quot.sound. No sorry or new axiom occurs in the production file.
HigherMomentChecks.lean and HigherMomentChecks2.lean are scratch name-search
files containing intentional failed checks, not production dependencies.

## General weighted Jensen result

For nonnegative w_n,f_n, with sum w_n=1 and the explicitly stated
summability hypotheses,

    (sum w_n f_n)^k <= sum w_n f_n^k,       k>0.

The proof applies finite Jensen with the unused tail weight placed at
value zero, then takes the limit of finite sums. For geometric weights
w_n=(1-r)r^n, 0<=r<1, this gives

    [(1-r) series(f,r)]^k <= (1-r) series(f^k,r).

All logarithmic-centered representation-error even moments are summable
at 0<r<1, proved directly by a polynomial/geometric majorant. No higher
moment convergence or representation independence is assumed.

## Necessary higher-moment bound

For a hypothetical witness A,c, let e_n=r_A(n)-c log n and
L(r)=-log(1-r). For every natural k>0 and every real d<c^k,

    eventually as r -> 1 from below,
      d < (1-r)/L(r)^k * sum_n e_n^(2k) r^n.

Principal declaration:

    Erdos66AbelHigherMoment.normalized_even_moment_eventually_gt

This follows from the previously checked sharp second-moment Abel lower
bound and Jensen. The geometric normalization is (1-r)/L(r)^k, NOT
[(1-r)/L(r)]^k. The latter would have an incorrect extra power of 1-r.

## Scope

The lower coefficient is c^k, with no factorial or comparable extra factor.
Taking 2k-th roots therefore still detects only square-root-logarithmic
fluctuations. This is fully compatible with e_n=o(log n), and is not a
disproof. No uniform growing-k amplification from Boolean convolution
structure has been established.

A possible stronger moment method would have to prove genuinely new
inequalities, rather than treating representation counts as independent
random variables or assuming Gaussian moment lower bounds. The generic
second-moment stability theorem and Jensen alone do not supply those
inequalities. The compatible infinite construction is also still missing.
