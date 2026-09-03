# Scale check after the actual-factor restriction

The original conjecture is still UNSETTLED. No Lean source was changed in
this review, and no incomplete result was submitted. Spec.lean retains its
sole admission at line 17287, for 0 < epsilon < 1/3. Its proved unconditional
endpoint remains eventual M(N) >= N^(2/3).

The new GaussianUnitResidueDirections theorem was reviewed as an input to
collision counting, rather than merely as a necessary condition.

For the exact permutation carrier let

    B=6h+7, N_h=2*B^(h+1), Q=6*B*(B-1).

Since B>=7, Q<=B^3 and hence Q^2<=B^6. Thus the new cutoff

    Q^2 <= 16*normSq(p)

removes only a subpower range of normalized factor norms relative to N_h as
h grows. More generally, every FIXED power Q^k is subpower in N_h. This
scale observation is not an impossibility theorem for stronger methods.
In particular it does not bound the number of actual collisions satisfying
the four divisibility alternatives: candidate membership of the output
roots still has to be used.

No useful new count or compatible selector for those surviving collisions
was obtained. The factor-normalization theorem remains fully verified, but
it cannot presently supply the unproved Sidon hypothesis in
AllowedAlphabetCandidate.near_linear_of_eventually_sidon.

Neither the common-residue restrictions nor the previously proved full-
interval bounds were applied to arbitrary sparse selections. No unrestricted
fixed-power upper bound, and no improvement of the actual lower exponent,
was established in this review.

Spec.lean SHA-256 remains:

    257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940
