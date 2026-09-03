# Affine boundary-repair investigation

Erdos 773 is still UNSETTLED. Spec.lean has not been edited. Its only admission remains in 0 < epsilon < 1/3; the verified unconditional endpoint is eventual M(N) >= N^(2/3).

## New checked auxiliary module

AffineSlopeRepairObstruction.lean imports only FormalConjecturesUtil. It contains no admissions, builds without warnings, and has an olean. Its four printed audits use only propext, Classical.choice, Quot.sound.

Log: /tmp/affine-slope-repair-obstruction.log.

- paired_slope_congruence: from integer rows x=u+12v-3w-L*cx and z=u+12v+3w-L*cz, and 6 dividing cz-cx, deduces 6 dividing x-z.
- carry_difference_mod_six: the corresponding constant-coefficient rows propagate divisibility of the carry difference by six from the initial column.
- targets_incompatible: two vectors of length 115, whose multisets are the explicit target lists below, cannot be pointwise congruent modulo six.
- no_target_repair combines the explicit row hypotheses with the target obstruction.

The target x multiset has 6 copies of 0, 29 each of 1,2,7, and 22 of 8. The target z multiset has 29 each of 1,2,7, and 28 of 8. Their lengths are both 115. The x vector must contain zero, while the z vector has no entry divisible by six.

IMPORTANT: this proves the stated conditional finite arithmetic obstruction. It does NOT prove completeness of the exploratory encoding, connect every factorial-carrier collision to these targets, or prove any Sidonness assertion for the full carrier. Nothing here is the negation of the original conjecture.

## Symbolic search script

Research/AllowedAlphabetAffineRepair.py investigates h=L*k-1, B=6*L*k+1, for L divisible by eight. It fixes the Gaussian factor

    n=3B(B-1), m=4n+1,
    (x,y,z,w)=(mu-nv,nu+mv,mu+nv,-nu+mv).

Factor digits in a finite collection of patches at positions j*k+b are represented as 6*s*k+t. Free root digits are represented as 6*(s*k+t). Multiplication is split into slope and constant coefficient equations, with constant carries in [-40,40]. This removes the large numerical base from the SMT arithmetic.

The reference factor words are ramps of period L*k, with offset (L/8)*k+2, and the previously investigated reset at the last two factor digits. Outside the patches they are fixed. Missing root labels are computed at K and K+1 and paired as affine functions. This two-sample identification is exploratory, not a proof that the formulas work for every k. Any returned model is independently tested as an exact integer identity and digit condition at K, K+1, and 2K+17. An infinite family would still require a separate symbolic and Lean proof.

`relaxed` omits permutation distinctness but still restricts output labels to the missing-label domain. `widealphabet` additionally replaces that domain by broad slope/offset intervals, and does not assert permutation distinctness. Neither relaxed flag searches the exact full alphabet.

## Completed outcomes

Before generalizing L, the script used L=8. These logs use the older filename convention:

- /tmp/allowed-affine-repair-12-5-255.log: UNSAT in 13.56 s.
- /tmp/allowed-affine-repair-12-5-1023-relaxed.log: UNSAT in 14.48 s.
- /tmp/allowed-affine-repair-24-9-1023.log: UNKNOWN, out of memory in 17.47 s. This is NOT UNSAT.

The first L=8 target mismatch above explains a necessary obstruction in that particular affine encoding. Increasing L to 24 removes the immediate endpoint-slope mismatch modulo six, but merely scaling all permitted slopes by three recreates a related obstruction after normalization. The `break` flag adds a patch with slope-one labels to avoid assuming that all free slopes are multiples of three.

- /tmp/allowed-affine-repair-L24-12-6-1023.log: UNSAT in 24.39 s.
- /tmp/allowed-affine-repair-L24-12-6-1023-relaxed.log: UNSAT in 11.67 s.

These remain restricted-instance results, not Lean nonexistence theorems or original-conjecture results.

The first wide-alphabet run built a needlessly large domain disjunction and was externally stopped after about one minute. It was replaced with interval inequalities. The current run's log is:

    /tmp/allowed-affine-repair-L24-12-6-1023-widealphabet-fast.log

Final outcome: UNKNOWN, reason `timeout`, after 600.32 seconds. No SAT model or candidate collision was obtained. No associated search remains running after this run finished. This timeout is not a nonexistence result.

## Other review

Reviewed bounded-capacity extraction, modular/fiber selectors, finite-field parabola lifts, and collision-container ideas. No square-specific rounding theorem, low-collision near-linear carrier, exponent improvement, or unrestricted fixed-power upper bound was obtained. The online problem reference could not be reached because DNS resolution failed.

Unchanged Spec.lean SHA-256:
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940
