# Quadratic carry shears are principal-unit conjugates

This does NOT settle Erdos 773. The original theorem in Spec.lean is unchanged,
with its one sorry at line 17287 for 0 < epsilon < 1/3. The actual proved bound
remains eventual M(N) >= N^(2/3).

## Verified module

Submission/QuadraticCarryShearConjugacy.lean imports the clean
QuadraticCarryParabola module, not Spec. It compiles without warnings or
admissions and has a built olean. All six printed result audits use only
propext, Classical.choice, and Quot.sound.

For the targets T_kappa(b), canonical high digits a_kappa(b), and roots
r_kappa(b) of QuadraticCarryParabola, the new results prove

    T_(kappa+2t)(b) == (1+pt)^2 T_kappa(b)       (mod p^2),
    a_(kappa+2t)(b) = (a_kappa(b)+tb) mod p,
    r_(kappa+2t)(b) == (1+pt) r_kappa(b)        (mod p^2).

The multiplier 1+pt is coprime to p^2. For odd p every kappa has the form
2t modulo p, with 0 <= t < p. Thus every quadratic-shear construction is in
the principal-unit orbit of the affine (kappa=0) construction, modulo p^2.

Public APIs, namespace Erdos773.QuadraticCarryShearConjugacy:

* multiplier_unit
* target_shear
* highDigit_shear
* root_shear
* exists_affine_conjugacy
* height_not_preserved

## The crucial limitation is also explicit

For lambda=1, mu=-1, label b=1, the affine root equals 1. The shear t=p-1
sends its canonical representative to

    1+p(p-1).

Hence modular conjugacy does not preserve small height. In particular the
existing affine height ceiling cannot be applied to a quadratic-shear
carrier merely by invoking this conjugacy. No new ceiling for the quadratic
case is asserted, and no useful small-representative lower bound was obtained.

The accompanying review considered amplification by lifting old integer
labels and by allowing several shear parameters. Neither yielded cross-fiber
compatibility or a near-linear count. The already recorded fixed-point 2/3
loss for small integer labels remains relevant; it was not proved anew.

## Verification

Log: /tmp/quadratic-shear-conjugacy.log
Build: .lake/build/lib/lean/Submission/QuadraticCarryShearConjugacy.olean

Spec.lean SHA-256 remains
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940.

No proof or disproof of the original conjecture has been submitted.
