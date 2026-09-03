# Verified formal Gaussian Sidon construction and exact specialization failure

This continuation does NOT settle Erdős 773. The conjecture in Spec.lean is
unchanged and still admitted for 0 < epsilon <= 1/3.

## The formal construction is now proved, not just suggested

`FormalGaussianSidon.lean` imports only FormalConjecturesUtil. For P in Z[X],
put

    Admissible d P := natDegree(P)<d and P(0)=1 modulo 3,
    E(P) = X^d + 6P.

The theorem `formal_sidon d` proves that the set of all E(P)^2 with admissible
P is Sidon IN Z[X]. More explicitly, `encoding_pair_matching` proves that

    E(P)^2+E(Q)^2 = E(R)^2+E(S)^2

implies (P,Q)=(R,S) or (P,Q)=(S,R).

The Gaussian polynomial used in the proof is

    F(P,Q) = X^d + 3(P+Q) + 3i(Q-P).

It is monic of degree d, with every lower coefficient divisible by the
Gaussian prime 3. Its constant coefficient has real part 6 modulo 9 and
imaginary part 0 modulo 9, so it is not divisible by 9. The existing Mathlib
Eisenstein criterion therefore makes F(P,Q) irreducible, hence prime, in
Z[i][X]. The formal identity

    2 F(P,Q) F(Q,P) = E(P)^2+E(Q)^2

and monic degree comparison identify one of the two factors. Real and
imaginary coefficients recover the ordered parameter pair.

All of this is proved over Gaussian integers, with no irreducibility claim
over C, no extra axiom, and no unproved specialization step. The coefficient
factor 6 makes the displayed half-sum/half-difference normalization integral
and monic; the definition itself uses no division.

Public APIs include `pair_coeff`, `pair_monic_degree`, `pair_injective`,
`pair_irreducible`, `norm_identity`, `encoding_pair_matching`, `formal_sidon`.

## The exact formal family still does not specialize automatically

`FormalGaussianSpecialization.lean` gives four explicit degree-18 parameters
P_0,...,P_3 with constant coefficient exactly 1. Thus all four are admissible
at d=19, and their encodings have leading coefficient 1, all lower
coefficients divisible by 6, and constant coefficient exactly 6.

The base is the PRIME 1439, verified by the kernel. At this base, their four
positive, distinct integer evaluations have a nontrivial equal-square-sum
relation. The exact formal discrepancy is

    E(P_0)^2+E(P_1)^2-E(P_2)^2-E(P_3)^2
      = 48 X^25 (1439-X) (X-1) (X^5-1).

`discrepancy_ne_zero` proves it is a nonzero polynomial. `collision` proves
its evaluation at 1439 vanishes. `formal_square_sidon` verifies Sidonness of
the four formal square values; `specialization_not_sidon` verifies failure
of Sidonness after evaluation. `value_injective` additionally verifies that
evaluation has not merely identified two of the root values.

The identity comes from the earlier fixed-constant carry construction after
scaling its short Gaussian factor by two, with parameters u=12, v=120 and
uv=1439+1. The final Lean theorem checks the polynomial identity directly by
`ring`; no Sympy result is trusted. Concrete integer values and primality
use trusted kernel arithmetic, not native_decide.

This is a counterexample to a blanket specialization rule for the exact
proved formal family, even at a prime base. It is NOT a counterexample to
the original asymptotic conjecture, and does not show every large subclass
or every prime base has a collision.

## The remaining quantitative issue

No estimate was obtained that bounds the number of carry-induced collision
supports in a near-linear-size specialization family by N^(1+o(1)). The
formal theorem alone supplies no such bound. The existing LowCollision
reduction is still conditional, and no actual main-gap exponent improved.

## Verification

Both modules compile without warnings or admissions and have built .oleans.
Their four and eight printed audits, respectively, use only

    propext, Classical.choice, Quot.sound.

Logs:

    /tmp/formal-gaussian-sidon.log
    /tmp/formal-gaussian-specialization.log
    /tmp/spec-formal-gaussian-check.log

Technical points resolved: polynomial definitions need a noncomputable
section; Gaussian coefficient projections require reducing the numeral
square explicitly; compute_degree can leave a final natural inequality;
and concrete Fin-vector entries should be reduced before numerical eval.
The temporary API-check file was deleted. No proof submission was made.
