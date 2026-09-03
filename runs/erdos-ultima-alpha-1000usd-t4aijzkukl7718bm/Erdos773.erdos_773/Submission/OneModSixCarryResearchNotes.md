# Carry obstruction at unbounded bases 1 modulo 6

`OneModSixCarry.lean` verifies the family derived in the preceding continuation.
For every integer s >= 0, the base is B=2304s²+4704s+2395, and the three
roots have constant-first digit lists:

    [6, 576s²+1404s+840, 828s²+1932s+1116, 60s+66, 1]
    [6, 1152s²+2568s+1428, 1332s²+2976s+1656, 72s+78, 1]
    [6, 1728s²+3732s+2016, 1692s²+3732s+2052, 84s+90, 1].

All digits are positive and less than B. All lower digits are divisible by
6, and the constant digit is exactly 6. The associated parameter polynomials
are admissible for `FormalGaussianSidon.formal_sidon` at degree 4. Thus the
formal polynomial squares are Sidon.

The formal discrepancy is checked by `ring`:

    E0²+E2²-2E1² = 288(s+1)² X² (B-X)(X+1).

At X=B this gives a nontrivial three-root square progression. The root values
are positive and strictly ordered. `specialization_not_sidon` checks that
the evaluated square values are not Sidon. `base_mod_six` proves B%6=1,
and `bases_unbounded` proves the family of bases is unbounded.

All six printed audits use only propext, Classical.choice, and Quot.sound.
Build log: /tmp/one-mod-six-carry.log. No admissions or warnings.

## Scope

This is not a disproof of Erdős 773. It does not give failure at every base
1 modulo 6, does not give an unbounded prime-base family, does not meet equal
histogram or half-base digit restrictions, and does not improve the bounds
for the unrestricted Sidon maximum. `Spec.lean` is unchanged.
