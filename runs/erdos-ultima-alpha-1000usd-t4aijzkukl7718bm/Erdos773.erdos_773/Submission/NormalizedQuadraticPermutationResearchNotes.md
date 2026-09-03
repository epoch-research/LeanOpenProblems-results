# Repeated-modulus normalization: verified permutation theorem

The original Erdős 773 conjecture is NOT settled. `Spec.lean` is unchanged
at SHA-256 257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940.
It retains its sole admission at line 17287 for 0 < epsilon < 1/3. The
verified eventual endpoint remains M(N) >= N^(2/3).

## New clean module

`NormalizedQuadraticPermutation.lean` imports only FormalConjecturesUtil.
It builds without warnings or admissions. Its six printed audits use only
propext, Classical.choice, and Quot.sound. Log:

    /tmp/normalized-quadratic-permutation.log

Namespace: `Erdos773.NormalizedQuadraticPermutation`.

For integer coefficients define quadratic(a,b,x)=a*x^2+b*x.

* `factor_coprime`: if m divides a and IsCoprime m b, then
  IsCoprime (m^k) (a*(x+y)+b), for every natural k.
* `modEq_iff`: under the same assumptions, outputs are congruent modulo
  m^k if and only if inputs are congruent modulo m^k.
* `bijective`: for a positive natural modulus m, the corresponding function
  on ZMod (m^k) is bijective.
* `range_eq_univ`: every output residue occurs.

No primality or oddness assumption is needed. Exponent zero is included.
The proof factors the output difference as

    (y-x)*(a*(x+y)+b),

and cancels its coprime second factor.

## Exact renormalization and stability

For the polynomial arising from roots q*x+r, the exact identity is

    quadratic(q,2r,p*x+s)
      = p*quadratic(q*p, 2*(q*s+r), x) + quadratic(q,2r,s).

`renormalize` verifies it. `renormalized_unit` shows that if m divides q and
2r is a unit modulo m, then 2*(q*s+r) is still a unit modulo m.
`renormalized_bijective` proves bijectivity modulo every m^k after an
arbitrary further index restriction x -> p*x+s.

Thus a modulus already dividing the normalized leading coefficient supplies
NO new missing-residue-class loss in the unit-linear-coefficient case. This
makes precise the obstruction noticed in the previous residue-iteration
review. It does not assert that all residue methods fail, and it is not an
upper bound for the original maximum. Fresh primes, cross-fiber correlations,
and non-unit classes are not settled by this lemma.

## Other review in this continuation

The formal Gaussian Sidon construction, moment constraints, and carrier
selection were reviewed without obtaining a new sufficient specialization
criterion. High multiplicity of vanishing at X=1 cannot simply be treated
as forcing large coefficients: the existing signed-jet constructions are
relevant. No near-linear low-collision carrier, improved actual exponent,
or fixed-power unrestricted upper bound was proved.

The main file was not enlarged with this auxiliary result. No incomplete
proof was submitted.
