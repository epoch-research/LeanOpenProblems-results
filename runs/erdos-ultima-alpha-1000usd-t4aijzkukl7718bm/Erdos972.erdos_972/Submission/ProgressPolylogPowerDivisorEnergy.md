# Polylogarithmic-power divisor cutoff: verified energy obstruction

The original conjecture is STILL UNRESOLVED. `Submission/Spec.lean` remains
unchanged with its original `sorry`. No complete proof, sufficient pointwise
prime-pair estimate, or irrational counterexample was obtained. No incomplete
proof was resubmitted during this development.

## New verified files

- `Submission/PolylogPowerDivisorLimit.lean`
- `Submission/RawMobiusCutoffEnergy.lean`
- `Submission/PolylogPowerDivisorEnergy.lean`

All three compile without errors or warnings. Their printed principal axiom
audits use only `propext`, `Classical.choice`, and `Quot.sound`.

These results concern the ACTUAL unnormalized detector from
`PolylogPowerPrimeDetector.lean`, not the normalized logarithmic-degree detector
from the earlier obstruction.

Write L(n)=Nat.log 2 n+1, t(n)=8 log L(n)/log n, J(n)=L(n)^6, and

    F(n)=E_{t(n)}(n)^{J(n)}       for n>1,
    F(n)=0                      otherwise.

For the divisor inversion at input n, define

    c(n,d)=profileCoeff (fun m => E_{t(n)}(m)^{J(n)}) d,
    T_D(n)=sum_{d<=D, d|n} c(n,d),
    M_D(n)=sum_{d<=D, d|n} mu(d),
    Q(D)=sum_{d,e<=D} mu(d)mu(e)/lcm(d,e).

## 1. Fixed-divisor limit

`PolylogPowerDivisorLimit` proves:

- `parameter_tendsto_zero`: t(n)->0.
- `adaptiveCoeff_tendsto`: c(n,d)->mu(d) for each fixed d.
- `full_divisor_identity`: F(n)=sum_{d|n}c(n,d), for n>1.
- `truncatedDetector_eq_divisor_sum`: T_D is precisely that expansion truncated
  to divisors <=D, for n>0.
- `truncatedDetector_sub_mobius_tendsto`: T_D(n)-M_D(n)->0 for each fixed D.

The moving exponent does not cause the fixed small-divisor coefficients to
vanish. They approach the ordinary Möbius coefficients.

## 2. Uniform lower bound on the raw Möbius quadratic mean

`RawMobiusCutoffEnergy` proves, elementarily:

- `primeSquareMass_le`: sum_{p prime, p<=N}1/p^2 <=12/25 for every N. The proof
  evaluates a finite sum through 40 and bounds the reciprocal-square tail.
- A totient product lower bound and a square-divisor union bound give, for
  n>0,

      mu(n)^2 phi(n)/n >=
        1 - sum_{p^2|n}1 - sum_{p|n}1/p.

- `squarefreeTotientRatio_half_interval`: for D>=80000,

      sum_{D/2<n<=D} mu(n)^2 phi(n)/n >= D/200.

  Small primes are cut at 200; the large-prime tails are absolutely summable.
- Using the existing Selberg diagonalization of Q(D), the upper-half divisors
  have no proper multiples <=D. This yields

      quadraticMain_mobius_lower: Q(D)>=1/200   for D>=80000.

## 3. Obstruction for the actual adaptive detector

`PolylogPowerDivisorEnergy` proves:

- `raw_square_mean_tendsto`: mean of M_D(n)^2 tends to Q(D).
- `raw_square_mean_pos_lower`: Q(D)>=1/(D!) for D>=1, by the exact average over
  the period D! and the value M_D(1)=1.
- A common positive bound for all D>=1 is

      c=min(1/200, 1/(80000!)).

  No enormous factorial is numerically evaluated.
- `powerDetector_square_mean_tendsto_zero`: mean of F(n)^2 tends to zero.
  This uses the existing zero prime density and the globally summable composite
  error, not the original prime-pair conjecture.
- The mean of (T_D(n)-M_D(n))^2 tends to zero.
- A three-square inequality shows that a uniform bound

      sum_{n<=N}(T_D(n)-F(n))^2 <= epsilon*N   for every N

  would force Q(D)<=3epsilon.
- `large_cutoff_energy_failure`: for every D>=80000 there is N>0 with

      sum_{n<=N}(T_D(n)-F(n))^2 > N/1000.

- `no_fixed_uniform_energy_cutoff`: there exists epsilon>0 such that, for EVERY
  D>=1, some N>0 has squared-error sum >epsilon*N.

Thus the direct raw-divisor analogue of the previous fixed-parameter uniform
L2 cutoff theorem also fails for the unnormalized polylogarithmic-power
prime detector. This closes the scope gap explicitly left by the earlier
logarithmic-degree obstruction.

## Scope and remaining task

This does NOT disprove Erdős 972. It does NOT rule out a different expansion,
optimized sieve weights, or sufficient averaged SIGNED cancellation. No
pointwise nonsummability estimate for the prime-input detector, strict
four-factor covariance gap, or alternative prime-pair lower bound was proved.

Do not replace the original `sorry` with one of these obstruction theorems.

Scratch files `CheckPowerLimitAPI.lean` and `CheckMobiusEnergyAPI.lean` contain
intentionally failed API checks and should not be imported.
