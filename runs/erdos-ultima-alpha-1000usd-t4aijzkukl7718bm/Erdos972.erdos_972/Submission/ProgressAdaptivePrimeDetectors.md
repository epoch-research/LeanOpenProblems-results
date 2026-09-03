# Adaptive finite-moment detectors — verified, conjecture still unresolved

`Submission/Spec.lean` remains unchanged with its original `sorry`. No pointwise divergence estimate at every irrational slope, no proof of the conjecture, and no irrational counterexample has been obtained. No incomplete proof was submitted.

Three new auxiliary files compile without warnings or errors. Their principal axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.

Write

* `L(n) = Nat.log 2 n + 1`,
* `E_t(n) = expDivisorSum t n = product_(p|n) (1-p^(-t))` for n>0.

## 1. PolylogMomentPrimeProxy.lean

Namespace `Erdos972PolylogMomentPrimeProxy`.

The adaptive parameter is `t(n)=8 log(L(n))/log(n)`. For n>1, the first `L(n)^8` geometric moments of `primeProxy(t(n),n)` form `finiteProxy n`.

Verified:

* at every prime q, `1/2 <= finiteProxy q <= 1`;
* define `detector n = (L(n)^2/n) * finiteProxy n`;
* at a prime, its value is between `L(q)^2/(2q)` and `L(q)^2/q`;
* at every composite n, `detector n <= 1/(n*L(n)^2)`;
* that envelope is summable over all natural n, by an explicit dyadic-block proof;
* consequently the complete composite error is summable.

No weighted prime-input divergence was proved. This construction alone would use a weighted-divergence target, stronger than mere infinitude in general.

## 2. PolylogPowerPrimeDetector.lean

Namespace `Erdos972PolylogPowerPrimeDetector`.

Using the same adaptive parameter, define for n>1

    powerDetector(n) = E_(t(n))(n)^(L(n)^6),

and zero for n=0,1. This needs only a single polylogarithmic power, rather than a sum of geometric moments.

Verified:

* `0 <= powerDetector(n) <= 1`;
* at every prime q, `3/4 <= powerDetector(q)`;
* for every composite n, `powerDetector(n) <= exp(-L(n)^2) <= 1/n^2`;
* the complete composite error is summable;
* for every alpha>=1, summability of the prime-input detector is equivalent to finiteness of the prime-pair set.

The last equivalence is exact, not the stronger weighted-divergence target from the first file. Its nonsummability side remains unproved at prescribed irrational slopes.

## 3. LogDegreePrimeDetector.lean — simplest and strongest representation

Namespace `Erdos972LogDegreePrimeDetector`.

For n>1 set

    tau(n) = 2 log(2)/log(n),
    normalizedEuler(n) = (4/3) E_(tau(n))(n),
    logDetector(n) = normalizedEuler(n)^(4 L(n)),

and set the detector to zero for n=0,1.

This is a SINGLE LOGARITHMIC-DEGREE POWER of an adaptive Euler product.

Verified:

* `normalizedEuler(q)=1` at every prime q;
* `0 <= normalizedEuler(n) <= 2/3` at every composite n>1;
* `logDetector(q)=1` at every prime q;
* `0 <= logDetector(n) <= 1/n^2` at every composite n;
* the complete composite error is summable over all naturals;
* its restriction to prime inputs along `floor(alpha*n)` is summable for every alpha>=1;
* `summable_primeInputDetector_iff_finite` gives the exact equivalence

      Summable (primeInputDetector alpha)
        iff {p | p.Prime and (floorMul alpha p).Prime}.Finite.

The composite estimate uses `(2/3)^4 < 1/4` and `n < 2^L(n)`. There is no hidden prime-distribution or irrationality hypothesis in these pointwise bounds.

## Precise remaining gap

The logarithmic-degree representation does NOT supply the required prime-input lower bound. Both its smoothing parameter and its degree vary with n, and its normalization also grows with the degree. Fixed-parameter/fixed-moment means cannot be applied at these moving choices without uniform arithmetic estimates.

Expanding a power of the Euler product still involves divisors throughout the output range; a small polynomial degree is not a small-divisor cutoff or a justification for discarding the signed large-divisor tail. No sufficient such tail bound or signed correlation estimate has been obtained.

In particular, do not claim that q^2 moments are necessary for all prime detection. That earlier scale concerned a fixed parameter. The new adaptive detector has logarithmic degree, but its required pointwise nonsummability remains equivalent to the original difficulty.

## Scratch/API notes

`CheckPolylogPowerAPI.lean` contains intentionally failed checks for nonexistent `Real.log_two_lt_one` and `one_sub_mul_le_pow`. Do not import it into a proof.

Useful actual APIs:

* `Nat.log_pos (hb : 1 < b) (hbn : b <= n)`;
* `Real.exp_nat_mul (x : Real) (n : Nat)`;
* `one_add_mul_le_pow (H : -2 <= a) n`;
* `Real.log_le_sub_one_of_pos`;
* `Summable.indicator`.

Beware that unrestricted `simp` on `Real.log_pow 2 2` can simplify the theorem itself to `True`; use explicit `simp only` with the numerical power identity when proving `log 4 = 2 log 2`.
