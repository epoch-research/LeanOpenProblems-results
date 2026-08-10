# Analysis of OEIS A113258 perfect-power conjecture

Conjecture: ∃ n>4, a(n)=b^e with b,e>1, where
a(n) = Σ_{i=0}^{n-1} (i+1)!^{(n-i)!}.

## Status: FALSE for all verifiable n, but a genuinely OPEN problem in general.

- a(4)=125=5^3 (only known perfect power; excluded by n>4).
- a(5),...,a(10) verified NOT perfect powers (exact + reliable modular checks).
- OEIS author's own comment poses this as an open question.

## What is COMPLETELY provable (in Submission/Spec.lean):
- a(n) ≡ 2 (mod 9) for n≥6, and a(5) ≡ 5 (mod 9).
- Neither 2 nor 5 is a quadratic or cubic residue mod 9.
- ⟹ a(n) is NOT a perfect e-th power for any e divisible by 2 or 3, for all n≥5.

## The irreducible gap: exponents e coprime to 6.
Reduce to prime p = smallest prime factor of e (p≥5). a(n)=c^p.
- 5≤p≤n-1: p | (n-1)!, so 2^{(n-1)!}=(2^{(n-1)!/p})^p is a perfect p-th power, and
  2^{(n-1)!} < a(n) < (2^{(n-1)!/p}+1)^p (sandwich): PROVABLE (factorial inequalities).
- p≥n: 2^{(n-1)!} is NOT a p-th power, sandwich fails. REQUIRES an effective lower
  bound on |2^{(n-1)!} - m^p| ≈ R := a(n)-2^{(n-1)!} ≈ 6^{(n-2)!}.

## Why congruences CANNOT settle the p≥n case (proven meta-obstruction):
For any modulus M and prime p coprime to λ(M), the p-th power map is a bijection on
(Z/M)^*. Since a(n) ≡ -1 (mod q) for all primes q≤(n+3)/2, a(n) is a unit mod any
fixed M. A prime p≥n can be chosen coprime to λ(M) for any fixed M. Hence no finite
set of congruences can exclude these exponents.

## Why even Baker's theorem (not in Mathlib) is insufficient in standard form:
Λ = (n-1)!·log2 - p·log m. Need |Λ| > 2^{-(n-3.585)(n-2)!} ≈ exp(-n·(n-2)!·log2).
Baker: |Λ| > exp(-C·log B·log A1·log A2) with B=(n-1)! (log B≈n log n),
A1=m (log m≈(n-2)! for p≈n). This gives exp(-C·n log n·(n-2)!), whose exponent
magnitude C·n log n·(n-2)! EXCEEDS the required n·log2·(n-2)!. So standard Baker
does not force a contradiction for p≈n. The problem is at/beyond the current frontier.

## Conclusion
Neither direction admits a complete Lean proof with the allowed axioms:
- TRUE: no witness exists for any verifiable n; larger n are unverifiable.
- FALSE: the p≥n regime is genuinely open (beyond elementary + standard Baker).

The submitted Spec.lean contains the complete, verified mod-9 reduction; the residual
coprime-to-6 case is the open kernel.
