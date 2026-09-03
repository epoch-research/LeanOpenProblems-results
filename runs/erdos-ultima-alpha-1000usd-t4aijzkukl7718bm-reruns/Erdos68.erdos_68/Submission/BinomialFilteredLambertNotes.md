# Congruences for the actual binomially filtered Lambert coefficients

Verified auxiliary progress, NOT a proof or disproof of Erdős 68.
`Submission/Spec.lean` remains unchanged with its original `sorry`.

`BinomialFilteredLambert.lean` compiles without warnings. All three printed
principal axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`.

## Definition and exact operator connection

For an integer sequence a, put

    filterStep(k,a)(n)=a(n)-choose(n,k)*a(n-k).

Iterate this over a finite list ks, starting with the original Lambert
coefficients a_n. This gives the integer sequence b_n=`filtered ks n`.
Formally it multiplies the exponential generating series by

    product_(k in ks) (1-z^k/k!).

The file does not rely on this formal-series description: it verifies the
exact real identity, with M=sum(ks),

    (n+M)! * applyShifts(ks, fun m => a_m/m!)(n) = b_(n+M).

Thus these are coefficients of the actual normalized row-cancelling
operator, not coefficients of a different comparison series or of a
small-tail carry.

## New congruences

1. If p is prime and every k in ks satisfies 0<k<p^(r+1), then

       b_(p^(r+1)) = 1 (mod p).

   Each filter changes that coefficient by a multiple of
   choose(p^(r+1),k), which is divisible by p. The unfiltered Lambert
   coefficient is already one modulo p.

2. If p is prime, n>=2, p divides n-1, and every k in ks satisfies
   2<=k<p, then

       b_n = 1 (mod p).

   Lucas's congruence gives choose(n,k)=0 modulo p because n=1 modulo p
   and 2<=k<p. Each filter therefore preserves the unfiltered
   predecessor congruence at this prime.

Neither theorem says b_n is exactly one. The second theorem does not
assert the full predecessor congruence modulo n-1 when that modulus has
small prime factors.

Principal declarations:

* `filterStep_modEq`
* `filterSteps_modEq`
* `filtered_prime_power`
* `choose_dvd_at_pred`
* `filtered_at_pred`
* `filterSteps_scaled_identity`
* `filtered_lambert_scaled_identity`

## Remaining gap

These congruences may constrain gcds and integer lifts for the filtered
coefficient windows. No bound on a useful complete lift, its coefficient
height, or the primitive denominator of a small affine form has yet been
proved. They do not establish irrationality or the required infinite
nonvanishing for integrally cleared forms.

The preceding first-row inverse review also produced no such bound:
rational inversion introduces additional denominators, and no reduction
of the aggregate integer coefficient pair sufficient to retain smallness
was established. No external numerical computation is used in the new
Lean declarations. No proof or disproof of Spec.lean has been submitted.
