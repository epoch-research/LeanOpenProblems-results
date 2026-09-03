# Nonrectangular geometric truncations: a verified obstruction

`GeometricClearingBarrier.lean` is auxiliary work, not a proof or disproof of
Erdős 68. It compiles with only `propext`, `Classical.choice`, and `Quot.sound`.
The conjecture in `Spec.lean` remains unchanged and unproved.

Write d_k=k!-1 and alpha=sum_(k>=2) 1/d_k.

## A prime divisor beyond k+2

The following statements are now Lean-verified:

* Every prime divisor of d_k exceeds k+1, for k>=2.
* Consequently gcd(d_k,(k+1)!)=1.
* For k>=4, at least one prime divisor of d_k exceeds k+2.

For the first claim, a prime divisor p must exceed k by factorial
divisibility. The possibility p=k+1 is excluded by Wilson: k!=-1 modulo p,
whereas p|d_k would require k!=1 modulo p.

For the third claim, suppose no prime divisor exceeds k+2. All prime factors
would then equal the prime p=k+2, so d_k=p^e. Since k>=4 and p is odd, k>=5
and k+1 is even and at least 6. Every even m>=6 divides (m-1)!: writing m=2a
with a>=3, one can use 2*a | 2!*a! | (a+2)! | (2a-1)!.
It follows that k+1 divides k!. But p=1 modulo k+1, so k!=p^e+1=2 modulo
k+1, a contradiction.

The theorem names are:

* `prime_dvd_pred_factorial_gt_succ`
* `pred_factorial_coprime_succ_factorial`
* `exists_prime_dvd_pred_factorial_gt_add_two`

These are elementary prime-support facts, not irrationality criteria.

## Denominator bound independent of truncation lengths

Let K>=5 and r>=0. Suppose M is a positive integer divisible by all three of

    d_(K-1), d_K, ((K+1)!)^r.

Then the verified `clearing_two_rows_bound` says

    ((K+1)!)^r * d_(K+1) < M.

Proof: choose a prime p>K+1 dividing d_(K-1), using the new prime lemma.
The existing consecutive-denominator coprimality shows gcd(p,d_K)=1.
Both p and d_K are coprime to (K+1)!, so

    d_K * p * ((K+1)!)^r | M.

Also p*d_K>d_(K+1), by d_(K+1)=(K+1)d_K+K and d_K>K.
This proves the bound.

## Application to positive geometric truncations

Sum the original rows 2 through K exactly. For a finite block of rows after
K, replace each 1/(k!-1) by an independently chosen finite geometric prefix

    sum_(j=1)^(r_k) 1/(k!)^j,

where r_k may be zero. Denote this rational approximation by R. Every
truncated row underestimates its original row. The error from the first
truncated row is exactly

    1 / (((K+1)!)^(r_(K+1)) * d_(K+1)).

The remaining errors are nonnegative and the omitted infinite tail is
positive. Therefore, for every positive integer M that clears at least

    d_(K-1), d_K, ((K+1)!)^(r_(K+1)),

one has

    M*(alpha-R)>1.

This is the theorem `mixedApprox_termwise_scaled_error_gt_one`.
Its parameters in Lean are K=n+3, n>=2; the exact prefix has n+2 rows and
the following truncated block has L+1 rows. Truncation lengths are arbitrary
natural numbers supplied by `orders : Nat -> Nat`.

## Essential limitation

The hypotheses impose **termwise** clearing. They do NOT follow just from
M being the reduced denominator of the total approximation R. Cancellation
between rows can invalidate the divisibility hypotheses; earlier work has
already exhibited such cancellation in the original partial sums.

Thus this theorem rules out the termwise-cleared construction, including
arbitrary nonrectangular geometric truncations after an exact prefix. It
neither gives a lower bound for every reduced denominator nor proves the
original series rational or irrational. No proof has been submitted.

## A verified reason the reduced-denominator limitation is essential

`MixedReducedCancellation.lean` now exhibits a mixed approximation in this
same family with reduced positive scaled error strictly below 1:

    R = S_5 + 1/6! + 1/(6!)^2 + sum_(k=7)^10 1/k!
      = 7057699/5630400.

Thus the greater-than-one conclusion is false if the multiplier is merely
the reduced denominator and the termwise divisibility hypotheses are removed.
See `MixedReducedCancellationNotes.md`. This is a single finite approximation,
not an infinite small-error construction and not a settlement of Erdős 68.

