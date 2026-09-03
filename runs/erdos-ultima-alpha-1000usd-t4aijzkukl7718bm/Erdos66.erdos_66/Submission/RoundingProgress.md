# Exact fractional model and the remaining rounding error

## Status

The original conjecture is still **not proved or disproved**. `Spec.lean` is
unchanged and retains its original `sorry`. The results below are auxiliary.

## Exact fractional construction

`FractionalProfileExplore.lean` constructs a sequence p_n with

    p_0 = 1,   0 <= p_n <= 1,   p_n decreasing,
    sum_{i+j=n} p_i p_j = H_{n+1}.

In particular, its convolution divided by log(n) tends to 1.

The construction uses t_0=0, t_n=1/(n(n+1)) for n>0, and the triangular recursion

    s_0=0,
    2 s_n = t_n + sum_{i+j=n} s_i s_j.

Nonnegativity is immediate by induction. The cumulative convolution inequality
and sum_{i<=N} t_i = 1-1/(N+1) imply every finite partial sum of s is at most 1.
Set p_n=1-sum_{i<=n} s_i. Formal power-series identities give

    (1-X)P = 1-S,
    2S = T+S^2,
    (1-X)^2 sum H_{n+1} X^n = 1-T,

hence P^2=sum H_{n+1} X^n. All steps are proved in Lean, not assumed.

Main theorem: `Erdos66Fractional.exists_fractional_harmonic_profile`.

## Rounding

`RoundingExplore.lean` defines an actual set by differences of floors of the
cumulative profile. Since 0<=p_n<=1, each floor increment is 0 or 1. Its indicator
a_n satisfies

    |sum_{i<N}(a_i-p_i)| <= 1.

For any rounding error e with prefix sums bounded by D, the same file proves

    |(e*p)(n)| <= 2D.

The exact decomposition is

    r_A(n) = H_{n+1} + 2(e*p)(n) + (e*e)(n).

Consequently, for bounded-discrepancy roundings,

    r_A(n)/log n -> 1  iff  (e*e)(n)/log n -> 0.

Main theorem: `logarithmic_limit_iff_quadratic_error`.
`rounded_profile_suffices` is explicitly conditional on the unproved quadratic
error estimate for the floor-rounded profile. It is not a proof of Erdős 66.

## Why the remaining estimate is not automatic

The checked example e_n=(-1)^n/2 has prefix sums bounded by 1/2 but

    (e*e)(n) = (n+1)(-1)^n/4.

Its normalized self-convolution does not tend to zero. This example is not a
counterexample to the original conjecture, nor does it decide the behavior of
the particular harmonic-profile rounding.

No proof or disproof of the required quadratic-error limit has been found.

## Update: averaged quadratic error is now controlled

See `MovingWindowProgress.md`. The same explicit rounded set now has a
checked logarithmic representation average on every moving-window sequence
with w(n)<=n and n/(w(n)^2 log n)->0. This is signed averaged control, not
the missing pointwise quadratic-error estimate. Spec.lean remains unresolved.
