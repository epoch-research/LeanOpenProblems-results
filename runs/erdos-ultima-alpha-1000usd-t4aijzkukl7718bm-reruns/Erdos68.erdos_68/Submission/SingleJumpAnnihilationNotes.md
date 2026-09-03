# Coincident single-jump row obstruction

This is verified auxiliary work, not a settlement of Erdős 68.
`Submission/Spec.lean` is unchanged with its original sorry.

`SingleJumpAnnihilation.lean` compiles and has a built olean. Its four
principal axiom audits contain only propext, Classical.choice and Quot.sound.

## Exact algebraic statement

Let a and b be different nonzero rational numbers. Fix any finite collection
of rational weights z_i and a partition P of their indices. If

    sum_i z_i * (if P(i) then 1/a else 1) = 0,
    sum_i z_i * (if P(i) then 1/b else 1) = 0,

then sum_i z_i=0. Writing L for the weight sum outside P and R for the weight
sum inside P, the equations are aL+R=bL+R=0; hence L=R=0.

The result extends to geometric rows with exponents k+1_P and l+1_P,
even when k and l differ. Unlike the earlier denominator-divisibility
lemma, this result permits unrestricted rational weights.

## Factorial specialization

For u>0 and arbitrary sample indices n_i in [4u,8u),

    floor(n_i/(2u)) = 2 + 1_(n_i>=6u),
    floor(n_i/(3u)) = 1 + 1_(n_i>=6u).

Both rows have their only jump at 6u, with different factorial bases.
`factorial_window_rows` therefore proves that simultaneous annihilation of

    r_d(n)=1 / ((d!)^floor(n/d) * (d!-1)),  d=2u and d=3u,

forces sum_i z_i=0. The sample indices need not be consecutive. Taking
z_i=w_i*n_i! gives the corresponding constraint on factorial-weighted
operators: their coefficient of alpha vanishes.

## Scope

This obstructs a proposed selective cancellation of the active Lambert
bands in short windows. It is not an analytic error lower bound and does
not exclude approximate cancellation, a longer sampling interval, or
cancellation of a combined group rather than each row separately.

No nonzero integer linear forms tending to zero, infinite carry changes,
or other complete proof or disproof of the original conjecture were found.
