# Divisibility-chain obstruction (not a disproof of Erdős 68)

The following auxiliary construction shows that the condition `A_n | A_(n+1)`
alone does not imply irrationality of `sum 1/(A_n-1)`. Its `A_n` are NOT the
factorials in the conjecture. This note is mathematical reasoning, not a new
Lean-verified theorem.

Set `A_0=1` and `r_0=1/4`. Recursively define

    q_n = floor((1/r_(n-1)+1)/A_(n-1)) + 1,
    A_n = q_n A_(n-1),
    d_n = A_n-1,
    r_n = r_(n-1) - 1/d_n.

The floor inequalities give

    1/r_(n-1) < d_n <= 1/r_(n-1) + A_(n-1).

Thus every remainder is positive and rational. Put `x_n=A_n r_n`. Then

    r_n <= [x_(n-1)/(1+x_(n-1))] r_(n-1),
    x_n <= x_(n-1) + r_n.

The second inequality follows from

    x_n = d_n r_(n-1) - 1 + r_n.

Inductively these inequalities imply

    r_n <= (1/4) 3^(-n),
    x_n <= 1/4 + sum_{i=1}^n (1/4) 3^(-i) < 3/8 < 1/2.

Indeed, `x_(n-1)<=1/2` makes the factor in the first bound at most `1/3`.
Consequently `r_n` tends to zero, and telescoping proves

    sum_{n>=1} 1/(A_n-1) = 1/4.

Also `A_(n-1) | A_n` by construction. Moreover

    q_n > (1/r_(n-1)+1)/A_(n-1)
        = (1+r_(n-1))/x_(n-1) > 2,

so these integers and their predecessors are strictly increasing. The first
values of `A_n` are `6, 24, 168, 2016`; their reciprocal denominators are
`5, 23, 167, 2015`.

No bound or asymptotic formula for the ratios `q_n` is claimed here. In
particular this construction does not treat the exact factorial ratios
`q_n=n+1`, and does not resolve the original conjecture.

`Submission/Spec.lean` remains unchanged, with the conjecture unproved.

## A fully verified ceiling-rule construction

`CeilingEngel.lean` now proves a rational reciprocal-series obstruction with
A_0=2, r_0=1/4, and the non-strict ceiling rule. Its theorem
`CeilingEngelDevelopment.rational_chain_series` includes positivity, oddness,
the divisibility chain after adding one, and real sum exactly 1/4.
Convergence follows from the verified bound r_n<=(1/4)*2^(-n), so this is not
just a nontermination claim. The first denominators are 5,23,167.
See the new section in ModifiedEngelNotes.md. The original conjecture remains
unsettled; these are different denominators.
