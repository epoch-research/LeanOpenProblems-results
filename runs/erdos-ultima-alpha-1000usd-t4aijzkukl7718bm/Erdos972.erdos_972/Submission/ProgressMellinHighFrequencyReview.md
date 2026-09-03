# High-frequency Mellin review — no settlement

Spec.lean is unchanged and retains its original sorry. This review adds no
proved prime-pair lower bound, no irrational counterexample, and no new Lean
theorem. No incomplete proof was submitted.

## Question examined

Could quantitative uniform cancellation of the actual Möbius Dirichlet
polynomials over polynomially growing frequency ranges close the gap left
by ProgressMellinCoefficient.md and ProgressMellinEnergy.md?

No sufficient argument was obtained. Such a quantitative Möbius estimate
has NOT been proved in this development. Even assuming a uniform subpower
relative saving, the direct supremum/energy argument is insufficient.

## Scaling check (an explanatory calculation, not a new Lean theorem)

In a balanced four-factor block, write each factor length as M and the
product scale as N=M^2. A ratio window corresponding to an additive floor
strip has logarithmic width of order 1/N, so its Mellin frequency range is
of order N. A schematic absolute bound has the form

    (1/N) * integral_{|t| <= N} |A(t) B(t) C(t) D(t)| dt.

Suppose the two actual-coefficient polynomials have supremum bounds
|A|,|C| <= epsilon*M. The other two mean-square estimates each have size
N*M up to logarithmic factors. Taking the two suprema and applying
Cauchy--Schwarz to B,D gives an upper bound of size

    epsilon^2 * N^(3/2) * (logarithmic factors),

not epsilon^2*N. A subpower relative saving in epsilon does not absorb
this power loss. Four-factor mean-square estimates avoid this power loss,
but retain the unsigned energy and do not supply the needed signed saving.
This is a limitation of these estimates, not a theorem ruling out another
use of the actual coefficients.

A hypothetical inverse principle saying that every large four-factor
correlation must come from a large individual Mellin coefficient was also
considered. No such principle was proved or imported. Diagonal
multiplicative correlations already show why an unrestricted version would
be false; removing those diagonals using irrationality still requires a
substantive arithmetic argument.

The remaining task is unchanged: a genuine signed four-factor lower gap,
a prime-pair correlation lower bound exceeding the prime-power error, or
an actual irrational counterexample. No new result in this review can be
substituted for any of these.
