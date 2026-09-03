# Near-linear fractional square-Sidon mass

This is NOT a settlement of Erdős 773. The original theorem in `Spec.lean`
still has one admission at line 2031, and the file was not changed.

## Verified definitions and results

`FractionalSquareSidon.lean` imports the existing clean collision bounds and
defines `Erdos773.Fractional.Feasible N w` by:

* 0 <= w(n) <= 1 for 1 <= n <= N;
* for every positive D,

      sum_{1 <= a < b <= N, b^2-a^2=D} w(a)w(b) <= 1.

The theorem `indicator_iff_sidon` proves that for A subset [1,N], the indicator
of A is feasible if and only if the squares of A form a Sidon set. Thus this
is an exact formulation on 0-1 weights, not an unrelated necessary condition.

The theorem `near_linear_fractional_mass` proves:

    for every epsilon>0, eventually in N there exists a feasible w with
    sum_{n=1}^N w(n) >= N^(1-epsilon).

In fact the constructed weights are uniform, w(n)=N^(-epsilon), with exactly
that total mass. The already verified divisor bound implies that eventually
every positive difference has at most N^(2epsilon) representations, so its
weighted capacity is at most N^(2epsilon)*N^(-2epsilon)=1.

`weighted_capacities` proves that all finite nonnegative linear combinations
of these individual difference-capacity constraints hold as well.

## Meaning and limitations

This identifies a limitation of the continuous pair-capacity relaxation.
There cannot be a fixed-power upper bound on its feasible total mass. Merely
adding nonnegative weighted sums of the same capacities does not change this.

It does NOT prove that arbitrary upper-bound methods must fail, nor that the
conjecture is true. A proof using the 0-1 condition can be stronger than the
continuous relaxation. No rounding theorem with subpower loss has been
proved for these weights. The original conjecture requires an actual set,
not a fractional weighting. The fractional result has deliberately not been
substituted for the original statement or inserted into `Spec.lean`.

The exploratory localized-interval counting in this continuation did not
yield a new bound on the actual maximum Sidon-subset cardinality.

## Verification

    lake env lean -s 65536 Submission/FractionalSquareSidon.lean

The three printed audits (`near_linear_fractional_mass`,
`weighted_capacities`, `indicator_iff_sidon`) contain only propext,
Classical.choice, and Quot.sound. No admissions are present.
Log: `/tmp/fractional-square-sidon.log`.

## Lossless rounding is false (verified continuation)

The same Lean file now proves `lossless_rounding_fails`. For N=7, set
w(5)=1/2 and w(n)=1 for the other roots in [1,7]. These weights are feasible
and have mass 13/2, but the maximum Sidon-subset cardinality of the first
seven squares is exactly 6.

The feasibility certificate is computed over rationals with `decide +kernel`
and then transported to the reals. The finite maximum is also kernel-checked.
All four printed audits are clean, including `lossless_rounding_fails`.

This refutes only the claim that feasible mass can always be rounded without
any loss. It does not refute rounding with a constant or subpower
multiplicative loss (or even a suitable additive loss in this small example).
No such asymptotic rounding theorem has been proved, and the original
conjecture remains unresolved.
