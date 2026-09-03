# Growing rational Fourier grid — not a settlement

Spec.lean is unchanged and retains its original sorry. No prime-pair lower
bound or irrational counterexample has been obtained.

This continuation goes beyond the fixed finite sets in
ProgressGeneralRationalFourier.md. All three new proof files compile and
principal declarations audit with only propext, Classical.choice, Quot.sound.

## GrowingRationalGrid.lean

Namespace Erdos972GrowingRationalGrid.

For positive B, gridIndices(B) consists of triples (q,a,j) satisfying

    1 <= a < q <= B,   -B <= j <= B.

Their image in ZMod J uses the exact integer representatives

    floor((a/q)*J) + j.

The number of indices is at most B^2(2B+1), hence at most 3B^3.
Nonreduced fractions, collisions modulo J, and overlapping bands are allowed:
the proof bounds an absolute mode sum over the image.

`rationalGrid_norm_sum_bound` proves the complete finite bound

    sum_{k in grid(J,B)} |FourierTerm(k)/J|
      <= 15(1+4*pi) B^5 v L^2 [Ep+40vL^2(Bd+1)].

It uses the actual recentered arithmetic remainder at both coordinates.
The hypotheses are the all-residue prime-input and ordinary divisor-residue
prefix bounds, for q<=B. The output DFT and global empirical input mean are
retained exactly as in the previous general rational-band theorem.

Define

    bandCutoff(u) = floor fourth-root(root64(u)),
    v = root64(u),   N=floor(u^6/alpha).

Then bandCutoff tends to infinity, is positive for u>0, and B^4<=v.
This is an explicit power-root cutoff, of order u^(1/256), not a diagonal
choice of increasingly large fixed finite sets.

## GrowingRationalGridBudgets.lean

Namespace Erdos972GrowingRationalGridBudgets.

`gridBudget` is the preceding finite bound at B=bandCutoff(u), with

    Ep=scaledRowError(dualScaleLoss alpha,u,v),
    Bd=236v u^4.

`gridBudget_tendsto` proves gridBudget/N -> 0 for alpha>=1.

The prime-row contribution uses B^6<=v^2, hence B^5/v^2<=1/B.
Logarithms divided by B vanish using the existing slower cutoff
root64(root64(u))<=B. The ordinary divisor contribution uses B^5<=v^2
and v^6<=u^2, reducing it to the already controlled logarithm/root64 budget.
No quantitative PNT error or moving fixed-mode limit is assumed.

`rationalGrid_density_zero` also proves

    card(grid(J,bandCutoff(u)))/J -> 0,
    J=floor(alpha*N)+1.

Thus the enlarged grid still occupies a vanishing fraction of the full
Fourier group. This is only a coverage statement, not a signed estimate
on the complement.

## GrowingRationalGridObstruction.lean

Namespace Erdos972GrowingRationalGridObstruction.

`eventually_rationalGrid_norm_sum_small` proves the growing-grid estimate
at every sufficiently large u satisfying ResidueTwoSidedScale alpha u.
All varying moduli q<=bandCutoff(u) are handled by the finite uniform row
bounds before the limit is taken.

`eventually_gridWithLow_small` adds any fixed finite set of low integer
frequencies. It bounds absolute sums, so overlap with the growing grid is
included. This does not assert control of a polynomially growing low band.

`finite_primeSet_forces_negative_growing_grid_complement` proves:
if the prime-pair set is finite, then for every fixed finite low set S,
epsilon>0, and B, there exists one scale u with

    u>B, growingCutoff(u)>B, bandCutoff(u)>B, N>0,
    OutputPrimeScale, FullTwoSidedScale, ResidueTwoSidedScale,

and

    |frequencyCovariance(gridWithLow(J,bandCutoff(u),S)^c)/N + 1|
       <= epsilon.

All eventual thresholds precede the single invocation selecting the actual
common scale. No independent existential scale sets are intersected.

## Unresolved task

The complement's signed contribution remains uncontrolled. The growing-grid
result excludes more frequencies than the earlier fixed-band theorem, but
it still does not contradict the forced value near -N. A sufficient lower
bound on the remaining correlation, another genuine prime-pair argument,
or an actual irrational counterexample is still necessary.

These auxiliary results do not replace the original sorry and have not
been submitted as a settlement.
