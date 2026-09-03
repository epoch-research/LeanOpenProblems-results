# General rational Fourier bands — original conjecture unresolved

`Submission/Spec.lean` remains unchanged with its original `sorry`.
No sufficient prime-pair lower bound or irrational counterexample has been
obtained. No incomplete proof has been submitted as a settlement.

## New verified results

All files below compile. `Submission/AuditRationalBands.lean` audits the
principal declarations with only `propext`, `Classical.choice`, and
`Quot.sound`. The new proof files contain no sorry declarations.

### 1. `ResiduePrimeRows.lean`

Namespace `Erdos972ResiduePrimeRows`.

* `floor_mod_eq_floor_fract` and `floor_mod_eq_iff_arc` identify
  `floor(x) % e = j` exactly with the half-open fractional-part interval
  `[j/e,(j+1)/e)` for nonnegative x.
* `fract_sub_arc` and `inputResidueRow_arc` translate each residue arc into
  an interior arc; the translation is retained.
* `input_residue_row_discrepancy` extends the dual prime-input row estimate
  from residue zero to every `j<e`, with exactly the same `scaledRowError`.
  This is uniform in `e<=v`, in j, and in all prefixes `X<=u^6`, at one
  specified rational approximant to alpha.

### 2. `ResidueDivisorCounts.lean`

Namespace `Erdos972ResidueDivisorCounts`.

* General fractional-part intervals are differences of initial intervals,
  giving twice the old ordinary rotation discrepancy.
* `residueDivisorPairs(alpha,X,d,e,j)` counts positive n<=X satisfying
  `d|n` and `floor(alpha*n)%e=j`.
* `reciprocal_scale_residue_prefix_bound` proves

      |count - X/(d*e)| <= 236*v*u^4,

  uniformly in positive d, positive e<=v, every j<e, and eligible X.
  This uses the same reciprocal rational approximant as the original
  covariance scales. The point n=0 and prefixes shorter than d are handled.

### 3. `ResidueRemainderPrefix.lean`

Namespace `Erdos972ResidueRemainderPrefix`.

The generic `centered_twisted_prefix_bound` applies to any real weight w
with |w|<=1, a prime-weighted prefix error Ep, and divisor-prefix bound B.
It retains both recentered Type-I profiles, the small cutoff Mangoldt term,
and the actual global empirical mean of the input remainder.

Define

    centeredResidue(alpha,e,j,n)
       = 1_{floor(alpha*n)%e=j} - 1/e.

For R=meanCenteredTypeII(W,W), W^2<=v<=N, L>=1, log N<=L-1,
|reciprocalMoebius W|<=1, the actual residue rows imply

    |sum_{n<=X} [R(n)-mean_N R]*centeredResidue(alpha,e,j,n)|
       <= Ep + 40*v*L^2*(B+1).

Here B is the ordinary residue-divisor count error. The error of replacing
`floor(X/d)/e` by `X/(d*e)` is included, not discarded.

### 4. `RationalBandFourierBounds.lean`

Namespace `Erdos972RationalBandFourierBounds`.

For q>0 and integer a nonzero modulo q, the exact character expansion in
all q centered residues gives a prefix bound q times the preceding bound.
A complex summation-by-parts lemma then controls the moving Fourier modes

    |k - (a/q)*J| <= H,    J=floor(alpha*N)+1.

The full finite estimate is

    |FourierTerm(k)/J|
       <= 5*(1+2*pi*H)*q*v*L^2
              *(Ep+40*v*L^2*(B+1)).

The actual recentered output DFT is bounded by `5*v*L^2*J`; neither an
unweighted output count nor an altered floor phase is substituted.

`rationalFrequency J q a j = floor((a/q)*J)+j` satisfies the required
nearness with H=|j|+1. Integer parts use the integer floor.

### 5. Common scales

`ResidueCommonScales.lean`, namespace `Erdos972ResidueCommonScales`, defines
`ResidueTwoSidedScale alpha u`, containing all the new prime-residue and
ordinary divisor-residue rows.

`exists_all_residue_scale` returns this alongside `OutputPrimeScale` and
`FullTwoSidedScale`. It obtains ONE reciprocal rational approximant, derives
the corresponding direct approximant, and proves all conclusions there.
It does NOT intersect independently selected existential scale sets.

`ResidueRecenterScales.lean` retains those additional row hypotheses in
`exists_residue_recenter_covariance_scale`, together with the three
Type-I covariance estimates and full arithmetic recentering correction.

`ResidueFourFactorReduction.lean` strengthens the finiteness obstruction
by also returning `ResidueTwoSidedScale`.

### 6. `RationalBandFourierScales.lean`

Namespace `Erdos972RationalBandFourierScales`.

`eventually_rational_term_small` proves, for each fixed q,a,j with q>0 and
a nonzero modulo q, that the normalized moving Fourier term is <=epsilon*N
at every sufficiently large u satisfying `ResidueTwoSidedScale`.

The finite bound is absorbed in `C*(D+4E)`, where

    C=q*(1+2*pi*(|j|+1)),
    D=the existing dual covariance budget,
    E=the existing joint covariance budget.

The factor two in the ordinary residue count error is retained. Eventual
thresholds use epsilon/(5C), before selecting a common good scale.

`RationalMode` packages a fixed denominator, numerator, offset, and the
positivity/nonzero hypotheses. `majorBands(J,S,T)` is the union of:

* the images of a fixed finite integer-frequency set S;
* the moving frequencies from a fixed finite set T of `RationalMode`s.

`eventually_major_bands_small` bounds the total band contribution by
epsilon*N. The proof bounds absolute sums of normalized modes, so possible
residue collisions and overlap between bands are covered.

### 7. `RationalBandFourierObstruction.lean`

Namespace `Erdos972RationalBandFourierObstruction`.

The strongest new statement is

    finite_primeSet_forces_negative_major_band_complement.

If the prime-pair set is finite, then for every fixed finite S,T, epsilon>0,
and B, there exists a SINGLE common scale with u>B, W>B, N>0, all three
row predicates, and

    |frequencyCovariance(majorBands(J,S,T)^c)/N + 1| <= epsilon.

## Remaining gap

This now treats arbitrary fixed nonintegral rational centers, not only
normalized frequency 1/2. It still does NOT bound the full complementary
signed contribution, which can occupy the many frequencies outside these
fixed-width, fixed-denominator bands. No estimate contradicting its forced
value near -N has been proved. In particular, one cannot take the finite
sets S,T to exhaust the varying Fourier group after the scale is selected.

The requested universal prime-pair conjecture remains unproved and
undisproved. The auxiliary results must not be submitted as its proof.
