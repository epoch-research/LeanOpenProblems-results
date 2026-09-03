# Uniform-in-modulus residue energy and exceptional proportions

## Original conjecture status

Erdos66.erdos_66 remains unproved and undisproved. Spec.lean is unchanged
with its original sorry. No proof was submitted. These are necessary
mean-square conditions for a hypothetical witness, not a settlement.

## Checked production files

* UniformResidueProfileExplore.lean
* UniformWitnessResidueExplore.lean
* UniformResiduePrefixExplore.lean
* UniformResidueExceptionalExplore.lean

All four compile and have current oleans. UniformResidueAudit.lean audits
17 principal declarations; UniformResidueAudit.log reports only propext,
Classical.choice, and Quot.sound. No production file has a sorry or axiom.

## 1. Removing the old modulus loss

For any positive modulus m and residue i, the centered residue indicator
has prefix discrepancy at most one, not m. Its complete m-block sums
vanish; in the remaining prefix it has sum either -t/m or 1-t/m, with
0<=t<m. Summation by parts against the antitone fractional profile p gives

    |projectionError(m,p,i,n)| <= 2.

For every nonnegative f, summing the nonnegative residue convolutions gives

    sum_i |projectionError(m,f,i,n)| <= 2 (f*f)(n).

L-infinity times L1 and p*p=H_(n+1) therefore yield

    sum_i projectionError(m,p,i,n)^2 <= 4 H_(n+1).

Thus the fractional aggregate energy has the modulus-independent bound

    residueEnergy(m,sqrt(c)*p,r) <= 4 c^2 H1(r),

where H1(r)=sum_n H_(n+1) r^n. This removes the old m^3 term.

## 2. One envelope for every modulus simultaneously

Write E(r)=sum_n [r_A(n)-c H_(n+1)]^2 r^n,
H2(r)=sum_n H_(n+1)^2 r^n, and K(r)=(1-r)/[-log(1-r)]^2.
The exact natural variance stability theorem gives

    residueEnergy(m,1_A,r)
      <= 4 c^2 H1(r) + sqrt(E(r)[4E(r)+6c^2 H2(r)]).

For a witness, E(r)K(r)->0, H1(r)K(r)->0, and H2(r)K(r)<=6
near 1. Consequently the scalar envelope

    U(r) = 4 c^2 H1(r)K(r)
           + sqrt((E(r)K(r))[4E(r)K(r)+36c^2])

satisfies U(r)->0 and dominates residueEnergy(m,1_A,r)K(r)
for EVERY positive m, on the SAME neighborhood of 1.

Theorem witness_all_moduli_energy_zero has the order of quantifiers

    for every epsilon>0, eventually r, for every positive modulus m.

Theorem witness_variable_modulus_energy_zero allows an arbitrary
radius-dependent modulus, without a continuity, growth, or boundedness
assumption.

## 3. Uniform ordinary-prefix energy

Let D_m(n)^2=sum_i projectionError(m,1_A,i,n)^2 and r_N=1-1/N.
Nonnegative coefficients give

    r_N^N sum_(n<N) D_m(n)^2 <= residueEnergy(m,1_A,r_N).

Since K(r_N)=1/[N log^2 N] and r_N^N->exp(-1),

    [sum_(n<N) D_m(n)^2]/[N log^2 N] <= U(r_N)/r_N^N -> 0

uniformly in m. The threshold precedes m in
witness_uniform_prefix_energy_zero. The modulus can be any function m(N)
in witness_variable_prefix_energy_zero.

## 4. Uniform exceptional proportions

For fixed epsilon>0 define the finite set

    badTargets(m,A,epsilon,N)={n<N : D_m(n)>=epsilon log N}.

Its normalized cardinality is at most

    prefixEnergy(m,A,N)/epsilon^2.

Hence, for every epsilon,delta>0, eventually N, for EVERY positive m,

    |badTargets(m,A,epsilon,N)|/N < delta.

The normalization here is the COMMON log N on the whole prefix, not
log n. The endpoint witness_variable_bad_proportion_zero permits m to be
chosen arbitrarily after seeing the prefix. Control of D_m simultaneously
controls every endpoint residue error, but only outside the displayed
exceptional target set.

## Limits of the result

Uniformity over moduli does not make the exceptional set empty and gives
no power-saving or repair rate. For m larger than the prefix, distinct
endpoints have distinct residues, and Boolean integrality naturally forces
energy on the order of N log N, not N log^2 N. This remains compatible with
the proved little-o upper bound. No logarithmic-order fluctuation
contradiction follows.

The missing positive directions remain uniform sublogarithmic quadratic
Boolean rounding, compatible changing-palette construction, globally
controlled repair satisfying the completion criterion, or cutoff-independent
finite feasibility. No such construction was supplied by this development.
