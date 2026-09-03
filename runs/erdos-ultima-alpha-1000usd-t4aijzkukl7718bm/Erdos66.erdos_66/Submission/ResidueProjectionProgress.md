# Joint all-modulus residue energy and density-one limits

## Status

The original conjecture is still unresolved. Submission/Spec.lean is
unchanged with its original sorry. No solution has been submitted.

## Verified production files

* ResidueEnergyProjectionExplore.lean
* NaturalResidueProjectionExplore.lean
* ResidueProfileProjectionExplore.lean
* WitnessResidueProjectionExplore.lean
* ResiduePairIdentityExplore.lean
* ResidueProjectionDensityExplore.lean

All six compile with current oleans. ResidueProjectionAudit.lean audits
sixteen principal declarations; ResidueProjectionAudit.log reports only
propext, Classical.choice, and Quot.sound. No production sorries or axioms
were added. ResidueProjectionDensityChecks.lean is only an API scratch file.

## Finite energy identity

For a homomorphism phi:G->H of finite additive groups, restrict f to the
fibers f_i of phi. The joint projection variance is

    V_phi(f) = sum_i sum_z [(f*f_i)(z)-(f*f)(z)/|H|]^2
             = sum_h [1_{phi(h)=0}-1/|H|] corr(f)(h)^2.

For arbitrary real f,g, the checked stability estimate is

    [V_phi(f)-V_phi(g)]^2
      <= ||f*f-g*g||_2^2 [2||f*f||_2^2+2||g*g||_2^2].

The proof is an autocorrelation identity and Cauchy--Schwarz, not an
assumed Fourier or pointwise splitting theorem.

## Exact natural-half-line transfer

Periodize summable real sequences through ZMod(m(k+1)), then let k tend
to infinity. The previously verified autocorrelation limit at shift zero
provides exact convergence of square sums. Thus the natural variance
satisfies the same stability inequality, with no periodization overhead
and no change of radius.

For the fractional harmonic profile p, summation by parts against the
periodic centered residue indicator gives

    |(p*p_i)(n)-(p*p)(n)/m| <= 2m.

Writing E(r)=sum_n [r_A(n)-c H_(n+1)]^2 r^n and
H2(r)=sum_n H_(n+1)^2 r^n, one obtains, for c>=0 and 0<r<1,

    residueEnergy(m,1_A,r)
      <= 4c^2 m^3/(1-r) + sqrt(E(r)[4E(r)+6c^2 H2(r)]).

Here residueEnergy is the sum over endpoint residues of the squared
centered projection error, weighted by r^n. Weighting the input sequences
by (sqrt r)^n is important: it puts every energy at exactly the same r.

If A,c satisfy the conjectured limit, then for each fixed m>0,

    residueEnergy(m,1_A,r) (1-r)/[-log(1-r)]^2 -> 0,
    sum_(n<N) sum_i projectionError(m,1_A,i,n)^2 = o(N log^2 N).

## Joint ordered residue-pair endpoint

The exact identity

    (f_i*f_j)(n) = if i+j=n mod m then (f*f_j)(n) else 0

identifies the m compatible ordered pairs at each target with the m
projections. Taking the Euclidean norm of the projection errors and using
the generic density-zero-exception diagonal theorem gives ONE set E with
count(E,N)/N -> 0 such that, for every i,j modulo m,

    if n in E then 0 else
      (1_(A,i)*1_(A,j))(n)/log(n+2)
        - (if i+j=n mod m then c/m else 0)
      -> 0.

Principal endpoint:

    Erdos66ResidueProjectionDensity.witness_pair_limits_off_density_zero.

## Precise remaining limitations

This is a necessary condition conditional on a witness. The modulus is
fixed before taking limits. The exceptional set has only density zero;
no power saving, weighted repair budget, or uniform rate has been proved.
It does not imply pointwise convergence of the residue self-counts and
does not produce or regenerate the mixed-color regularity of a changing
finite palette. It supplies no infinite witness, compatible finite-prefix
construction, uniform Boolean quadratic rounding, or logarithmic-scale
fluctuation contradiction.
