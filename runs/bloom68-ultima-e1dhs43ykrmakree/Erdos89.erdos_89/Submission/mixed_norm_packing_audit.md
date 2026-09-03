# Independent audit of mixed norm saturation and relative-unit packing

Verdict: both restricted arguments are sound. A fresh research agent read the
580-line actual-support proof, the elementary packing proof, and the previously
audited norm-element input. It found no fatal gap, missing torsion/weighted-log
factor, radial Hecke exception, or exact-norm/integrality error. The parent
independently checked the same central steps. No Lean file was modified.

## Relative-unit packing

The correct real group is T_infty=(S1)^r×(C*)^s, with paired coordinates
(z,z^-1) over each complex F-place. With beta=2log|z|, angular Haar coordinates,
and w roots of unity, its quotient by EXACT norm-one units has volume

  (2pi)^(r+s) R_rel/w.

All w roots have norm1, because F has a real place. The log kernel is exactly
these roots, and Dirichlet gives rank s. Angular twists of free-unit generators
do not change the product covolume. This matches the determinant convention
in the Akhtari--Vaaler corpus source, not a Euclidean hyperplane covolume.

For the proposed B, the beta width is2a, not a. The real angular factors are
unrestricted. For any ratio u of two points ofB that is a unit, the paired
norm factor is exactly

 |z-1|²|z^-1-1|²=16[sinh²(t/2)+sin²(phi/2)]².

Together with the real factors<=4 this yields |N_E/Q(u-1)|<1 for every
nonidentity candidate. It counts all conjugates, with no extra squaring.
Integrality contradicts that bound. This also excludes torsion candidates.

Injectivity implies vol(B)<=quotient volume by Weil's integration formula:
the periodization of1_B over the WHOLE discrete unit group is at most1.
Thus the claimed bound

  R_rel>=w 2^(-r)(4pi)^(-s)

is correct. In the Taylor bound use cosh(t)-1<=t²; the intermediate strict
inequality t²(cosh1-1)<t² needs t!=0. This harmless typo has been corrected.
The substitution gives precisely

  U²>=(2/pi)(4/pi)^r(32/pi²)^s>=256/pi^4,
  U>=16/pi²,  r,s>=1.

## Actual mixed support

The exact ideal obstruction is H=Cl(E)/Am_st. The joint quotient

 A_T=(I^1×R^s)/{((u),-beta(u)):N(u)=1}

is a compact Hausdorff group with torus kernel R^s/Lambda and finite quotientH.
The relation subgroup is closed in each ideal fiber. No splitting of H and
the torus is assumed, and discarding phases does not discard exact norms.

Characters omega induce unramified unitary Hecke characters ofE through
omega([a/c(a),0]) with the inverse archimedean factor. The principal formula
and weak approximation prove injectivity. A putative pure norm character
would have value1 on both principal ideals(2),(3), forcing radial parameter0
and then trivial omega. Thus the only leading pole is the trivial character.
Classical nonvanishing for GENERAL unitary Hecke characters (including infinite
logarithmic type) gives harmonic prime Haar distribution by Euler logarithms
and finite character approximation. The displayed Frobenian source alone is
finite-order, but the new proof explicitly states the general classical input
and supplies the needed character construction and pole check. Inert E-primes
have bounded reciprocal sum and ramified primes are finite; every nonempty
open ofA_T therefore has the required split-prime reservoir.

The robust net lemma is valid even for a target depending on all selected
primes: ifx_j∈g_j+V and-target∈g_j+V, then target+x_j∈V−V⊂W. The base ideal
puts each selected split prime wholly on cP. Switching one factor toP leaves
nonnegative exponents and preserves its norm ideal. The exact quotient sign
then gives an integral generator with EXACT normdelta, not a norm-unit multiple.

The accepted finite-prime element law supplies limiting means/variances of
finite-reservoir divisor counts. Requiring at leastm divisors per reservoir
allows greedy distinct selections even with overlaps. Take the box limit with
each finite reservoir fixed, THEN enlarge it; Chebyshev and divergence give
densityone. There is no growing-prime-set independence claim. Nor is there a
Haar-volume factor in this existential support count: each element needs only
one successful representation.

Beta bounda gives moduli e^(±a/2). With fixed epsilon and
 a=-log(1-epsilon)/2,
all conjugate moduli are<=2R(1-epsilon)^(1/4), eventually inside2R-2rho_E.
Rounding the midpoint yields actual endpoints. FirstR→infinity, thenepsilon→0,
givesD(P_R)~A(4R²). Projection is above a REAL F-place and injectivity onF
identifies distinct norm elements with distinct squared distances. There is
no extra factor2 or sqrt(e).

## Combined scope

These statements now identify the actual mixed fixed-field limit withU and
bound it uniformly below by16/pi². With the already audited CM result, all
specified full-polydisk FIXED-FIELD LIMITING constants are at least2/pi^(3/2).
They exclude an attempt to make those constants tend to zero by varying fields,
or a diagonal chosen sufficiently far into each field's asymptotic regime.

They DO NOT exclude varying-field/pre-asymptotic sequences. Merely having
R→infinity while fields vary does not place the examples in their respective
asymptotic regimes. There is no field/window/reservoir-uniform error bound,
no arbitrary-subset result, and no conclusion for either theorem of Spec.lean.
The earlier documents' proportional-mixed-rank arithmetic limitation is resolved
for these limiting constants by the new packing lemma, but the original
planar support problem and finite-height uniformity are still missing.
