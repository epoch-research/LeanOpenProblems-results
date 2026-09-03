# Joint codegree selection and whole-coarse-block deletion

## Original task status

The existential conjecture in `Submission/Spec.lean` is **not settled**.
The file remains unchanged and still contains its original `sorry`. No proof
or disproof has been submitted. All statements below are finite auxiliary
results, not an infinite witness or a negation of the conjecture.

## Completed and checked in this pass

### 1. Triple-event geometry and mean

`TripleCodegreeGeometryExplore.lean` now compiles in full. It proves that,
for distinct coarse targets b and q, the codegree of the selected Bernoulli
set is at most the number of realized nondegenerate three-coordinate events
plus 2. Each coordinate belongs to at most 3 events and each event conflicts
with at most 9. The extra 2 accounts for repeated-coordinate degeneracies.

`TripleCodegreeMeanExplore.lean` proves that the total monomial mass is at
most the maximum coordinate probability times the ordinary pair mean. For
probabilities sqrt(mu)*b(i+s), the resulting bound is

    W = mu*sqrt(mu)*b(s).

### 2. Joint selection — not a second independent realization

`BernoulliConcentrationExplore.lean` now exposes
`exists_simultaneous_bound_with_potential`: one may add an arbitrary
nonnegative potential Psi to the old two-sided tests, assuming the sum of
the old budget and E[Psi] is below 1. It returns both all the old bounds and
Psi(omega)<1. The original theorem is retained as a zero-potential wrapper.

`SignedRepBernoulliExplore.lean` similarly exposes
`exists_unsigned_signed_bound_with_potential`, retaining its original API.

`TripleCodegreeConcentrationExplore.lean` combines these with the existing
nonuniform Bernoulli matching MGF. For b != q and t >= 0:

    E exp(t*codegree(b,q)) <= exp(2t+(exp(9t)-1)W).

For all b,q <= Q, the codegree potential at threshold R has expectation at
most

    (Q+1)^2 exp((2-R)t+(exp(9t)-1)W).

`exists_unsigned_signed_codegree` returns ONE binary realization satisfying
unsigned concentration, signed concentration, and all off-diagonal codegree
bounds, whenever this budget plus the unsigned/signed budget is below 1.

`BinaryProfileCodegreeExplore.lean` carries this through the character
translation construction. Its theorem
`exists_binary_signed_profile_codegrees` returns the previous located
binary profile together with codegree(D,b,q)<=R for every b != q. Codegrees
outside the supported target range are zero.

### 3. Deletion and signed stability

`ExceptionalPairDeletionExplore.lean` already killed every sum in T by
removing all points incident to a T-pair. It has also gained support and
symmetry lemmas extending finite-range codegree bounds to all targets.

`SignedProfileDeletionExplore.lean` proves, for E subset D and |sigma|<=1,

    |signed_rep_D(q)-signed_rep_E(q)| <= r_D(q)-r_E(q).

Consequently, the same collateral bound 2*|T|*R controls the change in both
the unsigned and the signed profile.

`DeletedBinaryProfileExplore.lean` proves:

* every exceptional coarse sum is exactly zero after deletion;
* the global unsigned upper bound is preserved;
* at nonexceptional targets, the unsigned loss is at most 2*|T|*R;
* the signed bound now holds at EVERY coarse target, including T (where
  the signed convolution is zero).

The main theorem is `exists_deleted_binary_profile`. The only remaining
holes are in the unsigned profile, not in the signed bound.

### 4. An explicit feasible parameter regime

`TripleDeletionParametersExplore.lean` defines, for real m tending to infinity,

    mu = m^3
    s = ceil(exp(4m))
    L = floor(exp(12m))
    q0 = ceil(64*s^2/epsilon^2)
    t = m/9
    R = 236.

For every fixed epsilon>0, `eventually_parameters` proves jointly:

* all size/start/probability conditions;
* q0+3 <= exp(10m), while L >= exp(11m);
* the combined signed/unsigned/codegree selection budget is below 1;
* 2*236*(128*(1+log(L+1))^2/epsilon^2) <= epsilon*mu.

The estimates used are b(s)<=exp(-2m), mu*sqrt(mu)<=m^5 for m>=1, and

    unsigned budget <= 18 exp(-m),
    codegree budget <= 9 exp(1-2m)

once the elementary polynomial/exponential conditions hold.

`eventually_deleted_profiles`, for fixed 0<epsilon<=1, returns for EVERY
sufficiently large m and EVERY odd prime p>4(L+1) a translated profile
(a,T,E) with

    E subset [0,L],
    |T| <= 128*(1+log(L+1))^2/epsilon^2,
    q in T => epsilon*(s+1) < 4*(q+1),
    r_E(q)=0 for q in T,
    r_E(q) <= (1+epsilon)*mu everywhere,
    |r_E(q)-mu| < 2epsilon*mu for q0<=q<=L outside T,
    |signedFiber(E,a,q)| < 2epsilon*mu for every q<=2L.

All admissibility conditions on a+i and 2a+q are retained.

### 5. Common-width packet selection

`UniformWidthPacketsExplore.lean` specializes the existing joint Sidon
packet construction to a common choice width W. If a finite integer set A
has r_A<=V, local-window bounds give the uniform hit/avoidance mass

    H = K*2*sqrt(2WV)/W,  K=number of packet coordinates.

The single sufficient selection criterion is

    ((2K)^2+(2K)^4)/W + H + |Tests| exp(exp(t)H-tR) < 1.

`exists_uniform_width_packets` returns labelled choices, injectivity of all
packet points, avoidance of A, global Sidon uniqueness of undesignated
sums, and mixed count <2R at all tested targets. It preserves the labels so
that curve parameters can subsequently be attached to designated pairs.

This is stronger than independently selecting each repair packet: all
unintended sums across all packets share the same bound.

### 6. Only four fixed repair curve parameters are needed

`BalancedRepairParametersExplore.lean` proves:

* each sign delta in {+1,-1} is attained by chi(u*(1-u)) on at least
  (|F|-3)/2 parameters;
* if 4|B|+3<|F|, a pair u,v avoiding B exists with u+v=1 and
  chi(uv)=delta;
* if 4(|U|+2)+3<|F|, there are u,v,x,y nonzero, with

      u+v=x+y=1,
      chi(uv)=+1, chi(xy)=-1,

  and no opposite pair within {u,v,x,y}, nor between that palette and U.

The key exact identity is `balanced_pair_count`:

    pairCount(curve(u),curve(v),z)
      + pairCount(curve(x),curve(y),z) = 2

for EVERY plane target z. Including the reverse ordered pairs gives a
constant contribution 4. These same four parameters can be reused at every
coarse repair center: coarse labels distinguish the curves. Fresh parameters
per packet are unnecessary.

## Builds and audits

All files named above compile and have built oleans.
`TripleDeletionAxiomCheck.lean` and `WholeBlockRepairAxiomCheck.lean` report
only propext, Classical.choice, Quot.sound for the principal results.
The earlier `BernoulliMatchingExplore.lean` and `LateBadTargetsExplore.lean`
are included in the audit.

## Next finite steps — NOT YET PROVED

1. Instantiate common-width packets simultaneously for all exceptional
   coarse targets. There are O(m^2) targets and O(m^3) required packet pairs
   per target, hence K=O(m^5). A useful proposed choice is

       W=ceil(exp(2m)), t=m/2, mixed threshold R=28.

   The exception location bound permits this width inside each center's
   middle third for sufficiently large m. With V<=2m^3, one expects

       H=O(m^7 exp(-m)),
       collision cost=O(m^20 exp(-2m)),
       |Tests| exp(exp(t)H-tR)=O(exp(-2m))

   for |Tests|=O(exp(12m)). These scalar estimates and the natural-number
   labelled-packet interface have not yet been formalized.

2. Use two designated packet types per group, attaching (u,v) and (x,y).
   About floor(mu/4) groups per exceptional target give the missing main
   term, with rounding error <4. Undesignated pairs contribute at most two
   fine representations each; global Sidon uniqueness bounds new/new
   collateral by 4, and the joint mixed bound controls old/new collateral.

3. Prove the exact weighted aggregate decomposition and transfer the repaired
   family through the existing carry/thickening infrastructure.

## The main unresolved issue

Even completing all three finite steps would NOT prove the original
conjecture. No compatible infinite scale transition or justified change of
prime has been constructed. The original conjecture remains open in this
work, and no necessary-condition argument here proves its negation.


## Subsequent completion of the finite repair

The three finite steps listed above have now been completed in
`WholeBlockRepairProgress.md`. In particular, the packet choice width can
be taken to be s=ceil(exp(4m)) after restricting repairs to T0 intersect
[q0,L]; the mixed threshold is 14, and the total weighted collateral is
strictly below 116. `RepairedIntegerBlocksExplore.lean` now constructs
exception-free finite integer blocks with a global upper bound.
The infinite compatibility gap remains unresolved.
