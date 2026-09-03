# Further research checkpoint for Erdős 952

## Submission status

Neither the original theorem nor its negation has been proved. `Spec.lean`
remains unchanged, with its original two admissions. No submission claim has
been made. The results below must not be represented as settling the problem.

## Newly independently verified Lean module

`ProtectedWall.lean` has been compiled independently of `Spec.lean`. Its main
exports, including the finite-fiber loop-erasure theorem, component
correspondence, and conditional protected-wall obstruction, have only the
axioms `propext`, `Classical.choice`, and `Quot.sound`.

For a white predicate W on the wall lattice it defines

```
Wsharp(v) = W(v) or (W(v-1) and W(v+1)) or (W(v-i) and W(v+i)).
```

It proves that squared-radius-at-most-four connectivity on W corresponds
exactly to king connectivity on Wsharp, including equivalence of component
finiteness. Its complementary black predicate is

```
Bsharp(v) = B(v) and (B(v-1) or B(v+1)) and (B(v-i) or B(v+i)).
```

A winding-current certificate supported on Bsharp would exclude original
Gaussian squared steps at most eight. **No such certificate is supplied.**
The old certificate is supported on B, not Bsharp. The unconditional bound
therefore remains `C <= 8` with squared steps strictly `< C`.

## Mathematical reductions and limitations

The following are research arguments, not additional Lean-certified results.

### Exact stronger finite-sieve target

For a fixed Euclidean jump D, extinction in some finite Gaussian-prime-ideal
sieve is equivalent to a uniform bound on the size of admissible simple D-path
shapes. Here admissible means that the footprint misses a residue modulo every
Gaussian prime ideal. Failure of extinction at every finite cutoff gives an
infinite admissible path by finite branching and compactness. Conversely, CRT
translates an admissible path into any prescribed finite zero-coset sieve.

This would give a stronger, uniform-component-size result than the actual
Gaussian moat assertion. It is still not established for arbitrary D.

### A singular-series estimate cannot supply the missing factorial saving

For an admissible k-point Gaussian pattern H, write

```
S(H) = product_pi (1 - |H mod pi| / N(pi)) (1 - 1/N(pi))^(-k).
```

For k >= 2, elementary Euler-product and Chebyshev estimates imply
`S(H) >= (c log k)^k`: at norms <= 2k use admissibility to bound the first
factor below by `1/N(pi)`; at larger norms the logarithm of the factor is
bounded below by `-O(k^2/N(pi)^2)`. For a bounded-step shape of diameter O_D(k),
the familiar upper bound is `(C_D log k)^k`, since primes above the squared
diameter see all k points distinctly and contribute factors at most one.

Thus pruning any nonempty collection of the usual `k! S(H)` sieve main
terms cannot gain `k^(epsilon k)`. At
`k ~ A log R / log log R`, even one such main term is `R^(2+o(1))` after
multiplication by `R^2/(log R)^k`. This is a limitation of the majorant,
not a lower bound on actual prime patterns.

The needed actual-prime estimate remains an `o(R)` count of annular roots of
long simple prime paths. An infinite path supplies order R distinct roots,
without any assumption of monotone norm.

### Uniform fixed-order corridor restriction

For a fixed k-point bounded-step shape, choose one ideal above each split
rational prime p. If `p > D^2(k-1)^2`, its k offsets are distinct modulo that
ideal. On every horizontal row these impose k distinct forbidden classes of
the horizontal coordinate. Fixed-dimensional one-dimensional sieving therefore
bounds occurrences by `O_(D,k)(L/(log L)^(k/2))`, uniformly in the row and
finite-sieve phases, when the prime cutoff grows suitably with L.

Summing over rows and the finitely many step shapes excludes arbitrarily long
crossings of width `(log L)^A`, for every fixed A. This does not force an
arbitrary wandering path into a forbidden corridor. Embedded chordless paths
with only order R annular vertices can have large transverse excursions at
all long scales. A fixed finite sieve cannot be substituted for the growing
cutoff in this argument.

### Units do not anchor a percolating finite sieve

For D = 2, the zero-coset sieve by `(1+i), (3), (2+i), (2-i)` percolates while
the four Gaussian units form an isolated finite component. An explicit white
path is

```
e_n = 1 if n = 2 mod 5, and 0 otherwise
z_n = (n - 2 - e_n) + i (n + 3 + e_n).
```

Its steps are `1+i`, `2`, or `2i`; parity, the coordinate difference modulo 3,
and its nonzero norm modulo 5 verify whiteness. All nonunits within distance
2 of a unit are already removed by this sieve. Thus a universal unit-anchor
argument is unavailable.

### Local spectra do not detect winding

The pattern `{0, 1+i, 2, 1-i}` is universally admissible and induces K4 at
D = 2. CRT can preserve a translate of it while blackening every outside
vertex within distance D, using one sufficiently large fresh prime per
outside vertex. Consequently all sufficiently large complete cutoffs contain
isolated K4 components. Their adjacency and nonbacktracking eigenvalues are
3 and 2, respectively, even though the global white density tends to zero.
Untwisted adjacency norms, nonbacktracking walks, and ordinary local cycles
therefore cannot certify extinction. Winding information is essential.

A conditional algebraic observation is stronger than density alone: if a
finite zero-coset sieve has a unique quarter-turn-invariant infinite component,
its projection onto every individual CRT field is the full set of nonzero
residues. Indeed, translations keeping the whole component white must
stabilize it. Such translations form the product of the complements of its
individual projections, and rotational stability makes this additive
stabilizer an ideal. No nonzero coordinate ideal can stabilize a nonempty
subset of the unit set. This gives full *individual* projections, not full
joint product support or a useful period-independent density bound.

### Finite-state and reciprocity restrictions are not general obstructions

An admissible injective path cannot repeat a length-m step block k times unless
its nonzero displacement d is divisible, as a rational Gaussian integer, by
every split rational prime p <= k+1. Thus the product of those primes is at
most `|d| <= Dm`. This gives quantitative errors for any fixed finite-state
predictor. Separate coinvariant-group arguments exclude fixed-denominator
models. Neither argument excludes arbitrary nonstationary systems with
growing modular memory.

Fixed-gap quadratic and quartic reciprocity symbols reduce to characters of
fixed conductor: for `rho = pi + s`, `(pi/rho)` reduces to `(-s/rho)`, and
reciprocity expresses the latter using a modulus depending only on s. Such
fixed-window data return to a finite-congruence obstruction, rather than
providing a new coercive invariant. More elaborate growing-conductor spin
arguments have not been proved.

## Further endpoint and structural investigations

These investigations do **not** settle either theorem in `Spec.lean` and are
not additional Lean-certified results.

### An actual-prime spectral formulation

In a square annulus of radius `R`, join actual Gaussian primes whose distance
is at most the fixed bound `D`, leaving composite sites isolated. Let `L` be
this graph's unnormalized Laplacian, and let `Q` project onto the orthogonal
complement of its entire kernel. Define

```
F_R(k) = tr (2 Q - k^2 L)_+ = sum_{lambda > 0} (2 - k^2 lambda)_+.
```

Removing **all** zero modes is essential. This functional vanishes on every
component of size at most `k`, including isolated composites and small prime
constellations. An annular prime crossing of diameter comparable to `R`
forces

```
F_R(k) >= c_D R / (k log(2k)) - O_D(1).
```

Disjoint exponentially decaying bumps along a shortest crossing establish
this bound, using the quadratic ambient volume bound for intrinsic balls.
Consequently an upper bound `F_R(k) = o(R / log R)` at
`k ~ A_D log R / log log R`, along unbounded radii for each fixed `D`, would
suffice. **That upper bound has not been proved.**

This avoids the composite false-positive contribution in the earlier Selberg
endpoint remainder, but does not make the remaining connectivity dependence
accessible to a fixed-order prime estimate. Fixed-order sieving only yields
`F_R(k) <<_{D,m} R^2 / (k log^m R)` for fixed `m`, which is insufficient.
The functional is not monotone under adding edges, so replacing actual primes
by sieve survivors is not a valid upper bound.

There is a precise obstruction to a generic bounded-order spectral shortcut.
For the path graph on `s` vertices,

```
tr L^j = s * binom(2j,j) - 2^(2j-1),  1 <= j < 2s.
```

One can therefore make two forests with equal vertex counts, component counts,
and any fixed number of Laplacian moments: one consists entirely of short
paths, whereas the other includes a long path. The former has `F=0`; the
latter has `F` of order its length divided by `k`. These forests are not
asserted to be prime graphs. They show why the generic moment or truncated
forest-polynomial inference does not supply the missing arithmetic bound.

### Return lattices do not supply the missing coercivity

For a minimal two-sided bounded-step admissible path system, let `m_L` be its
number of length-`L` words. The additive lattice generated by displacements
between equal length-`L` contexts is a descending full-rank lattice `Lambda_L`.
Its index satisfies `index(Lambda_L) < C * m_L^2`. Finite-field skew products
force eventual divisibility of these lattices by every split rational prime,
and additional index factors from inert primes.

The audit found that these necessary lattice conditions lose indispensable
information. A modular coboundary can have the full residue field as its
image even when its return kernel is proper. Explicit recognizable S-adic
paths with a bounded decoration have a fixed 14-letter alphabet, squared
steps below `2305`, injective integrated paths, and return lattices eventually
contained in arbitrary factorial sublattices. They can also have genuine
omissions at every Gaussian prime of norm at most nine, zero entropy, and no
fourth powers, while their recognition lengths for the norm-five omissions
are arbitrarily large. Their average log-MST cost stays bounded.

Those examples **are not admissible at all Gaussian primes**: a CRT crosscut
through a sufficiently long bounded-width run forces a full image at one of
the norms `13, 17, 29, 37`. Thus they do not disprove the moat assertion. They
do refute an inference of geometric coercivity from the displayed filtration,
repeated-block restrictions, and fixed initial omissions alone. The full
simultaneous proper-image condition remains uncontrolled.

### Literature hypotheses remain insufficient

The number-field B-free dynamical results based on summable reciprocal ideal
norms do not apply to the Gaussian prime-ideal sieve. In the nonsummable case,
its random-phase measure collapses to the empty configuration; even the
root-conditioned local limit is an isolated vertex. Neither limit rules out
finite-cutoff infinite cores whose density tends to zero.

Conventional fixed-order prime estimates, random-model Hardy--Littlewood
results, and known Gaussian-prime narrow-sector results do not provide the
required growing-order, sufficiently small aggregate error. No conditional
estimate, model statement, or withdrawn claimed disproof has been inserted
into the submission.

## Later rooted and simultaneous-image investigations

The following remain paper-level arguments, separate from the Lean results.

* **Rooted sieve updates are nonlocal.** At a new Gaussian prime-ideal norm
  `q`, the newly deleted prime generators have radius `sqrt(q)`, whereas every
  newly deleted composite has radius at least `q`. Deleting only the finitely
  many generators cannot move the least-radius infinite-core point beyond
  `max(old_radius, sqrt(q)+D)`, by the last-exit argument for a ray. The remote
  composite deletions are indispensable to this approach.
* **A stronger strip restriction is available.** A large-sieve argument with
  growing shape length gives the quasipolynomial span bound
  `L <= exp(O_D(log(2W) log log(3W)))` for an admissible path in `W` rows.
  Equivalently, an excessively thin crossing has full projections modulo both
  Gaussian primes over some split rational prime of polylogarithmic norm.
  This still permits unrestricted wandering, and its square-box count is
  only `R^(2-o(1))`, not the required `o(R)`.
* **Entropy charges do not simply add.** Exact transfer matrices for the
  directed step alphabet `{2, 1+i, 2i}` show that the two norm-five exclusions
  cost strictly less SAW entropy together than the sum of their separate
  costs. Large-prime conjugate interactions can also have order `1/p`, not
  `1/p^2`, for a fixed directed alphabet. Generic symmetric periodic cores
  admit still smaller conditional losses through rare resonant corridors.
  These examples do not disprove a theorem specific to complete Gaussian
  prime sieves, but no such conditional-pressure theorem has been obtained.
* **Deep finite-component losses have a summable upper budget.** Distinct
  components lost from the nested infinite cores are mutually separated.
  Those touching the `sqrt(q)` front but extending to the remote scale `q`
  consume distinct actual-prime crossings in a common annulus. Slow-growing
  CRT path counts give a convergent sum of their counts weighted by
  `1/sqrt(q)`, even after fixed logarithmic factors. Infinitely many sparse
  losses are compatible with this estimate: it supplies neither a compulsory
  front deviation nor a contradictory lower budget.

The parent checked the finite norm-five transfer identities exactly in
`../ResearchScratch/PressureAudit.parent.py`. Its additional floating-point
renewal-equation checks are only regression tests, not proofs of arithmetic
estimates. None of these investigations supplies an all-bound argument.

## Newly verified actual-prime recurrence obstruction

`../ResearchScratch/FreshPrimeRecurrence.lean` proves that every position in
an injective Gaussian-prime sequence has a unique finite step context, and
therefore no tail has a recurrent step word. This needs no jump bound.

The proof fixes an initial prime, takes a prefix covering the path's complete
image in a finite residue group, and uses translation invariance of that
finite image to force any repeated prefix to revisit the initial prime's
divisibility class. Primality and injectivity allow only finitely many such
visits. The proof is independent of `Submission.Spec` and uses only the three
permitted axioms.

The companion `BoundedNonrecurrentPath.lean` verifies an injective path with
steps `1` or `1+i` that also has a unique context at every position. Thus
bounded steps and injectivity do not imply the recurrence needed to close the
argument. The consumer, expanded statements, independent strict builds, and
axiom audits are documented in `../ResearchScratch/FreshRecurrenceResult.md`
and `../ResearchScratch/FreshRecurrenceVerification.parent.json`.

`Spec.lean` is still unchanged and both target proofs remain admitted.

## Further recurrence and pairwise-coprimality audits

These are paper-level deductions, not Lean-certified theorems, and neither
supplies the missing unrestricted argument.

### Uniform strip restrictions still do not force recurrence

Set `epsilon(n)=(-1)^(number of base-four digits of n equal to 3)`,
`f(n)=sum_(j<n) epsilon(j)`, `b(n)=floor(log_2(n+1))`, and
`a_n=3n+i(3f(n)+b(n))`. Then

```
3 |m-n| <= |a_m-a_n| <= 5 |m-n|.
```

Every D-connected subset of this set inside any translated real-direction
strip of width W has diameter at most `80(W+4D+1)^2`. The aligned length
`B=4^k` substitution blocks have a transverse second difference of magnitude
at least `3 sqrt(B)-1`; filling index gaps in a D-connected set changes its
strip width by at most `10 floor(D/3)`.

Nevertheless **every** infinite injective bounded-jump traversal in this set,
including subsequences and reorderings with any fixed larger jump bound, has
no recurrent tail and has a unique finite context at each position. The
imaginary residues modulo three equal `b(n) mod 3`: bounded index jumps must
visit all three labels in successive exponentially long epochs, whereas any
fixed-length block sufficiently far out sees at most two labels.

Scaling and translating to `1+M A` imposes any selected finite family of
prime-ideal zero-class omissions by making M belong to those ideals. This is
not a globally admissible set. Indeed `f(4^k)=2^k`, `b(4^k)=2k`; for a split
prime p and `k=m(p-1)`, `m=1,...,p`, its images are
`3+i(3-2m)`, which cover either residue field over p. The scaled set still has
full images whenever `p` does not divide M. Thus recurrence extraction from
strip geometry alone is unavailable even in this stronger form.

### Exact pairwise-coprime translation criterion

For a distinct finite shape H, let `Delta=product_(i<j)(h_i-h_j)` and let
`b_pi` count residue classes modulo pi occupied by at least two vertices.
A pairwise-coprime translate exists exactly when `b_pi<N(pi)` for every pi.
Its exact translation density is

```
delta(H)=product_(pi | Delta) (1-b_pi/N(pi)).
```

For an m-point D-step shape (`D>=1`) satisfying the criterion, elementary
Chebyshev and Vandermonde bounds give `delta(H)>=exp(-K_D m)`, where one
possible constant is `K_D=8 log(2)+2+2 log(D)/log(2)`. Thus these finite gcd
constraints cannot supply a uniform `m^(-epsilon m)` saving on admissible
shapes.

For any admissible H and fixed nonzero past product P, CRT supplies arbitrarily
distant translates whose vertices are pairwise coprime, coprime to P, and all
composite: avoid the forbidden classes at divisors of `P Delta` and impose
one new congruence `t=-h_i mod rho_i^2` per vertex. Nothing here guarantees a
bounded jump to the new block.

A uniform bound B on admissible D-path lengths would also uniformly bound
pairwise-coprime nonunit D-path lengths. Remove vertices divisible by ideals
of norm at most B+1 (at most one vertex per ideal), and apply B to the
remaining blocks. Conversely, CRT makes admissible shapes pairwise coprime
and nonunit. This finite uniform weakening returns to the same unresolved
finite-sieve extinction problem.

There is also a genuine absolute-height bound: a pairwise-coprime set of
nonzero nonunits in `|z|<=R` has at most `2 pi_Z(R)` composite elements.
Each composite has a prime factor of norm at most R, and distinct elements
require distinct factors. Consequently an infinite pairwise-coprime nonunit
D-path would have only `O_D(N/log N)` composite vertices among its first N
vertices. Sparse arbitrarily long composite blocks are not excluded, so
removing composites need not preserve bounded jumps.

The finite-associate issue has now been handled in Lean: the independently
verified `../ResearchScratch/NonassociatePrimePath.lean` constructs, from any
hypothetical prime-path witness, one with the same start and strict step bound
whose distinct vertices are nonassociated and literally `IsCoprime`. It erases
last visits in the association quotient and lifts by units; merely deleting
associated vertices would not preserve edge lengths. The stronger exact lift
and all twelve axiom audits are recorded in
`../ResearchScratch/NonassociatePrimePathVerification.parent.json`. This
removes that technical issue but not the missing all-bound obstruction.

## Absolute-height, CRT, collinearity, and conductivity follow-up

The following paper-level deductions were independently checked. Their exact
finite arithmetic certificates were reconstructed in
`../ResearchScratch/ArithmeticBridgeAudit.parent.py`; its JSON report passes.
Neither that script nor the arguments below constitute a proof of Spec.

### Absolute-height interpolation does not supply the needed gain

For pairwise nonassociate primes `p_j`, put `P=product p_j`. If
`p_j^r | F(p_j)` for every j and every coefficient of F of degree below r has
modulus strictly below `|P|`, then `T^r | F`. Indeed its first nonzero
coefficient below degree r would be divisible by every p_j. This threshold is
sharp, attained by `P T^(r-1)`. On degree-less-than-r polynomials the exact
congruence lattice has real covolume `|P|^(2r)` and first coefficient-sup-norm
minimum `|P|`; small automatic multiples of `T^r` invalidate a naive
higher-dimensional auxiliary-polynomial argument.

For a prime block of diameter L below its minimum modulus R, its Vandermonde
Delta is coprime to P: every nonzero multiple of a vertex prime has modulus
at least R. Set `F(T)=product(T-p_j)`, `c=F(0)`, and `G=(F-c)/T`. The exact
interpolation ideals are

```
{f: p_j | f(p_j) for all j}                  = (P,T)
{f: p_i | f(p_j) for all i != j}             = (P,G)
{f: p_i | f(p_j) for all i,j}                = (P,F).
```

The latter two use distinct nodes modulo every vertex prime, supplied by
L<R. Moreover `Res(F,G)=P^(m-1)` exactly; the degree-less-than-m interpolant
to `1/T^r` at these nodes has exact common coefficient denominator `P^r`.
Thus these natural resultants and divided differences have no unexplained
prime-product saving.

There is even an actual-prime counterexample to retaining only global-prefix
height and Vandermonde/cofactor estimates. Any sequence with `|z_n|<=A+Bn`
satisfies, for `D_*=4e(A+B)`, all the path-style bounds

```
product_(k<m,k!=j)|z_j-z_k| <= D_*^(m-1) j! (m-1-j)!
|Delta_m| <= D_*^(m(m-1)/2) product_(j=1)^(m-1) j!.
```

Using split rational primes of indices `floor(n^2/(4 log n))`, choose Gaussian
prime generators in the first octant and alternate their signs. The prime
number theorem in progression gives modulus asymptotic to n, hence these
bounds and only order R annular vertices, but consecutive jumps tend to
infinity. This does not satisfy ordered bounded jumps or their sliding-window
consequences; those indispensable hypotheses cannot be discarded.

### Fresh large CRT primes cannot make remote crosscuts wind

If a diameter-R motif t+H has two distinct sites divisible by selected ideals
of spacing at least s, then, for each unit `u != 1`,

```
dist(t+H, u(t+H)+Lambda) >= s-2R
```

for every common period lattice Lambda contained in the two ideals. For
nearby points with difference e, the two ideal elements
`(h-f)+u(g-h)+e` differ by `(1-u)(h_1-h_2)`, so at least one is nonzero.
This is a phase-independent obstruction to gluing sufficiently large-prime
CRT crosscuts to their rotations.

A stronger finite-extension stability result holds over any nonempty
percolating finite sieve. Choose an old routing motif F containing
`a,a+P,a+iP`; put
`L_F=2 radius_a(F)+sqrt(2)|P|`. Adding k fresh prime ideals of spacing
`s>k L_F` cannot extinguish percolation. For zero-cosets,
`s>|a|+radius_a(F)+k L_F` preserves the infinite component at a itself.
The proof uses a coarse square mesh of F translates. A union of k colors,
each with separation greater than kL_F, has at most k vertices in any
L_F-connected component. Consequently bad coarse king components have
bounded diameter, and in the rooted case none encloses the origin; planar
outer-boundary duality supplies an infinite good mesh.

Induction and finite branching therefore produce sparse actual prime-ideal
zero-sieves that retain an infinite bounded-step path while admitting remote
composite crosscuts of every prescribed size. Every finite stage still has
full individual CRT supports. Such sieves omit many primes and do NOT have
the complete-cutoff prime/composite front. They are not counterexamples to
Gaussian moat; they rule out the unanchored sparse-CRT bridge.

### Even quantitative collinearity does not repair the geometric bridge

For the rough graph A described above, set `alpha=log(10)/log(16)<1`.
Every collinear subset of physical diameter R has cardinality at most
`32(1+R/3)^alpha`. More importantly, if v is its primitive integral direction
and `T=R/|v|`, its cardinality is at most `320(1+T)^alpha`, uniformly in
position and direction. These bounds persist under subsets and reorderings.

The proof subdivides aligned substitution blocks into sixteen children. The
normalized child height intervals have integer-level incidences
`1,3,6,9,10,9,6,3,1`, so a sufficiently flat affine line can hit at most ten
children. The uniform estimate `|f(v)-f(u)|<=8 sqrt(v-u)` controls the initial
scale. Stopping descent at the primitive parameter stride and summing the
geometric marker epochs gives the stated constants. The finite table and
rational constant inequalities were checked independently.

In contrast, arbitrary admissible collinear sets satisfy only the uniform
sieve bound `O((T+1)/sqrt(log(T+2)))`. Coordinate-primitivity ensures that at
least one ideal over each split rational prime has a nonzero direction and
therefore gives one omitted parameter class. Actual-prime sets satisfy the
same bound after deleting finitely many generator associates at each cutoff.
This linewise admissibility scale is sharp: real positive integers supported
only on rational primes 3 mod 4 are Gaussian-admissible and have this counting
order. Thus geometry can lie polynomially BELOW the available arithmetic
line-count threshold.

The Ramsey/Pomerance collinearity proof in corpus paper `1501.07550` gives no
bounded-average-gap conclusion for its extracted collinear points. An input
segment of index length m in a strip of width `D m/(bN)` can produce order N
collinear points in direction height at most order N, but with no bound on
m/N. The rough graph above meets that qualitative conclusion while excluding
the density strengthening that would be needed here.

### Exact complete-cutoff Kirchhoff non-tensorization

Let kappa be the isotropic effective conductivity per ambient area of the
full D-distance white graph, with unit edge conductances. This quantity
vanishes exactly when there is no nonzero period winding and ignores finite
components. At `D=3 sqrt(2)`, the exact values for sieving by `(1+i)` and
optionally the two ideals over five are

```
kappa(2)       = 34
kappa(2,+5)    = kappa(2,-5) = 85/4
kappa(2,+5,-5) = 385322/28989.
```

The last graph is the COMPLETE norm-five cutoff, and its entire survivor set
is connected (hence even has full joint CRT support). Nevertheless

```
kappa(2,+5,-5) - kappa(2,+5) kappa(2,-5) / kappa(2)
    = 9979/927648 > 0.
```

Thus primewise standalone logarithmic winding losses do not add. The parent
reconstructed all quotient matrices at sizes 1, 4, and 16, solved their full
Poisson equations over the rationals, checked all sixteen claimed corrector
values, and checked the two period-winding paths. This is not merely an
edge-density effect: the affine energies tensorize in the opposite direction;
the minimizing corrector reverses the sign.

The example uses norm five below D squared. It does NOT refute a bound
restricted to fresh ideals of norm greater than D squared, for which the
valid phase-averaging variational bound is
`K(S+pi) <= (1-2/N(pi)) K(S)` as quadratic forms. Iterating that bound gives
only polylogarithmic decay, not finite-cutoff extinction.

## Rooted and fixed-scaffold follow-up

The deductions in this section are paper-level, not new Lean certifications.
The exact finite checks below were added to
`../ResearchScratch/ArithmeticBridgeAudit.parent.py` and independently passed.
The original conjecture and its negation remain unproved.

### Protection cannot be inherited on the fixed old scaffold

Let L=P Z[i] be the old wall period, and let T be any finite collection of
fresh prime ideals. For an old-white finite motif F, CRT gives

```
exists lambda in L, F+lambda entirely new-white
  iff |F mod pi| < N(pi) for every pi in T.
```

The density of these translations is exactly
`product_pi (1-|F mod pi|/N(pi))`. The coefficient `(1+i)P` of the translation
parameter is invertible at every fresh ideal. Consequently, if all fresh
norms exceed m, no monotone black condition expressed as a conjunction of
clauses of at most m sites can gain any new support invariant under the
ENTIRE old period lattice. In particular

```
Core_L(B_new^sharp) = B_old^sharp.
```

This covers complete finite fresh cutoffs, not only sparse extensions.
Every old larger-step edge type still has infinitely many surviving old-period
translates. A phase-blind finite potential on old residues therefore cannot
improve after fresh sieving.

There is an explicit defect on the supplied walk at `v=147-149i`. The center
is black by label 6, but `v-i` and `v+i` are both old-white. Their original
coordinates are `298-3i` and `296-i`, separated by squared norm 8. All ten
label residues, the old periods P and iP, and the step norm were checked.
Even repetition only along `nP` cannot repair this defect: each fresh rational
characteristic p is at least 7, and its at most two selected ideals forbid at
most four n-residues for the two endpoints. Integer CRT leaves infinitely
many surviving bridge copies.

A valid larger-period transfer must instead retain the new phases. Choose
old residue representatives f(a) integrating the extinct old-edge graph, so
`w=f(a)+Pt`. A new edge of physical increment s has coarse increment
`delta=(f(a)+s-f(b))/P`; a fresh ideal excludes one channel-dependent residue
of t. On the finite new-phase graph, a potential g satisfying
`g(b,k+delta)-g(a,k)=delta` exists exactly when every closed walk has zero
voltage. Then `t-g(a,t mod Q)` is constant on components, proving finiteness.
The new representatives `f(a)+P g(a,k)` can be used at the next stage.
This is an exact iterative certificate format, NOT a proof such a potential
exists. Two independent coarse directions remain; finite old cells do not
reduce the enlarged graph to one-dimensional channels.

### Ordered index interpolation: valid arithmetic, missing rank defect

For a normalized prime path and its root pi, let q be the residue
characteristic at pi. For every `M=q^t`, characteristic-q Frobenius gives

```
Delta^M x_a = x_(a+M) mod pi != 0.
```

Thus the prefix interpolant of length M+1 at integer index nodes has maximal
degree M. Its leading coefficient has pi-valuation
`-e_pi (q^t-1)/(q-1)`, where `e_pi=v_pi(q)`. The factorial denominator cannot
be dropped. Note that `N(pi)>m` alone does NOT make index nodes distinct:
an inert prime q has norm q squared but characteristic q. Also binomial
polynomials on integer indices are not integer-valued on all Gaussian inputs.

Writing B for the unitriangular Pascal matrix, the index congruence lattice
has exact Newton-coordinate matrix `B^(-1) diag(p_j)`. Multiplication by the
interpolant has matrix `A=B^(-1) diag(p_j) B`, with

```
A_(k,l)=binomial(k,l) Delta^(k-l) p_l  (l<=k),
A_(k,k)=p_k,  det A=product p_j.
```

The large diagonal does not have a bounded-increment estimate. A valid
Hadamard comparison requires m INDEPENDENT admissible columns y with
`p_j | y_j`, initial modulus at most A, and increments at most E; only then
`product N(p_j) <= m^m A^2 E^(2m-2)`. The actual path supplies one column,
not such a family. In a high block, the stronger inequality
`E/R + H D/R^2 < 1` forces every such bounded-height column to be a constant
Gaussian multiple of the original path, by comparing consecutive integral
quotients `y_j/p_j`.

The ordered actual-prime block

```
5+2i, 6+i, 7+2i, 8+3i, 9+4i, 10+3i
```

has norms `29,37,53,73,97,109`, step norms squared 2, and diameter squared
26 below its minimum norm 29. Its norm product `43893143401` exceeds the
small-column Hadamard scale `43296768` by more than 1000. The short-vector
body is exactly the zero vector and the four unit multiples of this path.
The parent checked the full Newton matrix, this exact inequality, and the
raw/increment Hankels of orders 2 and 3; their respective norms are
`160,16,8,32`, coprime to all six vertex norms. No local prime-product
Hankel divisibility can be inferred from the diagonal evaluations.

For every fixed r, sliding increment Hankels of an infinite prime path must
be nonzero arbitrarily far out. If one order vanished eventually, the
Desnanot--Jacobi identity and the least such order give a fixed linear
recurrence; a finite increment alphabet then forces eventual periodicity,
contradicting primality and nonassociation. A hypothetical fixed-order
arithmetic divisibility law could force this forbidden vanishing via the
Hadamard bound, but no such law is proved. The marker countermodel has
arbitrarily late Hankels `J+iR_r` of norm `1+r^2`, so geometry and unique
contexts alone do not provide the needed rank defect.

### Intrinsic prime-component histories and their amplitude budget

For an actual prime D-component C let `a(C)` be its least radius, `b(C)` its
supremum radius, and `T(C)` the last complete cutoff at which it intersects
the infinite sieve core. After a fixed cutoff that isolates units,

```
C finite implies T(C) <= b(C)+D;
T(C)=infinity iff C is infinite.
```

The first bound uses completeness: all composite D-neighbors of C have
modulus at most `b(C)+D` and are removed by that cutoff. Rooted entrance is
exactly characterized by a prime component with

```
a(C) <= sqrt(X)+D and X<T(C).
```

Equivalently, entrance times are covered by the component intervals
`[max(X0,(a(C)-D)_+^2),T(C))`. Call nonempty such intervals front-exposed.
Using the previously derived core-density estimate at the AUXILIARY cutoff
`Y=eta log R`, whose period fits in the counting ball, gives

```
#{front-exposed C: R<=a(C)<2R}
    <= C_D R exp(-c_D (log R)^gamma_D).
```

Each such C lies entirely in the auxiliary core and contributes order R
vertices inside radius 4R. Hence its minimum-radius weights satisfy
`sum_C exp(c0 (log(2+a(C)))^gamma)/(1+a(C)) < infinity` for some c0>0.
This is a legitimate deterministic count, not a random-phase estimate at
the much larger cutoff X.

Under persistent entrance, the least active ancestor radius is either
bounded, in which case an actual prime component is infinite, or its
successive values a_j obey

```
limsup (a_(j+1)-a_j)/exp(c0 (log(2+a_(j+1)))^gamma) = infinity.
```

This follows from divergence of `sum (a_(j+1)-a_j)/(1+a_(j+1))`. It supplies
a genuine handoff-amplitude restriction, but does NOT exclude a single
permanently active prime component. The finite weighted sum of active
ancestors has a positive limit exactly when such an infinite component
exists; no estimate forcing that limit to zero has been obtained.

A quantifier caution is essential: one cutoff with `r_D(X)>sqrt(X)+D`
excludes infinite prime components meeting that particular ball only. To
exclude every possible starting point by this route requires such violations
at arbitrarily large cutoffs, not merely one fixed violation.

## Small-support S-unit localization: a new exact remaining target

Let F be a set of Gaussian PRIME ideals, `w(F)=sum_(pi in F) 1/N(pi)`, and
let U(F) consist of the nonzero Gaussian integers all of whose prime-ideal
factors belong to F, including the four units. The exact Euler mass is

```
(1/4) sum_(z in U(F)) 1/N(z)
    = product_(pi in F) (1-1/N(pi))^(-1) <= exp(2 w(F)).
```

A fixed four-point upper-bound sieve shows that the primes starting simple
four-vertex D-paths have annular count `O_D(R^2/log^2 R)`. On each horizontal
row, one ideal above every sufficiently large split rational prime forbids
four distinct classes; this is a fixed dimension-two one-variable sieve.
Therefore EVERY hypothetical injective infinite prime D-path satisfies

```
sum_n 1/N(x_n) < infinity.
```

No growing-dimensional factorial estimate is used here.

### Rooted small-support uniformity (RSU) -- UNPROVED

The following would settle the requested negation:

> For every D there is epsilon_D>0 such that, for every fixed nonzero a, the
> radius of the D-component of a in U(F) is bounded uniformly over all finite
> conjugation-stable F satisfying w(F)<=epsilon_D.

The bound may depend arbitrarily on a and D but not on the added primes.
Indeed a sufficiently late prime-path tail, together with its conjugates,
has total support weight below epsilon_D. All finite prefixes lie in these
U(F) graphs at the SAME root, so RSU would trap the entire tail in a finite
ball. Rooted finite branching makes RSU equivalent to exclusion of infinite
components for possibly infinite supports of that same small budget.

The ordinary S-unit theorem proves finiteness of all short edges for each
FIXED finite F, not this uniform assertion. The quantifier order cannot be
exchanged. The finite-generation hypothesis is explicit in corpus paper
`1107.5756`, lines 38--68.

Nor does small Euler mass imply globally finitely many short edges. CRT can
place composite pairs `z,z+1+i`, free of all prime factors of norm at most Y,
with `log N(z(z+1+i))=O(Y)`. Their support weight is `O(1/log Y)`. Rapidly
growing cutoffs produce infinitely many disjoint short edges with arbitrarily
small total support mass, but without a fixed-root connector.

### A proved finite-angular-support case

For fixed D and a FIXED finite set S of split rational primes, the components
of U(F) are uniformly bounded when F contains only primes above S, possibly
the ramified prime, and ANY inert prime ideals, even infinitely many. More
generally this holds when the primitive parts of all vertices use only S and
there are sufficiently many excluded split primes. This proof is paper-level
and uses the established Baker--Wuestholz theorem, not a Lean formalization.

Write `z=n b`, `w=m c` with primitive b,c. Their angular quotient
`b bar(c)/(bar(b)c)` lies in the fixed group generated by i and
`pi/bar(pi)` for pi above S. Baker--Wuestholz gives, with
`M=max(|b|,|c|)`,

```
|det(b,c)| >= c_S |b||c|/(1+log M)^C_S   if det(b,c)!=0.
```

A short edge also gives `m|det(b,c)|<=D|b|` and
`n|det(b,c)|<=D|c|`. Thus M, and then both endpoints, are bounded by constants
depending only on S,D. This holds even with unrestricted rational contents.
The logarithmic-forms theorem was checked in corpus `1403.2949`, lines
97--110; its constants depend on the fixed generators.

After deleting those finitely many direction-changing endpoints, components
lie on individual rational lines through zero. Choose `L=floor(D)+1` excluded
split rational primes q_j. Integer CRT gives periodically repeated blocks of
L forbidden parameters on EVERY such line, with period `Q=product q_j`.
Thus each remaining line component has fewer than Q vertices. Bounded degree
now gives a uniform bound on the whole component.

For a budget-uniform version, choosing the first L split primes and
`epsilon_0(D)=1/(2 max q_j)` forces all their ideals to be excluded. Every
collinear component then has a fixed bound Q_D. Under that budget, RSU is
therefore equivalent to a uniform bound on the number of direction-changing
edge endpoints REACHABLE FROM THE FIXED ROOT. Finite angular support supplies
such a bound, but small reciprocal mass alone does not yet do so.

Global angular-edge counting is again insufficient. CRT can make
`t+i, t+1+2i` (t even) primitive, noncollinear short-edge endpoints with all
prime factors above Y and support weight `O(1/log Y)`. Each split prime
excludes at most four t-residues, and inert prime factors are impossible for
these primitive points. Arbitrarily small support therefore permits infinitely
many remote direction-changing edges; no bounded root connection is provided.

### Important scope restrictions

For a divisibility antichain A of supported nonunit ideals with multiplicity
count Omega at least k and w(F)<=1, there is the elementary rank-free bound

```
sum_(b in A) [Omega(b)!/product_pi nu_pi(b)!]/N(b) <= w(F)^k.
```

Choose successive prime letters with probabilities `1/N(pi)` and stop with
probability `1-w(F)`: antichain prefix events are disjoint. This does not give
a geometric lower bound; a prime-path tail is already an antichain of small
reciprocal mass.

PRIME ideals, divisor closure, and the actual phase are indispensable. The
union of the nonprime ideals `p Z[i]` for rational primes p>Y has total
reciprocal ideal norm tending to zero, yet has an infinite D=2 path on the
real axis: beyond a fixed height no two consecutive integers are Y-smooth,
by the finite S-unit theorem. Splitting those ideals into Gaussian prime
factors makes the reciprocal mass diverge. Likewise, the almost-sure
no-black-percolation statement in corpus `1804.06486` is about random phases;
the zero phase already has the real-axis black ray. Neither result proves
RSU for Gaussian prime ideals.

No full RSU proof or fixed-root small-budget counterexample was obtained.
The remaining rooted transition estimate is not an available theorem or an
allowed axiom, and has not been inserted into the submission.


## Further small-support audits: divisor saturation is essential

The deductions below are paper-level. Neither the original conjecture nor
RSU has been proved, and none of this material has been inserted in Spec.lean.
The parent independently checked the quantifiers, the counting arguments,
and the cited number-field sieve and almost-S-unit statements.

### Multiplication, conjugation, and small lattice mass alone are insufficient

For A>=2, let V_A be the unit-saturated multiplicative monoid generated by
`n+i,n-i` for all integers n>=A. It contains the actual infinite step-one
path `n+i`, from the fixed root A+i. These points are primitive and consecutive
ones are noncollinear with zero, since their determinant is -1. Nevertheless,
counting formal monomials (collisions only decrease the sum) gives

```
(1/4) sum_(z in V_A) 1/N(z)
 <= product_(n>=A) (1-1/(n^2+1))^(-2)
 <= exp(4/(A-1)).
```

The same bound holds for every finite prefix's generated monoid, with the
same fixed root A+i and arbitrarily long reachable paths. Thus multiplication,
conjugation, rotations by units, and a small reciprocal lattice mass do not
supply RSU, even with its fixed-root quantifier.

This is NOT a prime-support counterexample. V_A is not divisor-closed.
For every ideal above a split rational prime, choose n>=A in the residue
class -i modulo that ideal. The prime saturation therefore contains all
split prime ideals, and has divergent reciprocal norm mass. Any successful
argument must actually use divisor saturation, rather than just products.

### A stronger-moment rooted theorem, not the required reciprocal-norm theorem

For conjugation-stable F, write S(F) for its split rational primes and put

```
v(F) = sum_(p in S(F)) 1/sqrt(p).
```

For every finite D,K and fixed nonzero a, the a-component is bounded uniformly
over F with v(F)<=K. Inert prime ideals and the ramified prime may be included
without any restriction. Here F can be infinite. The following proof is
elementary apart from the usual unique factorization and summation facts; it
does not require a logarithmic-forms theorem.

Let B(F) be the supported primitive Gaussian integers. Unique factorization
and positivity give

```
H(F) := sum_(b in B(F)) 1/|b|
 = 4 (1+eta/sqrt(2)) product_(p in S(F))
       (1+p^(-1/2))/(1-p^(-1/2)) < infinity,
```

where eta=1 if the ramified prime is allowed and eta=0 otherwise. A primitive
integer has no inert factor, ramified exponent at most one, and cannot
contain both conjugate primes above a split p.

Every supported nonzero integer has the unique expression z=n b with n>=1
and b primitive. For fixed noncollinear b,c and a fixed step delta, the
system `m c - n b = delta` has at most one real pair (n,m), hence at most one
positive integral pair. If K_D is the number of nonzero permitted lattice
steps, and B_0 is any finite subset of B(F), the number of noncollinear
edges with both endpoints in the radius-R ball is at most

```
K_D |B_0|^2 + K_D R sum_(b in B(F) \ B_0) 1/|b|.
```

The first term counts low-part/low-part edges by the unique-solution fact;
every other edge meets a vertex with primitive part outside B_0. It follows
that the number of such edges is o(R).

There are infinitely many excluded split rational primes. Choose
L=floor(D)+1 of them, q_1,...,q_L. CRT produces repeated blocks of L consecutive
forbidden signed integer parameters on every rational line through zero,
with period Q=product q_j. Consequently every collinear component has fewer
than Q vertices. An infinite simple D-path has at least a constant times R
noncollinear edges before first exiting radius R, because it has length at
least (R-|a|)/D and its collinear runs have bounded length. This contradicts
the o(R) bound (apply it at radius R+D for the final exit edge).

Finally, uniformity over F with v(F)<=K follows by finite branching at the
FIXED root: if no uniform bound existed, a limiting infinite path would have
union of prefix supports of v-mass at most K. This uses no unjustified
uniform tail estimate for H(F).

This stronger-moment result does not close the gap. Every infinite
bounded-step path has divergent reciprocal radii, since
`|x_n| <= |x_0|+Dn`. For a prime path, fixed split rational primes and CRT also
bound the lengths of its axis-only runs; transitions between different axes
occur only in a finite ball. Hence its nonaxis indices have positive lower
density, and their reciprocal radii already have divergent sum. Each split
rational prime accounts for at most eight distinct Gaussian prime vertices.
Thus the stronger moment v of a hypothetical prime path's conjugation-stable
support is infinite. The fixed-four-point sieve supplies reciprocal NORMS,
not reciprocal radii.

### Small actual prime supports may be invisible to all congruence characters

For every epsilon>0 there is conjugation-stable F with w(F)<epsilon such
that for every nonzero proper ideal q, supported elements coprime to q
represent ALL of `(Z[i]/q)^*`. F can avoid any prescribed finite set of primes.

Enumerate all pairs (q,a), with a an invertible residue. At one stage choose
Y large and use CRT to impose

```
z = a mod q,
z = 1 mod p for every Np<=Y with p not dividing q.
```

The unit condition also excludes primes dividing q. Thus all prime factors
of z have norm >Y. A bounded representative modulo
`M=q product_(Np<=Y, p not dividing q) p` has `N(z)<=N(M)` and z!=0.
Elementary Chebyshev bounds yield

```
log N(z) <= log N(q)+C Y,
w(support(z) union conjugate(support(z)))
 <= 2 log N(z)/(Y log Y) = O(1/log Y),
```

taking Y>=log N(q). Choose stage budgets forming a geometric series of total
less than epsilon, and union the supports. Taking each Y above the prescribed
finite set ensures its avoidance. Each residue pair has its chosen witness.

Therefore a nontrivial finite-conductor multiplicative character that is
identically one on all of U(F) cannot be forced merely by a small w-budget.
This does not rule out a character or invariant depending on the reachable
component rather than the whole support monoid.

### Even a global harmonic angular-edge potential can be too large

For one fixed sufficiently large D_*, arbitrarily small finite prime-support
budgets allow arbitrarily large sums of `1/max(|z|,|w|)` over noncollinear
D_*-edges in U(F). One may arrange infinite supports with divergent such sums
while EVERY component is finite. Thus this unrooted potential is also not a
replacement for RSU's rooted transition bound.

The number-field Maynard theorem in corpus 1403.5808 supplies a fixed
admissible rational tuple with two Gaussian-prime entries on
`R^(2-o(1))` translates in a radius-R annulus. The quantitative count follows
from its positive weighted excess and the subpower bound for each summand;
the parent checked introduction.tex lines 28--40 and the weights and
asymptotics in method.tex. Discarding O(R) real translates leaves
noncollinear prime pairs. Taking all prime ideals in the corresponding
constant-factor norm band gives `w(F_R)=O(1/log R)` and harmonic edge sum
at least `R^(1-o(1))`.

For the infinite version, separate successively chosen bands. At a finite
stage, fixed-S-unit finiteness bounds all its short-edge endpoints by B_j.
Require every later prime generator to have modulus >B_j+D_*. Any newly
admitted vertex then lies beyond that radius and cannot attach to an old
nontrivial component. Each edge of the final graph occurs at a finite stage,
and its component is sealed after that stage. Summable band budgets coexist
with divergent global harmonic edge sums. No fixed-root infinite connector
is constructed.

### Relevant almost-S-unit estimates still have the wrong budget

Corpus 2104.04367, Times23modq.tex lines 132--177, fixes a finite S and proves
an almost-S-unit gcd theorem. If two coprime pairs `a_j s_j,b_j t_j` have
S-supported parts s_j,t_j of height H and the two differences have gcd at
least H^delta, then H is bounded, the outside cofactors have size at least
H^(7 delta^2/512), or the ratios have a bounded multiplicative relation.
The checked statement is over Q. It charges outside-cofactor HEIGHT, not
reciprocal prime mass. An arbitrarily large excluded inert prime p has
weight p^(-2), while p^k has arbitrarily large wholly outside height. Thus
small w supplies no such height hypothesis, even before the number-field
extension needed here.

No full RSU proof, RSU counterexample, or proof of either theorem in Spec.lean
resulted from these audits.




## Root-sensitive capacity audit and stronger available support budgets

This follow-up produced a new Lean reduction, described separately below, but
no proof of either target. The analytic deductions in this section are
paper-level and were independently checked against their cited sources.

### Every fixed logarithmic reciprocal-norm moment is available

For every fixed A>=0, a hypothetical injective bounded-step Gaussian-prime
path satisfies

```
sum_n (log(2+N(x_n)))^A/N(x_n) < infinity.
```

Indeed the previous fixed-four-point sieve works for any FIXED k. There are
finitely many k-vertex D-step shapes. For split rational primes
p>D^2(k-1)^2, choose one Gaussian ideal above p; all k offsets are distinct
modulo it. On each horizontal row this excludes k distinct real-coordinate
residues. The dimension-k/2 upper-bound sieve gives at most
`O_(D,k)(R^2/(log R)^(k/2))` possible roots in a radius-R annulus. Sieve only to
a fixed small power of R so that no actual vertex is a sieving-prime generator.
The residue-count errors are uniform in the horizontal row. In dyadic annulus
R=2^j, the weighted contribution is `O_(D,k,A)(j^(A-k/2))`; fix
k>2(A+1) and sum. No growing-dimensional sieve estimate is being asserted.

Consequently an RSU theorem for sufficiently small

```
w_A(F)=sum_(p in F) (log(2+Np))^A/Np
```

for ANY ONE fixed A would already suffice to disprove the original theorem.
In particular w_1 is available (take k=6). This sufficient assertion is weaker
than unweighted RSU. Each fixed moment becomes arbitrarily small on a tail;
no common tail making all moments simultaneously uniformly small is asserted.

### Exact ordinary local capacities do not charge the rooted path enough

At a Gaussian prime ideal p, put q=Np and normalize the local absolute value
by |pi|_p=q^(-1). Its logarithmic equilibrium energies are

```
V(O_p)   = log q/(q-1),
V(O_p^*) = q log q/(q-1)^2.
```

The parent checked these in corpus 1507.01879,
`energy-height-bounds-6.tex`, lines 237--279, and independently derived them:
energy on units is log q times the sum, over r>=1, of the squared masses of
the `(q-1)q^(r-1)` unit classes modulo p^r. Balanced masses minimize each
summand; unit Haar measure attains all minima. The full ring has q^r classes.
Thus the EXTRA local loss for omitting zero is

```
log q/(q-1)^2,
```

whose sum over Gaussian prime ideals converges. It is not log q/q. In
particular the relative capacity product for unit envelopes at all primes
outside F lies between one fixed POSITIVE constant and 1, even for F empty.
This is a relative product, not an unjustified infinite-adelic theorem.

Pairwise coprimality permits at most one nonunit vertex at each prime.
Adding that singleton to O_p^* does not change capacity, since a finite-energy
measure cannot put positive mass on a point. Ordinary capacity therefore
forgets which vertex was exceptional, including whether it was the root.
The unit-envelope Green charge of an integer root a is exactly

```
G_env(a)=sum_(p|a) q log q/(q-1)^2.
```

For a Gaussian-prime root this is `N(a) log N(a)/(N(a)-1)^2`, which tends to
zero, and its sum along a hypothetical path is finite by the moment estimate.
This defeats a uniform-per-vertex charge argument, NOT every capacity method.
An actual reachable component could have a much thinner p-adic closure than
the maximal unit envelopes; no estimate proving the needed thinning exists.

A finite determinant audit reaches the same boundary. For
`B(t,h)=h binom(floor(t/h),2)+(t mod h) floor(t/h)` and m distinct pairwise
coprime Gaussian integers, their Vandermonde Delta satisfies

```
v_p(Delta) >= sum_(r>=1) B(m-1,(q-1)q^(r-1)).
```

Discard the possible nonunit, balance the remaining residues, and count equal
pairs at each depth. This gives
`log N(Delta) >= (1/2)m^2 log m-O(m^2)`, whereas bounded successive steps give
`log N(Delta) <= m^2 log m+O_D(m^2)`. The factor-of-two dimensional gap remains.
Adjoining the auxiliary point 0 adds the genuine factor product x_j, but only
`O_(x_0,D)(m log m)` to its logarithmic norm. No Hankel divisibility or missing
family of independent auxiliary polynomials is inferred.

### Even weighted small supports may have the full permitted profinite closure

For any positive weight omega(q) tending to zero and any epsilon>0, one may
choose conjugation-stable prime support F with total omega-weight <epsilon
such that U(F) represents EVERY invertible residue modulo EVERY nonzero ideal.
Enumerate the residue pairs; for each choose a sufficiently large Gaussian
prime in that class, with its conjugate cost below a summable stage budget.
The needed fixed-modulus prime-element progression theorem was checked in
corpus 1403.5808, `method.tex`, lines 37--45. This improves the earlier
CRT-only construction to weights such as `(log(2+q))^A/q`.

For such supports the profinite closure is exactly the product of O_p for
p in F and O_p^* for p outside F. To match a finite cylinder, multiply supported
prime powers to prescribe its valuations, then match all remaining unit
parts by the unit-residue property. Consequently all tests by one-variable
polynomials f in Q(i)[T] with `f(U(F)) subset Z[i]` reduce exactly to their
local integrality on those envelopes, by continuity and intersection of all
local integer rings. This is about the WHOLE monoid, not its root component.
It supplies no fixed-root connector and is not an RSU counterexample.

The accessible S-unit graph results still fix finite S and use S-unit
DIFFERENCES. Multivariate capacity/interpolation results in corpus 2111.14180
explicitly identify algebraic independence of auxiliary polynomials as an
additional issue and exhibit cases where it fails. These do not fill the
missing component-sensitive bound.

### Newly Lean-verified same-bound coprime-norm reduction

`ResearchScratch/CoprimeNormPrimePath.lean` (312 lines) now proves
`CoprimeNormPrimePath.exists_coprime_norm_prime_path`: any hypothetical witness
can be replaced by a prime path with the SAME root and strict integer step
bound, whose integer squared norms are pairwise IsCoprime and injective.
The vertices are injective as well. No monotonicity of norms is asserted.

The proof folds z into `(max(|re z|,|im z|),min(|re z|,|im z|))`, proves this
is nonexpansive, and applies the existing finite-fiber last-visit erasure.
A single fixed unit/conjugation symmetry unfolds the initial vertex back to
the original root. Distinct prime fold representatives are coprime to each
other AND to their conjugates; multiplying Bezout identities and taking real
parts yields coprimality of their rational norms.

The independent consumer uses the precise conjunction and strict-bound input
convention of Spec and also checks Nat.Coprime for absolute norms. Both files
compile with autoImplicit=false, relaxedAutoImplicit=false, warningAsError=true.
Six axiom checks contain only propext, Classical.choice, Quot.sound; the
consumer asserts that neither target declaration is loaded. The module imports
only the previously verified NonassociatePrimePath module, not Spec.
See `ResearchScratch/CoprimeNormPrimePathResult.md` and
`ResearchScratch/CoprimeNormPrimePathVerification.json`.

This is a conditional reduction, not a proof or disproof of Gaussian moat.
The root-sensitive component bound, even for the stronger available w_1
budget, remains unresolved. Spec.lean is still unchanged with two admissions.

## Geometric detour and multiscale-wiggliness audit

No target proof resulted. This section is paper-level; its exact finite
geometric regressions are in `ResearchScratch/KochDetourAudit.py`, `.json`,
and `.log`. These are not Lean certificates of either target theorem.

### Even uniform coarse-scale wiggliness is insufficient by itself

Put A(x+iy)=-y+i(x+y), so A has order six, and define words

```
W_0=(1),
W_(k+1)=W_k A(W_k) A^(-1)(W_k) W_k.
```

Their nested-prefix limit, integrated from the fixed root 1, is an injective
Gaussian-lattice ray with steps in `{+/-1,+/-i,+/-(1-i)}`. The k-th prefix has
4^k edges and displacement 3^k. This is a triangular-lattice Koch construction
under an invertible real-linear change of coordinates, not a prime path.

The untranslated prefix lies in
`T_k=3^k conv{0,1,(1+i)/3}`. Its four child triangles have disjoint interiors
and meet only at consecutive joining endpoints. After its first 4^k edges,
all future untranslated vertices have real part at least `2*3^(k-1)`.
Consequently the vertex count in a radius-R ball is comparable to R^s, where
`s=log(4)/log(3)<2`. The exact audit verifies all six rational separating-axis
certificates for the child triangles, A^6=1, and the integer prefix assertions
through k=8 (65,536 edges). The general inductive argument is separate from
these finite regressions.

Every sufficiently large ball centered on the ray contains a whole block
`A^j W_k` of scale 3^k comparable to its radius. The block contains a
nondegenerate triangle of that scale; the six maps A^j have uniformly bounded
distortion. Its Jones beta numbers are therefore bounded below by a fixed
positive constant at all sufficiently large scales. Prefix length, absolute
turning, and standard Jones energy are comparable to 4^k, despite endpoint
distance only 3^k. The traveling-salesman inequalities used here were checked
in corpus 1303.7305, `wiggly14.tex`, lines 85--96.

Yet for every fixed B>=0 the ray satisfies

```
sum_(vertices z) log^B(2+N(z))/N(z)
 <<_B sum_k (1+k)^B (4/9)^k < infinity.
```

Thus even uniformly positive relative-width wiggliness at every large scale,
polynomially growing detour, and divergent turning/Jones energy coexist with
all available logarithmic moments and subquadratic vertex growth. The exponent
s is a LARGE-SCALE vertex-growth exponent: the polygonal lattice ray itself
is a countable union of segments, so no Hausdorff dimension s claim is made.

This does NOT satisfy prime-divisor avoidance or pairwise coprimality. For
example, it contains both 2+i and 10, with `10=(2+i)(4-2i)`. The countermodel
only rules out an inference using the stated geometric properties alone.

### An exact no-double-counting detour budget

For a finite injective polygonal path, choose any binary subdivision tree
with individual edges as leaves. For an internal interval having endpoints
a,b and splitting vertex m, let

```
delta_I=|a-m|+|m-b|-|a-b|,
c_I=|a-b|,
h_I=distance(m,line(a,b)).
```

Cancellation of child and parent chords gives exactly

```
sum_I delta_I = path_length - endpoint_distance.
```

Convexity of the two distances gives

```
delta_I >= sqrt(c_I^2+4h_I^2)-c_I >= 2h_I^2/(c_I+h_I).
```

The first inequality is sharp when m projects to the chord midpoint; the
second follows by rationalizing and using sqrt(c^2+4h^2)<=c+2h. Therefore a
path of M steps of length at most D has

```
sum_I 2h_I^2/(c_I+h_I) <= D M.
```

Prime-induced charges must fit one subdivision tree or have a proved overlap
bound. Multiple prime labels do not by themselves make detour charges
additive. Indeed one isolated split-prime zero coset can be avoided by a
collinear real-axis path with steps at most two, skipping the multiples of
its rational residue characteristic. Its transverse detour cost is zero.
Actual bounded-jump obstacle clusters, rather than individual deleted sites,
are needed for this approach.

### The arithmetic lower bound must exceed the moment budget

Let R_j=4^j. Before first reaching radius 2R_j, take the last visit to radius
at most R_j. The resulting prime-path crossing lies in
`[R_j-D,2R_j+D]`; these annuli are disjoint for sufficiently large j. This
construction does not assume monotone norms.

For detour, total turning, or standard Jones energy E(P_j), geometry gives
`E(P_j)<=C_D #P_j`. The fixed logarithmic moments therefore imply, for every
fixed B,

```
sum_j j^B E(P_j)/R_j^2 < infinity.
```

An arithmetic lower bound `E(P_j)>=c R_j^2/j^C` at infinitely many scales
would contradict this (take B=C). Any fixed subquadratic power remains
compatible with all these moments; even `R_j^2 exp(-sqrt(log R_j))` is
compatible. No such near-quadratic arithmetic lower bound has been proved.
The known long-corridor estimates are far below it, and a sum of independently
attributed prime costs is unjustified.

A further literature check found an imaginary-quadratic Jacobsthal theorem
in corpus 2110.06973, `main.tex`, section 3. It bounds how far along a horizontal
line one must search for an element coprime to a FIXED ideal by a power of
its number of rational prime factors. It is a surviving-point gap bound,
not a bound on diameters of survivor components or a uniform fixed-root
small-support theorem. It does not supply the missing implication.

Spec.lean remains unchanged. The prior coprime-norm Lean reduction is still
verified; no additional all-bound proof or admissible counterexample was found.

## Uniform growing-block sieve and a subpower-weighted support budget

The argument below was independently audited, including the growing-k error
terms, but is a PAPER result, not a Lean formalization. It does not settle
Gaussian moat. No submission declaration was modified.

### Statement

For each fixed D>=1 there are positive constants delta_D,c_D,C_D such that,
for all sufficiently large R, putting

```
k(R)=floor(delta_D log R/log log R),
```

the number of roots z in `R<=|z|<2R` starting a simple k(R)-vertex
Gaussian-prime D-path is at most

```
C_D R^2 exp(-c_D log R/log log R).
```

This is stronger than the earlier fixed-logarithmic savings, but it is still
`R^(2-o(1))`, not the `o(R)` needed to rule out annular crossings.

### Explicit Bonferroni proof

Let K be the number of nonzero Gaussian steps of modulus at most D. There
are at most K^(k-1) simple k-vertex step shapes H, including their initial
vertex 0. Choose a fixed b>2, depending only on D, so that

```
L=(1/2)log(b/2)>log K+4.
```

Sieve by one Gaussian prime ideal above each rational prime p=1 mod 4 in
`D^2 k^2<p<=k^b`. The k offsets are distinct modulo that ideal: their nonzero
differences have norm at most D^2(k-1)^2<p. On each fixed horizontal row, the
real coordinate therefore has exactly k forbidden classes modulo p.

Let P be the number of these rational primes, rho_p=k/p, and
`lambda=sum_p rho_p`. Mertens' theorem in the progression 1 mod 4 gives

```
lambda/k -> (1/2)log(b/2)=L
```

as k tends to infinity; D and b are fixed. Choose a fixed integer M satisfying

```
M>max(e^2(L+1), log K+4),
r=2 ceil(Mk/2).
```

Write e_j for the elementary symmetric sums of the rho_p. The even
Bonferroni truncation T_r satisfies

```
T_r <= product_p(1-rho_p)+e_(r+1)
    <= exp(-lambda)+lambda^(r+1)/(r+1)!
    <= exp(-lambda)+exp(-Mk).
```

For the first inequality use the adjacent odd and even Bonferroni bounds;
no monotonicity of the summands is assumed. For the last, with n=r+1>=Mk,
`n!>=(n/e)^n` and lambda<=(L+1)k give
`lambda^n/n!<=(e(L+1)/M)^n<=exp(-n)`.
For sufficiently large k, lambda>=(L-1)k, hence

```
K^k T_r <= 2 exp(-3k).
```

The interval discrepancy is controlled directly, without a hidden uniform
sieve theorem. An intersection of j of the forbidden residue sets contains
exactly k^j CRT classes; its count in an interval of N consecutive integers
is `N product rho_p+O(k^j)`, with absolute error at most k^j. Summing absolute
errors through order r yields

```
E <= sum_(j<=r) binom(P,j) k^j
  <= (1+kP)^r
  <= exp((M+2)(b+2)k log k),
```

using P<=k^b, k>=2, and r<= (M+2)k. Choose

```
0<delta_D<1/[8(M+2)(b+2)].
```

For k=k(R), the inequality log k<=log log R gives E<=R^(1/8).
Multiplying by all shapes and O(R) horizontal rows gives total error
`O(R^(9/8+o(1)))`, hence `O(R^(5/4))`. The main term is
`O(R^2 exp(-3k))`; the error is negligible relative to it. Floor effects cost
only a constant factor, and one may take c_D=3delta_D.

Finally the primality-to-sieve implication is valid at these growing lengths:
all vertices of a block rooted in the annulus have modulus at least R-Dk>=R/2,
while k^b<R^2/4 eventually. Thus a vertex prime cannot equal, up to associates,
a sieving-prime generator. Count survivors in the enclosing integer square;
points outside the annulus only enlarge that count and are not assumed prime.
All parameters b,M,delta_D are fixed before R grows.

### Consequence for hypothetical prime paths

For some eta_D>0, for example any eta_D<c_D/4, every injective prime D-path
satisfies

```
sum_n exp(eta_D log(3+N(x_n))/log log(3+N(x_n)))/N(x_n) < infinity.
```

Every vertex in a radius-R annulus starts its own k(R)-vertex simple forward
block. The count above therefore bounds path vertices, without assuming any
radial monotonicity. Throughout that annulus,

```
log(3+N(z))/log log(3+N(z))
    = (2+o(1)) log R/log log R.
```

Its weighted contribution is bounded by a decaying exponential of
`log R/log log R`. On dyadic annuli R=2^j this is `O(exp(-a j/log j))`, whose
sum converges. There are only finitely many small vertices by injectivity.
The denominator log log(3+N(z)) is positive at all Gaussian-prime norms.

Thus the proposed rooted small-support theorem would only need to hold for
sufficiently small support mass with this stronger weight

```
omega_D(q)=exp(eta_D log(3+q)/log log(3+q))/q.
```

Conjugating a prime-path tail increases the support budget by at most a factor
two. Its weighted tail budget tends to zero, so the same fixed-root reduction
to supported integer components applies IF that component theorem is proved.

It remains unproved. The weight is still q^(-1+o(1)) and does not control the
reciprocal-radius sum, which diverges on every bounded-step ray. An upper
count R^(2-o(1)) still allows the order-R vertices of an annular crossing.
The whole-monoid profinite/character obstruction also remains applicable,
since omega_D(q) tends to zero. No uniform connective-constant loss or other
root-sensitive arithmetic bound was obtained in the further exploration.

## Verification commands

```
lake env lean Submission/WallBound.lean
lake env lean Submission/ProtectedWall.lean
sha256sum Submission/Spec.lean
```

The expected unchanged submission hash is
`7f93966b075d7db9756df434e41aa6eca9c5ec3493f038524bc009aeadb82c81`.
