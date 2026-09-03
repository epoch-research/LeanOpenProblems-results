# Small Gaussian factors and the proposed maximum-degree route

This is NOT a settlement of Erdos 773. The strongest actual lower bound is
now RelaxedSquareLower.eventual_power_lower, M(N)>=N^(2/3)/75 eventually.
The present module does not yet prove a maximum-degree counting bound.

## Completed module

GaussianCollisionFactorization.lean imports only FormalConjecturesUtil.
All five audits are clean and a built olean exists. Log:

    /tmp/gaussian-collision-factorization.log

For nonzero Gaussian integers z,w with equal norms:

1. factorization supplies g,h with z=g*h and w associated to g*conj(h).
2. small_factor also achieves norm(h)^2<=norm(z), allowing either w or
   conj(w) to be associated to g*conj(h).
3. primitive_part removes the rational-integer gcd of the real and
   imaginary coordinates without increasing the norm.
4. small_primitive_factor combines these: h is nonzero, its integer
   coordinates are coprime, and norm(h)^2<=norm(z).

The factorization uses extract_gcd in the Gaussian Euclidean domain.
After cancelling the common norm, coprimality gives h|conj(k); equal
positive norms imply that the quotient has norm one and is a unit.
Swapping g,h if necessary makes the latter factor small. This is a genuine
integer factorization result, not an assumed small-base specialization.

## Further completed encoding steps

Three additional clean modules now complete the elementary normalization
and residue steps. All have built oleans and permitted-axiom audits.

GaussianOddFactor.lean:
- Same-parity coprime integer coordinates are both odd.
- Divide by 1+i in that case. The new coordinates are coprime and have
  opposite parity; the norm decreases. Its conjugate is associated to
  itself, so the output factor changes only by a unit.
- small_odd_factor gives the small primitive opposite-parity factor.

GaussianQuadrantFactor.lean:
- Classifies the four possible Gaussian units by their coordinates.
- squareCoords(z) is the finset {re(z)^2,im(z)^2} over the integers.
  Both association and conjugation preserve this invariant.
- A unit rotates any nonzero factor into re>0, im>=0, preserving
  coprimality and opposite parity.
- quadrant_factor gives z=g*h, normalized h, norm(h)^2<=norm(z), and
  squareCoords(w)=squareCoords(g*conj(h)). Both input and output changes
  from the unit normalization are explicitly checked.

GaussianFactorResidues.lean:
- Coprime coordinates imply IsCoprime re(h) norm(h).
- If z=g*h, norm(h) divides im(z)*re(h)-re(z)*im(h).
- partner_congruence: for a fixed real input coordinate and factor h,
  any two possible imaginary coordinates differ by a multiple of norm(h).
- output_unique: fixing z and nonzero h uniquely determines the other
  unordered squared-coordinate set, even if the factorizations use
  differently named g's.
- norm_height: the small factor has norm<=2N when input roots a,b<=N.
  This avoids needing sqrt(2) in the eventual finite counting statement.

Logs:
    /tmp/gaussian-odd-factor.log
    /tmp/gaussian-quadrant-factor.log
    /tmp/gaussian-factor-residues.log

The combined audit source is GaussianFactorAudit.lean, with all 16 clean
checks in /tmp/gaussian-factor-combined-audit.log.

## Still missing

- Assemble the factor witnesses into a finite covering or injection for
  incident square-collision supports. For fixed factor and partner, the
  proved output uniqueness must be connected to the ordered natural root
  pair or the four-root finset, without a multiplicity loss.
- Convert partner_congruence into the finite interval fiber bound N/q+1.
- Count normalized primitive opposite-parity directions with q<=2N,
  including the periodic sieve and weighted harmonic sum below.

No incident-degree bound or new Sidon bound follows until these steps are
proved. The unit-norm axis factor can be excluded as trivial pair matching
or safely charged O(N); this choice has not yet been assembled into a
finite counting theorem.

## Proposed quantitative count

With the encoding established, the target bound is a sum of N/q+1 over
primitive opposite-parity first-quadrant Gaussian directions with q<=2N.
The expected leading coefficient is 1/pi, which is below 1/3.

A finite small-prime sieve may suffice without full Mobius inversion:
opposite parity and exclusion of common factors 3,5,7 are periodic modulo
210. Their density is

    18432/44100 = (1/2)*(8/9)*(24/25)*(48/49).

Split the first quadrant at u=v, using symmetry, and bound v/u in rational
bins. A sufficiently fine upper-step approximation to

    integral_0^1 1/(1+t^2) dt

(for example an upper bound 793/1000 from about forty bins) gives a product
with the displayed density below 1/3. The largest u is at most sqrt(2N), so
the factor two from quadrant splitting cancels the half in log(sqrt(2N)).
The periodic row errors and the +1 per direction should contribute O(N).
This entire counting step is unproved. Existing PeriodicCollisionWeights
and ParityTriangleCount supply similar finite summation infrastructure.

## Exploratory computation only

Research/SquareIncidentProfile.cpp sorts all unordered distinct-root square
pairs, groups equal norms, and counts incident four-supports exactly.
Outputs are /tmp/square-incident-2000.log and /tmp/square-incident-8000.log.
No numerical extrapolation is used in any theorem. The finite maxima being
below 1/3 do not prove the proposed asymptotic degree bound.

Even a completed degree bound below (1/3)N log N would not settle the main
conjecture. It could help avoid maximum-degree trimming; a sharp enough
extraction theorem would still be needed even for the coefficient-one
2/3 endpoint, and all smaller epsilon would remain.

## Update: the complete incident-degree count is now proved

The previous "still missing" items above have all been completed. The new
clean modules are GaussianIncidentEncoding, GaussianIncidentCounting,
GaussianDirectionWeights, GaussianRadialBins, GaussianRadialCounting,
GaussianDirectionSum, and GaussianIncidentDegree. They all have built
oleans; their printed axiom checks contain only the three permitted axioms.

GaussianIncidentDegree.finite_degree_bound proves, for 1<=a<=N,

    degree(edges [1,N],a) <= N*((83/250)*log(2N)+28006).

GaussianIncidentDegree.eventual_degree_bound proves, uniformly in a,

    eventually degree(edges [1,N],a) <= (333/1000)*N*log N.

The covering counts actual four-root supports. Each fixed direction and
partner determines the ordered output pair uniquely. Directions have
coprime opposite-parity coordinates and norm <=2N. Partners form one residue
class modulo that norm, giving N/q+1. The period-210 sieve sum is kernel
checked as 18432; forty rational radial bins give the triangle reciprocal
bound (83/250)*(1+log R)+14000. The axis contributes at most one, the two
positive triangles are symmetric, and R=floor(sqrt(2N)). The direction
count is at most 4N. No numerical extrapolation is involved.

Logs: /tmp/gaussian-incident-encoding.log,
/tmp/gaussian-incident-counting.log, /tmp/gaussian-direction-weights.log,
/tmp/gaussian-radial-bins.log, /tmp/gaussian-radial-counting.log,
/tmp/gaussian-direction-sum.log, /tmp/gaussian-incident-degree.log.

This remains an arithmetic input, not a new Sidon lower bound. To avoid
maximum-degree trimming after sampling, uniform sampled-degree control is
still needed. A possible elementary route is a high-moment bound for each
triple link: if the link has D edges and maximum vertex degree K, its q-th
sampled edge-count moment should be <=(p^3 D+3qK)^q. With q proportional to
log N, the existing subpower pair-codegree bound makes the error negligible
and gives a union bound over all centers. Even that step would not supply a
new exponent or settle the conjecture.
