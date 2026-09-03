# Near-square sieve deletion: a concrete consequence of an eventual gap hole

## Outcome

No contradiction and no proof of the target were obtained. This attempt was to descend through the prime factors of the composite points that disappear in the last stage of the Eratosthenes sieve. The calculation below gives an explicit necessary condition for an eventual hole, and identifies why this particular descent does not close. It uses actual integer factorization, not a model of prime indicators.

`Spec.lean` was neither read for re-auditing, edited, nor used as a premise in this pass. No Lean proof, axiom, or admitted helper was added.

## 1. An exact deletion constraint, with global consecutivity retained

Assume that for some fixed `0<a<b` and `N0`, all globally consecutive prime gaps at indices `n>=N0` avoid `(a log n,b log n)`. Fix

    a < A < B < b,    L = log X,    y = sqrt(X).

PNT implies, uniformly for a prime `p` in `(X,2X]` and its global index `j(p)`,

    log j(p) = log p - log log p + o(1),
    log j(p)/L -> 1.

Thus, for all sufficiently large X, a globally consecutive prime gap in `(A L,B L)` with both endpoints in `(X,2X]` is forbidden by the assumption. The strict interior margins are important; `log(index)` has not been identified exactly with `log X`.

Define

    R_X = {m in (X,2X] : every prime divisor of m exceeds sqrt(X)}.

Order its elements as `r_1<...<r_M`. Let `E(X)` count those adjacent pairs with

    A L < r_(i+1)-r_i < B L.

For X>4, every composite member of R_X is `p q`, where p,q are primes, `sqrt(X)<p<=q`, and `pq<=2X`. Three prime factors, counted with multiplicity, would give a number exceeding `X^(3/2)>2X`. Prime squares are included. Let S(X) be the number of these composite members.

Every edge counted by E(X) must touch a composite member. Indeed, if its two endpoints were prime, any intervening prime would also lie in R_X and between these two adjacent members. Hence they would be **globally consecutive primes**, contrary to the assumption. A composite vertex has degree at most two in the ordered path, so the exact inequality is

    E(X) <= 2 S(X).                                             (1)

No boundary error is needed: only edges with both endpoints in `(X,2X]` are counted.

A sharper finite statement is available. If the runs of adjacent band edges have lengths `ell_1,...,ell_t`, then

    sum_j ceil(ell_j/2) <= S(X).                                (2)

This is the minimum-vertex-cover bound for disjoint paths. Equivalently, if I(X) counts band-edge incidences at composite vertices, and J(X) counts band edges having two composite endpoints, then

    E(X) - I(X) + J(X)

is exactly the number of prime--prime band edges in R_X. Such edges are genuine prime-gap hits. Consequently a single positive value of this expression, or the stronger sufficient certificate `E(X)>2S(X)`, would suffice at that scale; a positive-density gap law is not assumed. A prime-gap hit can contain composite members of R_X, so the converse identification of all prime-gap hits with prime--prime R_X edges is NOT asserted.

## 2. The composite population has an explicit second-order size

Unique factorization gives the exact sum

    S(X) = sum_(sqrt(X)<p<=sqrt(2X), p prime)
             [ pi(2X/p) - pi(p) + 1 ].                         (3)

The `+1` counts q=p, so prime squares have not been silently discarded. All prime arguments in (3) lie between `sqrt(X)` and `2sqrt(X)`. PNT, uniformly on this fixed multiplicative range, yields

    pi(2X/p)-pi(p)+1
      = (2/L)(2X/p-p) + o(sqrt(X)/L).

Uniformity here is an absolute error, not a relative asymptotic for arbitrarily short intervals. Summing the error over O(sqrt(X)/L) primes is legitimate. Partial summation using PNT a second time gives

    S(X) = (4/L^2) integral_(sqrt(X))^(sqrt(2X)) (2X/t-t) dt
             + o(X/L^2)
         = (4 log 2 - 2 + o(1)) X/L^2.                         (4)

Alternatively, scale p=u sqrt(X), q=v sqrt(X). The ordered factor region is

    1<u<=sqrt(2),    u<=v<=2/u,

whose area is `log 2-1/2`; the two prime densities each contribute `2/L`. This independently checks the constant. Prime squares contribute only `O(sqrt(X)/L)=o(X/L^2)`.

Combining (1) and (4), the eventual hole has the concrete arithmetic consequence

    E(X) <= (8 log 2 - 4 + o(1)) X/log^2(X)                    (5)

for EVERY sufficiently large X, for every fixed interior band `(A,B)`.

This is much smaller than the total number `(1+o(1))X/log X` of members of R_X. It is a necessary consequence, not an existence theorem. No lower bound contradicting (5) has been established here.

## 3. The attempted descent through p and q fails at a precise place

The intended next step was to use the eventual-hole assumption at the smaller heights of p and q to show that these semiprimes cannot conceal every band edge. Three arithmetic checks prevent that inference.

**No common divisor transports a short edge.** If distinct `m,n in R_X` satisfy `|m-n|<B log X<sqrt(X)`, then

    gcd(m,n)=1.                                                (6)

A common prime divisor would exceed sqrt(X) and divide a nonzero smaller difference. In particular, for an endpoint `m=pq`, neither p nor q divides its neighbouring endpoint `m+h`. Dividing by p gives `q+h/p`, not another integer, much less a second prime. Rounding loses the edge entirely. This is an exact obstruction to the proposed factor descent, not an estimate of its efficiency.

**The two factors of the same endpoint are usually at the wrong separation.** For each fixed K>0,

    #{sqrt(X)<p<=q, pq<=2X, q-p<=K log X} = O_K(sqrt(X)).       (7)

There are `O(sqrt(X)/log X)` choices of p, and at most `K log X+1` integer choices of q for each p. Therefore (7) is `o(S(X))`. A factor pair that itself could be a forbidden consecutive prime gap at the smaller height must belong to (7), for a suitable fixed K depending on b. Most semiprime endpoints do not directly test the missing band between their own factors. This argument does NOT claim the assumption forbids nonconsecutive prime-pair distances.

**Moving a factor to its next prime changes the wrong physical scale.** Replacing q by its next prime q' changes pq by `p(q'-q)>=2p>2sqrt(X)` for large X. This is much larger than the original `B log X` window. Thus applying the assumption to the next gap after q does not control the local R_X edge. The same applies with the factors interchanged.

The exact arithmetic statistic acquired instead is a bilinear nearest-rough-neighbour correlation. Write `R_y(n)=1` when n is positive and has no prime factor at most y. For a semiprime m=pq, its positive-side band incidence is

    sum_(A L<h<B L, h integer, pq+h<=2X)
       R_y(pq+h) product_(1<=t<h) (1-R_y(pq+t)).                (8)

There is a corresponding negative-side formula, with the lower interval boundary imposed. Summing (8) and its negative-side version over the prime factors in (3) gives I(X). Factoring pq has not eliminated the endpoint or intervening-integer conditions in (8). PNT evaluates (3), but does not evaluate (8). The gap statistic therefore does not obey a closed one-variable Buchstab recursion just from the one-point rough-number count.

This is the first unclosed implication in the attempted descent: no relation was proved that turns the smaller-height missing-gap conditions for p and q into a contradiction for the logarithmic-shift, consecutive-neighbour condition in (8).

## 4. Why complete-period sieve statistics do not supply the missing lower bound

Let `Q_y=product_(p<=y) p`. The full periodic sifted set has exact density

    phi(Q_y)/Q_y ~ exp(-gamma)/log y
                 = 2 exp(-gamma)/log X,

by Mertens' product theorem. But at `y=sqrt(X)` its restriction to `(X,2X]` is R_X, whose density is

    |R_X|/X = (1+o(1))/log X,

by PNT and (4). Thus replacing this particular short segment by a uniform phase modulo Q_y is already wrong in the leading ONE-point constant: `2 exp(-gamma)` is not 1. Also `Q_y=exp((1+o(1))sqrt(X))` is far larger than X. This does not rule out a correctly localized theorem with a Buchstab correction; it rules out silently transferring a complete-period law here.

Source checks:

- `/corpus/src/1302.2296/1302.2296.tex`, lines 29--45: the reduced-residue gap moments sum over a COMPLETE period. Lines 210--212 explicitly use summation over all residues modulo q. These are not lower bounds for E(X) in the near-square-root initial segment.
- `/corpus/src/1802.07604/1802.07604.tex`, lines 103--123: the sieved set is periodic and the main theorem supplies a large gap. Lines 139--148 explicitly require the period to fit inside the desired physical interval to transfer a periodic gap; their prime application uses sieve cutoff about log X, not sqrt(X).

The deductions (1)--(8) require only unique factorization, finite counting, PNT and partial summation. Mertens is used only for the failed periodic-transfer check. No prime-pair asymptotic, gap-selected BV estimate, or sieve independence assumption is used.

## Verification and stopping point

The area integral and constants in (4)--(5) were checked independently by symbolic integration. The incidence identity, degree bound, and run bound were exhaustively checked as finite graph algebra on paths of up to eight vertices. No numerical prime-gap search was performed.

The substantive result of this pass is (5), with the exact factor-descent obstruction (6)--(8). A lower bound contradicting (5), or a sparse positive certificate `E-I+J>0` on unbounded scales, remains unproved. Such a certificate is not being asserted as a new lemma. The attempted lower-scale propagation fails before it supplies one, and the checked periodic sieve theorems do not repair that failure.
