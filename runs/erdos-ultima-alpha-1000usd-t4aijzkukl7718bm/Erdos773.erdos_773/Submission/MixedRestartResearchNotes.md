# Mixed regularization and batched restart inputs

## Status of the actual task

The original conjecture is NOT settled. Spec.lean is unchanged and has its
sole sorry for 0<epsilon<=1/3. No incomplete proof has been submitted in this
continuation. The strongest actual lower bound remains

    M(N) >= N^(2/3)/36 eventually.

Neither the coefficient-one endpoint nor any exponent above 2/3 is proved.
Even the endpoint would not settle the smaller-epsilon range.

## Completed mixed regularization

The following modules compile and their printed audits use only propext,
Classical.choice, and Quot.sound:

- PolynomialSidonSlopes
- UniformLayerRegularization
- RegularizationCommonNeighbors
- RegularizationSharedLinks
- MixedLayerRegularization
- FiniteHypergraphRestriction
- GreedyResidualRegularization

MixedLayerRegularization.exists_regularization takes a rank-2/3/4 system
with prescribed degree caps D2,D3,D4, pair codegree K>=1, distinct-edge
intersection cap two, and graph common-neighbor cap C. It constructs a prime
p and a mixed regularized G on exactly 24*p^3 copies, with

    cap = max(max(D3,D4), 2*PolynomialSidonSlopes.height(D2)+5),
    cap <= p <= 2*cap,
    height(D2) = 3*(D2+1)^3.

All three rank degrees are exactly their prescribed caps simultaneously.
Pair codegree stays <=K, intersections stay <=2, graph common neighbors
stay <=C+3. Every independent B in G gives independent A in H with

    |B| <= 24*p^3*|A|.

There is no additional density loss. Construction order is rank 4, then 3,
then 2. New rank-two affine slopes are selected from a Sidon reservoir;
its proof is PolynomialSidonSlopes.seed_sidon, NOT square-Sidonness.

The main existential uses a dependent prime-proof binder and a local Fact
instance, so Fintype (ZMod p) exists already when the proposition elaborates.
This fixes the pending elaboration error from the previous continuation.

### Shared rank-three links

RegularizationSharedLinks.links H x y is the family of two-sets A avoiding
x,y for which both insert x A and insert y A are edges. Its cardinality is
count H x y. For distinct x,y, any common upper bound B for these counts is
preserved EXACTLY by each regularization layer, hence by the assembled model.
This universal preservation is now included in MixedLayerRegularization.Result
and in exists_regularization.

The key overlap_rigid theorem says that two distinct regularized edges
with at least two common vertices must lie together in a single OLD copy.
All new/new and old/new intersections have size at most one.

### Actual greedy residual transport

FiniteHypergraphRestriction transports degrees, pair degrees, common
neighbors, intersections, and independence to the subtype of an actual
finite carrier. This prevents accidentally counting deleted ambient vertices.

GreedyResidualRegularization.exists_restart_model applies the construction
to all active residual supports on Q=available H I, with carrier cardinality
24*p^3*|Q|, not 24*p^3*|ambient|. Its transfer gives J subset Q with

    I union J independent,
    |B| <= 24*p^3*|J|,
    |I union J| = |I|+|J|.

The original system need only have edges of size <=4 and I independent;
residual ranks 2..4 follow from availability. Identifying duplicate residual
supports decreases rank degrees and pair codegrees. Common-neighbor counts
agree with the actual greedy closure graph. Shared-link preservation is
stated universally from the restricted residual system to the regularized
model. No stochastic profile estimate is part of this theorem.

## Correct mixed common-neighbor tails

Completed:

- GreedyMixedCommonTails
- GreedyMixedCommonProfiles

GreedyMixedCommonTails uses the original indexed common-neighbor patterns,
but separates them by actual selected-witness support size r=0,1,2,3,4.
All witness incidences are <=4*K^2, without assuming four-uniformity.
The zero-support count is <= the original graph common-neighbor count.
For r>0, its first-crossing packing tail has power p^r, NOT p^3:

    P(hit selectedCost_r > r*(4*K^2)*k)
      <= (3*|supportLayer_r|*p^r/(k+1))^(k+1).

This is conditional on the explicit capped TargetLaw; the target cap
r*(k+1)<=cap is retained. prefix_common_tail sums all four positive-support
tails and adds the initial deterministic common-neighbor cap.

GreedyMixedCommonProfiles.one_support_bound proves, if rank-two degrees at
both endpoints are <=D and the shared rank-three link count is <=B,

    |supportLayer_1| <= 2*D*K+2*B.

Every one-support pattern either uses a rank-two edge, or is one of the
two middle-vertex roles of a shared rank-three link. No assumption bounding
B by the initial graph common degree is made. This identifies a necessary
additional profile to control during restarts, not an obstruction to all
possible restarts.

## Batched alternative: completed finite inputs

Completed and audited:

- IndexedBernoulliMoments
- WeightedBernoulliLowerTail
- BernoulliHitCounts
- GreedyBatchState
- GreedyBatchGraphLoss
- GreedyBatchPromotions
- GreedyBatchDegreeStep

### Overlap-sensitive indexed moments

IndexedBernoulliMoments handles a finite index family T with r-element
supports C(i). Supports may repeat. Let K_j bound the number of indices
whose support contains any fixed j-set. It proves

    E[X^q] <= budget(r,q,K,p)^q,
    budget = sum_{j=0}^r choose(r*q,j)*K_j*p^(r-j).

The corresponding Markov tail is (budget/L)^q. In particular an overlap
in one vertex still pays p^(r-1); it is not charged at probability one.
The proof is an explicit finite Bernoulli expectation identity, not an
independent-edge approximation.

### Weighted lower tails

WeightedBernoulliLowerTail.relative_lower_tail proves for independent marks
with density p, weights 0<=w_i<=W and W>0, and mu=p*sum_i w_i,

    P(sum_i w_i*mark_i <= (1-eta)*mu)
      <= exp(-eta^2*mu/(2*W)),  eta>=0.

The Laplace transform is computed from the actual finite product law.
The negative-exponential quadratic bound is proved by differentiation.
Only vertex marks are independent; no edge-indicator independence is used.

### Hit-count lower concentration

BernoulliHitCounts treats an indexed family of sets D_i with |D_i|<=s and
vertex incidences <=M, M>0. The number of sets hit by a mark set R satisfies

    sum_i |D_i intersect R| <= hitCount(R)+pairCost(R),

where pairCost retains the original index i and every two-subset of D_i.
Its rank-0/1/2 incidence caps are

    K0=|T|*choose(s,2), K1=s*M, K2=M.

Consequently, for mu=p*sum_i |D_i| and L>0,

    P(hitCount <= (1-eta)*mu-L)
      <= exp(-eta^2*mu/(2*M)) + (budget(2,q,K,p)/L)^q.

All indexing, pair multiplicities, linear double counts, and finite union
bounds are verified. This is intended to control loss of residual edges
when graph neighborhoods are marked, but that application is not done.

### Conservative batch state and exact expectation

GreedyBatchState marks an arbitrary R, rejects ALL marked vertices lying
in fully marked forbidden edges, and retains the independent set J.
The next carrier Q excludes ALL of R, including the rejected marked vertices,
and also every v lying in an edge e with e.erase v subset R.

This intentional carrier restriction is important. Removing marked vertices
from J does not reopen constraints, because they remain absent from Q.
The sufficient next system consists of every e\\R of size >=2 lying in Q.
Empty residuals are already handled by independence of J; singleton
residuals cannot meet Q. extension proves that any independent A in this
next system, A subset Q, gives an independent J union A in the original H.

For p in [0,1], delta>=0, the actual finite expected reward satisfies

    E[|J|+delta*|Q|] >= p*V - sum_e |e|*p^|e|
      + delta*((1-p)*V - sum_e |e|*p^(|e|-1)).

There is no local profile conclusion here. The residual system is a
SUFFICIENT system for extensions; equality with the ordinary residual of
J is not claimed, since it contracts the larger tentative set R.

### Graph-loss application now completed

GreedyBatchGraphLoss proves that graph neighborhood cardinality is exactly
the rank-two degree, and uses the killing set

    kills(H,x,e) = union_{z in e.erase x} (neighbors(H,z).erase x).

Only the tracked endpoint is excluded, NOT its entire neighborhood.
Unconditional concentration is sufficient: if an old edge survives in Q,
none of these killing marks occurred. This avoids unnecessarily conditioning
on survival of the endpoint.

For |e|=j and graph degree D, killing-set cardinality is at most (j-1)*D,
and its deficit below (j-1)*D is at most

    (j-1)+choose(j-1,2)*C.

Each mark belongs to at most D*P killing sets of a prescribed incident-edge
family, by pair codegree. For old rank-two edges the sharper bound is C,
by graph common neighbors; the mark x itself is excluded. These statements
are proved, not hypotheses on random samples.

old_survival_tail applies BernoulliHitCounts.lower_tail to these actual
killing sets. It bounds the upper tail of uncontracted old-edge counts in Q.
kill_mean_lower supplies the deterministic mean lower bound. No promotion,
shared-link evolution, or simultaneous whole-stage theorem is included yet.

Latest log: /tmp/greedy-batch-graph-loss-4.log. All eight audits are clean.

### Promotion tails and full rank-degree accounting now completed

GreedyBatchPromotions.family indexes each original incident rank-r edge e
and every k-set of e.erase x. Its exact cardinality is

    degree(layer H r,x)*choose(r-1,k).

Every nonempty specified-subset incidence is <=8*P when r<=4, by the
original pair-codegree cap P. Thus cost_tail applies the overlap-sensitive
moment theorem with this exact rank-zero budget and 8*P for each positive
overlap rank. Repeated selected supports still retain their edge indices.
contraction_count injects actual rank-(j+k) to rank-j contractions into
these selected witnesses.

GreedyBatchDegreeStep then proves the deterministic inequalities

    degree(next_2,x) <= oldCount_2 + cost(3,1) + cost(4,2),
    degree(next_3,x) <= oldCount_3 + cost(4,1),
    degree(next_4,x) <= oldCount_4.

oldCount_j counts original incident rank-j edges wholly contained in Q.
The proofs account for deduplicated residuals, all original ranks <=4,
and the distinction between uncontracted survivors and promotions.
These are not yet simultaneous sampled degree caps or an iteration theorem.

Logs: /tmp/greedy-batch-promotions-1.log and
/tmp/greedy-batch-degree-step-1.log. All nine printed audits are clean.

## Proposed next work (NOT proved)

The batched route may avoid a long moving-envelope theorem:

1. At an exact mixed degree profile, mark with p=delta/d_eff, where
   delta is small compared with 1/(1+t^2).
2. The old rank-j loss estimate is now done in GreedyBatchGraphLoss.
   Instantiate its mean and tail at the desired local scales. No survival
   conditioning is needed; only the endpoint itself is excluded from marks.
3. Promotion tails and all-rank deterministic degree accounting are now
   proved. Instantiate their budgets and combine with old-edge losses;
   the resulting simultaneous scalar degree caps are still to be established.
4. Track shared rank-three links as an additional upper profile. Their
   old two-vertex carriers should lose about 2*p*D2 of their mass; new
   links arise from rank-3/4 pairs and need explicit indexed counts.
   A bound of order d_eff*K times polylogarithmic factors would make the
   one-support common-neighbor budget manageable.
5. Graph common-neighbor caps may accumulate O(K) per short stage if the
   shared-link profile is controlled. This claim is not yet a theorem.
6. Use a penalized weighted reward |J|+delta_future*|Q| to select a batch
   satisfying all local caps. This can avoid separate global carrier-size
   concentration. Then regularize and transfer density recursively.
7. Prove all scalar stage errors, rounding, volume growth, and iteration
   bounds. No such iteration theorem is currently available.

The tentative rationale is that repeated regularization has quasipolynomial
volume over O(log N) stages (with fixed small stage constant), while the new
local tails could be exponentially small in a positive power of d_eff.
This must be proved at the required shrinking scales. It is not a substitute
for the missing uniform local-profile bootstrap.

## Logs and final-file status

Latest clean mathematical build logs:

- /tmp/uniform-layer-final.log
- /tmp/regularization-common-final.log
- /tmp/regularization-shared-links-2.log
- /tmp/mixed-layer-shared.log
- /tmp/finite-hypergraph-restriction-3.log
- /tmp/greedy-residual-shared.log
- /tmp/greedy-mixed-common-2.log
- /tmp/greedy-mixed-common-profiles-2.log
- /tmp/indexed-bernoulli-moments-2.log
- /tmp/weighted-bernoulli-lower-tail-3.log
- /tmp/bernoulli-hit-counts-5.log
- /tmp/greedy-batch-state-2.log

Some logs contain harmless unused-section-variable or tactic-style lints.
Their theorem audits contain only the allowed axioms. All named modules have
built oleans. No explicit sorry was added to any of these modules.

Spec.lean SHA-256 remains:
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14

Combined 44-declaration audit: Submission/MixedRestartAudit.lean;
log /tmp/mixed-restart-combined-audit.log. Latest Spec check:
/tmp/spec-mixed-restart-check.log (the known admission remains).

## Further batch reasoning to check in the next continuation

The proposed shared-link cap can have the form B=b*d_eff, with b a small
positive power of the original size, much larger than P and chosen moments
but much smaller than the terminal d_eff. For an old shared-link family of
size near B, graph-neighborhood hits should remove about 2*p*D2 of the
links. Its one-mark incidence is at most D2*P (each shared-link vertex has
at most P link incidences). This may permit the same hit-count concentration.
If the family is far below B, a deterministic upper bound suffices instead.

New shared links can be partitioned by original edge ranks (3,4), (4,3),
and (4,4). The first two have one selected witness; the last has two,
since a common selected fourth vertex would give an original intersection
of size three, violating the cap. Plausible finite index budgets are
D3(x)*P, D3(y)*P, and 3*D4(x)*P respectively, with bounded marked-vertex
incidences. NONE of these shared-creation counting statements or tails has
yet been formalized in this continuation.

Common-neighbor caps need not shrink at each batch if their increments can
be bounded by a fixed very small power of the original size; over O(log N)
stages this could remain negligible compared with terminal d_eff. This
requires correct mixed support-2/3/4 cardinality budgets in addition to the
already proved support-1 budget, and an application to the conservative
batch next-system rather than the ordinary residual of an independent R.
The latter distinction must not be skipped: tentative R can be dependent.

No scalar parameter choice, stage union bound, regularized batch iteration,
or new asymptotic square-Sidon bound has been proved.

## New finite batch results (next continuation, verified)

Nine further modules have been completed:

- GreedyBatchSharedWitnesses: indexed original sources (e,A,f) for new
  shared links. Support size is (r-3)+(s-3) under intersection cap two;
  total mass <=D_r*choose(r-1,2)*P, positive incidence <=2P^2.
  Both (3,4) orientations and (4,4) have actual Bernoulli moment tails.
- GreedyBatchSharedLoss: old shared two-links have kill size <=2D2,
  kill incidence <=D2*P, and a proved mean deficit <=2+C per link.
- GreedyBatchSharedStep: the actual next shared count is at most the old
  surviving count plus the two (3,4) costs and the (4,4) cost.
- GreedyBatchCommonBudgets: support masses for common-neighbor creation:
  rank1 <=2D2*P+2B; rank2 <=4(D2+D3)*P;
  ranks3,4 <=3(D2+D3+D4)*P. Positive incidence <=4P^2.
- GreedyBatchCommonStep: next common count <=old common count plus the
  four support-layer costs. No independence of tentative marks assumed.
- GreedyBatchCommonTail combines these into an unconditional finite tail.
- GreedyBatchStructure proves pair-codegree and distinct-edge intersection
  caps for next H R, plus shared-link monotonicity under carrier restriction.
- BernoulliEvents proves indexed union bounds and capped_exponential_tail.
  The latter replaces mu by L in exp(-eta^2*mu/(2M)) when X<=n:
  if mu<L, the event X>=n-(1-eta)*mu+L is empty.
- GreedyBatchSelection proves selection avoiding finitely many bad events
  with reward >=lowerReward - V*sum(bad probabilities). The reward is
  |chosen|+delta*|carrier| and is <=V for delta<=1. Only the explicit
  finite tail bounds are required; there is no conditioning on the future.

The pending add_le_add_right error in BernoulliEvents was fixed with
add_le_add _ le_rfl. The complete extended audit has 77 clean checks:

    /tmp/mixed-restart-extended-audit.log

No simultaneous stage with every tail numerically instantiated has yet
been proved. The original conjecture and the coefficient-one endpoint
both remain unproved.

## Proposed scalar parameters (NOT PROVED)

A fixed-size batch loses N^{-O(kappa)} after logarithmically many stages.
Use a shrinking batch instead. Let m be a very small positive power of N,
q=m^10, P<=m, terminal d>=m^1000, and T^3<=m. Start at t=1, after adding
artificial ranks two and three by mixed regularization. Set

    h=1/(m^2*(1+t^2)),  p=h/d,
    a=1-1000/m^2, A=3+6000/m^2, B=3+3000/m^2,
    F2=A*d*t^2, F3=B*d^2*t, F4=d^3, Dj=ceil(Fj),
    t'=t+h, d'=d*exp(-a*((t+h)^3-t^3)).

The spare profile coefficients are intended to absorb all old-loss,
promotion, multiple-hit, ceiling and Taylor errors. Candidate thresholds:

    eta=1/m^2,
    Lold_j=100*Dj/m^4,
    L31=2*p*D3+D2/m^4,
    L41=3*p*D4+D3/m^4,
    L42=3*p^2*D4+D2/m^4,
    Bcap=ceil(m^50*d), LsharedOld=100*Bcap/m^4,
    Lshared34=Lshared44=m*d,
    Lcommon_r=m^52 (all four r),
    C_i=3+i*(4*m^52+3), eventually <=m^60.

Promotions must be bounded near their means, not by fixed multiples.
The intended moment-tail ratios for leading promotions are 1-O(1/m^2),
so q=m^10 gives exp(-Omega(m^8)). Every local tail is hoped to be
<=exp(-m^7). Shared-link loss has factor approximately 2pD2, while Bcap
shrinks only at the one-d scale, leaving room for its creation costs.
Capped_exponential_tail handles small old shared families.

At most about 2m^3 stages suffice. If initial volume and d are <=m^A,
one regularization uses <=m^(10A+30) copies eventually. All stage volumes
should therefore be <=exp(m^5). This is dominated by the proposed tails.
These estimates still need actual proofs, not just substitution.

Backward density induction candidate:

    alpha(t,d)=(1-10^6/m)*(T-t)/d.

For exact mixed degrees, put z=D2*p+D3*p^2+D4*p^3. Expected continuation
reward per vertex is p*(1-z)+delta_future*(1-p-z). Use exp(a*Delta)>=1+a*Delta
and the slack 10^6/m to pay for Q/d mismatch and failure penalties. At each
stage select R, restrict next H R to its true carrier, regularize to the
next ceilings, apply the future density bound, transfer, and extend chosen.
The dependent tentative R must not be passed to the independent-set
ordinary residual theorem.

Endpoint arithmetic proposal (also NOT PROVED): sampled carrier
|A|>=(1-delta)*N/log N and degree<(1999/6000)*N/(log N)^2. Choose
T^3=(19999/60000)*log N, slightly between the degree constant and 1/3.
For example m approximately N^(1/10^9) leaves terminal d much larger than
m^1000. This could yield a coefficient strictly above one at exponent 2/3.
It still would NOT settle any epsilon<1/3; a new square-specific ingredient
would remain necessary for the original task.

## Complete finite scalar certificate and density iteration (verified)

The next five modules are now built and axiom-audited:

1. GreedyBatchScalarTails
   - budget_mono, moment_mono, and hitCaps_mono.
   - old_degree_tail has the explicit retention

       retention(j,D,C,p,eta) =
         1-(1-eta)*p*((j-1)*D-((j-1)+choose(j-1,2)*C)).

     The subtraction here is REAL subtraction of the two natural terms.
     Its threshold is Dj*retention+L. Rank two uses incidence C; higher
     ranks use D*P. All old exponentials are capped uniformly by L.
   - old_shared_tail uses B*retention(3,...)+L, assuming retention>=0,
     so the actual shared count may be any n<=B.
   - promotion_tail and shared_creation_tail replace actual degree masses
     by prescribed upper degree caps, with explicit scalar moment errors.

2. GreedyBatchCertificate
   - Caps records D2,D3,D4,P,C,B. Margins records the three old-rank margins,
     three promotion thresholds, three shared thresholds, and common(r).
   - Regular H c is exact rank-2/3/4 degree regularity, rank and intersection
     bounds, pair codegree, common-neighbor and shared-link caps.
   - ProbabilityRange is 0<=p,eta<=1, D2*P>0, C>0, and nonnegative shared
     retention. Margins.Positive supplies strictly positive thresholds.
   - vertex_tail and pair_tail instantiate ALL fourteen types of tests:
     six vertex tests and eight ordered-pair tests, including all four
     common-neighbor support layers. There is no TargetLaw hypothesis.
   - bad_tail: if every displayed scalar error <=b, and b>=0, then

       prob(Bad) <= (6V+8V^2)*b.

   - Fits gives the five deterministic target inequalities. NextBounds
     records the resulting three degree caps, shared cap, and common cap.
   - exists_batch proves some R has NextBounds and

       reward >= lowerReward - V*(6V+8V^2)*b,

     provided the right side is positive. No uninstantiated LOCAL
     probability assumption remains; only explicit numeric errors remain.

3. GreedyBatchReward
   - weighted_card_sum exactly double-counts the rank-weighted edge sums.
   - load = D2*p+D3*p^2+D4*p^3,
     rate = p*(1-load)+delta*(1-p-load).
   - lowerReward_eq: lowerReward H p delta = V*rate for Regular H c.
   - tests_mono controls the union-bound factor at larger forward volume.

4. GreedyBatchDensityStep
   - post c adds exactly 3 to its graph-common cap, leaving other caps.
   - copies c = 24*(2*cap(c.D2,c.D3,c.D4))^3 is an explicit upper factor.
   - UniformDensity c V delta quantifies over ALL finite types of a fixed
     universe, all Regular H c, and volumes <=V, and asserts an actual
     independent set of density >=delta.
   - regularize_next restricts next H R to carrier H R BEFORE mixed
     regularization. It preserves shared caps and transfers independent
     sets to the restricted residual. Tentative R is not assumed independent.
   - continue_batch invokes a future UniformDensity at post c', transfers
     it to Q, and extends chosen H R. The resulting cardinality is at
     least the weighted reward. Forward volume requirement: copies(c')*V<=W.
   - density_step combines the actual certificate and this continuation.
     Its numerical rate condition is

       0<rho<=rate(c,p,delta) - (6V+8V^2)*b.

     It also requires 0<=delta<=1, all local scalar errors<=b, Fits,
     and the explicit forward volume bound. No future success event is
     conditioned on or silently assumed.

5. GreedyBatchSchedule
   - Schedule stores current and target caps, margins, p,eta, densities,
     failure budgets, moment orders, and forward volumes at every index.
   - Valid s T consists solely of the finite numeric conditions needed by
     density_step, post(target_i)=current_(i+1), and terminal density zero.
   - iterate proves UniformDensity at EVERY i<=T by exact backward induction.

The combined audit now contains 94 clean declarations:

    /tmp/mixed-restart-stage-audit.log

The proposed m-dependent schedule is NOT yet shown Valid. In particular,
no scalar Fits estimates, uniform exp(-m^7) error estimates, explicit
volume asymptotics, or endpoint conversion have been proved. Thus neither
the coefficient-one endpoint nor any exponent above 2/3 follows yet.
The original Spec theorem is unchanged and still admitted for epsilon<=1/3.

### Sanity checks on proposed scales (reasoning only)

For m>=large, eta=m^-2, q=m^10, h=1/(m^2*(1+t^2)), p=h/d,
t>=1, t^3<=m, d>=m^1000, P<=m and C<=m^60:

- The rank2 fit uses old margin 100D2/m^4 and two promotion margins
  D2/m^4. Its total added margin is 102D2/m^4. The profile gap A-3a
  is 9000/m^2, leaving several thousand D2/m^4 per stage. Rank3/4
  have even larger relative coefficient gaps. Ceiling, Euler and mean
  deficit corrections should be much smaller. This is not a proof.
- Shared-old hit correction leading mean is <=about 18B/m^4, compared
  with threshold 100B/m^4. Its overlap corrections have powers no larger
  than m^-26 (up to t,P factors). The uniform exponential exponent is
  at least roughly m^41, since B approximately m^50*d and M=D2*P.
- Leading promotion31/41 errors need a ratio 1-O(m^-2), so their moments
  give exp(-Omega(m^8)); all other local errors can have constant ratios.
- Common support-four's largest overlap term is about m^42, below m^52.
  The support-one mean from shared links is about m^48, also below m^52.
- The near-mean promotion margins dominate overlap terms (<=m^21),
  since D2/m^4>=m^996. All of these comparisons need uniform Lean proofs.

A suggested next split is: first prove scalar tail estimates under coarse
scale inequalities (before ceilings), then prove Fits for the exponential
profiles, then validate the finite schedule and convert its output. The
full user conjecture would STILL require a separate square-specific idea.

## Elementary moment scalars (verified)

GreedyBatchMomentBounds.lean is built. Its five audits, and the combined
99-declaration audit /tmp/mixed-restart-moment-audit.log, are clean.

- budget_uniform: if K(0)<=n and positive-overlap caps <=M, p in [0,1],

    budget(r,q,K,p) <= n*p^r + r*M*(r*q+1)^r.

  The rank-zero leading term is NOT inflated by a constant.
- hit_budget retains the necessary one-overlap p factor:

    budget(2,q,hitCaps(n,s,M),p)
      <= n*s^2*p^2/2 + 2*q*s*M*p + 2*q^2*M.

- moment_exponential: budget<=(1-u)*L implies the q-moment tail
  <=exp(-q*u), for L>0 and p>=0 (with u in [0,1] as public hypotheses).
- hit_exponential adds the old-hit exponential, giving <=2exp(-q*u)
  if eta^2*L/(2M)>=q*u.
- shrinking_scale: for m>=20, q=m^10, u=1/(20m^2),

    exp(-q*u) <= exp(-m^7).

Thus it is simpler to use b=2*exp(-m^7), not exp(-m^7), for ALL local
errors. This leaves all volume comparisons unchanged in scale.

## Simplified next scalar proof plan (NOT PROVED)

Avoid proving each tail directly with all d,t ceilings. First establish
coarse reusable inequalities for m>=100:

1. For rank r<=4, q=m^10, positive cap M<=8m^2,

     r*M*(r*q+1)^r <= m^46.

   Indeed r*q+1<=5m^10, the left side <=20000m^42, and m^4>=20000.
   So every promotion/shared/common budget <= its EXACT mean +m^46.

2. Near-mean margin: if S>=m^52 and mu<=10S/m^2, then

     mu+m^46 <= (1-1/(20m^2))*(mu+S/m^4).

   One can use m^46<=S/(4m^4), L=mu+S/m^4<=11S/m^2,
   and uL<=11S/(20m^4). This covers all three promotions with
   S=D2 or D3, once their exact leading means are bounded appropriately.

3. Loose margins: if mean<=L/4 and m^46<=L/4, then budget<=L/2,
   hence <=(1-u)L. This covers shared creations and common support layers.

4. Uniform old-hit tail: use natural n,s,D,M with

     M>0, m^30*M<=n, s<=3D, D*p<=4/m^2,
     q=m^10, eta=1/m^2, L=100n/m^4.

   Then s*p<=12/m^2. The leading hit correction <=72n/m^4.
   The overlap terms are <=26m^20*M <= n/m^4 (m^6>=26 suffices),
   so the budget <=73n/m^4, below (1-u)L (even u<=1/4 suffices).
   The exponential condition reduces to M*m^16<=1000n, immediate
   from m^30*M<=n and m>=1. Thus hitError<=2exp(-m^7).

These coarse cap conditions are amply supplied by the proposed profiles:
- D2*p<=4/m^2 (A is near 3; keep this bound, not the looser 10/m^2).
- D2>=m^30*C; D3,D4,B>=m^30*(D2*P).
  Even B approximately m^50*d gives a ratio >=m^47/4 when t<=m.
- D2,D3>=m^52.
- Exact leading promotion means are 2D3*p, 3D4*p, 3D4*p^2. They should
  be <=10D2/m^2, <=10D3/m^2, <=10D2/m^2, respectively.
- Positive caps <=8m^2 follow from P<=m.
- Shared thresholds m*d and common thresholds m^52 dominate both their
  means and m^46. The common rank-one mean from B is only O(m^48).

This reduces proving all local errors to a short list of cap inequalities;
the large powers of d are no longer inside each probability argument.
No scale-tail module implementing items 1--4 exists yet. No new admission
has been introduced in the completed modules.

## Coarse uniform scale-tail lemmas (now verified)

The four numbered scalar steps above are now implemented in
GreedyBatchScaleTails.lean. The file builds cleanly apart from two style
lints; all five audits are clean. Combined audit:

    /tmp/mixed-restart-scale-audit.log  (104 declarations)

Namespace Erdos773.GreedyBatchScaleTails defines

    u(m)=1/(20m^2), failure(m)=2exp(-m^7).

Completed APIs:
- u_nonneg and u_le_quarter (m>=1).
- overlap_error (m>=100,r<=4,M<=8m^2): r*M*(r*m^10+1)^r<=m^46.
- budget_scale: the exact rank-zero mean plus m^46 bounds the budget.
- near_mean_margin (m>=100,S>=m^52,mu<=10S/m^2):
  mu+m^46 <=(1-u(m))*(mu+S/m^4).
- loose_margin: mean and overlap each <=L/4 imply budget <=(1-u)L.
- scaled_moment combines these with the moment exponential and gives
  <=exp(-m^7), with no unproved probability input.
- old_scaled proves the uniform old-hit calculation under the exact
  coarse conditions in item 4 above. Its conclusion is the full
  hitError(n,s,M,m^10,p,1/m^2,100n/m^4)<=failure(m).

Thus the next task is to wrap these into the fourteen actual scalar errors
using a ScaleConditions structure for caps. No explicit d,t trajectory or
ceiling comparisons are part of these completed theorems.

Suggested graph-level coarse hypotheses (not yet assembled):
- m>=100, p in [0,1], C>0,D2*P>0,P<=m.
- D2,D3>=m^52.
- m^30*C<=D2; m^30*(D2*P)<=D3,D4,B.
- D2*p<=4/m^2.
- 2D3*p<=10D2/m^2; 3D4*p<=10D3/m^2;
  3D4*p^2<=10D2/m^2.
- shared leading means D3*P*p and 3D4*P*p^2 <=(m*d)/4,
  and m^46 <=(m*d)/4.
- each common mass(r)*p^r<=m^52/4 for r=1..4; its overlap
  m^46<=m^52/4 follows automatically from m>=100.

Use scaled margins:
 old(j)=100*degreeCap(j)/m^4;
 promo31=2pD3+D2/m^4, promo41=3pD4+D3/m^4,
 promo42=3p^2D4+D2/m^4;
 sharedOld=100B/m^4, shared34=shared44=m*d;
 common(r)=m^52.
All positive-overlap caps are <=8m^2 when P<=m. The scalar errors then
follow from old_scaled and scaled_moment. ProbabilityRange's nonnegative
shared retention can also follow from D2*p<=4/m^2 and m>=100.

Lean pitfalls encountered:
- `<m` also parses matroid notation, not just `<=m`/unicode <=; insert space.
- `ring_nf at ...` before linarith was essential when divisions with
  different numerical numerators were treated as unrelated atoms.
- `push_cast at hterm2` was needed to align m^10 casts with other powers.
- `field_simp` sometimes solves the equality completely; avoid an
  unconditional trailing ring in those cases.

## All fourteen scaled errors and the scaled density step (verified)

GreedyBatchScaledErrors.lean and GreedyBatchScaledStep.lean now compile
without warnings or admissions. Their eight audits are clean. Combined:

    /tmp/mixed-restart-scaled-stage-audit.log  (112 declarations)

GreedyBatchScaledErrors.Conditions c m p d is exactly the coarse graph-level
list above. It has named fields large,p_nonneg,p_le_one,common_pos,dp_pos,
pair,degree2,degree3,old2,old3,old4,oldShared,graph_load,promotion31,
promotion41,promotion42,shared34,shared44,shared_overlap,common.
The structure's m^30 and m^52 cap inequalities are NATURAL inequalities.
The leading-mean and graph-load bounds are REAL inequalities.

- margins c m p d is precisely the specified scaled Margins.
- vertex_errors and pair_errors bound all fourteen scalar expressions by
  failure(m)=2exp(-m^7), with q=m^10, eta=1/m^2.
- margins_positive proves every threshold positive from Conditions.
- probability_range proves ProbabilityRange, including nonnegative shared
  retention. Thus these are NOT extra numerical hypotheses in the new step.
- near_promotion, loose_shared and common_moment are public intermediate APIs.

GreedyBatchScaledStep.density_step requires only Conditions, Fits for these
margins, pair-cap monotonicity, future delta in [0,1], rho>0, the scalar rate
inequality with tests(V)*failure(m), copies(c')*V<=W, and a future
UniformDensity(post c') W delta. It concludes UniformDensity c V rho.
Every stochastic tail has been instantiated inside this theorem.

## Next deterministic profile-Fits strategy (reasoning only, not implemented)

A simpler route than sharp Taylor expansions suffices. Put

    kappa=1/m^4, h=1/(m^2*(1+t^2)), p=h/d,
    Delta=(t+h)^3-t^3, d'=d*exp(-a*Delta),
    F2=A*d*t^2, F3=B*d^2*t, F4=d^3, FB=m^50*d.

Use generic coefficient conditions

    3<=B<=A<=4, 0<=a<=1, 0<=eta<=1,
    (1-eta)*A >= 3*a + 1000/m^2.

The proposed A=3+6000/m^2, B=3+3000/m^2, a=1-1000/m^2,
eta=1/m^2 have MUCH more gap: about 8997/m^2 rather than 1000/m^2.
This spare factor makes coarse estimates sufficient.

### Polynomial/exponential lower bounds

For t>=1, 0<=h<=t, and h^2*t<=kappa, prove

    Delta <= 3*t^2*h+4*kappa,
    Delta*(t+h) <= 3*t^3*h+11*t*kappa,
    Delta*(t+h)^2 <= 3*t^4*h+25*t^2*kappa.

One convenient calculation uses
Delta<=3*t^2*h+4*t*h^2 and (t+h)^2<=t^2+3*t*h.
Their product is <=3*t^4*h+25*t^3*h^2 because h<=t.
Then multiply h^2*t<=kappa by t or t^2. All inputs are nonnegative.

Using ONLY exp(-x)>=1-x gives the profile lower bounds

    F2' >= F2+2*A*d*t*h-3*a*A*d*t^4*h-25*F2*kappa,
    F3' >= F3+B*d^2*h-6*a*B*d^2*t^3*h-22*F3*kappa,
    F4' >= F4-9*a*F4*t^2*h-12*F4*kappa,
    FB' >= FB-3*a*FB*t^2*h-4*FB*kappa.

No second-order exponential theorem is needed. Convert d'^2,d'^3 with
Real.exp_nat_mul (or exp_add), and use 0<=a<=1 on the error terms.

### Coarse old-count/ceiling upper bound

A generic scalar lemma can control old-retention expressions. Suppose
n<=F+1, n<=2F, F>=m^4, D2>=F2, k<=3, 0<=eta<=1, p>=0,
k*D2*p<=1, and p*deficit<=1/(2m^4). Then

 n*(1-(1-eta)*p*(k*D2-deficit))+100*n/m^4
     <= F*(1-(1-eta)*p*k*F2) + 202*F/m^4.

Proof: the no-deficit retention r=1-(1-eta)*p*k*D2 lies in [0,1].
Thus n*r<=(F+1)*r<=F*r+1. Replace D2 by F2 in the loss using F>=0.
The deficit costs <=F/m^4 since n<=2F; the 100n margin costs <=200F/m^4;
and 1<=F/m^4. For j=2,3,4 use k=j-1 and deficit k+choose(k,2)C;
for shared links use k=2, deficit=2+C. All deficits <=3(C+1).

The profile regime d>=m^1000,C<=m^60 ensures
p*3(C+1)<=1/(2m^4). The existing graph_load<=4/m^2 ensures kD2p<=1.
Natural ceilings satisfy F<=Dj<=F+1 and Dj<=2F. FB has the same property.

Each leading promotion rounding costs only O(p) or O(p^2), hence at most
Fj/m^4 once Fj>=3m^4 and p<=1. The added promotion margins cost <=2Fj/m^4.
Consequently all rank update thresholds are bounded by the ideal ODE
expression plus 250Fj/m^4 (208 suffices for rank2; 205 for rank3).
Shared update costs at most 250FB/m^4 too: 3md<=3FB/m^4 for m>=1.

### Comparing ideal updates to future profiles

The time step satisfies h*t^2>=1/(2m^2) when t>=1. Hence
((1-eta)A-3a)*h*t^2 >=500/m^4. This absorbs the rank2 constants 250+25
and its direct 4->2 term, since 3*d*h^2<=F2/m^4 (A>=3,t>=1,h^2<=m^-4).
The leading rank2 promotion coefficient 2B is <=2A, so no error is charged.
For rank3 the coefficient 3 of its leading promotion is <=B, and the
loss gap is twice as large. Rank4 has three times the gap. Shared-link
loss gap is 2(1-eta)A-3a >=2000/m^2 since a>=0; again ample room.

Finally future ceilings dominate F2',F3',F4',FB'. The common cap can be
exactly C'=C+4*m^52, since all four common thresholds are m^52. Post
regularization adds 3, agreeing with C_i=3+i*(4*m^52+3).

No file implementing these profile-Fits inequalities exists yet. Also
unproved: Conditions for the ceiling profiles, rate inequality, actual
schedule stopping time and volume bounds, endpoint application to squares.
The ORIGINAL smaller-epsilon conjecture still requires a new idea even
if every remaining endpoint step succeeds.

## First deterministic profile modules (verified)

Three more modules now compile and are built:

- GreedyBatchProfileLower: delta(t,h)=(t+h)^3-t^3, delta_error proves all
  three polynomial bounds listed above. rank_two,rank_three,rank_four,
  shared prove the four exponential lower bounds. ideal_two/three/four/
  shared prove the normalized ideal-update comparisons assuming

      500*kappa <= ((1-eta)*A-3a)*x,

  with x=h*t^2, y=h/t, z=(h/t)^2<=kappa. The ideal error allowance is
  250 profile*kappa in all four inequalities.

- GreedyBatchCeilingErrors: old_upper proves exactly the 202F*kappa
  old-survival/ceiling/deficit bound above, for REAL arguments n,F,D,F2,k,
  deficit,p,eta,kappa. promotion_upper proves

      w*D+E*kappa <= w*F+3*S*kappa

  from D<=F+1, E<=2S, w<=S*kappa, w,kappa>=0.

- GreedyBatchProfileStep defines a(m),A(m),B(m) and step(m,t) as above.
  coefficients proves 3<=B<=A<=4, 0<=a<=1, and the coefficient gap
  >=1000/m^2 for m>=100. step_bound gives h<=m^-2;
  step_squared gives h^2<=m^-4; step_squared_time gives h^2*t<=m^-4
  for t>=1; step_time_squared gives h*t^2>=1/(2m^2).
  step_gap combines them into the 500/m^4 loss-gap hypothesis.

Combined audit has 128 clean declarations:

    /tmp/mixed-restart-profile-audit.log

No pending Lean error in any completed current module. No profile family
with natural ceilings has been defined yet; that should be the next module.
The actual theorem and endpoint remain unproved.

## More detailed upcoming profile/Conditions plan (not yet implemented)

Define f2=A(m)*d*t^2, f3=B(m)*d^2*t, f4=d^3, fb=m^50*d,
nextD=d*exp(-a(m)*delta(t,step(m,t))). Define a Caps from the natural
ceilings of f2,f3,f4,fb, with P in [1,m] and graph common cap C. Target
caps use nextD,t+h and C+4*m^52; post adds the extra 3 as required.

Under m>=100, d>=m^1000, 1<=t<=m, C<=m^60, useful elementary bounds:

    3*d*t^2<=D2<=4*d*t^2,
    3*d^2*t<=D3<=4*d^2*t,
    d^3<=D4<=2*d^3,
    m^50*d<=Bcap<=2*m^50*d.

For D2's upper bound use A<=15/4 and rounding <=d*t^2/4. This sharper
A bound follows from m>=100. The main coefficients theorem only records
A<=4; extend it or prove the sharper bound separately.

Then Conditions follows by routine scalar comparisons:
- m^30*C<=m^90<=d<=D2.
- m^30*D2*P<=4*d*m^33<=d^2<=D3,D4.
- m^30*D2*P<=4*d*m^33<=m^50*d<=Bcap.
- D2,D3>=m^52.
- D2*p<=A*h*t^2+p <=(15/4)/m^2+1/(4m^2)=4/m^2.
- Leading promotions use D3<=4d^2t,D4<=2d^3, d*p=h, h<=m^-2,
  and t>=1. They are all below the 10S/m^2 bounds in Conditions.
- Shared34 <=4*m*d*t*h<=4*d/m<=(m*d)/4 because t*h<=m^-2.
- Shared44 <=6*m*d*h^2<=(m*d)/4.
- m^46<=(m*d)/4 from d>=m^1000.
- Common rank1 mean <=8/m+4m^48<=m^50.
- Common rank2 mean <=4m*(4/m^2+4/m^4), using D3*p^2<=4t*h^2<=4/m^4.
- Common rank3 mean <=3m*(4+4+2)=30m, using p<=1 and D4*p^3<=2h^3<=2.
- Rank4 mean <=rank3 mean since p<=1. All are <=m^50<=m^52/4.

For Fits, first use old_upper on the four old terms. All deficits are
<=3(C+1), and p*3(C+1)<=1/(2m^4). Profiles Fj>=3m^4 allow each source
rounding weight 2p,3p,3p^2<=Fj/m^4. promotion_upper yields three target
margins per promotion. Therefore the three degree thresholds are bounded
by ideal expressions +250Fj/m^4, and the shared threshold by its ideal
expression +250fb/m^4 (since 3md<=3fb/m^4).
Then apply the normalized ideal comparisons and exponential lower bounds.
Useful substitutions x=h*t^2,y=h/t,z=(h/t)^2; multiply ideal_two by d*t^2,
ideal_three by d^2*t, and the other two by d^3 or fb. field_simp (d,t>0)
can align the normalized quantities with the raw profile expressions.
Future ceilings dominate the future real profiles. Common Fits is exact.

## Upcoming rate/volume/iteration strategy (reasoning only)

Use lambda=1-10^6/m and density_i=lambda*(S-t_i)/d_i, where S is the
actual terminal time. Given s=S-t-h>=0, future density is
lambda*s*exp(a*Delta)/d. Since 1-p-load>=0, exp(a*Delta)>=1+a*Delta gives

 d*rate-lambda*(s+h)
   >= h*(1-lambda-load)
      +lambda*s*(a*Delta-(p+load)*(1+a*Delta)).

Target a coarse lower bound on the bracket:

    bracket >= -10000*h*t^2/m^2.

Indeed p+load<=20*h*t^2, a*Delta<=7*h*t^2, and their product is
<=140*h^2*t^4<=140*h*t^2/m^2. The leading loss coefficient
A-3a=9000/m^2, the higher-rank terms are <=O(h*t^2/m^2), and rounding
terms use d>=m^1000. For S^3<=m, s*t^2<=m, so the total continuation
loss is <=10000h/m. The slack 10^6/m in lambda comfortably pays this
and load<=O(m^-2), leaving, for example, rate>=currentDensity+p/m.
No exponential upper estimate is necessary for this lower reward.

For forward volumes, assume d0 and initial V are <=m^A for a fixed A.
One regularization has copies<=m^(9A+65), so use

    B=10A+100, V_i=m^(A+B*i).

Then copies*V_i<=V_(i+1). With i<=2m^3 and m sufficiently large depending
on A, V_i<=exp(m^5), using log m<=m. The total rate penalty is
<=28exp(2m^5-m^7), which is below p/m since p>=1/(2m^(A+4)). This can
be proved by explicit polynomial comparisons and exp monotonicity/log,
not necessarily a complicated uniform asymptotic theorem.

Let t0=1 and t_(i+1)=t_i+step(m,t_i). Stop at the first t_i>=T, where
T^3=(19999/60000)*log N and eventually T^3<=m/16. There are at most
2m^3 steps because, while t_i<T, step>=1/(m^2*(1+T^2)). Terminal
S<=T+m^-2<=T+1, hence S^3<=m eventually. Use S, not T, as the density
horizon so terminal density is exactly zero. All intermediate d_i are
at least d0*exp(-a*((T+1)^3-1)), still a fixed positive power of N.

Initial sample's small cardinality loss must be chosen SMALL ENOUGH.
UntrimmedSquareLowerResearchNotes confirms arbitrary fixed 0<delta<1:
|A|>=(1-delta)N/log N and maximum degree<(1999/6000)N/log^2 N.
Do NOT reuse delta=1/1000 for the endpoint coefficient comparison; its
loss exceeds the tiny coefficient gain. Choose e.g. delta=1/100000.
The ratio (19999/60000)/(1999/6000) is about 1.00045, with cube-root
gain about 0.00015, so this smaller loss leaves a positive margin.

All of this still addresses only the coefficient-one exponent-2/3 endpoint.
No new exponent and no original-conjecture settlement has been obtained.

## Actual ceiling profiles now satisfy every tail condition (verified)

GreedyBatchProfiles.lean and GreedyBatchProfileConditions.lean are built and
clean, with 13 further audited declarations. Combined audit:

    /tmp/mixed-restart-conditions-audit.log  (141 declarations)

GreedyBatchProfiles defines f2,f3,f4,fb, probability=step/d, nextD, and
caps(m,d,t,C,P) via the four natural ceilings. Its Range m d t C P records:

    m>=100, d>=m^1000, 1<=t<=m, 1<=C<=m^60, 1<=P<=m.

The lower bound 1<=C was ADDED as common_one to match the positive graph
incidence cap used by the certificate. Planned C_i>=3 satisfies it.
Range exposes m_pos,m_one,power_le_d(k<=1000),m_le_d,d_large(>=100),d_pos.
upper_coefficient proves A,B<=15/4. cap_bounds proves all eight coarse
ceiling bounds listed previously. probability_pos, probability_mul and
probability_le_one are verified.

GreedyBatchProfileConditions adds:
- power_slack: c*m^i<=m^j for i<j,c<=100,m>=100.
- step_weighted: h*t^2<=m^-2, h*t<=m^-2, h<=1.
- WeightedBounds and weighted_bounds: D2*p<=4h*t^2;
  D3*p<=4dth, D3*p^2<=4t*h^2; D4*p<=2d^2h,
  D4*p^2<=2d*h^2, D4*p^3<=2h^3; Bcap*p<=2m^50h.
- incidence_ratios proves all six NATURAL m^52/m^30 cap requirements.
- graph_load, promotion_means, shared_means, common_means prove all the
  remaining REAL scale inequalities. Common means are all <=m^50,
  then <=m^52/4. The proof does not use unproved distribution hypotheses.
- conditions is the complete theorem:

    Range m d t C P ->
    GreedyBatchScaledErrors.Conditions
      (caps m d t C P) m (probability m d t) d.

Thus tail validation for the actual ceiling profiles is FINISHED. Do not
redo it. Remaining deterministic work is Fits, rate, volume/time schedule,
and endpoint transport. The conjecture itself is still not settled.

### Upcoming Fits implementation details (not yet implemented)

Define future caps as caps(m,nextD(m,d,t),t+step(m,t),C+4*m^52,P).
Two pieces can be separated:

1. Future ideal bounds: prove

 f2*(1-(1-eta)*p*f2)+2*p*f3+3*p^2*f4+250*f2/m^4 <= future f2,
 f3*(1-2*(1-eta)*p*f2)+3*p*f4+250*f3/m^4 <= future f3,
 f4*(1-3*(1-eta)*p*f2)+250*f4/m^4 <= future f4,
 fb*(1-2*(1-eta)*p*f2)+250*fb/m^4 <= future fb.

Use ProfileLower ideal_two with x=h*t^2,y=h/t,z=(h/t)^2,kappa=m^-4,
then multiply by d*t^2. y>=0 and z<=kappa follow from h/t<=h (t>=1)
and step_squared. step_gap supplies the coefficient-gap hypothesis.
Multiply ProfileLower.rank_two by A*d. field_simp with d,t>0 aligns
both comparisons to the raw f2 expression. For f3 multiply ideal_three
by d^2*t and rank_three by B*d^2; use exp(-aDelta)^2=exp(-2aDelta).
For f4 use exponent 3 and multiplier d^3. For shared use multiplier fb.

2. Current rounding bounds: all real profiles F satisfy F>=3m^4.
This follows from 3m^4<=m^5<=d and F>=d. Derive the generic deficit bound

    probability*3(C+1)<=1/(2m^4).

It suffices first to show 6(C+1)m^2<=d: C+1<=2m^60 gives
6(C+1)m^2<=12m^62<=m^63<=d. Multiply this inequality by p>=0,
use d*p=h and h*m^2<=1, then multiply by m^2 to get the claimed bound.

Apply CeilingErrors.old_upper for k=1,2,3 and deficits 1,2+C,3+3C,
and k=2,deficit=2+C for shared. Its load condition follows from
k*D2*p<=12/m^2<=1. Natural ceilings satisfy n<=F+1<=2F;
F>=3m^4 gives 1<=F/m^4. Each promotion weight 2p,3p,3p^2<=3<=F/m^4,
so promotion_upper applies to the matching source/target ceilings.
The resulting total constants are <=250, as previously described.
Future ceilings dominate real future profiles. The common target cap
C+4m^52 gives exact Fits.common since there are four identical thresholds.

No future-ideal or full Fits module exists yet. All current files compile.

## Full actual-profile Fits is now proved

GreedyBatchFutureProfiles.lean proves the four real ideal future bounds
(two,three,four,shared) exactly as stated in the preceding plan. It compiles
with style/unreachable-tactic lints only; all four audits are clean.

GreedyBatchProfileFits.lean is also built. Its APIs:
- profile_large: all four real profiles >=3m^4.
- deficit_bound: p*3(C+1)<=1/(2m^4).
- ceil_small: F>=3m^4 gives ceilF<=F+1<=2F and 3<=F/m^4.
- old_bound: generic k<=3, deficit<=3(C+1) old ceiling estimate.
- promotion_bound: source/target ceil estimate with witness weight in [0,3].
- shared_margin: md<=fb/m^4.
- fits: for every Range m d t C P, the actual current caps and scaled
  margins satisfy Fits for the target caps

    caps(m,nextD(m,d,t),t+step(m,t),C+4m^52,P).

No hypothesis says nextD>=m^1000 in this Fits theorem. That lower bound
must be supplied globally when iterating so the NEXT stage has Range.
The graph-common +3 is still applied by post during regularization.

The combined audit now has 150 clean declarations:

    /tmp/mixed-restart-fits-audit.log

No pending Lean error in any current completed file. Original Spec.lean
is unchanged. No original-conjecture settlement or endpoint theorem yet.

## Concrete next rate proof plan (not implemented)

Use lambda(m)=1-10^6/m, density(m,S,d,t)=lambda*(S-t)/d. Assume m>=2*10^6,
Range at the current stage, S>=t+h, S^3<=m. Let z=load(currentCaps,p),
x=h*t^2, u=a*Delta, and s=S-t-h>=0.

Useful scalar geometry to prove first:

1. From ceil upper bounds (NOT the coarser degree factors),

    z <= A*x + B*t*h^2+h^3+p+p^2+p^3.

   Each ceiling adds p^j, and d*p=h handles the exact leading terms.
2. WeightedBounds gives z<=10*x and p+z<=20*x, because p<=h,
   h<=t, and t>=1. step_weighted gives x<=1/m^2, hence p+z<=1.
   In particular z<=10/m^2 and the continuation multiplier is nonnegative.
3. 0<=u<=7*x, and u>=3*a*x. Use Delta>=3t^2h, Delta<=3t^2h+4th^2,
   h<=t and 0<=a<=1.
4. Consequently u*(p+z)<=140*x^2<=140*x/m^2.
5. B*t*h^2<=4*x/m^2, using B<=4 and h*t<=m^-2.
   h^3<=x/m^2. Also p<=x/m^2 because d>=m^2, d*p=h, and t^2>=1.
   Since p in [0,1], 2p+p^2+p^3<=4p.
6. Exact coefficient identity A-3a=9000/m^2 then gives

    bracket = u-(p+z)*(1+u) >= -10000*x/m^2.

   The actual sum of constants is only 9000+4+1+4+140=9149.
   Use ring_nf before linear arithmetic to align the divided terms.

For the reward, future density satisfies exactly

    delta_future = lambda*s*exp(u)/d.

Use exp(u)>=1+u, lambda*s/d>=0, and 1-p-z>=0. After multiplying by d,

 d*rate-lambda*(s+h)
   >= h*(1-lambda-z)+lambda*s*bracket.

As lambda in [0,1] and s*t^2<=S^3<=m, the last term is >=-10000h/m.
The first term is >=10^6*h/m-10h/m^2. Therefore rate >=currentDensity+p/m
with enormous spare slack. This is the rate theorem to prove next.

A future failure penalty <=p/m then gives the numerical density-step rate
hypothesis. The previous volume plan V_i=m^(A+(10A+100)*i), i<=2m^3,
should supply this uniformly. No rate or volume module has been written yet.

## Rate, volume, and total failure penalty are now proved

Four further modules are built and axiom-clean. Combined audit:

    /tmp/mixed-restart-rate-volume-audit.log  (174 declarations)

1. GreedyBatchRateGeometry
   precise_load retains the exact leading A coefficient; coarse_load gives
   z<=10ht^2, p+z<=20ht^2, z<=10/m^2 and p+z<=1. growth(m,t)=a*Delta.
   growth_bounds gives 0<=growth<=7ht^2 and growth>=3aht^2.
   growth_load and small_terms prove the previously listed error bounds.
   bracket_lower proves the full >=-10000ht^2/m^2 inequality.

2. GreedyBatchDensityProfile
   efficiency(m)=1-1000000/m; density(m,S,d,t)=efficiency*(S-t)/d.
   efficiency_bounds gives 1/2<=efficiency<=1 for m>=2000000.
   next_density is the exact exp(growth) formula, and future_lower uses
   exp>=1+growth. rate_margin is now proved:

     density(m,S,d,t)+probability(m,d,t)/m
       <=rate(currentCaps,p,density(m,S,nextD,t+h))

   under Range, m>=2000000, S>=t+h, S^3<=m.
   density_bounds gives density in [0,1] when t<=S,S^3<=m;
   density_pos gives positivity when t<S; nextD_pos and nextD_le are proved.

3. GreedyBatchVolume
   IMPORTANT: increment was enlarged from the proposed 10A+100 to

       increment(A)=30A+100,
       volume(m,A,i)=m^(A+increment(A)*i).

   This permits much simpler, deliberately coarse degree bounds. Under
   Range and d<=m^A, degree_power bounds ALL three degrees by m^(3A+7).
   The regularization cap is <=m^(9A+26), so copies_bound proves
   copies(caps)<=m^(increment A). volume_step gives the forward recurrence.
   For i<=2m^3 and 3*increment(A)<=m, volume_exponent<=m^4 and
   volume_exp gives volume<=exp(m^5), using log m<=m.

4. GreedyBatchFailurePenalty
   probability_lower gives p/m>=1/(2m^(A+5)) under Range,d<=m^A.
   tests_exp and penalty_exp bound total failure by 28exp(2m^5-m^7).
   logarithmic_budget and exponential_small prove this is
   <=1/(2m^(A+5)) whenever m>=A+100. No asymptotic black box is used.
   penalty and volume_penalty conclude tests(V_i)*failure(m)<=p/m
   for all i<=2m^3 with 3*increment(A)<=m.

Thus Conditions, Fits, the real density rate margin, forward regularization
volume growth, and the full summed failure penalty are ALL verified.
Remaining work for this approach is to assemble an actual finite time
trajectory and prove its range/terminal conditions, apply the schedule
iteration, and instantiate the result to the square sampler and endpoint.
The original conjecture still has its unchanged sole admission.

### Upcoming trajectory assembly (not yet implemented)

Define

 time_0=1, time_(i+1)=time_i+step(m,time_i),
 scale_i=d0*exp(-a(m)*(time_i^3-1)),
 common_i=3+i*(4*m^52+3).

Prove time strict monotonicity, scale_succ=nextD(scale_i,time_i), scale
antitonicity for d0>0, and common_i<=m^60 for i<=2m^3,m>=100.
For the last bound, common_i<=3+8m^55+6m^3<=17m^55<=m^60.

For a FIXED length L, the finite generic theorem should assume

 m>=2000000, 3*increment(A)<=m, 1<=P<=m,
 L<=2m^3, time_L^3<=m,
 0<d0<=m^A, m^1000<=scale_L.

Then Range holds at every i<=L: times in [1,time_L]<=m, scales between
scale_L and d0, common caps in [3,m^60]. Use density horizon S=time_L.
Every i<L has positive density, and terminal density is exactly zero.
All ingredients of GreedyBatchSchedule.Valid now come from proved APIs.
The target caps have common_i+4m^52; post adds 3 to match common_(i+1).
Copies depend only on degrees, so copies_bound can use the next-stage
Range with common_(i+1), even though the pre-post target common cap is 3 less.
This yields UniformDensity at initial caps(m,d0,1,3,P), volume=m^A,
density=efficiency(m)*(time_L-1)/d0.

To choose L from a desired T>1, show time_(2m^3)>=T whenever T^3<=m.
If it were below T, all earlier times are below T, so every increment is
>=1/(m^2*(1+T^2)). Hence time_(2m^3)>=1+2m/(1+T^2)>=1+T, a contradiction
(the last comparison uses T>=1 and T^3<=m). Choose the least L with time_L>=T.
Then L<=2m^3 and time_L<=T+1/m^2<=T+1. If T^3<=m/16, terminal time cubed
is <=m, since time_L<=2T. The terminal scale lower bound can be supplied
by d0*exp(-a*((T+1)^3-1)); this still leaves a fixed N power in the endpoint
arithmetic because the horizon cube constant is strictly below 1/3.

Initial mixed regularization still needs explicit volume bookkeeping.
The sampler is four-uniform with no initial common/shared constraints;
artificial rank2/rank3 targets at t=1 are legitimate, and post gives C=3.
One may use a much larger fixed volume exponent A to cover this first
regularization. The later generic trajectory accepts any fixed A once m
is sufficiently large. Do not reintroduce an extra density loss at transfer.

Technical additions: `lambda`/unicode lambda is reserved in Lean identifiers;
the rate proof uses `ell`. `<=increment` (unicode) parses InitialSeg notation
`<=i`, just as `<=m` parsed matroid notation: always insert whitespace after
inequality symbols. Root mul_le_mul_right is a monotonicity lemma, not the
old iff; use le_of_mul_le_mul_right ... hd for cancellation.

### Completed checkpoint: trajectory and finite physical-horizon iteration

The formerly proposed trajectory assembly is now proved in
GreedyBatchTrajectory.lean, including stopping_small and terminal_scale.
GreedyBatchProfileIteration.lean proves valid, uniform_fixed, and
uniform_horizon. The last theorem yields uniform independent-set density

    (1-1000000/m)*(T-1)/d

for regular profiles caps(m,d,1,3,P) on at most m^A vertices, assuming
m>=2000000, 3*(30*A+100)<=m, 0<d<=m^A, 1<=P<=m,
T>=1, T^3<=m/16, and m^1000<=d*exp(-a(m)*((T+1)^3-1)).
No conditional local concentration, Fits, rate, volume, or failure-budget
hypothesis remains. Initial regularization and arithmetic application to
squares have NOT been completed. In particular the coefficient-one endpoint
and the original conjecture remain unproved. The actual completed lower
bound remains eventually M(N)>=N^(2/3)/36.

These modules have been added to MixedRestartAudit.lean. The conjecture in
Spec.lean is unchanged and still contains its sole admission.

### Completed arithmetic application: coefficient-one two-thirds endpoint

GreedyBatchInitialExtraction proves initial four-uniform regularization
and exact density transfer, including ambient finite carriers. The initial
model fits within m^(A+increment A); there is no density penalty.
GreedyBatchSquareCertificate proves the finite square-specific certificate.
GreedyBatchSquareScales supplies all explicit parameter comparisons.
GreedyBatchSquareEndpoint.eventual_endpoint now proves

    eventually M(N) >= N^(2/3).

The parameters are m=ceil(N^(1/10^9)), A=10^9,
d=(kappa*N/log(N)^2)^(1/3), T=(c*log(N))^(1/3), P=m,
kappa=1999/6000, c=19999/60000. Sampling uses delta=1/100000.
The scale proof keeps the terminal margin explicitly: with
smallDelta=1/240000, d>=N^(1/3-smallDelta),
(T+1)^3-1<=(c+smallDelta)*log(N), and a(m)<=1. Thus the terminal
scale is >=N^(1/120000), while m^1000<=N^(1/500000).
The three coefficient losses each cost at most 1/100000; the exact
rational inequality loss^9*c/kappa>=1 supplies the endpoint.

All four modules compile and their main axiom audits are permitted.
They have been added to MixedRestartAudit.lean. The endpoint dependency
closure consists of 178 clean modules and 28523 lines, with only the
FormalConjecturesUtil import outside that closure. It does not import Spec.
The endpoint is not yet consolidated into Spec.lean. The original theorem
is STILL UNSETTLED for every 0<epsilon<1/3, and Spec remains unchanged
with its original single admission. No proof submission has been made.

### Main file updated: endpoint consolidated, original statement unchanged

IMPORTANT: older notes saying Spec.lean is unchanged or has its admission
at line 2031 are now superseded. The checked endpoint dependency closure
has been consolidated into Spec.lean, preserving the exact original
conjecture statement and the sole import FormalConjecturesUtil.

Spec.lean now proves the branch epsilon>=1/3 and retains ONE admission
for 0<epsilon<1/3, at line 17287. This is STILL NOT a settlement.
No incomplete proof has been submitted.

Current Spec SHA-256:
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940

The pre-consolidation file is saved in Submission/SpecBeforeEndpoint.txt.
The clean existing upper bounds remain in their auxiliary modules; they
were not copied into the new consolidated main file. The main file now
contains the actual lower endpoint M(N)>=N^(2/3) eventually. Its audit
uses only propext, Classical.choice, Quot.sound. The original conjecture
itself still uses sorryAx because of its explicitly unresolved branch.

Dependency refactoring removed the earlier greedy trajectories that were
being imported only for carrier-transport helpers.
FiniteHypergraphRestriction now supplies down_injOn, restrict_card,
degree_all_eq, and restrict_induced. UniformAmbientSampling uses these
helpers directly. GreedyBatchInitialExtraction.selection uses the same
lightweight restriction API. GreedyBatchSquareCertificate imports only
PrioritySquareSidonLower and SquareCollisionIntersections, rather than
the older untrimmed certificate. All modified modules compile.

The endpoint closure is now 107 modules / 17367 source lines; the single
file has 17291 lines. Each imported module is wrapped in its own section
to preserve file-local options. Seven source files had an open top-level
noncomputable section; these are explicitly closed in the consolidation.
The main file's exact conjecture type and one-import list were compared
programmatically with the original.

Fresh logs:
/tmp/spec-endpoint-consolidated.log
/tmp/endpoint-consolidated-3.log
/tmp/mixed-restart-endpoint-refactor-audit.log (194 permitted-axiom checks)
/tmp/carrier-transport-refactor.log
/tmp/uniform-ambient-refactor.log
/tmp/greedy-batch-initial-transport.log
/tmp/greedy-batch-square-cert-transport.log
/tmp/batch-square-endpoint-refactor.log

Further arithmetic review of logarithmic prime encodings, higher-dimensional
modular lifts, and multiplicative selectors yielded no valid exponent
improvement or original-conjecture disproof. No such claim is made.

### Further bounded-denominator rotation review

SmallRotationLifting.lean now proves the valid no-carry lifting statement
and equal-norm orthogonality argument. In particular, a positive-inner-product
common-norm digit class excludes nontrivial rational rotations with denominator
q<=Q if 3*Q*H<B. All five main audits are clean; the module has a built olean.
See SmallRotationLiftingResearchNotes.md for exact scope.

No control of the complementary large-denominator collisions was obtained,
and no actual Sidon exponent improved. Spec.lean remains unchanged at
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940,
with the admission at line 17287 for 0<epsilon<1/3. Its recheck completed
without errors. No proof or disproof of the full conjecture is available,
and no incomplete result was submitted.

### Partial-fiber and near-critical-capacity re-review

Rechecked PartialResidueFibers, WeightedPartialFibers, MatchingCoherenceBound,
ArbitraryModulusFullFibers, and the near-critical capacity obstruction notes.
No source proof or main conjecture statement was changed in this continuation.

The full-fiber bound already covers arbitrary positive moduli, shifted starts,
and unequal full lengths, with a divisor-factor loss and exponent 2/3+o(1).
It does not cover arbitrary sparse partial fibers. The exact partial-fiber
compatibility condition still requires disjoint ACTUAL positive-difference
sets; modular matching alone does not supply this. No compatible near-linear
partial family was found.

The generic bounded-capacity counterexamples already occur inside [1,N^2]
with carrier size N^(1-epsilon), fixed capacity depending on epsilon, and
Sidon maximum at most N^(4/5). Thus near-square-root ambient density does not
repair the generic conversion shortcut. These sets are not asserted to be
square sets and do not disprove Erdos 773.

Revisiting Gaussian-factor matching, digit specialization, and prime/logarithm
encodings did not yield a proved exponent improvement. There is no new
near-linear selector or fixed-power upper bound for the actual square maximum.
Spec.lean retains its sole admission for 0<epsilon<1/3. No proof was submitted.

### Growing-statistic construction review (no new theorem)

Rechecked GrowingMomentObstacle, PrimitiveGrowingMoments, PrimeMomentCollisions,
MomentCongruence, and PrimePowerEnergyCarryObstacle. The established collision
families rule out the corresponding blanket sufficient criteria. They do NOT
show that every statistic class is bad or exclude a specially chosen large
class. No such successful special class was constructed in this continuation.

Also reconsidered collision factorization after congruence restrictions, the
adjacent-index/cube reductions, and positive/ordered digit restrictions. No
unrestricted lifting theorem or collision-count saving was proved. In particular,
no assertion of a new obstruction for all ordered-digit families is being made.

The available modular scalar inequalities are already known to remain compatible
with near-linear cardinality at every modulus. The extracted root cubes are
sparse and do not meet the full-fiber hypotheses. Neither observation settles
the conjecture in either direction.

No Lean source was changed. Spec.lean still has the same one import, the exact
original statement, and the admission at line 17287 for 0<epsilon<1/3. The
proved endpoint is N^(2/3). No complete proof or disproof is available, and no
incomplete result was submitted.

### Seed amplification and alternative modular targets (review only)

Re-examined seed concatenation with roots q*x+a and the exact quadratic
collision expansion. No subpower-loss amplification theorem was obtained.
Seed Sidonness over the integers does not provide pair matching modulo a
small q, and even genuine modular pair matching leaves cross-fiber positive
square-difference compatibility. The earlier base-81 seed obstruction and
full-fiber bounds retain their stated, construction-specific scope.

Considered quadratic high-square-digit targets A*b^2+B*b+C and the swapped
parabola target with low coordinate b^2 and high coordinate b^4. This was
mathematical exploration only: no new height estimate, favorable low-root
count, or asymptotic Sidon construction was proved. In particular these
variants must not be cited as an exponent improvement or a disproof.

No Lean source changed in this continuation. Spec.lean remains at the same
hash and has its sole sorry at line 17287, for 0<epsilon<1/3. No complete
proof or disproof of Erdos 773 has been obtained; no incomplete result was
submitted.

### Reversible-insertion counting lemma completed

ReversibleInsertionCapacity.lean proves the local LYM level ratio and its
consequence for unique-parent insertion on unordered states. For a nonempty
k-th level of a downward-closed family on N vertices, a uniform lower bound
D on assigned child counts satisfies D*(k+1)<=N-k. All three main axiom audits
are clean, and the module has a built olean. See ReversibleInsertionResearchNotes.md
for the precise assumptions and limitations.

This does not exclude all entropy-compression algorithms and does not improve
the square-Sidon exponent. No repair of the reconstruction/choice-count gap
was found. Spec.lean is unchanged and recompiled without errors; the remaining
admission is still for 0<epsilon<1/3 at line 17287. No incomplete result was
submitted as a proof or disproof of the conjecture.

### Modular modelling and amplification review (no new theorem)

Examined reducing an integer square-Sidon seed modulo a modulus near the
square of its cardinality. The seed's integer Sidon property alone does not
exclude new modular pair-sum aliases. No subpower-loss modular reduction
estimate was proved, and cross-fiber positive-difference compatibility would
still be needed after such a reduction.

Reconsidered denominator-labelled rational squares, inert-prime valuation
codes, and unions of short root intervals. No near-linear integer construction
with correct denominator/root-height accounting was obtained. These reviews
are not new impossibility theorems for all such constructions.

No Lean source changed in this continuation. Spec.lean retains the exact
original conjecture, its sole FormalConjecturesUtil import, and its one
admission at line 17287 for 0<epsilon<1/3. The established endpoint remains
eventual M(N)>=N^(2/3). No complete proof or disproof was obtained or submitted.

### Low-collision carrier review (no new result)

Rechecked the proved LowCollisionSelection.power_count_bound and the exact
lowCollision_iff_near_linear equivalence. To use this route, an actual integer
root carrier of near-linear size and only N^(1+o(1)) four-root supports is still
needed. No such carrier was proved in this continuation.

Reviewed residue-class and fixed-degree digit-box candidates, including the
possibility of using formal Gaussian irreducibility to count, rather than
entirely exclude, carry collisions. No rigorous power saving beyond the
available thinning/affine counts was found. Informal distribution heuristics
were not promoted to either an upper bound or a lower bound. In particular,
no theorem excluding all digit-box refinements is asserted.

Also reconsidered additive-doubling and popular-root-gap information. No
supersaturation theorem for arbitrary square-Sidon candidates was obtained,
so this supplies no fixed-power upper bound disproving Erdos 773.

No Lean source changed. Spec.lean is unchanged, with the exact original
statement, one import, and one sorry at line 17287 for 0<epsilon<1/3. The
proved endpoint remains eventually N^(2/3). No proof or disproof was submitted.

### Joint-capacity checkpoint documented

JointCapacityResearchNotes.md now documents IntegerSumCapacity and
JointCapacityObstruction, including their clean axiom checks. The joint
sum/difference capacity-two examples are ordinary integer carriers of size
about n^16 at height n^40, with maximum Sidon cardinality below n^15. They
are NOT square-set counterexamples. The previously proved near-critical
ambient-density examples have not been extended to the new sum bound.

### Prime-residue rotation restriction completed

PrimeResidueRotation.lean proves that roots all congruent to 1 modulo an
odd prime l cannot satisfy a nondegenerate parameterized rational rotation
with denominator q=u^2+v^2<l^2/2. Both numerator signs are allowed. The
explicit carrier has K roots below l*K. All five principal audits are clean;
see PrimeResidueRotationResearchNotes.md for the exact hypotheses.

This does not assert Sidonness of the carrier and supplies no control of the
remaining large-denominator collisions. No actual exponent improvement or
fixed-power upper bound was obtained. Spec.lean remains unchanged at hash
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940,
with the remaining admission at line 17287 for 0<epsilon<1/3. The proved
endpoint is eventually M(N)>=N^(2/3). No proof or disproof was submitted.

### Quadratic-height limit of the prime-residue carrier

Extended PrimeResidueRotation.lean with an explicit four-distinct-root
collision in the residue class 1 modulo every l>=1, at height
10*l^2+7*l+1. The whole carrier roots(l,K) is therefore non-Sidon for
K>=10*l+8. Both new theorem audits are clean; see the updated research note.
This does not bound the best Sidon SUBSET and does not negate Erdos 773.

Reviewed the generic capacity/extraction route, partial-fiber amplification,
and leading energy-checksum ideas. No new conversion, carry-lifting theorem,
or improved actual exponent was obtained. Separating coarse blocks alone
still leaves within-block and cross-fiber collisions to prove absent. These
reviews are not asserted as impossibility theorems for all such methods.
The external problem reference remains inaccessible because DNS lookup fails.

Spec.lean is unchanged, with its exact original statement and one sorry at
line 17287 for 0<epsilon<1/3. The established bound is eventually
M(N)>=N^(2/3). No incomplete proof or disproof was submitted.

## Composite-modulus two-row rotation extension

New clean module: CompositeResidueRotation.lean. It imports only
FormalConjecturesUtil and has four clean permitted-axiom audits.
For a primitive Pythagorean rotation with both rows carrying four integers
congruent to one modulo a nonzero odd modulus l, it proves l divides the
off-diagonal leg, l^2 divides q-p, and l^2<2*q. If all four coordinates are
positive it improves the last inequality to l^2<q. Primality and
squarefreeness are not assumed. The rotation equations and primitivity are
explicit hypotheses; the new module asserts no universal transfer or
upper bound on q.

This remains a denominator cutoff, not a control of the remaining collisions
or a near-linear Sidon selector. The main conjecture is still unresolved.
Detailed scope: CompositeResidueRotationResearchNotes.md.
Build/audit log: /tmp/composite-residue-rotation.log.
Fresh main check: /tmp/spec-composite-residue-check.log (no errors, expected
admission warning). Spec.lean is unchanged at SHA-256
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940,
with its sole sorry at line 17287. No incomplete proof was submitted.


## Positive primitive square-gap family

CompositeResidueRotation.positive_primitive_square_gap is now proved and
built. For every odd m=2t+1>1 it supplies four positive, distinct roots
congruent to one modulo m, at height 5*m^2+5*m+1, with a primitive rotation
whose diagonal gap is exactly q-p=m^2. In particular m^3 does not divide it.
This blocks unconditional iteration of the preceding square-divisibility
lemma. It does not bound the maximum Sidon subset or disprove Erdős 773.

The module now has five clean principal axiom audits and no warnings or
admissions. Detailed formulas and the polynomial Bezout certificate are
in CompositeResidueRotationResearchNotes.md. The build log remains
/tmp/composite-residue-rotation.log. Spec.lean was not changed and still
has its sole sorry for 0<epsilon<1/3. No incomplete proof was submitted.

## Large-sieve and correlated-difference review

This continuation made no Lean source changes and proved no new main-gap
bound. The standard additive large-sieve calculation for square-residue
supports was reviewed: the lower Fourier mass at each prime must be compared
with a large-sieve bound that retains the diagonal contribution proportional
to cardinality. The calculation did not yield a fixed positive exponent
loss. A divisor-weighted/larger-sieve review likewise supplied no such bound.
This is not a theorem ruling out all stronger, correlation-sensitive sieves.

The already proved simultaneous scalar modular inequalities remain compatible
with near-linear hypothetical cardinalities. The short translated-intersection
and universal-affine reductions were rechecked; their hypotheses still do not
match, and no transfer giving an unrestricted upper exponent was found.

Sparse-fiber compatibility, common defect restrictions, and the generic
bounded-capacity examples were also reviewed without a new selector. The
near-critical generic obstruction has its proved difference-capacity bound;
no new joint sum-capacity extension was made in this continuation.

Spec.lean is unchanged, with its sole sorry at line 17287 and the original
statement/import intact. No incomplete proof was submitted.

## Varying-base and reciprocal-specialization review

No new Lean theorem or actual asymptotic bound was obtained. Spec.lean was
not edited. The formal Gaussian-Eisenstein construction and the existing
rational-base and prime-denominator counterexamples were rechecked.
Individual evaluation injectivity still does not imply pair-sum injectivity.

Varying the base, reversing/transforming the polynomial, and imposing common
coefficient sums were considered, but no transfer preserving Sidonness at a
near-linear height/cardinality ratio was proved. The older rational examples
do not themselves refute every additional common-statistic condition; no new
such counterexample or positive theorem is claimed here. Straight carry-free
coefficient bounds still incur an unacceptable height cost for this task.

A reference lookup was retried via a direct HTTPS DNS endpoint and timed out;
no new external mathematical reference was retrieved. No complete proof was
submitted. Spec.lean remains at SHA-256
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940,
with its sole sorry at line 17287 for 0<epsilon<1/3.

## Small canonical representatives of the parabola lift

Two new clean modules were proved and built:
ParabolaSmallRepresentatives.lean and ParabolaMirrorRepresentatives.lean.
Their eight principal axiom audits use only the permitted axioms, and the
modules have no warnings or admissions.

For the existing exact carry-aware parabola lift r_p(b), the level with
high digit a has at most 2a-1 labels; high digits through H therefore have
at most H^2 labels. Every subfamily of these roots below height N satisfies
cardinality^3 <= N^2, without a Sidon or half-band assumption.

The exact complementary-root identity is also proved:
(p^2-r_p(b))+p=r_p(p-b). It yields a cardinality bound of
(floor(N/p)+1)^2 for the complementary roots. Arbitrary independent sign
choices at each label satisfy cardinality^3 <= 5*N^2. Thus choosing small
representatives, even with label-dependent signs, cannot make this specific
parabola lift a near-linear root-height construction.

These are NOT ceilings for arbitrary modular constructions or for the
original maximum. No main-gap exponent was improved and no disproof was
obtained. Detailed scope and formulas are in
ParabolaSmallRepresentativesResearchNotes.md. Logs:
/tmp/parabola-small-representatives.log,
/tmp/parabola-mirror-representatives.log.

A fresh main compile completed without errors in
/tmp/spec-parabola-small-representatives-check.log, with the expected admission
warning. Spec.lean is unchanged at SHA-256
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940,
with its sole sorry at line 17287. No incomplete proof was submitted.

## Completed affine-target height ceiling (continuation checkpoint)

Three clean modules `QuadraticBandPacking`, `AffineParabolaLevelBound`, and
`AffineParabolaHeightBound` now prove a uniform construction-specific ceiling
|B|³≤6400 N² for unit-affine carry targets at any positive modulus. The final
module's reserved-binder and beta-reduction errors have been fixed; all three
principal audits are clean. Details and precise scope are in
`AffineParabolaHeightResearchNotes.md`. This excludes an extension of the earlier
fixed-target construction, not arbitrary sparse-fiber or square Sidon sets.
The original Spec.lean conjecture still has exactly its small-ε admission.

### Independent signs for arbitrary unit-affine targets

`AffineParabolaHeightBound.signed_affine_height_card_ceiling` is now checked:
allowing f(b)%p to equal either b or p-b independently at each label gives
|B|³≤51200 N². The sign classes are treated with slopes lam and -lam. All
four principal height module audits use only the permitted axioms. The
module compiles without warnings or admissions; the existing log was updated.

The sparse-fiber amplification route was reviewed again, without a new
cross-difference compatibility estimate or actual exponent improvement.
No near-linear carrier or unrestricted fixed-power upper bound was proved.
A fresh main check in /tmp/spec-affine-height-check.log has no errors, and
still reports the expected admission. Spec.lean retains exactly one sorry at
line 17287, its unchanged conjecture and import, and SHA-256
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940.
The completed endpoint remains M(N)≥N^(2/3) eventually. No settlement was
obtained or submitted in this continuation.

### Gaussian factorization and positive-selection review

Rechecked the clean small_primitive_factor theorem against the integral
bounded-difference and fractional-capacity results. No square-specific
subpower-loss rounding theorem or near-linear selector was obtained.
The small-factor normalization does not itself control the remaining
factor choices, and the existing generic capacity obstructions cannot
be treated as square-set counterexamples.

Revisited specialization of the formal rotation model and sparse residue
fibers. Neither supplied a quantitative relation-preserving specialization
at near-linear root height or the needed actual cross-difference control.
These are unresolved estimates, not new impossibility theorems.

The affine-target ceiling also must not be silently extended to targets
with an additional quadratic term in the label: the checked height theorem
has precisely the affine target stated in its hypotheses. No new theorem
about those more general targets is claimed here.

No Lean source was modified in this review. The original conjecture is
still unresolved for 0<epsilon<1/3; no proof or disproof was submitted.

## Quadratic-shear positive lifting criterion completed

`QuadraticCarryParabola.lean` is clean and built. For target high digit
kap*b^2+lam*b+mu over an odd prime field, lam nonzero, it proves carry-aware
pair matching and actual Sidonness on either low-digit half-band. Arbitrary
root representatives are allowed. The finite height transfer is |B|<=M(N)
on one half-band, or |B|<=2*M(N) without choosing the band in advance.
All seven principal audits use only the permitted axioms. Details and
explicit formulas are in QuadraticCarryParabolaResearchNotes.md.

The required small-representative count has NOT been obtained. No actual
exponent beyond 2/3 or original-conjecture disproof was proved. Spec.lean
is unchanged, with its sole sorry at line 17287. No incomplete settlement
was submitted.

### Same cubic norm checksum at prime-power moduli

The proposed power-of-three extension of the verified 27-root seed was
checked with exact integer arithmetic and then certified in Lean.
NormChecksumExample now has fails_at_nine and fails_at_twentyseven, with
explicit four-root collisions. Its updated ten principal axiom audits are
clean; see NormChecksumResearchNotes.md and /tmp/norm-checksum-example.log.
This only rules out an all-powers assertion for that same formula. It does
not prove eventual failure along every power, bound Sidon subsets, or
negate the original conjecture.

The current main result remains eventual M(N)>=N^(2/3); the small-epsilon
branch is still unresolved. Spec.lean was not changed in this continuation.

## Genuine F_9 checksum extension checked

`FieldNineChecksum.lean` now verifies failure of the field-arithmetic version
of the cubic norm checksum, separately from the earlier ZMod 9 failure.
The proof constructs K=F_3(theta), theta^2=-1, proves |K|=9 and irreducibility
of X^3-X-1 over K, then verifies the four-root collision
2247^2+774^2=2262^2+729^2. All five principal audits are clean.
See FieldNineChecksumResearchNotes.md for exact scope and the correction
of an exploratory-script sign error caught during formal verification.

This excludes only this particular formula and encoding at F_9. It supplies
no fixed-power upper bound for the original problem and no new positive
exponent. Spec.lean remains unchanged with its one small-epsilon admission.

### Unrestricted-source and translated-structure recheck

The original reference was retried; DNS resolution still fails. The local
Sidon API contains no theorem that closes the original small-epsilon gap.
Rechecked the finite short-translation and cube extraction statements
against UniversalAffineSidonBound. The selected finite family of translates
still does not provide its all-affine-maps hypothesis. No new uniform bound
for B+{0,h}, no profitable augmentation estimate, and no actual exponent
improvement was obtained in this review. These statements are gap reports,
not proofs that every refinement of those approaches must fail.

No Lean source changed. Spec.lean retains its exact conjecture and one sorry
at line 17287. The latest main compile is /tmp/spec-field-nine-check.log,
with no errors and the expected admission warning. No settlement was
submitted.

### Further unrestricted amplification/upper-bound review

Considered whether a useful submultiplicative bound for the actual M(N)
would combine with the density-zero upper bound to yield a fixed-power
loss. No such bound was proved: projection to root digits does not preserve
square-pair matching, and Sidonness under affine root maps is not controlled
by the unshifted maximum. No submultiplicative law is assumed or asserted.

Rechecked the full short-translation/cube extraction and augmentation routes.
No quantitative gain beyond the existing results was obtained. In particular,
a finite cube of root translates cannot be replaced by the all-affine-maps
hypothesis, and a count of blockers does not furnish a profitable exchange.
No Lean source was changed; the small-epsilon admission remains. No complete
proof or disproof was submitted.

### Complete allowed-alphabet permutation review

Revisited the unrefuted narrower candidate consisting of permutation words
using the entire allowed multiples-of-six alphabet, with the fixed leading
and Eisenstein constant digits. Such factorial-sized families can have the
needed near-linear exponent as the alphabet/base grows, but Sidonness after
integer evaluation has not been proved.

The existing full ordinary-alphabet counterexample and the all-distinct
histogram counterexamples do not by themselves refute that exact family.
No new counterexample to it, no carry-control theorem, and no low-collision
estimate were obtained. In particular, neither the formal Gaussian Sidon
theorem nor common histogram data was silently used as an evaluation theorem.

No Lean source changed in this review. The original conjecture remains
unsettled, with the same single small-epsilon sorry in Spec.lean. No proof
or disproof was submitted.

### Rotation and multiscale continuation review

Rechecked the standard Sidon definition and the existing small-denominator
rotation, Gaussian factor, partial-fiber, and bounded-capacity reductions.
No implication closing the original small-epsilon branch was found. In
particular, the denominator cutoff leaves a collision count too large for
the current alteration argument; individual difference multiplicity bounds
are not a bound on the total number of surviving four-root supports.

Considered imposing compatible digit restrictions at several block scales.
No carry-transfer theorem or favorable total collision count was proved.
The known single-scale specialization failures do not, by themselves,
refute every multiscale refinement. Conversely, imposing several such
conditions does not justify a formal-to-integer transfer without a new proof.
The norm-checksum review also confirmed that the existing failure at the
prime 13 already excludes the same formula under cubic irreducibility alone.

No Lean source changed in this continuation. There is no new exponent bound,
near-linear selector, or disproof. Spec.lean still has its single admission
for 0<epsilon<1/3 and the checked eventual two-thirds endpoint. No incomplete
proof was submitted.
