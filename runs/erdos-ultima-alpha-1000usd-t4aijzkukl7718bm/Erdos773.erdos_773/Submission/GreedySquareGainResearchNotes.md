# Concrete greedy extraction and an actual square-Sidon improvement

**Later update:** The growing-horizon concentration and square transfer are
now completed too. GreedyLogGainResearchNotes.md records the stronger actual
bound M(N)>=(1/10000000)*N^(2/3) eventually. The fixed-horizon account below
is retained as the proof's intermediate stage; its former growing-horizon
missing steps are no longer missing. Erdős 773 is still unsettled.

This is NOT a settlement of Erdős 773. The main conjecture in Spec.lean is
unchanged and retains its sole admission for 0<epsilon<=1/3. However, unlike
the preceding trajectory continuations, this work DOES improve the actual
square-Sidon lower bound: its leading multiplier is now unbounded.

## Strongest verified square-Sidon result

File: GreedySquareSidonLower.lean
Namespace: Erdos773.GreedySquareSidonLower

`eventual_log_lower c hc` proves, for every real c>=0,

    eventually M(N) >= c*N/(N*log N)^(1/3),

where M is the ACTUAL Finset.maxSidonSubsetCard of {1^2,...,N^2}.
`normalized_max_tendsto` proves equivalently

    M(N)*(N*log N)^(1/3)/N -> infinity.

The previous strongest actual bound had the fixed multiplier 5/4. The new
result is stronger, but does NOT imply M(N)>=N^(2/3), because the multiplier
is fixed before the eventual threshold is chosen. No rate of divergence is
proved. In particular it supplies neither the epsilon=1/3 endpoint nor any
fixed exponent greater than 2/3. It is not a proof or disproof of Erdős 773.

## Verified modules and audits

Fifteen modules, 2050 lines, 55 printed checks:

* GreedyProfileRecords
* GreedyProfileGuard
* GreedyGuardControls
* GreedyProfileExtraction
* GreedyUniformMoments
* GreedyIntegratedVariance
* GreedyUniformCosts
* GreedyRoundedHorizon
* GreedyPolynomialFailure
* GreedyPolynomialExtraction
* GreedyBoundedDegreeExtraction
* GreedyAmbientExtraction
* GreedySquareCertificate
* GreedySquareScales
* GreedySquareSidonLower

All compile without warnings or admissions and have built .olean files.
Their audits depend only on propext, Classical.choice, and Quot.sound.
None imports admitted Spec.lean.

Current audit: /tmp/greedy-concrete-extraction-audit.log (55 checks).
Combined with the preceding twenty modules:

    /tmp/greedy-square-gain-combined-audit.log

has 173 clean checks across 35 modules. Audit sources are retained as
GreedyCurrentAudit.lean and GreedyCombinedAudit.lean. CheckGreedyAPI.lean was
removed. No native evaluation or new axiom was used.

## Actual guard and initialization

Parameters records V,d,rho,K. Profiles F2,F3,F4 and widths E2,E3,E4 are indexed
by Fin 3; physical time is n*d/V. In a regular four-uniform hypergraph of
original degree d^3, all initial recorded degrees equal their profile centers
EXACTLY. Signed initial errors equal minus the corresponding initial widths.

The crossing event is stated at each vertex's STORED clock. Its exact
characterization is width <= sign*(recorded_degree-center). Avoiding both
signs gives the profile tube at the stored clock; on a live valid ready
state it is the actual current degree tube.

The concrete guard is Valid together with Q, degree, and common-neighbor
boxes. Auxiliary failure means some earlier chosen subset witnesses a large
common-neighbor count. This is monotone under extending the chosen carrier.

Crucially, `reach_running_QBox` proves the availability box at EVERY reachable
running state under this actual guard. The proof is noncircular: a running
successor passed the previous guard, so deterministic Q-box propagation
applies; a running hold is impossible because the previous Q box already
implied Ready. Thus good reachable running states satisfy both Ready and the
whole guard. `full_run_of_goodPath` yields an independent set of EXACT size T;
there is no remaining early-stop alternative.

## Fully instantiated drift and moment controls

Let upper_j=center_j+width_j and qmin=Qprofile-EQ. Raw caps are C+1 for d2
and upper_2+1 for d3,d4. The raw variance numerators are

    (C+1)*(2*upper_3+upper_2^2),
    (upper_2+1)*(3*upper_4+2*(upper_2+1)*upper_3),
    (upper_2+1)*(3*(upper_2+1)*upper_4).

Actual second-moment bounds are 2*raw/qmin+2*(signed_profile_increment)^2.
`GreedyGuardControls.control` discharges every drift and guard obligation
using the previously verified physical drift inequalities. The safe-choice
factor is retained throughout; it is never replaced by Q.

The finite common-neighbor first-hit probability at threshold C=16*k is at
most

    V^2*(9*D*(T/L)^3/(k+1))^(k+1).

This follows by exact carrier-law transfer, witness packing with pair
codegree one, and a union over ordered distinct vertex pairs.

`independent_of_certificate` combines this with the six actual crossing
tails. No drift, guard, path, or early-stop assumption remains in that
certificate: all outstanding inputs there are explicit scalar inequalities.

## Integrated variances and six-test costs

Put B=1+tau and S=(30+4*K)*B^4. The uniform signed slope is at most

    S*d^(j+1)*(d/V), j=0,1,2.

With V>=d^3, variance scales are

    ((C+1)*d^2, d^4, d^5),

and their time-integrated scales are

    ((C+1)*d, d^3, d^4).

The common factor is

    Z=((1200*B^6+2*S^2)/q(tau))*B.

`integrated_variance` proves sum v_n <= Z*integratedScale. The total increment
caps are

    b2=C+1+S/d,
    b3=b4=(5*B^2+S)*d.

When rho<=1 and S<=d, let P=Z+5*B^2+S+2. Initial widths are exactly
(d*rho,d^2*rho,d^3*rho), and all six crossing probabilities are bounded by

    exp(-d*rho^2/(4*P*(C+1))).

Thus totalCost <=6 times this exponential. This is a bound on the actual
recorded process, not on a surrogate or merely on its differential equation.

## Unconditional polynomial-family extraction

Use natural m, d=m^4, rho=1/m, K=4000, original degree D=m^12, C=16*m, and

    L=floor(V*q(tau)/2), T=floor(V*tau/d).

Rounding is explicit: L>=V*q(tau)/4 when V*q(tau)>=4; T/L<=4*tau/(d*q(tau));
T<=L under 4*tau<=d*q(tau); and T>=V*tau/(2*d) when V*tau/d>=2.

For fixed tau>=1 and polynomial volume exponent A, with m^12<=V<=m^A,
all numerical hypotheses hold eventually. The total failure probability is
bounded by

    m^(2*A)*(1/2)^(m+1)
      +6*m^A*exp(-m/(68*fixedPenalty(tau))),

which tends to zero. The auxiliary base is bounded by
576*tau^3/(q(tau)^3*(m+1)), eventually <=1/2. These are actual proved limits,
not assumed tail estimates.

`GreedyPolynomialExtraction.eventually_independent` therefore gives, for
every fixed tau>=1, an independent set of size at least

    V*tau/(2*m^4)

in every linear regular degree-m^12 four-uniform hypergraph in the stated
volume interval, once m is sufficiently large.

`GreedyBoundedDegreeExtraction` removes exact regularity by the earlier
prime-field regularization. It uses at most 8*m^12 copies and preserves
linearity. For m>=2, an original volume <=m^A becomes <=m^(A+15), so the
threshold is still uniform. Independence density transfers without loss.
The empty original carrier is handled separately. Consequently any fixed
multiplier c*V/m^4 is eventually attained for MAXIMUM degree at most m^12.

`GreedyAmbientExtraction` transports this to arbitrary ambient finite
carriers. Lifted degrees, edge sizes, intersections, and independence are
proved exactly, rather than hidden behind an assumed transport result.

## Square-specific transfer with logarithms retained

Start with the existing logarithmic-sampling theorem at loss 1/2. It gives
an actual AP-free root carrier A subset [1,N] with

    |A| >= N/(2*log N), |A|<=N,
    |edges(A)| <= N^2/(log N)^3.

The full interval has pair codegrees <=N^(1/16) eventually. For X=N,L=log N
put

    r=X^(1/4), p=1/r, mu=L^2/(16*r),
    D=128*r/L^2, m=ceil(D^(1/12)).

Unlike the earlier coarse controlled-linearization estimate, the new finite
certificate uses the ACTUAL retained-edge count:

    p|A|-p^6|A|^2*K^2-mu*p^4|edges(A)|
       <= |B|-mu*|edges(B)|.

Both cost terms are at most p|A|/4 eventually. Degree trimming then gives a
linear AP-free B of size >=p|A|/4 and maximum degree <=8/mu=D<=m^12.

The rounding estimates prove

    m^12<=4096*D,
    m^12*L^2<=524288*r,
    X<=m^96.

The last inequality follows eventually from L^2<=X^(1/8); hence the generic
m-threshold applies uniformly at every sufficiently large square height N.
The ambient greedy theorem with exponent 96 and multiplier 1024*c supplies
an actual Sidon subset. Pure algebra (including the cube of the real one-third
power) then gives exactly

    c*X/(X*L)^(1/3) <= M(N).

Thus the new bound is not just an improvement for an abstract hypergraph.
Every square-specific sampling, linearization, rounding, regularization,
and density-transfer loss has been included.

## Remaining gap and possible next work

No quantitative growing-horizon concentration theorem is proved yet. The
scalar horizon bounds allow logarithmic-cube-root time, but the new failure
analysis is at each FIXED tau. Quantifying its dependence on tau could give
a fixed logarithmic gain and possibly remove the current log-loss up to a
constant. That would still remain at square-Sidon exponent 2/3, not 1-o(1).
A square-specific exponent improvement or a fixed-power upper bound is still
needed to settle the original problem.

No new valid near-linear arithmetic selector or disproof was found in the
review of digit, factorization, interval, p-adic, or amplification ideas.
Existing obstruction results concern their particular sufficient methods,
not arbitrary Sidon subsets.

Spec.lean remains unchanged. Latest check:

    /tmp/spec-greedy-square-gain-check.log

It reports only the original admission and pre-existing harmless warnings.
The sole sorry remains at line 2031, with SHA-256

    917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.

The new lower bound is in the clean scratch dependency chain and has NOT
been consolidated into Spec.lean. No settlement or proof submission occurred.
