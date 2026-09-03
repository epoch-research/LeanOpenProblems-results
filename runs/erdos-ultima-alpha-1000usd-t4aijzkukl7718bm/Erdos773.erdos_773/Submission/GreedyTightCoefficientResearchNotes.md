# Improved actual N^(2/3) coefficient

This does NOT settle Erdos 773. The main conjecture, import, and sole sorry
in Spec.lean are unchanged. The exact epsilon=1/3 assertion is still open
in this project, as is every smaller positive epsilon.

## Strongest actual theorem now

File: GreedyTightSquareLower.lean
Namespace: Erdos773.GreedyTightSquareLower
Theorem: eventual_power_lower

    eventually M(N) >= (1/8192)*N^(2/3).

Here M(N) is Finset.maxSidonSubsetCard of the first N positive square values.
This is an ACTUAL Sidon lower bound, not a bound for a fractional relaxation,
a conditional extraction certificate, or a bound on a lower-bound expression.
All sampling, linearization, trimming, and concentration obligations are
instantiated. It improves the previous rational coefficient 1/10000000 by
more than a factor 1200, without improving the exponent.

The coefficient remains less than one. In particular this theorem does NOT
prove M(N)>=N^(2/3), and cannot remove the original epsilon=1/3 endpoint.
It also does not justify any N-dependent substitution in an older fixed-
multiplier eventual result.

## What changed, and what did not

The existing finite growing-horizon certificate is reused unchanged:

    M(N) >= tau*p*|A|/(8*n^8),

where

    X=N, L=log N, r=X^(1/4), p=1/r,
    mu=L^2/(16r), D=128r/L^2, n=ceil(D^(1/24)),
    |A|>=X/(2L),
    horizonBudget(tau)=exp(10000*(1+tau)^3)<=n.

There is no new probabilistic theorem and no new assumption about the
arithmetic collision hypergraph. The improvement comes solely from sharper
eventual ceiling bounds, volume exponents, and the allowed logarithmic time.

### Tight ceiling bound

GreedyTightSquareScales.ceil_root24_tight proves that when D>=0 and
D^(1/24)>=1000,

    ceil(D^(1/24))^24 <= (26/25)*D.

It uses ceil(x)<x+1<=(1001/1000)x and the exact rational inequality
(1001/1000)^24<=26/25. The earlier proof used the much coarser factor 2^24.

`tight_degree` applies this once n>=1001, obtaining

    n^24*L^2 <= (3328/25)*r.

The ceiling threshold is eventually guaranteed by the volume bound and
N >= max(M,1001)^97, where M is the greedy-certificate threshold.

### Volume exponent 97

Eventually L^2<=X^(1/388). Consequently

    X^(24/97)*L^2 <= X^(1/4)=r <=128r,
    X^(24/97)<=D<=n^24,
    X<=n^97.

The last implication is checked by raising to the 97th power, using the
exact rpow identity, and taking an ordered 24th root. No real/natural power
casts are left implicit. The older proof used X<=n^192.

The eventual logarithmic estimate follows from the already available
isLittleO_log_rpow_atTop with exponent 1/776, followed by squaring. It also
implies the older L^2<=X^(1/8) hypothesis needed for the unchanged sampling
and overlap-cost estimates.

### Larger permitted horizon

Define

    tightHorizon(L)=L^(1/3)/100,
    tightHorizon(L)^3=L/1000000.

When L>=10^12, the horizon is at least 100. Hence

    (1+tau)^3 <= (101/100)^3*tau^3,
    10000*(1+tau)^3 <= L/97.

The last numerical comparison is exact:
97*1030301=99939197<100000000.
Together with X<=n^97 this gives

    horizonBudget(tau)<=exp(L/97)=X^(1/97)<=n.

Thus the N-dependent horizon satisfies the UNIFORM certificate already
proved in GreedyGrowingSquareCertificate, now applied with volume exponent
97. There is no illicit use of a fixed-horizon eventual theorem.

### Exact final scale conversion

Let R=(XL)^(1/3). The tight degree estimate gives

    (r*L*n^8)^3 <= (3328/25)*X*L.

Since 3328/25 <= (128/25)^3, it follows that

    16*r*L*n^8 <= (2048/25)*R.

The finite certificate and |A|>=X/(2L) therefore imply

    M(N) >= tau*X/((2048/25)*R)
         = (1/8192)*X^(2/3).

`tight_scale_lower` proves all divisions, positivity conditions, cube
comparisons, and the final real-power identity.

## Endpoint investigation and remaining work

The existing sharp unordered collision count already has a leading
coefficient below 1/12. However, that fact alone is not an independent-set
theorem with a unit N^(2/3) coefficient. The current extraction route still
has substantial losses from thinning to a linear hypergraph, degree
trimming, and conservative trajectory control. Only the rounding/horizon
losses described above have been improved in this continuation.

No asymptotically sharp average-degree extraction theorem was proved. No
claim is made here that all possible refinements of the current route are
impossible, or that a limitation on a certificate is an upper bound on M(N).
The original task still requires a new exponent argument (or a fixed-power
upper bound), even if the unit-coefficient endpoint is eventually resolved.

## Verification

Two new built modules, 246 lines:

* GreedyTightSquareScales.lean: seven audited lemmas.
* GreedyTightSquareLower.lean: the actual eventual lower bound.

They compile without warnings or admissions. They do not import the
admitted Spec theorem. All eight new axiom checks use exactly propext,
Classical.choice, Quot.sound. The combined source
GreedyTightCombinedAudit.lean now checks 199 declarations across 43 modules;
all 199 pass with only the permitted axioms and no warnings.

Logs:

* /tmp/greedy-tight-square-scales.log
* /tmp/greedy-tight-square-lower.log
* /tmp/greedy-tight-combined-audit.log
* /tmp/spec-tight-square-lower-check.log

Spec.lean still has its sole sorry at line 2031. SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
No new proof was consolidated into Spec.lean, and no complete proof or
disproof of the conjecture was submitted.
