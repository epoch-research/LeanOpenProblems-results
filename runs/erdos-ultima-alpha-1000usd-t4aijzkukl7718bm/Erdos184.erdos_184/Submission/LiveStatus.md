# Current status

Original Submission/Spec.lean is unchanged and UNSOLVED, retaining its sorry.
No proof or disproof has been submitted. No active development job.

Latest checked modules, all with current oleans and permitted axiom audits:
- EndpointSupportCompletion
- PruneLeafPaths
- OptionPathProjection
- OptionLeafParity
- BoundedEndpointPaths

BoundedEndpointPaths.exact_endpoint_partition proves an at-most-n SIMPLE-PATH
partition, with endpoint multiplicities 1 at odd vertices, 2 at supported even
vertices, and 0 at isolated vertices. This is NOT the required cycle-and-edge
bound. The source contains the exact statement, and ResearchNotes contains
proof details and logs.

New unproved candidate: every even graph has a cycle decomposition whose
every cycle meets a specified contained spanning tree. Exact external tests
through order8 found no counterexample; no general proof is available.
The closed-trail-to-simple-cycle step is a real gap, not supplied by the
endpoint path theorem. Do not revive fixed-pair absorption: unrestricted
spanning paths already fail on D=path0123456, H=D+triangle036, and nonedge
spanning trees have the earlier 41-vertex gadget obstruction.

Other open routes: valid selective compression, dominated Best-singleton
leaf deletion plus compression, arbitrary even-minimal core control, or a
genuinely different proof of the original O(n) bound.

Another UNPROVED candidate, finite-tested only: arbitrary prescribed endpoint
pairs in an all-odd graph with a universal vertex. All 32768 labeled order8
instances passed /tmp/universal_prescribed_paths.cpp. No general result and no
completed original-conjecture reduction. See ResearchNotes for exact scope.

Further external-only checks: the two-color monochromatic endpoint claim passed
all 243 all-odd order8 graph shapes and all 91 connected subcubic order10 shapes.
Universal prescribed pairs also passed all 404 order10 cones over even subquartic
order9 graphs, testing all 945 matchings per graph. None is a general theorem.
Original conjecture still UNSOLVED, Spec unchanged; no active job.

NEW REFUTED bridge: an odd spanning tree and a connected all-odd host need NOT
have a common full simple-path endpoint matching, even with disjoint edges.
A 12-vertex corona-C6/caterpillar example has 686 host and 243 tree matchings
with empty intersection, independently externally checked. The union DOES
have a three-cycle tree-hitting partition, so tree-hitting itself remains open.
See the latest ResearchNotes entry. Spec remains unchanged and UNSOLVED.

Continuation: no settlement or new Lean theorem. The even-minimal separating-
cycle criterion remains unproved. Exact order7 diagnostics refute the generic
bound number(G)<=value(G-v)+degree_F(v), even with an extra constant1:
K3 join I4, best singleton degree0 at a clique vertex, number7 versus deleted
hull5. This does NOT refute the dominated Best-LEAF proposal. See ResearchNotes
and /tmp/singleton-vertex-loss7.log. Spec unchanged; no active process.

NEW VERIFIED AUXILIARY MODULES: SeparatingCycleReduction and SmallSeparatingCores
(217 lines total, allowed axioms, current oleans). The former proves the
component budget number(G)+cc(G)<=n CONDITIONAL ON separating cycles in all
nonempty even-minimal cores, and transfers it to the original proposition.
The latter verifies the criterion for number<=3 and packages a hypothetical
original failure into a nonempty even-minimal core with number>=4, supported
degrees>=4, and ALL cycle deletions preserving reachability. No existence or
exclusion of such a core has been proved. Spec remains unchanged and UNSOLVED.
SmallSeparatingCores required -M8500 for its large import closure; the first
module compiled with -M7000. One Lean process at a time. See ResearchNotes/logs.

External structural obstruction: no separating cycle does NOT imply number=Delta/2.
A64-vertex10-regular independent twin blowup of a bridgeless5-regular base has
no separating cycle, but deleting four central twins leaves five components,
so no Hamilton cycle and hence no five-cycle decomposition. See ResearchNotes
and /tmp/twin_blowup_separator.py. This does NOT concern even-minimal cores.
Petersen blowup JSON certificate serialization repaired and rerun successfully.
Spec still unchanged/UNSOLVED; no Lean job active.

NEW VERIFIED: NonseparatingEdgeConnectivity, SpanningEvenCoreTransport,
ComponentSeparatingCores, ConnectedCoreObstruction. The connected-component
transport gap is now CLOSED: the sufficient hypothesis requires separating
cycles only for CONNECTED nonempty even-minimal cores. Original failure would
yield a connected4-edge-connected even-minimal nonseparating core, number>=4.
All four modules have current oleans and permitted-axiom audits; the last uses
-M8500, the others-M7000. See latest ResearchNotes and /tmp logs.
The general structural hypothesis remains UNPROVED. Spec unchanged/UNSOLVED.

NEW VERIFIED: MinimalParityCorrection (current olean, -M7000, permitted axioms).
Any parity correction T in nonempty globally Minimal G satisfies
support(G)+6<=8*|E(T)|. This is NOT a decomposition-number upper bound.
The exact order8 parity diagnostic finished: 268435456 graphs,564355 cores,
40320 failures of bestSingles=minParity, but ZERO globally minimal failures.
All claims of equality in arbitrary graphs must therefore be withdrawn;
globally minimal equality is still unproved. See ResearchNotes and logs.
Spec unchanged/UNSOLVED. No active job.

Further completed external diagnostics (no new original proof):
- Fixed matching completion is FALSE even in all-odd graphs: triangle067
  with leaves5 at0,1 at6,and2,3,4 at7; demands05,16,23,47 force paths leaving
  the triangle uncovered. Does not refute the two-color or universal claims.
- Best singleton=min parity correction held on1201 stored core entries
  (order9 plus restricted double-split catalogue), but is still unproved.
- Raw two-choice transfer fails on a NONMINIMAL order7 graph even for a Best
  singleton edge; target HULL still increases. See ResearchNotes for edges.
No active jobs. Spec unchanged/UNSOLVED; no settlement submitted.

NEW VERIFIED: TwoColorInitialPacking, OneEvenPaths, CloseAdjacentEndpoints,
AlmostUniversalEvenCycles (current oleans, -M7000, permitted axioms).
- Two colors: an admissible initial packing and color-restricted maximum exist;
  full coverage is STILL UNPROVED.
- Exactly one even-degree vertex: FULL simple-path partition with each other
  vertex endpoint once; 2*pathCount+1=|V|. This is not a cycle bound.
- Even graph with an almost-universal vertex missing exactly one neighbor:
  2*number G<=|V|-2. Special case only, not the original conjecture.
External two-color tests now pass all connected order10 all-odd graphs without
universal vertices (maxdegree<=5 and exactly7), plus all509 subcubic order12
shapes. These finite checks are NOT general proofs. See ResearchNotes/logs.
Spec unchanged/UNSOLVED; no settlement submitted. No diagnostic job remains.

NEW MATHEMATICAL OBSTRUCTION (not Lean-formalized): unrestricted Best-leaf
vertex deletion has unbounded hull loss, even for globally Minimal graphs.
Wedge m copies of K3 join I4 at a clique vertex v and attach a pendant edge vz.
There is a Best singleton forest with degree_F(v)=1, but number=7m+1 and
hull(G-v)=5m. See the latest ResearchNotes entry and the exact external base
certificate /tmp/best-leaf-wedge-certificate.json. This does not address the
DOMINATED Best-leaf route or a rule choosing a suitable leaf, and does not
refute the original conjecture. An order8 classified diagnostic is still
running at this note (/tmp/best-leaf-vertex-loss8.log/.exit).
Spec remains unchanged and UNSOLVED; no original settlement submitted.

The order8 classified diagnostic has now finished (exit0, all268435456 graphs).
Maximum dominated Best-leaf hull loss was2; this is finite evidence only.
The generic Best-leaf loss is unbounded by the wedge construction, regardless
of the order8 maximum3. No processes remain active. Original Spec is unchanged
and UNSOLVED; no proof/disproof has been submitted.

NEW VERIFIED: TransferSingletonForest.lean (206 lines, current olean,
-M7000, permitted axiom audits). Adjacent full transfer preserves reachability
and acyclicity. Along a Best singleton edge, it transports the singleton forest
with unchanged size and makes the sender a leaf; the transferred remainder
is exactly transfer(G\\F), and the two images partition the target's edges.
The remainder may change parity, and the transported forest is NOT proved
optimal. No hull monotonicity follows yet. A parity-corrected-target-only
number comparison is refuted by a four-vertex path (see ResearchNotes).
No active jobs; original Spec unchanged and UNSOLVED; no settlement submitted.

Further reassessment found no settlement. ExactEdgeDeletion cannot be combined
directly with global-minimal singleton bounds: even-minimal G need not have
G-e globally minimal (two triangles sharing a vertex already obstruct this).
The additional nonseparating-core hypothesis remains an unproved possible
restriction. Extracting a minimal hull maximizer loses the single-path parity
structure. No new Lean theorem, no jobs, no Spec change, no submission.

Latest continuation: one-edge equal-number singleton monotonicity is FALSE
on hull-saturated graphs. A chain of m copies of B=K3 join I4 minus03, closed
by a new two-edge path, has number=value=6m+1 and BestSingles4m. Removing one
new edge preserves number/value but lowers BestSingles to3m+1. Base profiles
and explicit m=2 partitions are externally checked, NOT Lean-formalized;
see the latest ResearchNotes entry and /tmp/singleton-pruning-chain-certificate.log.
This does NOT refute the weaker minimal-core monotonicity claims (all equal-
number minimal cores here are spanning trees), and does NOT settle Spec.
Spec remains unchanged with its original sorry. No job is active and no
original proof/disproof has been submitted.

Latest continuation: two further auxiliary restrictions, neither Lean-formalized
nor an original settlement. (1) Global Minimal graphs do NOT have uniformly
bounded degeneracy or edge density: grouping equal neighborhoods in K_(r,t)
shows its hull maximizers have all but O_r(1) large-side vertices of degree r
for fixed odd r and t large. A concrete non-3-degenerate minimal core exists
inside K_(5,1560); see ResearchNotes for the full counting argument.
This does NOT refute bounded MINIMUM degree of global cores.
(2) General binary Best-remainder fractional exactness is FALSE. PG(3,2)
minus one point is globally Minimal (number5, BestSingles2, proper hull4),
and all seven Best remainders have integral number3 versus fractional12/5.
Exact external uniform-cover certificate in /tmp/projective-best-gap-certificate.log.
The GRAPH-specific version remains unproved/unrefuted. No active jobs.
Spec unchanged and UNSOLVED; no original proof or disproof submitted.

Latest verified continuation: NonCutHalfDegreeLoss.lean compiles with allowed
axioms only. At any vertex v with G-v Preconnected, number(G)<=hull(G-v)+
ceil(degree(v)/2). Under failure of the original, the highly connected global
minimal obstruction can therefore be required to have degree(v)>2C AND
hull(G-v)+C<number(G) at every vertex. This is a conditional obstruction,
not a contradiction or a counterexample construction. No uniform selective
loss bound is proved. Spec remains unchanged/UNSOLVED. No jobs are active.

Latest continuation: independently confirmed two nine-vertex local obstructions
with exact external cycle-partition recursion (/tmp/check_repair_examples.py,
/tmp/check-repair-examples.log). Dominated double smoothing raises number2 to3;
unrestricted repair raises2 to4, but lacks two K_(2,3) edges. The actual
dominated repair is NOT refuted and remains UNPROVED. Details and edge lists
are appended to ResearchNotes. No new Lean theorem, no original settlement,
and no active diagnostic/build. Spec remains unchanged with its original sorry.

NEW VERIFIED: UnrestrictedRepairObstruction.lean, current olean, exit0,
allowed axioms only. Even nine-vertex source has number2; unrestricted repair
has number4. Missing_common_edges explicitly excludes the two K_(2,3) spokes,
so the dominated candidate remains unproved/unrefuted. This is NOT an original
settlement. Endpoint-color and tree-marker conversion gaps remain. Spec is
unchanged/UNSOLVED. No live compilation or diagnostic remains.

Continuation audit: reread NonCutHalfDegreeLoss, MinimalSingletons,
MinimalParityCorrection, MinimalCycleConnectivity, SmallCoreRigidity,
MaximumTripleThreshold, and EvenCoreHullGap. No new closing lemma was proved.
The degree-dependent vertex loss, the rigid-triple threshold, and the additive
hull gap still do not imply a uniform linear bound. No new Lean file or proof
was produced in this continuation. Spec remains unchanged with its original
sorry; no proof/disproof has been submitted.

NEW VERIFIED: ThreeHubOptimalRemainders.lean and
OptimalRemainderDualCriterion.lean, current oleans, exit0, permitted axiom audits.
For K_(3,3q+1), q>=3, EVERY Optimal remainder is dual-exact but neither
EvenMinimal, CycleCritical, nor CycleRigid. Separately, existence of SOME
exact-dual Optimal remainder on every globally Minimal graph implies the
original with constant3. That universal existence hypothesis remains UNPROVED.
External catalogue check:84 cyclic cores,4176 Best remainders, all certified
exact by block-degree bounds; no LPs needed. This finite evidence is not a
general theorem. See latest ResearchNotes entry. No live jobs. Spec unchanged
with its original sorry; no original proof/disproof submitted.

Latest continuation: examined MAXIMUM-singleton (fewest-cycle) optima.
A structured13-vertex chain source has number13 and is globally Minimal by
an exact external seven-vertex block check plus the stated separation argument.
Its maximum-singleton count is10; the closing edge is never singleton in such
an optimum. All576 max-singleton remainders are biconnected, maxdegree4,
minimum3/maximum5 cycles: neither block-degree saturation nor rigidity follows.
ALL1805 optimal remainders remain dual-exact (361 degree certificates,1444
rational duals checked on every cycle). These are EXTERNAL checks, NOT new
Lean theorems. General dual exactness and the original remain unresolved.
See latest ResearchNotes for artifacts and precise scope. Spec unchanged;
no original submission and no live jobs.

Latest continuation: nonnegative-exactness for MAXIMUM-singleton optima is
refuted by an unbounded chained-block family (mathematical argument plus exact
external local certificates, NOT Lean verified). G_m has6m+1 vertices/number;
all max-singleton remainders have number m+1 but a THREE-cycle edge cover, so
nonnegative cycle-upper dual total<=3. Independent enumeration checks all24
local remainder types admit3 terminal covering paths. Explicit m=3 remainder
has a4-cycle partition and an exact signed dual (negative closing-edge weight).
Some OTHER Optimal splits still have positive exact duals. Thus the general
HasExactOptimalRemainder criterion remains unproved/unrefuted. Spec unchanged
and UNSOLVED; no original submission or live job. See ResearchNotes/artifacts.

Latest continuation: no original settlement and no new Lean theorem. The
nongraphic PG(3,2)-minus-one obstruction has exactly seven Optimal splits, ALL
with two singleton elements; each has signed fractional remainder cost12/5<3.
So its obstruction extends beyond Best to ALL Optimal splits. Exact external
verification only; it is not graphical and does not refute the original or the
graph-specific sufficient criterion. Spec is unchanged/UNSOLVED. No active job.

NEW VERIFIED: EdgeCriticalSmallCorrection (current olean, permitted axioms).
Any parity correction of size<=2 in an EdgeCritical graph is Optimal; hence
smaller-than-Best corrections there must have size>=3. This is NOT a linear
cycle-count bound. Generic extension to arbitrary corrections is refuted
for cographic regular matroids by the BOND system of K3 join I3: number5,
Best4, min correction3, all elements optimally exposable, but hull7. It is
nongraphic and not globally Minimal. Exact external certificate only for
that obstruction; see latest ResearchNotes. Graphical general case remains
unproved. Original Spec unchanged/UNSOLVED; no active jobs or submission.

Latest external obstruction: the parallel B=K3 join I4 minus03 family also
refutes a universal non-cut leaf-loss bound for MAXIMUM-singleton optima.
For even m, global Minimal 2-connected G_m has number13m/2+1; ALL max-singleton
optima have5m+1 singles and make the closing edge v--z the only singleton at z.
G_m-z is connected with hull6m, giving loss m/2+1. External exact local profiles
and explicit certificates, NOT Lean formalized. This does not refute SOME
favorable leaf, higher-connectivity restrictions, or the original conjecture.
See newest ResearchNotes and /tmp/parallel-max-singleton-leaf-certificate.log.

Continuation audit: reread OptimalRemainderDualCriterion, CycleDualBound,
MinimalSingletons, MinimalParityCorrection, MaximumTripleThreshold, and the
bipartite density/minimum-degree guards. No closing lemma was obtained.
Fractional signed bounds do not supply integral exactness; dense global cores
do not refute a selective bounded-minimum-degree rule. No new Lean theorem,
original proof, or original disproof. Spec remains unchanged with its original
sorry. No build or diagnostic was launched in this continuation.

Continuation: no closing result from the dominated Best-leaf route. A direct
local partition check explains why identifying BOTH block terminals cannot
amplify the one-path lower bound: B has two terminal paths with a four-piece
cofactor. This matches the old nonminimal dominated-amalgam construction.
No new Lean theorem; Spec remains unchanged/UNSOLVED. No active jobs.

NEW VERIFIED: SquareBudgetArithmeticObstruction.lean (current olean, exit0,
permitted axioms). Positive abstract count sequences satisfy strict square
core descent, both numerical accounting inequalities, and the simple-graph
edge cap, yet their initial k/n ratio is arbitrarily large. This rules out
closing the route from those estimates alone. The sequences are NOT graphs
and do NOT disprove the original. No new structural charge was proved.
Spec unchanged/UNSOLVED, no active jobs, no original settlement submitted.

Continuation audit: checked OptimalSingletonForest, SingletonSubsetDeletion,
OptimalSingletonDeletion, and MaximizerReachability against the exact-dual
criterion. Their additive inheritance statements do not imply dual exactness
or unrestricted minimal-core singleton monotonicity. Strict Best-singleton
growth remains refuted by StrictSingletonDescent; no such hypothesis was used.
The finite Best-remainder block-degree certificates are not a general theorem.
No new closing lemma, no original proof/disproof, no build or diagnostic.
Spec remains unchanged/UNSOLVED.

Latest continuation: audited the favorable singleton-leaf route and the
maximum-partition rigid-subfamily route. Leaf existence plus the established
half-degree loss does not provide a uniform favorable-leaf bound. The rigid
triple threshold does not extend to arbitrary optimum by the checked results.
No new structural bridge or Lean theorem was obtained. The current problem
reference could not be fetched (DNS resolution failure). Spec remains unchanged
(SHA256 509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5),
with its original sorry. No original proof/disproof or submission was made.

Continuation: considered lifting a small nonrigidity witness to a proper even
subgraph preserving the ambient optimum. The existing Petersen-line-graph
local-even-replacement obstruction prevents the unrestricted local step; its
source is not EvenMinimal, so the global-minimal restricted step remains open.
No proof of that restricted step, first-bad-core reduction, or original linear
bound was obtained. No new Lean theorem or original submission; Spec unchanged.

NEW VERIFIED: MixedDualCriticality.lean (current olean, exit0, permitted
axioms). A full signed mixed dual is exact on an EdgeCritical graph iff the
graph is acyclic; every cyclic such graph has gap>=2/3. This is NOT a linear
bound or a refutation of the separate optimal-even-remainder exactness route.
See latest ResearchNotes. Spec unchanged/UNSOLVED; no active job or original
submission.

Continuation: re-examined fractional rounding. The existing verified EvenRing
family already has EXACT fractional cycle-only cost two and unbounded integral
cost, so unrestricted multiplicative rounding fails even for even graphs.
Only an additive order-sized loss or a suitable core restriction remains
viable here; neither was proved. No new Lean theorem, original settlement, or
active job. Spec unchanged with its original sorry.
