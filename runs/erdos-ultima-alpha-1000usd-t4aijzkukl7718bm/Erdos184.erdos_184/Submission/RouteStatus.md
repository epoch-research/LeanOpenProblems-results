# Route status — original Erdős184 still unsolved

Spec.lean is unchanged and contains its original sorry. Do not submit it as a
settlement. Latest verified modules: ExactEdgeDeletion and EvenCoreHullGap.
See ResearchNotes.md for precise statements, audit logs, and historical details.

## Established sufficient conditions whose main hypothesis remains UNPROVED

- Arbitrary even-minimal core rigidity / heredity of even-minimality.
  Only optimum<=3 is established (SmallCoreRigidity).
- Uniform low-degree or edge-excess bounds for arbitrary even-minimal cores.
- SquareAccessible for initially EvenMinimal graphs (SquareCoreReduction).
- Fixed relative hull gain on even graphs (RelativeHullCriterion is an iff).
  EvenCoreHullGap shows this gain already implies a linear bound on each core.
- A suitable EXISTENTIAL or averaged contraction/compression step.
  Universal versions below are false. No selection theorem has been proved.
- All-odd arbitrary-degree SIMPLE-path decomposition in this workspace.
  This is a known theorem mathematically, but only the subcubic case has been
  reconstructed and verified here. Do not substitute trails for paths.
- A uniform terminal bound for NestedAlongEdges graphs, and a VALID selective
  compression argument reaching that class.

## Proposed shortcuts already REFUTED (do not retry as universal lemmas)

- CycleCritical -> EvenMinimal: doubled Petersen, verified.
- Square cofactor criticality/accessibility assuming only initial CycleCritical:
  PetersenSquareGraph, verified.
- Universal adjacent compression on GLOBAL edge-minimal graphs:
  ChainRingCompressionObstruction, verified.
- Uniform additive contraction loss for the EVEN-support hull, even on rigid
  minimal cores: TripleBundlePort, verified at circuit-code level. A simple
  graph realization is described in notes, but graph transport is not checked.
- Uniform one-generator binary-extension hull loss: TripleBundleCode, verified.
- General even-subgraph diminishing returns, even with rigid base and triangle
  increments: Work.DiminishingReturns, verified. SquareMarginal is also checked.
- Nonadjacent parity-preserving compression, including common-neighbor variants:
  several rigid-core obstructions recorded; distinguish exact verified modules
  from the external diagnostics.
- Matroid/submodular rank behavior of the even hull on maximum cycle families:
  explicit graphical diagnostic in notes; not a general rank function.
- Purely local replacement of a nonrigid two-cycle union preserving ambient
  optimum: line-Petersen diagnostic refutes it without global minimality.
- Independence of even-degree vertices in globally minimal graphs, even after
  excluding bridges: K3 join I4, exact external diagnostic.
- Arbitrary binary minimal-core rigidity: nonregular binary counterexamples.
- Automatic optimality of squares selected by critical deletion + core
  extraction when initial graph is merely CycleCritical: doubled-Petersen
  five-cycle observation in notes. Initially EvenMinimal case is UNPROVED.

## Quantitative facts that do NOT by themselves close the gap

- Even G: 6*number(G)+|support(G)| <= 6*EdgeHull.value(G).
- EvenMinimal G: EdgeHull.value(G) <= number(G)+(n-2).
- Global-minimal G: optimum singleton count >=(|support(G)|+6)/8.
  This is a fraction of VERTEX count, not a fraction of number(G).
- Exact edge deletion for even G:
  number(G-e)=min_{C containing e}(number(G-C)+|C|-1).
  The edge-local shortest-cycle formula follows under CycleCritical.
- No-C4 and bounded-codegree cases have linear estimates, but the available
  smallest-counterexample reductions do not supply a universal codegree bound.

No original proof/disproof has been obtained. No active jobs at this update.

## New path progress: clean-cycle absorption is now general (verified)

CleanEndpointCycleAbsorption.absorb_clean_cycle_ended handles two paths whose
four distinct endpoints lie on the unused cycle and whose internal vertices
avoid it. Outside-cycle intersections are unrestricted; every cyclic order is
covered. CleanCycleMaximality.unused_cycle_internal_contact shows that every
unused cycle of a maximal admissible endpoint packing has an INTERNAL contact
with a packed path. Handling such internal contacts remains unproved. See the
latest ResearchNotes entry and the three new modules, including the intermediate
FourSpokeCycleAbsorption. None settles the original conjecture.

EndpointEscape.lean additionally verifies that every unused-cycle vertex has
two distinct neighbors whose endpoint paths avoid that vertex. The neighbors
may be endpoints of the same path, and their incident edges need not be unused.
This does not yet provide a valid terminating absorption sequence.

## New: actual branch bijections and finite endpoint fans (verified)

EndpointRotation, EndpointBranches, PartialInjectionFan, EndpointFans are now
checked.  The previously unformalized branch map is a bijection, and every
unused neighbor begins a nonrepeating finite fan ending at an endpoint whose
path avoids the center.  Fans from distinct unused neighbors are disjoint.

Still missing: simultaneous path reassembly along these fans, and most
importantly a terminating absorption argument.  Fan disjointness does NOT
imply disjointness of the terminal paths (which can even be the same path).
The arbitrary-degree all-odd theorem and independent selective-compression
bridge remain unproved.  See the latest ResearchNotes entry for exact scope.
Original Spec remains unchanged and UNSOLVED.  No original settlement submitted.

## Superseding update: simultaneous fan REASSEMBLY is now checked

EndpointFanRotation, EndpointFamilyRotation, EndpointFanAccounting,
TwoEndpointFanRotation, FanCycleAbsorption and FanCycleMaximality all compile.
The earlier reassembly gap is closed: two distinct unused neighbors give an
actual rotated family with exact edge/end-point defects and no repeated edges.
If the terminal paths are vertex-disjoint, this absorbs the old unused cycle.
Consequently every unused-cycle vertex has two escaping endpoint paths that
meet at some other vertex.  They may still be the same path.

Remaining: handle these intersecting terminal paths with a terminating
augmentation.  No arbitrary-degree all-odd theorem or valid selective
compression bridge has been proved.  Original Spec remains UNSOLVED.

## Superseding update: one-clean-endpoint absorption is now checked

OneEndpointFanRotation, OneFanCycleAbsorption, EndpointOwnedCycleContact compile
with permitted axiom audits. One packed endpoint path meeting an unused cycle
only at that endpoint now gives an ACTUAL augmentation, without any restriction
on intersections with the escaping terminal path outside the cycle. Hence some
cycle vertex's own endpoint path has an internal cycle contact. This strengthens
the arbitrary-path internal-contact obstruction, but does not eliminate it.
The general terminating augmentation and independent original O(n) bridge remain
UNPROVED. Spec is unchanged and UNSOLVED; no settlement submitted.

## New checked moves: terminal coincidence and arbitrary intersections

SameTerminalCycleRelocation constructs an actual new packing plus one unused
cycle when the two terminal endpoints belong to one path. A maximal packing
forces the new cycle to be at least as long as the old one; no termination
claim follows. Its global alternative separates this from DISTINCT intersecting
terminal paths.

IntersectingTerminalExchange handles the distinct case by joining and bypassing.
It restores endpoint uniqueness and edge-disjointness in an actual new family,
with loss bounded by the two terminal path lengths. Maximality implies
|old cycle| <= |first path| + |second path| + 1. Bypassed edges are NOT asserted
to form a single cycle. Arbitrary full absorption and a strictly improving
measure remain missing, as does the independent original O(n) bridge.
Spec is still unchanged and UNSOLVED. No settlement has been submitted.

## Caution: a nondecreasing two-fan-only algorithm is now refuted

FanRelocationTrap is checked: a six-vertex all-odd graph has an admissible
nine-edge packing with an unused triangle and an explicit twelve-edge full
packing. At each triangle vertex, both fan terminals belong to one length-three
path; same-path relocation creates a five-cycle and leaves only seven covered
edges. All paths are dirty on the original triangle. Thus the current local
moves do not themselves give a nondecreasing algorithm from arbitrary packings.
This does NOT refute arguments starting with global Maximal L: the example is
explicitly not maximal. RelocationMaximality separately proves that an exact
one-cycle relocation retains maximality iff cycle lengths agree.
Additional exchanges or a different extremal argument are still necessary.
Original conjecture remains UNSOLVED, Spec unchanged, no settlement submitted.

## Superseding: arbitrary-degree all-odd path decomposition VERIFIED

AllOddPaths.all_odd_path_partition is now checked with permitted axioms.
The endpoint-defect argument in EndpointDefectAbsorption removes every unused
cycle from a globally maximal endpoint packing, without degree restrictions.
OccurrenceFanBranches through EndpointDefectStep provide the actual rotations
and exact accounting, selecting one occurrence of any repeated endpoint label.
See latest ResearchNotes. The original O(n) cycle-and-edge bridge remains open;
Spec is unchanged and UNSOLVED. No original settlement submission.

## Superseding: full terminal NestedAlongEdges bound VERIFIED

UniversalBound.universal_bound proves number(G)<=3*(|V|-1) for any graph with a
universal vertex, via parity forest correction and explicit charging of one
leaf path. NestedBound.nested_bound proves number(G)<=3*|V| for every terminal
NestedAlongEdges graph. The even cases have the sharper factor 1/2.
PrescribedEndpointPaths.complete additionally generalizes all-odd absorption
from unique endpoints to any realizable positive endpoint multiset.

Thus the path theorem AND terminal bound are closed. The independent selective
compression / global reduction remains UNPROVED. The old universal adjacent
Minimal compression hypothesis is FALSE; do not use it. Spec unchanged and
UNSOLVED. All new principal axiom audits use only the permitted axioms.

## Secondary-optimal induced singleton forest VERIFIED

SingletonCycleExchange and OptimalSingletonForest now prove existence of an
optimal even/singleton split minimizing the singleton count, and that each
component of its singleton forest is induced in G. Exact finite testing (NOT
Lean proof) found no failure of full compression along such singleton edges up
to 8 vertices, but the general rule remains UNPROVED. The one-private-edge
variant, even with a degree-increasing direction, has a pendant-padding
counterexample described in ResearchNotes; do not use it universally on Minimal
G. An independent terminal bound for dominated singleton-star configurations
also remains unproved. Original Spec unchanged and UNSOLVED.

## Superseding: even the nonedge spanning-tree fixed-pair rule has an obstruction

The restricted absorption proposal at the end of the previous continuation
is false. A41-vertex gadget construction makes every demand a host nonedge,
keeps the demand graph a spanning tree, and supplies an initial routing with
an unused triangle, but saturated vertices prevent any full fixed-pair routing.
See the final ResearchNotes entry and /tmp/disjoint_tree_gadget_obstruction.py.
This is mathematical reasoning and an exact external diagnostic, NOT a Lean
proof or an original Erdős184 disproof. Spec remains unchanged and UNSOLVED.

## New verified auxiliary reductions: MaximizerReachability and AcyclicDeletion

Hull-maximizing subgraphs preserve all reachability. A cycle deletion from a
globally minimal graph therefore admits a minimal-core descent with unit loss
and unchanged reachability. Separately, deleting any forest from an even graph
cannot decrease its decomposition number; hence even G satisfies
number(G)<=number(G-v). The latter residual is generally NOT even, so this
cannot be iterated for free. Both modules compile with permitted axiom audits.
Neither supplies the original linear bound. Spec remains unchanged and UNSOLVED.

## New checked auxiliary inequality: ParityForestDeletion

A parity correction T contained in a deleted forest M gives
number(G)<=number(G-M)+|E(T)|, provided G-T is even. The optimal-singleton
forest case follows. This does not bound accumulated correction costs.
An odd-neighbor-count-only vertex deletion rule is false for subdivided stars.
The dominated Best-leaf and selective compression gaps remain unproved.
Original Spec is unchanged and UNSOLVED; no settlement submitted.

## New checked result: general endpoint-bounded path decomposition

BoundedEndpointPaths.exact_endpoint_partition now supplies one endpoint at
odd vertices, two at supported even vertices, none at isolated vertices,
and at most n simple paths. This does not bound the number of cycles and
single edges needed after converting those paths.

A stronger tree-hitting cycle-decomposition hypothesis was considered and
externally tested through order8 without a counterexample. It remains wholly
UNPROVED. Closed-trail refinement can create tree-free cycles; no argument
controlling them was found. See ResearchNotes for test scope and a new small
obstruction to unrestricted fixed-pair spanning-PATH absorption.
Original Spec unchanged and UNSOLVED; no settlement submitted.

## Superseding: connected separating-core transport VERIFIED

NonseparatingEdgeConnectivity proves that an even graph with no separating
cycle retains all reachability after any three-edge deletion. ComponentSeparatingCores
now proves even-minimality and nonseparation pass to component graphs, using
SpanningEvenCoreTransport for removal of isolated ambient vertices. Thus the
sufficient hypothesis may be restricted to connected nonempty even-minimal
cores. ConnectedCoreObstruction packages original failure into a connected,
4-edge-connected such core with number>=4. The structural hypothesis is still
UNPROVED; this is not a settlement. Spec unchanged, audits permitted.

## New quantitative nonseparating-core reduction VERIFIED

NonseparatingCoreBudget proves that a linear bound on connected nonseparating
even-minimal graphs alone suffices. Under original failure, that restricted
class has unbounded number/order ratio (and is 4-edge-connected). This does
not supply the missing bound or a counterexample. See ResearchNotes for exact
statements and audit logs. Original Spec remains unchanged and UNSOLVED.

## Stronger simultaneous obstruction VERIFIED

HighDegreeNonseparatingBudget combines separating-cycle credit with low-degree
cycle pruning. Original failure forces, for every B, a connected nonseparating
even-minimal graph with number>B*order AND every degree>4B+2. The terminal
high-degree estimate is still unproved; this is not a contradiction or an
original counterexample. Spec remains unchanged and UNSOLVED.

## Actual square extraction VERIFIED; discard charge remains unresolved

SquareExtractionAccounting now constructs the extraction, rather than assuming
its endpoint conditions. For even G it gives even discarded J<=G with
number(G)<=15*n+5*number(J) and |E(J)|+4*number(G)<=|E(G)|+24*n.
For even-minimal G above 6*n it gives a strictly smaller even-minimal core
with the same inequalities. All three axiom audits are permitted. The factor
five prevents an immediate linear induction; no uniform discard budget or
square-accessibility theorem is proved. Spec remains unchanged/UNSOLVED.

## New exact-dual criterion and infinite-family distinction VERIFIED

OptimalRemainderDualCriterion proves that SOME dual-exact Optimal remainder on
every globally Minimal graph would suffice for the original, with constant3.
The existence hypothesis is still unproved. ThreeHubOptimalRemainders proves
it for K_(3,3q+1), while every Optimal remainder for q>=3 fails EvenMinimal,
CycleCritical and CycleRigid. Thus remainder exactness is genuinely distinct
from those false inheritance shortcuts. Catalogue evidence is finite only;
see ResearchNotes. Original Spec remains unchanged and UNSOLVED.
