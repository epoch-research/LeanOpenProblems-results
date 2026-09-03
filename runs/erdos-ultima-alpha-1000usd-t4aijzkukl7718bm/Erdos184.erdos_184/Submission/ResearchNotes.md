# Latest continuation: extracted kernels and efficient labelled-cycle certificates

The original Spec.lean is STILL UNSOLVED and unchanged. An incomplete submission
was made and was rejected by verification; the user explicitly requested continued
work. No proof/disproof has been obtained. Do NOT resubmit the retained sorry.

New checked modules, all with current oleans and permitted axiom lists:

- JunctionLayout.lean: `Junction`, `LocalJunction`, `localJunctionEquiv`;
  `exists_junction_layout` and `exists_junction_kernel` extract the actual shared
  vertices of an arbitrary covering cycle family, provided each piece has at least
  two contacts. Cyclic order is not assumed. Check: /tmp/junction-layout-check2.log.
- CoreJunctionKernel.lean: `contacts_of_triple_bounds`, `walks_of_cycle_family`,
  `junction_card_of_family`, `three_core_junction_family`. A hypothetical nonrigid
  minimal core of optimum three has a covering indexed maximum cycle family to
  which the preceding extraction applies. Check: /tmp/core-junction-kernel-check3.log.
- ColoredKernel.lean: `Family.colorLabels_valid`, `color_number_iff`, and
  `color_maximum_bound_iff`. These transfer exact minimum counts and maximum bounds
  for EVERY original color subfamily. Check: /tmp/colored-kernel-check4.log.
- ThreeKernelReduction.lean: `family_restrictions`, `exists_kernel`. All full-core
  minimality/nonrigidity and all color-subfamily maximum bounds are transported;
  every three-color union has a partition of at most two circuits. This is an
  actual reduction to kernels, NOT a proof excluding them.
  Check: /tmp/three-kernel-reduction-check4.log.
- JunctionCounts.lean: general local junction bound b*(|K|-1), exact double-counting
  when every junction lies on two pieces; `maximum_junction_bounds` gives at most
  l*(l-1) junctions and at most 2*(l-1) markers per cycle in a degree-at-most-four
  maximum family of l cycles. Check: /tmp/junction-counts-check3.log.
- LabelCycle.lean: `LabelKernel.Cycle` lists distinct labels and junctions around
  a cycle, allowing parallel-edge circuits of length two. `Cycle.circuit` proves
  the code-circuit property directly via parity propagation, without enumerating
  all subsets. Check: /tmp/label-cycle-check2.log.
- LabelCycleCertificates.lean: computable `CycleData`, `PartitionData`, with
  decidable `Valid` predicates and `PartitionData.exists_partition` preserving
  exact cardinality. This permits polynomial-size finite certificates checked by
  ordinary decide. Check: /tmp/label-cycle-certificates-check2.log.
- SixKernelCertificates.lean: compact kernel-level versions of the thirteen
  existing two-cycle certificates. It compiled in 23 seconds, with allowed axioms.
  NO completeness assertion. Generator /tmp/generate_six_kernel_certificates.py;
  check /tmp/six-kernel-certificates-check.log.
- LabelKernelEmbedding.lean: injective edge/vertex relabelling with unordered
  endpoints (permits orientation reversals and extra isolated junctions).
  `valid_map`, `hasNumber_map_iff`, `minimalCore_map_iff`, `rigid_map_iff`, and
  `upper_bound_map_iff`. Check: /tmp/label-kernel-embedding-check3.log.

Combined audit through the cycle certificate interface:
/tmp/axiom-check-continuation8.log. The last two modules have their own clean audits.

Pending check: SmallOrderNormalization.lean uses ordinary decide to verify
normalization of Marked.Order n for n=0,...,5 (two through seven markers).
It starts at marker zero and chooses the orientation whose next marker is smaller
than its previous marker. A `CycleData` also records the corresponding edge-label
permutation. Its build log/exit are /tmp/small-order-normalization-check.log and
/tmp/small-order-normalization-check.exit; this was running at this note update.

Technical notes:
- Use `noncomputable local instance : DecidableEq (Sigma i, Fin (m i)) :=
  Classical.decEq _` for predicates that must match the existing path-family
  transport. The default Sigma DecidableEq otherwise differs definitionally.
- Explicit @LabelKernel.code with classical edge/junction instances is useful
  inside nested existential kernel statements.
- `minimal_expandGraph_iff` has `(EvenMinimal graph AND number graph=k)` on its
  left, not the reversed conjunction.
- Rewrite a dependent graph parameter BEFORE introducing its decomposition.
- `Nat.card_coe_set_eq`, `Set.ncard_eq_toFinset_card'`, and normalization of
  Fintype.card via Nat.card resolve the remaining finite-instance mismatches.
- The map-then-biUnion lemma is `Finset.image_biUnion`, not `biUnion_image`.
- For Prop-valued certificate predicates defined as conjunctions, use qualified
  lemma names (`CycleData.circuit h`), not `h.circuit` dot notation.

Still missing: the higher-layout completeness/exclusion proofs, and—independently—
the unconditional arbitrary-core bound needed by the ORIGINAL conjecture. The
additional mathematical reconsideration of core shelling, one-cycle augmentation,
and additive rank-sized fractional rounding produced no new general theorem.

# Latest checked generic contact-kernel and partition correspondence

Spec.lean is still unchanged and UNSOLVED. The following close infrastructure
steps only, not any higher-layout completeness or unconditional core bound.

- ContactKernel.lean compiles (/tmp/contact-kernel-check.log). It proves
  ContactLayout.exists_ordered_family: arbitrary contact layouts admit the
  recursively encoded directed cyclic orders and a covering path Family,
  with exact edge coverage for each original cycle. Family.expandGraph_colorLabels
  identifies every union of original cycles with its expanded label set.
- PathKernelPartitions.lean now compiles
  (/tmp/path-kernel-partitions-check2.log). Its three Family results transport
  partitions in both directions with exact cardinality and prove
  kernel_upper_bound_iff for MAXIMUM partition bounds. The graph-code helper
  GraphCircuitCode.decomposition_of_partition constructs the corresponding
  graph decomposition from a circuit-code partition.
- The only pending compile issue was a missing `include hcover`: section
  hypotheses occurring only in proofs are otherwise omitted by Lean.
- Principal axiom lists contain only propext, Classical.choice, Quot.sound.

# Current continuation: core-rounding investigation (still unresolved)

## Arbitrary marked-cycle segmentation and numeric triple restrictions checked

Spec.lean remains unchanged and UNSOLVED. New current oleans:

- MaximumTriplePatterns.lean (DoubleTripleContacts, CycleContactLower):
  AdmissibleTriple a b c means each <=2, every pair-sum >=2, and not all two.
  admissible_triple_cases gives exactly the all-positive (not222) patterns
  or a permutation of (0,2,2). three_piece_contacts_sum proves the pair-sum
  lower bound without needing disjoint contact sets. maximum_triple_admissible
  proves these numerical restrictions for any triple in a maximum cycle
  family of maximum degree<=4 whose triple union has number<=2.
  three_core_admissible_family packages this for an EXPLICIT hypothetical
  nonrigid minimal core of number three. No exclusion theorem yet.
  /tmp/maximum-triple-patterns-final.log, exit 0.

- MarkedCycleSegmentation.lean (FourPointSegmentation): general source-indexed
  Segmentation.splice inserts a new marker on a selected path.
  Marker 0=Fin2; Marker(n+1)=Marker n+Unit.
  Order 0=Unit; Order(n+1)=Order n*Marker n.
  next n o is a COMPUTABLE successor map produced by recursive insertions.
  Marker n has n+2 elements; Order n has (n+1)! elements.
  Marked.exists_segmentation proves every injectively marked cycle is
  segmented in one of these finitely encoded directed cyclic orders.
  No rigidity, max/min count, or restricted number of markers is assumed.
  /tmp/marked-cycle-segmentation-check3.log, exit 0.

- NumberedCycleSegmentation.lean (MarkedCycleSegmentation):
  Segmentation.reindex; computable markerEquiv : Marker n equiv Fin(n+2);
  nextFin n o; nextFin_ne;
  exists_numbered_segmentation for ANY Fin(n+2)-indexed junction list.
  /tmp/numbered-cycle-segmentation-check2.log, exit 0.

All principal axiom lists are the permitted three. These close the generic
segmentation gap for higher-order finite layouts; no four-/five-/six-/seven-
layout completeness theorem has been formalized yet.

The recursive order encoding retains both orientations (unlike the earlier
Python orders(), which quotiented reversal). For m junctions it has (m-1)!
orders, versus (m-1)!/2 canonical undirected ones. Its labels are FIXED junction
indices, with src=id and dst=nextFin, not positions in a cyclic vertex list.
A finite normalization/reindexing can connect it to earlier canonical tables.

Next useful step: generic assembly of ContactLayout with these arbitrary
segmentations, preserving exact per-color edge coverage. Then use kernel
transport to express local min/max constraints as finite code predicates.
The four-/five-/six-/seven-layout tables still require genuine completeness
verification; even completing number-three core rigidity will not alone
settle the arbitrary-core degree/edge bound needed for the original theorem.

Lean notes: splice must define copied walks explicitly, then compare EDGES
and IsPath after copies; raw equality of differently indexed walks is ill-typed.
Use explicit (henew u) in rewrites. For dependent walk edges, reindexing uses
congrArg (fun i => (S.path i).edges) (e.apply_symm_apply i), not simp alone.
Marker 0 does not synthesize OfNat through its definition: annotate (0:Fin2).
Nat.factorial_succ must be given (n+1) explicitly when rewriting the RHS.

## New general path-kernel transport and exact nonalternating-220 exclusion

The original conjecture remains UNSOLVED, Spec.lean unchanged. All modules
below have current oleans and successful standalone checks with only the
allowed three axioms. These complete the local (2,2,0) order restriction and
supply a general exact path-substitution transport, not core rigidity.

Dependency chain and checks:

1. PathSeries.lean (RigidityDegree): even_at_of_elsewhere;
   path_start_degree; even_path_subgraph_bot (walk induction);
   path_internal_even; path_subgraph_all_or_none. A subgraph of a simple path
   even at all internal vertices is either empty or the whole path.
   /tmp/path-series-check2.log, exit 0.
2. PathSubstitutionProjection.lean (PathSeries): Family.internal_neighbors;
   even_subgraph_path_all_or_none; selectedLabels; mem_selectedLabels;
   even_subgraph_edges_iff and even_subgraph_edgeFinset. Requires coverage of
   the host graph by the path Family; every even subgraph selects whole paths.
   /tmp/path-substitution-projection-check2.log, exit 0.
3. PathKernel.lean (Projection): pieces, expandGraph, expandEdges;
   path_subgraph_injective; exact union/degree formulas; validLabels (even
   incidence at each junction); expandGraph_even_iff;
   selectedLabels_expandGraph; expandGraph_selectedLabels; injectivity.
   /tmp/path-kernel-check2.log, exit 0.
4. SupportTransport.lean (SerialMinimum), namespace Erdos184Serial:
   abstract support expansion preserving empty, union, order, disjointness,
   validity, and lifting valid subwords. Proves circuit_iff, partition transport
   with exact cardinality, hasNumber_iff, rigid_iff, minimalCore_iff.
   /tmp/support-transport-check2.log, exit 0.
5. PathKernelTransport.lean (PathKernel, GraphCircuitCode, SupportTransport):
   COMPUTABLE LabelKernel.valid / LabelKernel.code from src,dst; instance
   Family.supportTransport; exact kernel count/minimality/rigidity equivalences.
   Principal graph-facing statements: number_expandGraph_iff,
   minimal_expandGraph_iff, rigid_expandGraph_iff, expandGraph_univ,
   number_iff_kernel_full. /tmp/path-kernel-transport-final2.log and .exit=0.
   The earlier final.log is a failed check; use final2.
6. KernelMarker.lean: Partition.marker_count, rigid_of_marker,
   hasNumber_of_rigid. NonAlternate220 kernel on Fin8 labels / Fin4 junctions:
   first circle 0-1-2-3-0, the other two parallel-path circles 0-1-0 and 2-3-2.
   Markers {0,2,4,5,6,7}; every circuit has exactly two markers (ordinary decide).
   full_rigid and full_number =3. /tmp/kernel-marker-check2.log, exit 0.
7. NonAlternate220Lift.lean: full_valid_any and full_number_any normalize
   DecidableEq instances; subdivision_number_three for an arbitrary Family
   realizing that kernel. /tmp/nonalternate220-lift-check2.log, exit 0.
8. NonAlternate220Assembly.lean: sizes [4,2,2], canonical contact layout,
   assembled_number_three and contact_number_three; marker swap 2<->3;
   alternating_segmentation_of_number_le_two. For a (2,2,0) contact layout
   whose union has number<=2, the four contacts on the first cycle can be
   segmented ONLY in the alternating order [0,2,1,3]. No rigidity assumed.
   /tmp/nonalternate220-assembly-check3.log, exit 0.

Operational notes from these modules:
- Finset.card_biUnion accepts Set.PairwiseDisjoint on the indexing finset.
- Finset.biUnion_inter exists; filter_sdiff does not (prove by ext/simp).
- SimpleGraph.degree_le_of_le takes v implicitly; use (v := u).
- Use degree_eq_zero_iff_notMem_support (not degree_eq_zero_iff).
- Kernel valid/circuit decidability must be supplied by unfolding the code and
  infer_instance. Finite circuit-marker checking on 8 labels is inexpensive.
- To transfer a computed code theorem to classical DecidableEq instances,
  quantify explicitly over i8/i4 and substitute Subsingleton.elim equalities
  to instDecidableEqFin 8/4. See full_number_any.
- Keep Family transport definitions on classical DecidableEq instances; mixing
  explicit host instances caused defeq errors in toFinset/biUnion. Computable
  LabelKernel.code itself remains parametrized by arbitrary DecidableEq.
- Fin literals of dependent Fin(sizes k) in location tables need explicit
  constructors <value, by decide>. After fin_cases, change the concrete
  Segmentation target before rewriting its vertex map.

## Maximum switching now verified without rigidity

MaximumSwitching.lean imports MaximumCoreFamilies and compiles cleanly
(/tmp/maximum-switching-check.log, exit 0, current olean). New results:

- indexed_maximum_of_bound: an indexed family covering a graph and a matching
  upper bound on all cycle-partition cardinalities yields IsMaximum.
- IsMaximum.no_three_common_vertices: the pair-intersection bound in walk form.
- maximum_arc_contact_subsingleton and maximum_contacts_alternate: in a union
  of three cycles for which every cycle partition has at most three pieces,
  if the first two cycles meet at exactly two switching vertices and the third
  avoids those vertices but meets the second, its two contacts with the first
  must lie on opposite arcs. This uses a count-preserving two-cycle switch
  and the maximum pair-intersection bound, NOT a rigidity hypothesis.

This verifies the order restriction for the two-double/one-single triple
pattern. The disjoint-end pattern (2,2,0) needs a different minimum-count
argument: nonalternation has exact minimum three, whereas alternation has
minimum two. That lower bound for arbitrary path substitutions is still
unformalized.

Finite triple spectra were rechecked from the established exact enumerator:
111: one order, spectrum (2,3).
211: one order, spectrum (2,3).
221: three orders, nonalternating two have (2,4), alternating one has (2,3).
220: three orders, nonalternating two have (3,3), alternating one has (2,3).
222: 23 orders (2,4), four orders (3,5).
These spectrum computations are NOT themselves Lean theorems; the new
maximum-switching and doubled-triple results prove the stated restrictions
without relying on trusting the computations.

## New checked unrestricted segmentation and doubled-contact exclusion

Spec.lean remains unchanged and UNSOLVED. The new modules below close the
specific generic-extraction gap for doubled-contact triples, not the
arbitrary-core or optimum-three-core rigidity problem.

- FourPointSegmentation.lean (imports RigidityDegree): canonical path splitting
  with support coverage; PathThirds in either marker order; arbitrary cycle
  segmentation into four paths in one of the three cyclic orders up to reversal.
  four_segments_orders_any does NOT assume rigidity. Build
  /tmp/four-point-segmentation-check2.log, exit 0, current olean.
- DoubleTripleAssembly.lean: uniform Fin 27 certificate tables, the explicit
  location reindexing, and contact_at_least_four. Arbitrary cycle lengths and
  all cyclic orders of the six prescribed junctions are now handled. Build
  /tmp/double-triple-assembly-check.log, exit 0, current olean.
  Generator /tmp/generate_double_triple_assembly.py.
- DoubleTripleContacts.lean: six_contact_vertices extracts the junction list
  from pair-contact cardinalities two and empty triple intersection.
  two_contacts_at_least_four constructs a >=4-piece cycle partition of the
  three-cycle union. maximum_three_pieces_double_contacts says three pieces
  in a MAXIMUM cycle decomposition meeting pairwise in exactly two vertices
  must share a common vertex. maximum_three_pieces_four_degree excludes such
  a triple entirely when the ambient graph has maximum degree <=4. This last
  result applies in particular to hypothetical nonrigid optimum-three cores.
  Build /tmp/double-triple-contacts-final.log and .exit=0, current olean.

The final theorem axiom audits use only propext, Classical.choice, Quot.sound.
The new finite certificates are now connected to a genuine unrestricted
structural graph statement. The remaining higher-layout completeness steps
and the general linear-bound bottleneck are still unproved.

## Continuation audit: latest results confirmed

Spec.lean is STILL UNRESOLVED and unchanged. The 27 theorems in
DoubleTripleCertificates.lean compiled successfully; the final log is
/tmp/double-triple-certificates-check2.log (exit 0), with only the allowed
three axioms. They cover the 27 cyclic-order kernels for a triple of cycles
with two separate contacts per pair. Layout extraction is not yet proved.

CoreBlockReduction.lean now proves least-optimum hypothetical nonrigid
minimal cores are vertex-irreducible and branch-cut-irreducible. In particular
this holds for hypothetical nonrigid cores of optimum three. The theorem
exists_irreducible_block_of_nonrigid_core is CONDITIONAL on such a core
existing, not an assertion of existence or an exclusion theorem. Build:
/tmp/core-block-reduction-check2.log, exit 0.

CycleContactLower.lean proves one-vertex leaf-piece additivity and
two_contacts_of_number_le_two: in a family of at least three edge-disjoint
cycles whose union has optimum at most two, each piece has at least two
contacts with the rest. Build /tmp/cycle-contact-lower-check2.log, exit 0.

The exact finite regular-four experiment finished through n=15:
/tmp/regular4-disjoint3.log, exit 0. All three four-edge-connected graphs
at n=15 without a two-Hamilton-cycle decomposition have three
vertex-disjoint cycles. All other such failures through n=15 have a two-edge
cut. This does NOT prove the proposed general shortcut.


## Latest continuation: checked finite certificates and one-vertex separation

The original conjecture is STILL UNSOLVED. Spec.lean has not been changed.

New checked Lean modules (all principal axiom lists contain only propext,
Classical.choice, Quot.sound):

- CyclePartitionLift.lean (imports RigidityDegree): Family.Circuit packages a
  realized cycle and its exact path labels; ofModel and ofParallel constructors;
  decomposition and number_le lift labelled partitions with exact cardinality.
  ofParallel works even if a path has no private internal vertex.
  /tmp/cycle-partition-lift-final.log, .exit=0; current olean.

- SixCycleCertificates.lean: thirteen independently kernel-checked two-cycle
  witnesses, each for arbitrary internally disjoint path substitutions of the
  representative's 30-edge / 15-junction kernel. No completeness assertion.
  Generator /tmp/generate_six_cycle_certificates.py; witness data
  /tmp/six-cycle-hamilton-certificates.json. Compile log
  /tmp/six-cycle-certificates-check.log, .exit=0; current olean.

- SixCycleCertificateFamily.lean: finite-index (Fin 13) interface via
  sourceTable/targetTable and subdivision_number_le_two. No claim that arbitrary
  layouts belong to this list. /tmp/six-cycle-certificate-family-check.log,
  .exit=0; current olean.

- MaximumCoreFamilies.lean: IsMaximum; existence of a maximum cycle-only
  decomposition; maximum subfamilies remain maximum; subfamily rigidity iff
  number equals displayed cardinality; strict core-number bound for proper
  subfamilies; incidence count and degree<=4 in nonrigid cores of optimum three.
  three_core_maximum_family gives, under an EXPLICIT hypothetical nonrigid
  minimal core of optimum three, a maximum partition with >3 pieces, pairwise
  contacts <=2, at most two pieces through any vertex, and every triple union
  of number <=2. Does NOT exclude those conditions.
  /tmp/maximum-core-families-final.log, .exit=0; current olean.

- CircuitSeparation.lean (imports SerialMinimum): Separation requires disjoint
  coordinate supports and independent validity. Partition filtering/splitting;
  HasNumber additivity; MinimalCore and Rigid iff both factors; nonrigid minimal
  factor theorem. Full validity is included where needed: abstract Code itself
  does NOT assume closure under disjoint union.
  /tmp/circuit-separation-final.log, .exit=0; current olean.

- GraphVertexSeparation.lean (imports GraphCircuitCode, CircuitSeparation):
  TouchAt A B v says supports meet only at v. Parity, code_separation,
  number_sup = number A + number B, minimal_sup_iff, rigid_sup_iff,
  nonrigid_minimal_sup_factor. Exact graph one-vertex gluing, no new axioms.
  /tmp/graph-vertex-separation-check3.log, .exit=0; current olean.
  Earlier check/check2 logs contain failed attempts; use check3.

New finite orbit counts (not Lean-verified completeness): the 217 four-cycle
maximum-four records form 9 layout orbits; the 656 five-cycle maximum-five
records (for the displayed representative multiplicity patterns) form 32
layout orbits. Data: /tmp/4-layout-orbits.json, /tmp/5-layout-orbits.json.

Internet check: ordinary DNS unavailable; direct DNS-over-HTTPS to 1.1.1.1
and 8.8.8.8 also timed out. No later literature result was retrieved.

## Latest continuation: six- and seven-cycle local-layout checks (experimental)

Spec.lean is still unchanged and UNSOLVED. No finite experiment below is a
Lean theorem, a proof of core rigidity, or a settlement of Erdős 184.

Six-cycle layouts passing every maximum-five local filter:
- 276,744 representations; each has an independently checked decomposition
  into two Hamilton cycles. No proper-even-support audit was done at this size.
- Canonicalizing underlying graphs gave 710 graph isotypes. Exact circuit
  spectrum DP gave maximum counts 6, 7, or 8. Exactly 7,284 representations
  have maximum six, all in the all-single-contact pattern.
- Canonicalizing the displayed six-cycle layouts gave 13 layout orbits.

Artifacts: /tmp/six-cycle-records.jsonl, /tmp/six-cycle-isotypes.json,
/tmp/six-cycle-spectra.json, /tmp/six-cycle-max6.jsonl,
/tmp/six-layout-orbits.json. Spectrum and orbit scripts exited 0.

Seven-cycle check /tmp/seven_cycle_local.py now completed (exit 0):
- 13 prefix layout orbits, each extended by inserting six new junctions.
- All-single-contact case: 203,125 prefix extension tuples tried, ZERO
  extensions pass all six-subfamily maximum-six filters.
- One-/two-double cases have no admissible maximum-six prefix.
- Thus the script never needed its Hamilton-decomposition server. The output
  /tmp/seven-cycle-records.jsonl is empty; there was no no-Hamilton candidate.
- Log: /tmp/seven-cycle-local.log, exit: /tmp/seven-cycle-local.exit.

Scope warning: admissibility comes from prior finite kernel enumerations.
Extraction of arbitrary graph layouts into these kernels is not formalized;
local-to-global rigidity and bounds for arbitrary optimum counts remain open.
The result does not alone imply a linear cycle decomposition bound.

## Latest continuation: quantitative irreducible-core reduction checked

The original conjecture remains UNSOLVED; Spec.lean is unchanged and still
has its original sorry. No proof/disproof has been submitted.

New checked module: `Submission/IrreducibleBound.lean`, importing
GraphCoreIrreducible. Namespace `Erdos184Work.IrreducibleBound`. It has a
current olean; `/tmp/irreducible-bound-check.log` and `.exit` (0). All printed
axiom lists are only propext, Classical.choice, Quot.sound.

Definitions and lemmas:
- `branches_le_card`.
- `cut_of_not_irreducible`: failure of BranchCutIrreducible supplies a two-edge
  cut with a branch vertex on each side.
- `closures_branch_sum`, `closure_sizes`, `closures_branches_pos`:
  branch counts add, and fresh-closure vertex counts total n+4.
- `potential G := card V + 4 * branches G - 4`.
- `potential_add`: this potential is exactly additive across a two-edge cut
  when both closure factors have positive branch counts.
- `minimal_potential_bound`: under a uniform bound k<=C*n on irreducible
  minimal EVEN cores, every minimal even core with positive branch count
  satisfies k<=C*potential+1. Strong induction is on branch count; the
  identity k(join)=k(left)+k(right)-1 cancels the two additive ones.
- `minimal_linear_bound` and `even_linear_bound`: for 1<=C, the same
  irreducible-core hypothesis gives k<=5*C*n for ALL even graphs.
- `asymptotic_of_irreducible_core_bound`: that hypothesis suffices for the
  original asymptotic cycle-and-edge proposition via the checked even-graph
  reduction. The factor-five assertion above concerns EVEN cycle counts;
  the final mixed-graph statement merely asserts existence of the O(n) f.

IMPORTANT: the bound on branch-cut-irreducible minimal cores is an EXPLICIT
UNPROVED HYPOTHESIS, not a new axiom and not a proved structural fact. The
conjecture is not settled by this conditional theorem. The closure overhead
is now controlled quantitatively, so a full rigidity theorem would be stronger
than necessary: a uniform linear bound just on these irreducible cores suffices.

Audit: `Submission/AxiomCheckIrreducibleBound.lean`,
`/tmp/axiom-irreducible-bound.log` / `.exit`.

The irreducible-core structural step was reconsidered but not proved. Do not
assume irreducible cores have a feedback vertex: even rigid cores joined at
articulation vertices can have no branch-separating two-edge cut and no single
feedback vertex. A block reduction would be needed before that stronger
structural proposal. Nor can cycle number be bounded by branch count alone:
K_(2,2k) is a rigid minimal core with only two branch vertices and optimum k.
No new exploratory numerical search was run in this continuation.

## Latest continuation: subdivision and GENERAL two-edge-cut reductions checked

The original Erdős 184 proposition is STILL UNSOLVED. Spec.lean is unchanged
(SHA256 509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5)
and retains its original sorry. No proof/disproof was submitted.

The previous scope limitation concerning parallel virtual closure edges and
coincident endpoints is now resolved by fresh-vertex closures. All modules
listed below compile, have current oleans, and the combined axiom audit is
clean (only propext, Classical.choice, Quot.sound).

New checked modules, dependency order:

1. `PointCode.lean` (imports SerialMinimum), namespace Erdos184Serial:
   `pointCode` on Unit, all subsets valid; `point_circuit_iff`,
   `point_partition_eq`, `point_hasNumber`, `point_rigid`, `point_minimalCore`.
   This supplies the second factor of a one-coordinate series extension.

2. `GraphSubdivision.lean` (imports GraphSerialTheory and PointCode),
   namespace Erdos184Work.GraphSubdivision:
   `split G t a b : SimpleGraph (V ⊕ Unit)` removes old port ab, adds a--new
   controlled by G.Adj a b and b--new controlled by () ∈ t. For a≠b,
   `even_split_iff` says it is even iff G is even AND the two controls match.
   All old-vertex degree formulas are proved by explicit neighbor finsets
   and handshaking, including parity in the converse direction.

3. `GraphSubdivisionEdges.lean`: injective `edgeMap` / `edgeEmbedding` on
   Sym2 V ⊕ Unit, replacing the old port by one half-edge and the extra
   coordinate by the other. `edgeFinset_split` is an exact edge-set identity.

4. `GraphSubdivisionTheory.lean`: `subdivide G a b`, a single subdivision
   of an actual edge (or an isolated added vertex if the edge is absent).
   - `serial_valid_iff`: the subdivided graph code is exactly the abstract
     serial code of code G and pointCode after edge relabeling.
   - `number_subdivide`, `minimal_subdivide_iff`, `rigid_subdivide_iff`:
     for EVEN G and a PRESENT port, count is unchanged and both core notions
     are equivalent. Do not state count invariance for arbitrary odd graphs.
   - `degree_subdivide_old`, `degree_subdivide_new`, `card_edges_subdivide`.
   - `subdivide_eq_split` is useful when an actual port edge is known.

5. `GraphIsoCore.lean`: `even_iso`, `minimal_iso_iff`, `rigid_iso_iff`.
   The last uses evenness of the source; the minimality equivalence itself
   does not require evenness. Number isomorphism invariance is the older
   `BlockRestriction.number_eq_of_iso` from Work.

6. `GraphTwoCut.lean`, namespace Erdos184Work.GraphTwoCut:
   - `join G H a b c d` joins sides by ac and bd.
   - `closure G a b : SimpleGraph (V ⊕ Bool)` adds fresh path
     a--false--true--b. If a=b, this is a triangle; old edge ab is allowed.
   - `expanded` subdivides each of the two cross-edges twice.
   - `expansionIso`: expanded is isomorphic to GraphSerial.switch of the
     two closures at their fresh false--true ports.
   The only distinctness hypothesis is `a ≠ b ∨ c ≠ d`, i.e. the two
   crossing edges are distinct. Either pair of endpoints may coincide.

7. `GraphTwoCutTheory.lean`:
   `closures_even`, `number_join`, `minimal_join_iff`, `rigid_join_iff`,
   `nonrigid_minimal_join_factor`. For even join and distinct crossing edges:
       number(join) = number(left closure)+number(right closure)-1;
       minimal(join) iff both closures minimal;
       rigid(join) iff both closures rigid.

8. `GraphCutPartition.lean`: `partitionIso` realizes an arbitrary partition
   S,Sᶜ as join of induced sides under the exact two-crossing-edge adjacency
   formula. Gives `number_two_edge_cut`, `minimal_two_edge_cut_iff`,
   `rigid_two_edge_cut_iff`, `nonrigid_minimal_two_edge_cut_factor`.

9. `GraphBranchCount.lean`, namespace Erdos184Work.GraphBranchCount:
   `branches G := ∑ v, if 2 < degree G v then 1 else 0`.
   `branches_iso`, `branches_split`, `branches_expanded` prove invariance;
   `branches_join` is ADDITIVE across the two fresh closures. Additional
   `closure_degree_left/right/new`, `branches_closure_left/right` identify
   old degrees with the original joined graph and new degrees with two.
   `nonrigid_minimal_join_smaller` gives strict branch-count descent if both
   sides have positive branch counts. It does not claim fewer raw vertices.

10. `GraphCutBranch.lean`:
    `crossPairs G S` is the finset of adjacent pairs in S × Sᶜ.
    `exists_cut_endpoints` extracts a,b,c,d from crossPairs.card=2.
    `partition_branches_left/right` identify branch counts on each side.
    `nonrigid_minimal_two_cut_smaller`: a nonrigid minimal even graph with
    a two-edge cut and a branch vertex on EACH side has a nonrigid minimal
    EVEN fresh closure with strictly fewer branch vertices.

11. `GraphCoreIrreducible.lean`:
    `BranchCutIrreducible G`: every two-edge cut has a side with all degrees≤2.
    `branchMinimal_irreducible`: global minimality of branch count among
    nonrigid minimal even cores implies this property.
    `exists_irreducible_of_nonrigid_core`: if any nonrigid minimal even core
    exists (in a fixed universe), one exists with BranchCutIrreducible.
    This is a CONDITIONAL existence reduction. It does not establish that
    such a core exists or is impossible. Connectedness is not asserted.

Final logs/exit files (0):
- /tmp/point-code-check
- /tmp/graph-subdivision-check
- /tmp/graph-subdivision-edges-check
- /tmp/graph-subdivision-theory-check
- /tmp/graph-iso-core-check
- /tmp/graph-two-cut-check
- /tmp/graph-two-cut-theory-check
- /tmp/graph-cut-partition-check
- /tmp/graph-branch-count-check2  (older similarly named logs contain failures)
- /tmp/graph-cut-branch-final     (older similarly named logs contain failures)
- /tmp/graph-core-irreducible-check
Each has `.log` and `.exit`.
Combined audit: `Submission/AxiomCheckTwoCut.lean`,
`/tmp/axiom-check-two-cut.log` and `.exit` (0). All printed dependencies clean.

New targeted exact obstruction, NOT Lean formalized:
`/tmp/splitting_all_vertices.py`, `/tmp/splitting-all-vertices.log`, exit 0.
For the Petersen line graph (15 vertices, optimum three), all SIXTY ways of
smoothing a vertex along two edges to NONADJACENT neighbors produce an even
simple graph whose degree-two suppression has two Hamilton cycles. Thus all
these smoothings lower the cycle optimum to two. Every vertex has degree four
and is nonsaturated. This refutes the unrestricted proposed rule that a
nonsaturated vertex always admits an optimum-nondecreasing SIMPLE smoothing.
The Petersen line graph is NOT minimal, so no core-restricted rule is refuted.
For adjacent-neighbor smoothings the script creates parallel edges and finds
no two-Hamilton decomposition; no exact larger optimum is asserted for those.

Next mathematical bottleneck: the branch-cut-irreducible core case remains
unproved. Neither core rigidity, a uniform core degree/edge-excess bound, nor
square accessibility follows from the new cut reductions. Do not present
these supporting theorems as a settlement or repeat the now-refuted
unrestricted smoothing argument. No computations or Lean builds remain active.

## Extension to disjoint contacts and five-cycle kernels (exact finite checks)

The original conjecture remains UNSOLVED; no new Lean proof is asserted here.

1. `/tmp/four_cycle_zero_kernels.py`, log
   `/tmp/four-cycle-zero-kernels.log`, exit file 0, allows pair-contact
   multiplicities 0, 1, or 2, with no triple contacts. Every triple is filtered
   to exact spectrum (2,3). There were 93,853 order tuples visited and 3,757
   survivors. Full spectra: (2,4): 217; (2,5): 3,080; (2,6): 460. No nonrigid
   minimal sub-support or cycle-critical/nonminimal sub-support was found.

2. `/tmp/four_cycle_local.py` saves all 217 maximum-four records to
   `/tmp/four-cycle-local-min3-max4.json` (the historical filename is misleading:
   these records have minimum TWO, not three). Their multiplicity patterns
   are: all pairs nonzero with at most two doubled pairs; or a doubled
   four-cycle with its two diagonal pairs absent. This is an exact finite
   observation, not a Lean classification theorem.

3. `/tmp/five_cycle_local.py`, log `/tmp/five-cycle-local.log`, completed all
   8,311 surviving five-cycle kernels. It restricts every four-cycle family
   to those 217 records. The five doubled-pair graphs tested, up to relabeling,
   were: empty, one edge, two disjoint edges, a two-edge path, and a two-edge
   path plus a disjoint edge. These are the five-vertex patterns suggested by
   the four-cycle constraints. All full-support minima were TWO. Counts by
   pattern, grouped by full maximum (5,6,7):
       empty:                    156,   87,  0
       one doubled pair:         396, 1530, 18
       two disjoint doubles:      24, 3184,104
       two adjacent doubles:      80, 1972,  0
       path plus disjoint edge:    0,  672, 88
   The exact DP also checked all even sub-supports of every survivor and
   found no nonrigid minimal core or cycle-critical/nonminimal support.

A second run `/tmp/five_cycle_max5.py` also completed normally, independently
repeating all 8,311 cases and recording exactly 656 maximum-five survivors in
`/tmp/five-cycle-max5.jsonl`; its log is `/tmp/five-cycle-max5.log`.
No experiments or proof builds are left running at this checkpoint.
The extraction of arbitrary graphical maximum decompositions into these
finite kernel layouts has NOT been formalized. Even such an extraction
would not settle cores with six or more pieces, let alone arbitrary optimum.
These checks must not be presented as a proof of core rigidity or Erdős 184.

## Latest exact four-cycle kernel experiment (completed; no obstruction)

`/tmp/four_cycle_kernels.py` completed with exit 0 in about ten seconds.
It considered four cycle pieces, pairwise contact multiplicities 1 or 2,
no triple contacts, and pruned every triple to spectrum (2,3). Of 85,834
cyclic-order tuples visited, 3,658 survived the filters. Their full-support
spectra were (2,4): 214, (2,5): 2,984, and (2,6): 460. None had a nonrigid
minimal even sub-support or a cycle-critical/nonminimal sub-support under
the exact circuit DP. `/tmp/four-cycle-min3-max4.json` is empty. This is a
finite filtered kernel experiment, NOT a classification of all graphs or
a proof of minimal-core rigidity. Spec.lean remains unresolved.

## Latest continuation: graphical serial-switch reduction is now checked

The original Erdős 184 proposition is STILL UNSOLVED. Spec.lean is unchanged
and still contains its original sorry; no proof/disproof has been submitted.

New checked modules (all have current oleans):

1. `GraphCircuitCode.lean` (imports RigidityDegree and SerialMinimum),
   namespace `Erdos184Work.GraphCircuitCode`:
   - `code G`: valid finite edge words are exactly even subgraphs of G.
   - `circuit_iff_number_one`, `circuit_piece`: its atoms are precisely simple
     cycle pieces (expressed through optimum one and connected 2-regularity).
   - `graph_cycle_partition`, `circuit_partition_graph`: conversion in both
     directions preserving the number of pieces.
   - `hasNumber_iff`, `minimalCore_iff`, `rigid_iff`, `nonrigid_minimal_iff`:
     exact agreement between the abstract and graphical notions.

2. `CircuitTransport.lean` (imports SerialMinimum), namespace Erdos184Serial:
   `circuit_map_iff`, `hasNumber_map_iff`, `minimalCore_map_iff`, `rigid_map_iff`
   for an injective coordinate map preserving validity. Transport back uses
   the fact that every piece lies inside the mapped full support.

3. `GraphSerial.lean` (imports GraphCircuitCode), namespace
   `Erdos184Work.GraphSerial`:
   `switch G H a b c d` removes port edges ab and cd in two disjoint vertex
   sets, replacing them by cross-edges (inl a,inr c) and (inl b,inr d).
   The first cross-edge is present iff ab was present in G; the second iff
   cd was present in H. `even_switch_iff` proves that the switched graph is
   even iff both factors are even AND both ports have matching membership.
   Degree formulas and the handshaking lemma prove this without assuming
   anything about minimality or cycle decomposition bounds.

4. `GraphSerialEdges.lean` (imports GraphSerial and CircuitTransport):
   `edgeEmbedding` explicitly relabels the retained port coordinates as the
   two cross-edges; `edgeFinset_switch` proves the exact edge-set identity.

5. `GraphSerialTheory.lean` (imports GraphSerialEdges):
   - `serial_valid_iff`: exact realization of the abstract serial code by
     this graphical switch, via the injective edge relabeling.
   - `number_switch`: for even factors with present ports,
       number(switch G H) = number G + number H - 1.
   - `minimal_switch_iff`: the switch is EvenMinimal iff both factors are.
   - `rigid_switch_iff`: the switch is CycleRigid iff both factors are.
   - `nonrigid_minimal_switch_factor` and
     `nonrigid_minimal_switch_smaller`: a nonrigid minimal switch has a
     nonrigid minimal factor, with strictly fewer vertices.

All final printed axiom lists are propext, Classical.choice, Quot.sound.
Logs/exit files (all exit 0):
`/tmp/graph-code-check`, `/tmp/circuit-transport-check`,
`/tmp/graph-serial-check`, `/tmp/graph-serial-edges-check`,
`/tmp/graph-serial-theory-check` (each with .log and .exit).
Final combined audit: `Submission/AxiomCheckGraphSerial.lean` and
`/tmp/axiom-graph-serial-check.log` / `.exit`.

Scope caution: this is an explicit simple-graph serial-switch theorem.
A representation theorem for EVERY arbitrary two-edge cut has NOT been
implemented. Cuts whose virtual closure edge already exists require a
parallel-edge/subdivision treatment; cuts with coincident endpoints need
separate handling. The higher-connectivity/minimal-core bottleneck is still
unproved. These reductions do NOT establish core rigidity or the linear
bound in Spec.lean.

Additional exact exploratory check, NOT a Lean theorem:
`/tmp/regular_r12_even.py` checked 40 Eulerian parallel extensions of Sage's
regular R12 matroid, obtained by duplicating at most six of its twelve
columns. Every zero-sum support was checked by circuit DP; no nonrigid
minimal core was found. Logs `/tmp/regular-r12-even.log` / `.exit` (0).
This is not evidence sufficient to assert rigidity for all regular cores.
Network DNS remains unavailable; a fresh reference-site request failed.

## Latest continuation: exact serial optima and minimal-factor reduction

The original conjecture is STILL UNRESOLVED. Spec.lean is unchanged, with
its original sorry. No proof/disproof was submitted.

New checked module: `Submission/SerialMinimum.lean` (imports SerialCore),
namespace `Erdos184Serial`. Current olean exists;
`/tmp/serial-minimum-check.exit` is 0 and all printed axiom lists are clean.
This is a general circuit-system result, NOT yet a Lean realization theorem
for arbitrary graphical two-edge cuts.

Definitions:
- `HasNumber C s k`: a partition of cardinality k exists, and every partition
  of s has cardinality at least k.
- `MinimalCore C s k`: HasNumber plus strict upper bounds on all proper
  valid supports. Thus it includes the full-support lower bound omitted by
  the older `Minimal` definition. Validity of s itself remains a separate
  hypothesis, as in the graph development's evenness hypotheses.

Main checked results:
- `serial_partition`, `serial_hasNumber`: for used tied ports, the exact
  minimum is k+l-1. No rigidity hypothesis is required.
- `parallel_partition`, `parallel_hasNumber`: for unused ports, counts add.
- `serial_minimalCore`: arbitrary minimal inputs glue to a minimal output;
  this strengthens the earlier result restricted to rigid inputs.
- `serial_minimalCore_iff`: for valid local supports with known optima,
  the serial output is minimal iff both inputs are minimal.
- `serial_rigid_iff`: rigidity of the output iff rigidity of both factors.
- `nonrigid_minimal_serial_factor`, `nonrigid_serial_factor`: a nonrigid
  minimal serial system has a nonrigid minimal factor. The latter chooses
  the local optimum counts internally and proves k+l=N+1.

The integral assembly proof uses the already checked fractional gluing with
all input coefficients one. Exact unit coverage gives a genuine disjoint
partition; nonempty circuits make its indexing injective. For the reverse
minimality implication, a support omitting a port is paired with the other
factor after deleting the port-containing piece of an optimum partition.
That cofactor has exact optimum l-1, which provides the needed lower bound.

No missing graphical core-rigidity, square-accessibility, density, or
rounding hypothesis has been proved. The serial representation of general
simple-graph two-edge cuts (including virtual-edge/parallel-edge cases) is
NOT implemented. Do not claim that the auxiliary factor theorem alone
settles either graphical core rigidity or Erdős 184.

The pending SerialCore build was checked: exit 0 and permitted axioms.
Combined check: `Submission/AxiomCheckSerial.lean` and
`/tmp/axiom-check-serial.log` (rechecked after adding SerialMinimum).

## Latest continuation: checked serial gluing, and its limitations

`Submission/SerialCore.lean` now compiles with a current olean; the final
`/tmp/serial-core-check.exit` is 0. All printed axioms are permitted. Its
independent circuit-system model assumes closure under nested differences.
It proves serial rigidity/minimality for rigid inputs, and constructs an
exact nonnegative fractional cover of cost cost(left)+cost(right)-1.
The tied port coordinates are retained; this is not unrestricted two-sum.
`Minimal` in this module does not by itself assert full-support optimality;
`serial_rigid` supplies that fact in the applications.

A mathematical application (NOT yet fully Lean formalized) rules out every
constant-factor rounding bound for arbitrary binary minimal cores. Let B_r
be the binary code on E(K_r) generated by cuts and the all-ones word, r>=5.
Every nonzero proper word is a circuit, full support is rigid of count 2,
and complements of vertex-stars with weight 1/(r-2) give fractional cost
r/(r-2). Serial gluing b copies gives rigid integral count b+1 and a
fractional cover of cost 1+2b/(r-2). Taking r>=2b+2 keeps that cost <=2.
These systems are nongraphic, so this does NOT disprove the conjecture or
rule out graphical core rounding. The base classification and infinite
application are mathematical arguments, not claimed Lean theorems.
Exact small checks in `/tmp/serial-core-glue.log` finished with exit 0.

Spec.lean is unchanged and still contains sorry. No settlement is claimed.


## Latest continuation: cycle-criticality is not abstract minimality

The original conjecture remains unresolved; Spec.lean is unchanged. No new
Lean proof of the missing graph-specific inheritance or rounding statement
was obtained in this continuation.

A precise attempted simplification was tested: does exposure of EVERY circuit
in an optimum (cycle-criticality) imply minimality among ALL proper even
supports? It is FALSE for binary circuit systems. This was checked by exact
finite DP, NOT by a Lean proof and NOT as a graph counterexample.

A connected binary example has columns in F2^6:

    [57,20,53,7,22,16,53,27,24,8,49,3,62,41,2].

It has 15 elements, rank 6, 512 even supports, and 157 circuits.
The full support has minimum partition size 3 and maximum 5.
Deleting ANY one of its 157 circuits leaves minimum exactly 2.
Nevertheless, proper support mask 4037 (zero-based positions
0,2,6,7,8,9,10,11) has minimum = maximum = 3.
Its three disjoint circuits have masks 1537, 68, 2432; its complement
partitions into circuit masks 16402 and 12328. Thus local strict decreases
on every circuit deletion do not force a strict decrease on every proper
even support. A minimum partition of the full support has masks
173, 1858, 30736; a maximum partition is the displayed five circuits above.

Sage confirms the full matroid is connected, neither graphic nor cographic,
and has both a Fano and a dual-Fano minor. Therefore it is NONREGULAR and does
not refute any graph-specific converse or any conjecture about minimal
regular cores. It blocks only an abstract binary proof of that converse.

Artifacts (all finished):
- `/tmp/circuit_critical_dp.cpp`, executable of the same basename.
- `/tmp/check_critical_converse.py`, log `/tmp/critical-converse.log` (exit 0).
- `/tmp/check_critical_multiplicities.py`, log
  `/tmp/critical-converse-multiplicities.log` (exit 0).
- `/tmp/check_critical_random.py`, log `/tmp/critical-converse-random.log`
  (exit 0, witness found in sample 7).
- `/tmp/analyze_critical_counter.py`, log `/tmp/critical-counter-analysis.log`
  (exit 0). This independently recomputes every support and cofactor.

The structured tests before the witness also show that columns 1,...,15
plus two additional copies of 1 form a NONRIGID MINIMAL binary core of
minimum 4 and maximum 6. These are finite observations, not formal theorems.
No proof/disproof was submitted, and no computation remains running.


## New checked obstruction: square marginal costs, even in bipartite graphs

`Submission/SquareMarginal.lean` (192 lines, imports Work) is checked, with
current olean. Log `/tmp/square-marginal-check.log`, exit file 0.
All reported axioms are propext, Classical.choice, Quot.sound.

The eleven-vertex bipartite graph is the edge-disjoint union of four squares:
- Base S: (0,1,2,3,0) and (0,4,5,6,0).
- Increment T: (1,7,6,8,1).
- Increment C: (1,9,4,10,1).

Exact integral counts: c(S)=c(S+T)=c(S+C)=2, but c(S+T+C)=3.
Thus adding C has marginal cost zero at S and one at S+T. This refutes
unrestricted diminishing returns even with BOTH increments squares and the
entire union bipartite. Main theorem: `square_diminishing_returns_false`.
`full_bipartite` provides an explicit Boolean bipartition; `other_square`
and `square_graph`/`square_length` identify both increments as squares.

Crucially, `full_not_minimal` is also proved: vertex 1 has degree six, but
the base square (0,4,5,6,0) avoids it. Saturated-core rigidity therefore
excludes minimality. This does NOT refute SquareAccessible on minimal cores,
core rigidity, or Erdős 184. It only rules out one possible exchange argument.

The pending R10 parallel-extension check below also finished. No builds or
searches remain running. Spec.lean is unchanged and STILL CONTAINS SORRY;
no proof/disproof of the original statement was obtained or submitted.


## Completed parallel-extension check

`/tmp/r10-parallel-extension.py` completed with exit 0. Adding two parallel
copies at positions 0, 4, 9, or 13 of the two-R10 core gives, in each case,
20 elements, cycle-space dimension 11, 2048 states, and 484 circuits.
The full support has minimum 3, maximum 4, and is NOT minimal.
No nonrigid minimal subcore occurs in any of these four finite systems.
This is an exact auxiliary computation, not a Lean proof or a general
inheritance theorem. It does not settle the graphical conjecture.

Spec.lean is unchanged, with its original sorry. No new Lean proof of an
integral bound was obtained. Existing conditional reductions were rechecked;
none of their missing hypotheses follows from the currently checked results.

## Targeted exact LP checks (NOT Lean proofs)

`/tmp/known-core-fractional.py`, log `/tmp/known-core-fractional.log`, uses Sage's
PPL rational LP solver on the three previously identified binary minimal cores:

- Columns 2,...,13: integral 3, exact fractional 12/5 (gap 3/5).
- Eleven-element parallel-pair core: integral 3, fractional 5/2 (gap 1/2).
- Nineteen-element core from the earlier shelling test: integral 4, fractional
  13/4 (gap 3/4).

These finite examples do NOT establish a general rounding theorem. In fact,
minimal cores are closed under direct sum, so their positive additive gaps
accumulate. An additive gap <1 cannot hold for arbitrary binary cores.

## Connected regular-matroid obstruction to additive gap <1

A cleaner connected example is the 2-sum of TWO copies of R10 along a column.
Its binary columns in F2^9 are

    [2,4,8,16,7,14,28,25,19,
     32,64,128,256,97,224,448,385,289].

Exact circuit DP reports:
- 18 elements, rank 9, 512 cycle-space states, 255 circuits.
- Full support minimum = maximum = 3.
- Every proper even support has minimum at most 2: the full support is a
  RIGID MINIMAL CORE in this regular matroid.
- Exact fractional circuit-cover cost = 9/5. Hence its additive gap is 6/5,
  already exceeding one, and the multiplicative gap is 5/3.

Nine ten-element circuits, each with coefficient 1/5, give the primal value:
bit masks 47709, 62897, 87674, 117720, 154926, 167751, 208043, 221925, 242070.
Sage independently checked that these are circuits and each element appears
exactly five times. No circuit has more than ten elements, so uniform dual
weight 1/10 proves the matching lower bound 18/10 = 9/5.
Sage also confirms the matroid is connected, NOT graphic, and NOT cographic.
Regularity follows from the standard R10 2-sum construction; this is not a
Lean-checked regular-matroid theorem in the development.

An elementary model of the example uses two K3,3 edge sets. A cycle-space
support either has all vertex degrees even in both blocks, or all odd in both.
An even nonempty support inside one K3,3 is one cycle. A proper all-odd support
is a perfect matching or a five-edge double star; the full nine-edge K3,3 is
the only remaining all-odd support. This explains minimality and rigidity:
a full partition has either one global circuit and one local cycle per block,
or three global circuits from perfect matchings. Both counts are three.

Artifacts:
- `/tmp/circuit_core_dp.cpp`, executable `/tmp/circuit_core_dp`.
- `/tmp/r10_chain_exact.py`, log `/tmp/r10-chain-exact.log`, exit 0.
- `/tmp/r10-two-sum-properties.py`, log `/tmp/r10-two-sum-properties.log`, exit 0.
- `/tmp/r10-chain-{1,2,3}.kernel` and corresponding `.circuits` files.

The three-R10 chain was also checked: 26 elements, rank 13, 8192 states,
1852 circuits, full minimum 3 and maximum 4, fractional optimum 29/15.
Its full support is NOT minimal. All minimal subcores in this particular
finite system were rigid. No general conclusion follows.

This rules out deriving an additive core gap <1 from regular-matroid axioms
alone. It does NOT refute a graph-specific core-rounding statement, and it
is NOT a disproof of Erdős 184. The constant-factor core route remains
unproved; no valid simultaneous-exposure or square-accessibility argument
was found. No builds or searches remain running.

---

# New checked cycle-only fractional bound

The original conjecture remains UNRESOLVED. Spec.lean is unchanged.

Two new unconditional modules are checked, with current oleans and clean axiom
lists (only propext, Classical.choice, Quot.sound):

- `Submission/CycleDualBound.lean` imports TightDual.
  `heavyGraph_acyclic` proves that edges of signed weight >1 form a forest
  when every simple cycle has weight <=1.
  `card_meeting_edges_le` injects the pieces meeting a fixed edge set into it.
  `total_le_two_card_sub_one` proves, for EVERY even G and signed cycle-only
  upper certificate w,

      sum_e w(e) <= 2 * (|V|-1).

  Proof: from any cycle partition, select the pieces meeting the heavy forest.
  There are at most n-1 such pieces, each of weight <=1. Their removal leaves
  all edge weights <=1, so Work's signed cycle-and-edge dual bound applies to
  that remainder. No integral rounding or core-rigidity hypothesis is used.

- `Submission/FractionalCycles.lean` imports CycleDualBound.
  `scaled_total_le` and `functional_full_graph_le` give the scaled support
  function bound. Hahn--Banach separation then gives the cycle-only convex
  hull membership and `exists_fractional_cycle_decomposition`: every EVEN
  finite graph has a nonnegative exact fractional cover using ONLY connected
  2-regular pieces, of total cost at most 2(n-1).

  This is a genuine cycle-only analogue of Work's earlier cycle-and-edge
  fractional cover. Its real coefficients are NOT an integral partition.
  Existing even ring examples still rule out pure multiplicative rounding for
  arbitrary graphs. An additive O(n) loss, or a suitable bound only on minimal
  cores, remains unproved.

Logs: `/tmp/cycle-dual-bound-check.log` and `.exit` (0), and
`/tmp/fractional-cycles-check.log` and `.exit` (0).

No proof or disproof of Spec has been submitted. The contraction example below
is also now fully checked, including its NONMINIMALITY; it remains auxiliary.

A combined import/axiom check also passed:
`Submission/AxiomCheckContinuation.lean`, log `/tmp/axiom-continuation-check.log`,
exit 0. It checks the new dual bound, cycle-only fractional cover, contraction
bundle, nonminimality, and the existing conditional square-accessibility theorem.
No proof builds or searches remain running at this checkpoint.

Further avenues considered, NOT proved:
- A bounded multiplicative integral/fractional gap restricted to minimal cores
  would now suffice, because the cycle-only fractional bound is linear. Existing
  unbounded-gap examples for arbitrary graphs do not establish such a core bound.
- An additive O(n) rounding bound remains missing.
- A fixed-size ODD cycle cover is not enough either: the rigid chain of tripled
  links closed by one edge is covered by three cycles with the closing edge
  appearing three times, but can have unbounded integral optimum. Thus cancelling
  repeated edges from an odd cover must not be treated as cost-free, even on cores.
- The mathematical square-accessibility gap was revisited but not closed.

---

# Current continuation: parallel-pair test and finite-check optimization

The original conjecture remains UNRESOLVED; Spec.lean is unchanged. No new
unconditional theorem closing square accessibility has been obtained.

## Exact nongraphic parallel-pair obstruction (not a Lean theorem)

A targeted test of whether a minimal binary circuit system must retain
minimality after deleting a parallel pair found an immediate counterexample.
The eleven labeled columns in F2^4 are

    [1,2,3,4,5,7,8,9,10,12,1].

The two copies of column 1 form the distinguished two-element circuit.
The full support has minimum/maximum circuit-partition counts **3/4**; every
proper zero-sum support has minimum at most **2**, so the full support is minimal.
Deleting the distinguished pair leaves minimum/maximum **2/3**, and a proper
cofactor subset still has minimum 2. Thus that cofactor is NOT minimal.

There are 128 zero-sum supports including empty and 57 circuits; the circuit
length histogram is 1 of length 2, 12 of length 3, 23 of length 4, 21 of length 5.
An optimum full partition, with the two 1's distinguished, is
`[1,2,3]`, `[4,5,8,9]`, `[7,10,12,1]`.
An optimum cofactor partition is `[2,3,4,5]`, `[7,8,9,10,12]`.
The size bound 11 > 2*5 also certifies the full lower bound of three.

Artifacts: `/tmp/parallel_core_cofactor.cpp`, executable
`/tmp/parallel_core_cofactor`, `/tmp/parallel-core-cofactor.log`. The search stopped
at this first example. An independent Python recurrence in `/tmp/binary_core.py`
confirmed the full nonrigid minimal core. These are exact computations, NOT
Lean-checked proofs and NOT graphical counterexamples.

Sage verified that the full matroid has BOTH Fano and dual-Fano minors, hence is
not regular. The cofactor is isomorphic to the cographic matroid of K3,3 and is
regular. Log `/tmp/parallel-core-matroid.log`. Thus an argument using only binary
circuit axioms cannot establish the parallel-pair shortcut; a genuinely graphical
(or stronger regular-matroid) argument would still be required.

## Contraction example and nonminimality: NOW CHECKED

The complete example has passed. Current checked modules:

- `ContractionBaseData` (imports TightDual): graph definitions, parity, five-cycle cover.
- `ContractionContractedData` (imports BaseData): three-cycle contracted cover and optimum 3.
- `ContractionGapData` (imports ContractedData): six cycles giving fractional cost 3.
- `ContractionModels` (imports BaseData): the two embedded block models.
- `ContractionGapLower` (imports Models): two internal cycles plus degree 6 give optimum 5.
- `ContractionGap` (imports GapData and GapLower): exact cycle-only primal/dual
  values 3 on both graphs, and `single_contraction_gap_drop_two`.
- `ContractionNonminimal` (imports BaseData): `graph_not_evenMinimal`, from
  six vertex-disjoint triangles whose union has optimum at least 6, whereas
  the full graph has optimum at most 5. This explicitly rules out using the
  example against a contraction rule restricted to minimal cores.

Authoritative final logs:
`/tmp/contraction-final-check.log` and `.exit` (0), and
`/tmp/contraction-nonminimal-check.log` and `.exit` (0).
All printed final axiom lists contain only propext, Classical.choice, Quot.sound.
Old chain/model logs may contain failures that were subsequently fixed.

Finite checks use ordinary `decide +kernel`, not native computation axioms.
The graph uses an edge LIST rather than a repeatedly reduced Finset literal.
Avoid concurrent large Lean builds: the cgroup memory limit is 10 GB.

Additional normalization for weighted sums with different Fintype instances:

    simp only [SimpleGraph.edgeFinset, ← Set.toFinite_toFinset] at ...

Do not run unrestricted `norm_num at h` on the resulting sum: it may rewrite
one side back to a computable filter. Use `h.trans (by norm_num)` to normalize
only the scalar right-hand side. Decidable `if` mismatches can be normalized
by splitting on their common predicate and simplifying both sides.

Spec has not been edited. The original conjecture is still unresolved.

---

# Latest continuation: square counting and a narrower core target

The original conjecture is STILL UNRESOLVED. `Submission/Spec.lean` is unchanged,
with SHA256 `509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5`.
No complete proof/disproof has been submitted.

## New checked square-counting module

`Submission/SquarePieces.lean` imports `Submission.ShortCycles`, has a current
olean, and `/tmp/square-pieces-check.exit` is 0. Both printed axiom lists contain
only propext, Classical.choice, Quot.sound. Namespace `Erdos184Work.SquarePieces`:

- `cycle_piece_four_le_of_coloring`: every cycle piece in a Boolean-colored
  graph has at least four edges.
- `rigid_of_edges_eq_four_mul_number`: a Boolean-colored graph with
  `|E| = 4 * number` is rigid.
- `square_subfamily_colored_card_le`: square pieces of ANY minimum decomposition
  that cross one common vertex bipartition number at most n. Their union is
  rigid by minimum-subfamily optimality and the four-edge lower bound.
- `fixedColoringEquiv`, `fixed_colorings_card`: exact finite counts of Boolean
  colorings with prescribed colors on a vertex subset.
- `four_cycle_coloring`, `square_piece_coloring`: explicit bicolorings of square
  pieces, proved by expanding a four-edge simple cycle (no SAT or native proof).
- `square_subfamily_card_le`: ANY square subfamily of a minimum cycle
  decomposition has size at most **8n**. Each square crosses at least
  `2 * 2^(n-4)` of the `2^n` Boolean colorings. Double counting and the preceding
  rigid bound give the result. This does not assume the ambient graph is a core.
- `five_mul_number_le_edges_add_nine_card`: every even G satisfies

      5 * number G <= |E(G)| + 9 * |V|.

  Indeed `5|D| <= |E| + 2*(triangle count) + (square count)`, and the previously
  checked triangle count is at most n/2. This is NOT a uniform linear bound.
  A sufficient still-UNPROVED core estimate is now `|E(R)| <= C*n + 4*number R`.

## New checked narrower structural reduction

`Submission/SquareCoreReduction.lean` imports SquarePieces, has a current olean,
and `/tmp/square-core-check.exit` is 0. Both printed axiom lists use only the
three permitted axioms. The proposed sufficient hypothesis is:

> Whenever an even-minimal core contains a four-cycle, SOME four-cycle has an
> even-minimal cofactor.

The source names this `SquareAccessible` and proves CONDITIONALLY that it implies
an optimum with at most 6n non-square pieces, hence `number <= 14n`, hence the
original asymptotic proposition. The checked proof repeatedly deletes accessible
squares; cycle-criticality gives exact unit loss, and once no squares remain the
verified four-cycle-free 6n bound applies. The square pieces created along this
chain are in one minimum partition, so the new 8n bound counts them.

**The accessibility hypothesis is unproved.** In particular, maximality of the
number of squares in an optimum does NOT by itself imply a square-free remainder:
K5 has two Hamilton-cycle optimum pieces, no square in any optimum, yet contains
squares. Nothing here permits silently transferring minimality to a cofactor.

The reduction helpers `lift_cycles_with_nonsquare_count` and
`add_square_with_nonsquare_count` preserve the count of non-square pieces.
`optimum_few_nonsquares_of_accessibility` is the edge-count induction;
`number_bound_of_accessibility` and `asymptotic_of_square_accessibility` are the
conditional conclusions. No proof of `SquareAccessible` for arbitrary minimal
cores is present.

Lean debugging: regularity parameters crossing graph differences needed the
usual degree/Fintype normalization before applying helper lemmas. Even the final
reflexive edge-count equality in the induction required normalizing
`SimpleGraph.edgeFinset_card` and `Nat.card_eq_fintype_card`; bare `rfl` hit
definitional-equality search. With these fixes, 200000 heartbeats suffice.

## Contraction-gap verification still in progress

The old unsplit `Submission/ContractionGap.lean` from the preceding continuation
was never fully checked. The first large build hit maxRecDepth; the next was
OOM-killed. The container's cgroup memory limit is **10 GB**, regardless of the
host's much larger reported RAM. A one-worker retry was deliberately stopped
at about 25 minutes without diagnostics, to optimize finite checks.

The source is now split, keeping the SAME namespace `Erdos184Work.ContractionGap`:

- `Submission/ContractionGapData.lean` imports TightDual. It contains the graph,
  explicit cycles, evenness, upper bounds, fractional cover, and contracted count.
- `Submission/ContractionGap.lean` imports ContractionGapData. It contains the
  block-model lower bound and the final matching primal/dual certificates.
- Backup of the original unsplit 467-line source:
  `/tmp/ContractionGap-before-split.lean`.

The data build is running with `-j1 -Dprofiler=true -Dprofiler.threshold=1000`;
Lean PID **69028** at the last check (elapsed about 8 minutes). Log:
`/tmp/contraction-data-check.log`. The exit file currently contains a STALE 143
from an earlier deliberately killed build; ignore it while PID 69028 is alive.
The current process started at Aug 27 23:00:44 and uses about 8 GB RSS (much of
that is shared imported data); actual cgroup usage remains well below 10 GB.
`graph_even` and `contracted_even` now split finite vertices with `fin_cases`
before `decide`. Direct list proofs replace the two universal edge-disjointness
checks. A separate `Submission/GraphEvenTest.lean` confirmed the split `graph_even`
proof in about 102 seconds, with clean axioms. It is only a test module and is
not imported by the development.

The intended example remains: 29-vertex simple even graph of integral count 5,
its single-edge contraction of integral count 3, and explicit cycle-only
fractional values both 3. This would refute unit-loss contraction-gap induction
for arbitrary even graphs, NOT Erdős 184. The graph is NOT an even-minimal core:
six vertex-disjoint triangles (0,7,9), (1,5,12), (2,4,14), (6,10,13),
(15,19,26), (16,18,28) form a proper even subgraph of count 6. This last observation
has not yet been formalized.

---

# Latest continuation: tight dual certificates on critical cores

The original conjecture remains UNRESOLVED. `Submission/Spec.lean` is unchanged
and still contains its original `sorry`; no proof/disproof has been submitted.

## New verified module

`Submission/TightDual.lean` imports `Submission.RigidityDegree`. Its olean is
current, `/tmp/tight-dual-check.exit` is 0, and all four printed axiom lists
contain only propext, Classical.choice, Quot.sound.

Namespace `Erdos184Work.TightDual`:

- `CycleUpperWeight G w`: every simple cycle has signed total weight at most
  one. This is a CYCLE-ONLY dual constraint. No edge-wise upper bound or
  nonnegativity is assumed, and no optimal dual value is defined here.
- `CycleUpperWeight.mono`, `piece_weight_le`, `piece_weight_ge`,
  `decomposition_weight_eq`, `CycleUpperWeight.total_le_number`.
- `cycle_weight_lower_of_critical`: in a cycle-critical even G, writing
  `T = sum_e w(e)` and `k = number G`, every cycle has weight at least
  `T - k + 1`. The proof exposes that cycle in a k-piece minimum, then
  bounds the sum on the other k-1 pieces by k-1.
- `unitWeight_of_critical_exact`: if additionally T >= k, every cycle has
  weight exactly one. Certificate EXACTNESS is an explicit hypothesis.
- `minimal_exact_dual_rigid_and_sparse`: exactness on an even-minimal G
  implies rigidity, `|E(G)| <= 2|V|`, and `number G <= |V|-1`, using the
  previously verified unit-certificate structure theorem.
- `strict_dual_gap_of_nonrigid`: every cycle-only upper certificate has
  T < k on a nonrigid, cycle-critical even graph.
- `partition_gap_bound`: if an even subgraph R <= G has cycle partitions
  A and B, and G is cycle-critical and even, then
  `|B| - |A| <= |B| * (number G - T)` (as a real inequality).
  No minimality or optimality of A and B is required.

These lemmas do NOT establish exact certificates for arbitrary minimal
cores, nor even a bounded gap there. The existing general fractional theorem
in Work uses cycles AND individual edges; do not silently identify its dual
with the cycle-only model above.

## Mathematical avenues reconsidered, still unproved

- Weak minimal-cofactor accessibility is still open in this development.
  Neither full heredity nor diminishing returns may be used to infer it.
- Restricting to smallest counterexamples gives stronger support and degree
  constraints than arbitrary core minimality, but no contradiction was found.
- An additive rank-sized rounding bound for binary circuit-partition LPs was
  considered as a possible route. It is NOT proved or assumed; ordinary LP
  basis size and integer Caratheodory estimates involve the wrong dimension.
  This is not a new theorem, and no conclusion is drawn from it.

No searches or proof builds are running at this checkpoint.

---

# Latest continuation: short-cycle counting and structured core gluing

The original conjecture remains UNRESOLVED. `Spec.lean` is unchanged, with its
original `sorry`. No complete proof/disproof has been submitted.

## New checked module

`Submission/ShortCycles.lean` imports `Submission.RigidityDegree` and has a
current cached olean. `/tmp/short-cycles-check.exit` is 0. All printed axiom
lists contain only propext, Classical.choice, Quot.sound.

Namespace `Erdos184Work.ShortCycles`:

- `cycle_piece_three_le_edges` and `cycle_family_three_mul_card_le_edges`.
- `rigid_of_edges_eq_three_mul_number`: equality in the elementary edge
  bound forces rigidity.
- `triangle_subfamily_rigid`: triangle pieces in ANY minimum decomposition
  have a rigid union. No ambient core/rigidity hypothesis is required.
- `triangle_piece_adj`: the vertices of a connected 2-regular three-edge
  piece are pairwise adjacent.
- `triangle_subfamily_twice_card_le`: at most n/2 triangle pieces occur in
  a minimum cycle decomposition. This uses their linear vertex intersections
  and Work's already checked minimum linear-subfamily theorem.
- `eight_mul_number_le_twice_edges_add_card`: for every even G,
  `8 * number G ≤ 2 * |E(G)| + |V|`.
- `four_mul_number_le_edges_add_card`: the weaker `4 * number G ≤ |E(G)| + |V|`.
- `even_bound_of_core_triangle_excess`, `triangle_excess_core_of_large_number`,
  `asymptotic_of_core_triangle_excess`: a CONDITIONAL reduction. A fixed C
  satisfying `|E(R)| ≤ C * |V| + 3 * number R` for every even-minimal R would
  imply `2 * number G ≤ (2*C+1) * |V|` for every even G and the original
  asymptotic proposition. The structural hypothesis is STILL UNPROVED.

The counting proof takes an optimum cycle family D and filters its triangle
pieces A. Every other cycle has at least four edges, hence
`4*|D| ≤ |E(G)| + |A|`; the checked `2*|A| ≤ |V|` finishes the estimate.
This is not a uniform linear bound when |E(G)| is large.

## Exact exploratory gluing checks (NOT Lean proofs)

`/tmp/glue_rigid_cores.cpp` and executable `/tmp/glue_rigid_cores`:
Take two copies of the seven-vertex, eleven-edge RainbowCore and identify
p vertices of one with p distinct vertices of the other, for every subset
and injection. Parallel edges are retained as distinct edges; the two-edge
circuits are included in the enumeration. Such parallel edges can be
subdivided to obtain simple graphs without changing the partition problem,
but that translation was not formalized here.

For every generated graph, enumerate all Eulerian edge supports via a
fundamental-cycle basis and compute minimum/maximum circuit partition counts.
Screen unsaturated nonrigid supports for cycle-criticality (every circuit
cofactor has strictly smaller minimum). No such candidate was found:

- p=3: 7,350 labeled gluing choices, 30,098,250 nonzero states,
  7,179,094 nonrigid states. Log `/tmp/glue-rigid-cores.log`.
- p=4: 29,400 choices, 240,815,400 states, 87,528,248 nonrigid states.
  Log `/tmp/glue-rigid-cores4.log`.
- p=5: 52,920 choices, 866,988,360 states, 400,428,552 nonrigid states.
  Log `/tmp/glue-rigid-cores5.log`.

These counts include isomorphic/repeated supports. The checks do not prove
core rigidity or any edge-excess hypothesis. All runs finished; no jobs remain.

## Mathematical status

Cycle-space/edge-excess estimates for arbitrary even-minimal cores remain
unproved. No inference from the finite gluing tests is used in Lean.
The one-cycle extension and unrestricted rigidity shortcuts are still not
available. The earlier warnings and obstructions below remain applicable.

---

# Latest checked progress: weighted incidence and edge excess

The original conjecture remains UNRESOLVED. `Spec.lean` is unchanged and no
proof has been submitted. The following auxiliary files are now checked, with
current cached oleans and only the three permitted axioms:

- `Submission/IncidenceExcess.lean`: `no_incidenceCycle_erase`, the weighted
  hypergraph bound `sum_card_sub_two_le_union`, `cycle_family_edge_excess`,
  and `rigid_edge_excess`. The last proves
  `|E(G)| ≤ |support(G)| + 2 * Critical.number G` for RIGID even graphs.
  All four axiom lists are clean; `/tmp/incidence-excess-check.exit` is 0.
- `Submission/CoreExcess.lean`: `three_mul_number_le_edges` and a CONDITIONAL
  reduction of the original conjecture to a uniform bound
  `|E(R)| ≤ C * |V(R)| + 2 * number R` on arbitrary even-minimal cores.
  That structural hypothesis is UNPROVED. `/tmp/core-excess-check.exit` is 0.
- `Submission/SpanningCoreObstruction.lean`: `nested_spanning_rigid_cores` gives
  connected rigid even-minimal graphs R < G on seven supported vertices with
  number R = 2 and number G = 3. The optimum can increase under a connected
  spanning extension. Thus a proper minimal cofactor need not lose a vertex
  or split a component. `/tmp/spanning-core-final-check.exit` is 0.

All three import `Submission.RigidityDegree`, not each other. The main
Work -> RigidTheory -> RigidityDegree chain remains unchanged.

The weighted inequality inducts by erasing a private vertex among pieces of
size at least three. It counts `sum (|piece| - 2)`, allowing arbitrarily small
pieces. Explicit `change` steps were needed to normalize `Set.ncard` against
`Nat.card`; the last errors were bookkeeping, not mathematical gaps.

The missing step is STILL a uniform estimate for arbitrary even-minimal
cores (or some other genuine proof of the conjecture). No theorem proved
here supplies that step.

---

# Latest continuation: minimal-cofactor investigation (still unresolved)

The original conjecture is STILL NOT SETTLED. `Spec.lean` is unchanged, with
SHA256 `509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5`.
No new Lean theorem was added in this continuation, and no proof was submitted.
The checked Work -> RigidTheory -> RigidityDegree dependency chain described
below remains current. Do not mistake the experiments below for Lean proofs.

## Exact exploratory tests of minimal-cofactor existence

Question: does every nonempty even-minimal core have SOME circuit whose
complement is again minimal? This remains UNPROVED, even as a general binary
cycle-system assertion. It would not alone imply rigidity or settle Erdős 184.

Completed exact tests (ordinary Python/C++, not kernel-checked):

- `/tmp/core_shelling.py`: full nonzero F2^4 representation, and R10 (previous
  continuation). No failure of existence of a minimal cofactor.
- `/tmp/shelling_code.py`, log `/tmp/shelling-code.log`: 250 systematic binary
  codes for each (code dimension, check rank) in (8,5), (10,5), (10,8),
  (12,6), (12,10); checks every codeword/minimal core. No failure.
- `/tmp/shelling_columns.cpp`, executable `/tmp/shelling_columns`, log
  `/tmp/shelling-columns.log`: 100 twenty-element restrictions of PG(4,2),
  each with 32767 nonzero words. Includes cores of optimum four. No failure.
- `/tmp/shelling_twosum.cpp`, log `/tmp/shelling-twosum.log`: the two-sum of
  two copies of the known twelve-element nonrigid binary core (columns
  2,...,13), along column 2. Twenty-two elements, 32767 nonzero words,
  1501 circuits, 128 optimum-four minimal cores. No failure.
- `/tmp/shelling_fano.cpp`, log `/tmp/shelling-fano.log`: 1000 systems obtained
  from four sampled Fano planes in F2^6, restricted to at most 22 points.
  Every even support was checked. No failure of minimal-cofactor existence.
  This run completed through trial 999; no searches remain running.

The C++ recurrence computes min and max circuit-partition sizes and the maximum
minimum size on all proper codewords. Numeric mask order respects inclusion;
proper-subset maxima recurse over deleting any contained circuit. These are
finite exact checks, not proofs of the general property.

## Longest-circuit shortcut is FALSE for binary systems

1. Series-extension obstruction:
   `/tmp/shelling_weight_obstruction.py` uses the known core on columns 2,...,13.
   Its full minimum/maximum are 3/4. Deleting {2,4,6} leaves min/max 2/3 and is
   not minimal. Replace each of these three coordinates by ten series copies,
   leaving the others single. The chosen circuit has length 30 and every other
   circuit has length at most 23, so it becomes uniquely longest. Series
   extension preserves the partition/minimality problem.
   In a GRAPH, subdivisions similarly make any chosen cycle uniquely longest;
   thus a universal graphical longest-cycle inheritance assertion would imply
   inheritance for EVERY cycle, hence the missing full core-rigidity theorem.

2. A nineteen-element SIMPLE binary example, no series weights needed:
   columns in F2^6 are
   `[58,26,15,24,53,23,52,35,49,2,51,33,45,21,13,54,62,34,60]`.
   Script `/tmp/analyze_shelling19.py`, log `/tmp/analyze-shelling19.log`.
   There are 8191 nonzero codewords and 605 circuits. The full support is a
   minimal core of minimum FOUR and maximum FIVE. Cofactor statistics are:

   circuit size | cofactor min/max | minimal? | count
   3            | 3/4              | no       | 25
   4            | 3/4              | no       | 75
   4            | 3/4              | yes      | 1
   5            | 3/4              | no       | 168
   6            | 3/4              | no       | 132
   6            | 3/4              | yes      | 92
   7            | 3/4              | no       | 112

   Hence NO longest circuit has a minimal cofactor, and NO circuit at all has
   a rigid cofactor. There ARE 93 minimal cofactors, all nonrigid.
   The unique size-four good circuit is {26,15,23,2}.
   All good circuits have even size, while the full support has odd size 19.
   Consequently there is NO partition of the full support (optimal or not)
   in which every displayed circuit has a minimal cofactor. This rules out
   that stronger generic shelling assertion too. It is NOT a graphical
   counterexample or a disproof of Erdős 184.

The earlier `/tmp/shelling_longest.py` and `/tmp/shelling_all_longest.cpp` runs
were deliberately stopped once the series-extension obstruction was noticed.
Their partial logs are not complete searches.

## Parity-extension follow-up (did not give a shelling counterexample)

`/tmp/shelling_parity_extension.py`, log `/tmp/shelling-parity-extension.log`,
adds one coordinate equal to codeword-weight parity to the nineteen-element
example. The resulting code has 8192 words and 1109 circuits. Full support
has min/max 3/5 and is NOT minimal. All its minimal subcores passed the
minimal-cofactor existence test. Thus this construction does not refute the
weaker shelling question.

## Directed / TU-flow rigidity obstruction

`/tmp/directed_core.py` checks all balanced arc subsets of complete symmetric
digraphs on 3 and 4 vertices. On FOUR vertices, the full twelve-arc digraph has
minimum directed-cycle partition size FOUR, maximum SIX, and every proper
balanced arc subset has minimum at most THREE. It is therefore a nonrigid
minimal core for DIRECTED cycles. This blocks an argument deriving rigidity
from total unimodularity / positive circulation decomposition alone. The
unoriented graph situation has additional cycles and is different; no graph
counterexample follows. This observation is exact Python, not a Lean theorem.

## Approaches reconsidered, without new proofs

- Local exposure of all cycles of a two-cycle nonrigidity witness is NOT enough
  in arbitrary even ambient graphs. This was ALREADY tested in
  `/tmp/local_two_cycle_reduction.py` and its log, using the Petersen line
  graph. Do not repeat that proposed local principle; the older notes below
  mention it alongside the K4 local obstruction.
- A possible graph-specific route would combine minimal-cofactor existence
  with analysis of a minimal one-cycle extension of a rigid core. BOTH steps
  remain unproved. No induction may silently assume either.
- Signed certificates, TU orientation, fractional rounding, greedy path
  conversion, and maximum-rigid-subgraph approximation were reconsidered but
  yielded no valid missing theorem.
- A speculative bounded-order approach for optimum-three, four-regular cores
  via vertex-disjoint cycle packing was considered but NOT established.
  In particular, no universal numerical order bound was proved.

No proof builds or exploratory searches are running at this checkpoint.

---

# New verified rigidity theorem (current continuation)

The original conjecture is STILL NOT SETTLED. `Submission/Spec.lean` remains
unchanged with its original `sorry`. SHA256:
`509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5`.
No proof has been submitted.

## Checked consolidated auxiliary modules

- `Submission/Work.lean`: unchanged, 17,988 lines, current cached olean.
- `Submission/RigidTheory.lean`: 4,640 lines, imports ONLY `Submission.Work`.
  Full consolidated check PASSED, `/tmp/rigid-theory-check.exit` = 0.
  Log `/tmp/rigid-theory-check.log`: no errors or sorryAx dependencies;
  style/unused-variable warnings only. All printed axioms are permitted.
- `Submission/RigidityDegree.lean`: approximately 100 lines, imports
  `Submission.RigidTheory`. Check PASSED, `/tmp/rigidity-degree-check.exit` = 0.
  Both printed axiom lists use only propext, Classical.choice, Quot.sound.

For NEW work, import `Submission.RigidityDegree` (or RigidTheory if the last
lemmas are unnecessary). Do NOT import both RigidTheory and its old component
files: the declaration names are identical. The old component files remain
as separately checked source/reference copies, but RigidTheory is consolidated.

## Major new unconditional auxiliary results

Namespace `Erdos184Work.CycleRings`:

- `no_ring`: an even rigid graph has no strong cyclic incidence pattern of
  any length >= 3 among any edge-disjoint cycle subgraphs.
- `no_incidenceCycle`: for ANY edge-disjoint cycle family D in an even rigid
  graph, `¬ ChordalIncidence.IncidenceCycle (pieceVertices D)`.
- `rigid_number_le_support`:
  `Rigidity.CycleRigid G -> (∀ v, Even (G.degree v)) ->
   Critical.number G ≤ G.support.ncard`.
- `rigid_family_private`: every nonempty edge-disjoint cycle family in an
  even rigid graph has a piece with a private vertex.
- `rigid_has_degree_two`: every nonempty even rigid simple graph has a vertex
  of degree exactly TWO.
- `even_bound_of_core_rigidity`: assuming every even-minimal graph on V is
  rigid, `Critical.number G ≤ Fintype.card V` for every even G on V.
- `asymptotic_of_core_rigidity`: the ORIGINAL asymptotic proposition (using
  Work's definitionally identical definitions) follows from the explicitly
  quantified hypothesis that all even-minimal cores are rigid.

The last two are CONDITIONAL. The crucial hypothesis
`EvenCore.EvenMinimal G -> Rigidity.CycleRigid G` is STILL UNPROVED.
No uniform bound for arbitrary minimal cores, or genuine superlinear
counterexample family, has been obtained.

Namespace `Erdos184Work.TriangleContacts`:
- `common_vertex_impossible` handles a strong three-cycle ring with any common
  vertex by a two-cycle switch producing three contacts with the third cycle.
- `intersection_eq_pair` enumerates one or two contacts of rigid cycle pairs.
- `patterns_bound` verifies all EIGHT multiplicity cases (each pair has one or
  two contacts), reducing by cycle permutation to the FOUR canonical kernels.
- `no_three_cycle_ring`, `no_subgraph_ring`, `no_incidenceTriangle`.
- `conformal`: the primal vertex-set hypergraph of any rigid cycle family is
  conformal (the separate ChordalIncidence lemma turns triangle exclusion into
  conformality).

## Verified proof architecture of the new rigidity theorem

1. `ChordalIncidence` (880 lines) proves the finite counting theorem:
   pieces of size >=3, pair intersections <=2, and no strong incidence cycle
   imply number of pieces <= size of their union. It uses conformality,
   chordal primal graphs, clique separators, and a private-vertex induction.
2. `PathSubstitution` and `ThreeCycleKernels` lift two-cycle decompositions of
   four concrete kernels through internally disjoint paths.
3. `RigidSwitching` proves pairwise intersection <=2 for arbitrary cycles in
   an even rigid graph, exact two-cycle switches, and alternation of contacts.
4. `CycleSegments`, `JunctionAssembly`, `ContactLayouts` extract local segments
   (independent of the chosen cycle roots), and assemble the four kernels.
5. `IndexedCycles` restricts arbitrary indexed cycle families to their edge
   union and proves that its optimum is exactly the index cardinality in a
   rigid ambient graph.
6. `TriangleContacts`, `TrianglePatterns`, `TriangleExclusion` exclude all
   strong three-piece rings, including the common-vertex case.
7. `CycleRings.Ring G n` represents a ring of n+3 cycle subgraphs with
   `vertex : Fin (n+3) -> V`, injective, and exact incidences
   `vertex i ∈ (piece j).verts <-> i=j or i=j+1`.
8. `Ring.shorten_at_zero` and `.shorten_at`: if consecutive pieces meet twice,
   switch them through the two outer contacts, keep ONE switched cycle and
   discard the other, obtaining a ring with one fewer piece. No partition
   replacement or common-vertex counting lemma is needed.
9. `Ring.shorten_chord`: a vertex shared at the ends of an interval and absent
   internally closes a shorter ring.
10. `Ring.no_chord`: in a shortest ring, consecutive intersections are already
    singletons by step 8. Rotate a nonconsecutive shared contact to piece 0;
    take the first positive piece containing it, using Finset.min'. The
    interval in step 9 then has length strictly between 2 and the full ring.
11. `Ring.clean_of_no_shorter` makes a shortest ring clean. The existing Work
    theorem `LongRing.minimal_linear_no_core` excludes it after restricting to
    its edge union. This avoids reconstructing a long clean chain explicitly.
12. `ring_of_incidence_walk` translates a ChordalIncidence witness into a Ring
    via p.getVert on Fin p.length and its edge labels.
13. Apply step 1 to get the linear rigid bound and a private vertex. In a full
    cycle partition, a private vertex has degree 2 by the degree-sum formula.

## Standalone source copies and logs

All of the following source copies have passed and have cached oleans:

```
ChordalIncidence -> PathSubstitution -> ThreeCycleKernels -> RigidSwitching
 -> CycleSegments -> JunctionAssembly -> ContactLayouts -> IndexedCycles
 -> TriangleContacts -> TrianglePatterns -> TriangleExclusion -> RingIndices
 -> CycleRings -> RingChords -> MinimalRings -> CleanRings -> RigidBound
```

They were concatenated (minus imports) to produce RigidTheory. Its sole import
is Work. `RigidityDegree` imports that consolidated module.

Individual latest exit files (all 0):
`/tmp/junction-assembly-check.exit`, `/tmp/contact-layouts-check.exit`,
`/tmp/indexed-cycles-check.exit`, `/tmp/triangle-contacts-check.exit`,
`/tmp/triangle-patterns-check.exit`, `/tmp/triangle-exclusion-check.exit`,
`/tmp/ring-indices-check.exit`, `/tmp/cycle-rings-check.exit`,
`/tmp/ring-chords-check.exit`, `/tmp/minimal-rings-check.exit`,
`/tmp/clean-rings-check.exit`, `/tmp/rigid-bound-check.exit`.
The earlier five files' final-check exit files are also 0.

Generators in /tmp:
- `generate_three_cycle_kernels.py`
- `generate_junction_assembly.py` (fixed dependent path-index coverage)
- `generate_contact_layouts.py`
- `generate_triangle_patterns.py`

## Additional Lean lessons

- `include hC in` / `include hd in` are needed when a section proof-only
  hypothesis does not occur in the theorem type. Otherwise it is out of scope.
- For equal dependent-index walks/subgraphs, rewriting the index often fails.
  Take `congrArg (fun i => (C i).edges)` or
  `congrArg (fun H : G.Subgraph => H.edgeSet)` first, then `dsimp only` and rw.
- Rewriting an if-selected subgraph under Connected/regular degree can remain
  stuck even with split_ifs. The robust proof used in Ring.shorten_at_zero is:
  normalize IsRegularOfDegree to Nat.card neighbor sets, then transport the
  whole property via `congrArg (fun H : G.Subgraph => ...) (if_pos hi)` and
  `.mpr`. Do not waste millions of heartbeats on direct instance conversion.
- `Fin.val_add_eq_ite` turns variable-modulus successor arithmetic into omega.
  `Fin.succAbove_right_injective` is the relevant injection lemma.
  `Fin.val_castLE` replaces deprecated Fin.coe_castLE.
- In zero_incidence, split_ifs left `P ∨ False`, which omega did not handle
  directly. `(try simp only [or_false])` before omega fixed it. Plain simp
  failed on the other branch with 'made no progress'.
- To convert `k ≠ 1` to `k.val ≠ 1`, an explicit Fin.ext proof was robust;
  a simp-only attempt left the original Fin inequality unchanged.
- `Set.ncard_le_card` bounds support ncard by Nat.card V.

## Current next research gap

Focus on arbitrary even-minimal cores, not on another rigid-graph bound.
The whole previously missing rigid incidence exclusion is now proved.
Possible sufficient routes (all still unproved):
- every even-minimal core is rigid;
- a weaker UNIFORM degree bound for even-minimal cores;
- existence of signed unit-cycle certificates on minimal cores;
- additive O(n) fractional rounding;
- or a real superlinear counterexample to the original statement.

Do not assume cycle deletion preserves minimality: rigidity is equivalent to
minimality of EVERY even subgraph, not merely minimality of the full graph.
Earlier local counterexamples in Work still apply. In particular, exposing
all cycles of a local K4 subdivision in optimum ambient partitions does not
force a local certificate or an optimum-preserving local deletion.

Exploratory reasoning in this continuation considered regular-matroid/TU
methods, maximal rigid subgraphs, and augmentation. None yielded a new theorem
about minimal cores. Global submodularity of the minimum cycle count is not a
safe premise (adding separate cycles can lower the optimum before it rises).
No new numerical searches were run. Attempts to fetch literature with curl
failed (HTTP status 000); there is no downloaded result to rely on.

No proof builds or searches are running at this checkpoint.

---

# Current development status

The original conjecture is NOT settled. `Spec.lean` remains unchanged and still has `sorry`.
Do not submit it as a complete proof. Established results are developed in `Work.lean`.

## Local certificate/deletion obstruction (new checked work)

`Submission/LocalObstruction.lean` has 568 lines and passed a full standalone
check with exit zero, recorded in `/tmp/local-obstruction-final-check.exit`.
Its log `/tmp/local-obstruction-final-check.log` has no errors, warnings, or
sorryAx dependencies. All five printed axiom lists use only the permitted three.
The body has been appended to Work, now 17,988 lines. The integrated build
passed with `/tmp/work-local-obstruction-check.exit` = 0. Its log
`/tmp/work-local-obstruction-check.log` has no errors or sorryAx dependencies.
The cached Work olean is current. The duplicate LocalObstruction source and
olean have been removed. Import Submission.Work for these declarations.
No builds or searches remain running.

Namespace `Erdos184Work.LocalObstruction`:

- The ambient graph is the previously verified `ThreeCycleObstruction.exampleGraph`,
  the fifteen-vertex, four-regular Petersen line graph, with optimum three.
- `localGraph` has ten edges and eight supported vertices. Its branch vertices
  are 12,4,9,11. The rim is triangle 4--9--11--4; the hub paths are
  12--2--4, 12--1--0--9, and 12--5--11. Thus it is a K4-subdivision.
- `local_le`, `local_subcubic` verify containment and maximum degree three.
- `degree_0`, ..., `degree_12`, `even_two_bits`, `even_three_bits` reduce evenness
  to three independent Boolean edge choices. `even_mask_classification` proves
  that every even edge subset is empty or one of seven explicit cycle patterns.
  This is a structural parity proof with eight final Boolean cases, not a large
  enumeration of arbitrary graphs.
- `rest0_bound`, ..., `rest6_bound` give two explicit simple cycles partitioning
  the complement of each local cycle in the ambient graph.
- `even_subgraph_classification`, `every_local_cycle_exposable` prove that deleting
  ANY nonempty even R <= localGraph lowers the ambient optimum from three to two.
- `no_unit_certificate`: the four subdivided triangles and three subdivided
  quadrangles each cover every local edge twice; a unit certificate would give
  the same sum both value four and value three. The contradiction is checked by
  expanding seven concrete walks and linear arithmetic.
- `local_obstruction` bundles these facts.
- `local_deletion_principle_false` disproves the following proposed LOCAL reduction:
  an uncertifiable subcubic K inside an arbitrary even G always contains a nonempty
  even R whose deletion does not lower number(G). The theorem does NOT assume G
  is globally even-minimal. It does NOT disprove certificate existence on minimal
  cores and is NOT a disproof of Erdős 184.

Exploratory exact tests (not all Lean formalized):
- `/tmp/local_k4_reduction.py`, log `/tmp/local_k4_reduction.log`, found the local
  obstruction above among all 7514 cycles of the Petersen line graph. Its concrete
  witnesses were subsequently checked in Lean, so the final theorem does not
  trust this Python/Sage search or its solver.
- `/tmp/local_two_cycle_reduction.py`, log `/tmp/local_two_cycle_reduction.log`,
  also found two edge-disjoint cycles meeting in three vertices such that EVERY
  cycle in their union is exposable in an optimum ambient partition. Thus the
  analogous universal local two-cycle deletion proposal is false too. This
  second example has NOT been formalized. Data are in
  `/tmp/local_two_cycle_counterexample.pickle` (old Petersen-line labeling).
- The explicit Lean K4 data and relabeling are in
  `/tmp/local_obstruction_data.pickle`; generator `/tmp/local_obstruction_data.py`.
  No search jobs remain running.

## Incidence-graph route considered (still UNPROVED)

A possible next structural goal is a linear bound for rigid even graphs, without
first proving signed certificate existence. No new Lean theorem on this route
has been written. The outline below is conjectural until all steps are checked.

Given a cycle partition, form the bipartite incidence graph of its pieces and
vertices. Rigidity already implies pairwise piece intersections have size <= 2.
The proposed next claim is that this incidence graph is chordal bipartite (has no
induced cycle of length >= 6). If true, a weakly simplicial vertex on the piece
side would imply a piece with a private vertex: nested vertex-neighborhoods and
no private vertex would make another piece contain all >=3 of its vertices,
contradicting the pair-intersection bound. Hereditary rigidity then gives a
linear piece bound by induction on supported vertices.

A possible way to establish chordal bipartiteness is to choose a shortest strong
Berge cycle over ALL partitions of a rigid graph:
- For length r >= 4, minimality should force extra intersections among selected
  pieces to occur only between adjacent pieces or at a vertex common to all r.
- A common vertex would saturate the degree lower bound on their union; a clean
  cycle avoiding it would contradict the verified feedback-vertex characterization.
- Swapping the four paths of two adjacent pieces sharing two vertices should
  either produce a shorter strong Berge cycle or a forbidden strong triangle.
- If all adjacent intersections are singletons, the existing clean-ring
  recombination gives two cycles instead of r.
- The r=3 case without a common vertex reduces to the forty finite three-cycle
  junction kernels previously enumerated in `/tmp/triangle_rigidity_kernels.py`.
  All were nonrigid computationally. A general subdivision/segment-lifting proof
  and the finite kernel verification have NOT been formalized.

Even if this route gives a bound for rigid graphs, the essential implication
`EvenMinimal G -> CycleRigid G` remains UNPROVED. It must not be silently used.
No uniform integral upper bound or original counterexample was obtained.
Spec remains unchanged with its original sorry.

## Additive-rounding sharpness (new checked work)

`Submission/AdditiveGap.lean` (236 lines) passed standalone Lean verification,
with no warnings or errors in `/tmp/additive-gap-final-check.log`. Its printed
axiom lists use only `propext`, `Classical.choice`, and `Quot.sound`.
Its body has been appended to Work, now 17,419 lines. The full integrated build
passed, with `/tmp/work-additive-gap-check.exit` = 0. The log
`/tmp/work-additive-gap-check.log` contains no errors or sorryAx dependencies.
The cached Work olean is current. The duplicate AdditiveGap source/olean have
been removed; import Submission.Work to use these declarations. No jobs remain running.

Namespace `Erdos184Work.AdditiveGap`:

- `graph p k` is K_(p,k*p), with vertex type `Fin p ⊕ (Fin k × Fin p)`.
- `piece` is an explicit family indexed by `Fin k × Fin p`. In each block,
  the two consecutive cyclic-shift matchings form a Hamilton cycle on K_(p,p).
- `piece_cycle`, `fractional_cover`: for p >= 2, every member is a simple cycle,
  and coefficient 1/2 on every member covers every edge exactly once.
- `fractional_cost`: the total fractional cost is k*p/2.
- `fractional_degree_identity`, `fractional_degree_bound`: for any finite
  nonnegative exact fractional cycle-and-edge cover, the degree at any vertex
  is at most twice the total coefficient sum.
- `fractional_cost_lower_bound`: the displayed cover of K_(p,k*p) is fractionally
  optimal, even among covers allowing single edges and arbitrary real coefficients.
- `integral_lower_bound_simplified`: for p = 2*m+1, every integral decomposition
  has at least k*(3*m+1) pieces. This reuses the established bipartite parity bound.
- `no_additive_coefficient_below_one`: for every real c < 1 and every fixed real B,
  some graph has an explicit exact fractional cycle cover of cost t, while every
  integral decomposition has more than t + c*|V| + B pieces. Take p = 2*m+1 and k=p,
  with m sufficiently large. The coefficient-one additive-rank proposal remains
  unproved and is NOT disproved by this result.

No uniform rounding upper bound has been proved. No change was made to Spec.
The stronger proposal to pack at most ceil(fractional cost) cycles leaving an
acyclic remainder is already excluded by EvenRing: in an even graph an acyclic
even remainder is empty, so that proposal would give pure multiplicative rounding.
The new lower bound is an auxiliary obstruction, NOT the negation of Erdős 184.

## Latest completed verification

- Work has 17,988 lines; its cached olean is current.
- Full integrated build passed: `/tmp/work-local-obstruction-check.log`;
  `/tmp/work-local-obstruction-check.exit` = 0.
- No errors or `sorryAx` dependencies were reported. Printed axiom lists use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- The seven new standalone modules also passed individually. Their duplicate
  sources and oleans have now been removed. No Lean build is still running.
- **Nonnegative and marker certificate existence for even-minimal cores is FALSE.**
- Signed unit-cycle certificate existence for arbitrary cores is still UNPROVED.
- **The extra edge-weight upper-bound assumption is no longer needed to deduce a
  linear bound from a signed unit-cycle certificate.** See below.
- Rigidity of arbitrary cores and a uniform degree bound for cores remain UNPROVED.
- No original counterexample or unconditional uniform integral bound has been obtained.

## Signed certificates force sparsity (verified and integrated)

Namespace `Erdos184Work.CertificateStructure` contains the following results:

- `hub_path_weight`, `no_three_spokes`, `no_cycle_with_hub`, and
  `neighbor_induce_acyclic`: a unit-cycle weighting excludes a cycle with a hub;
  the stronger three-spoke formulation is used below.
- `cycle_edge_cons`: reorient and rotate a cycle so a specified edge comes first.
- `certificate_of_single_edge_expansion` and `certificate_of_subdivide`:
  pull a certificate back through a subdivided edge, assigning the original edge
  the sum of the two replacement weights. No sign or size restrictions are used.
- `SubcubicCertificates G`: every subgraph of maximum degree at most three has
  some signed unit-cycle weighting. A full certificate implies this property.
- `SubcubicCertificates.mono` and `.of_iso`: hereditary and isomorphism transport.
- `SubcubicCertificates.contract_closed`: the property is preserved by contracting
  an adjacent pair (the discarded vertex remains isolated on the same ambient type).
  This does NOT assert that rigidity or a full certificate is contraction-closed.
- `SubcubicCertificates.neighbor_acyclic`: a cycle in a vertex neighborhood would
  give a subcubic three-spoke wheel, contradicting its certificate.
- `.exists_sparse_edge`: every nonempty graph satisfying the property has an edge
  whose common-neighbor set is subsingleton.
- `contract_edge_count_lower`, `contract_support_card_lt`: contracting such an edge
  loses at most two edges and strictly decreases the number of supported vertices.
- `SubcubicCertificates.edge_bound`: induction on supported vertices gives
  `|E(G)| <= 2 * |support(G)|`.
- `UnitCycleWeight.edge_bound`: any unit-cycle weighting forces `|E(G)| <= 2*n`.
- `UnitCycleWeight.number_bound` and `SubcubicCertificates.number_bound`: if G is
  even, `Critical.number G <= n-1`, without edge-wise bounds on the certificate.
- `even_bound_of_core_unit_weights`, `asymptotic_of_core_unit_weights`: signed
  unit-cycle weighting existence for every minimal even core would suffice for
  the original conjecture. This existence hypothesis is still unproved.
- `asymptotic_of_core_subcubic_certificates`: even the weaker subcubic certificate
  test on all minimal cores would suffice. This hypothesis is also unproved.

Source integration order: CertificateStructure, CertificateLift, CertificateMinor,
CertificateContraction, CertificateWheel, CertificateSparsity, CertificateReduction.
Their bodies are now in Work; the duplicate source modules and oleans were
removed after the successful integrated build.

Important verification lesson: grep for `: error` rather than just `error:`.
Lean diagnostics such as `error(lean.invalidField)` otherwise go unnoticed.
Check the command's actual exit status before considering an olean updated.

## Negative certificates and contraction obstruction (verified)

The graph has junctions 0,1,2,3 and nine private vertices. Between each pair
j,j+1 (j=0,1,2) are three internally disjoint two-edge paths; also add edge 0--3.
It is connected and even, with 13 vertices, 19 edges, and optimum four.
A signed certificate puts weight 1/2 on one edge of each branch, zero on the
other, and -1/2 on 0--3. Every simple cycle has weight one. Consequently it is
rigid and even-minimal. The nine local four-cycles force every branch's total
weight to be 1/2 in ANY unit-cycle certificate, and a global cycle forces
w(0--3)=-1/2. Thus nonnegative and half-weight marker certificates are impossible.
This is NOT a counterexample to the original conjecture.

Key declarations in `Erdos184Work.NegativeCertificate`:
`certificate`, `graph_connected`, `graph_even`, `graph_rigid`, `graph_minimal`,
`graph_number`, `every_unit_weight_negative`, `no_nonnegative_certificate`,
`no_marker_certificate`, `bounded_signed_certificate`, and
`core_marker_existence_false`.

Contracting edge 0--3 yields a ring of three triple-path bundles, with twelve
vertices and eighteen edges. Three explicit global cycles give optimum three;
a saturated degree-six vertex and an avoiding local cycle show that the result
is neither even-minimal nor rigid. `contraction_failure` includes exact fibers,
surjectivity, and the quotient adjacency formula of the contracting map.
Thus contraction need not preserve rigidity, even for connected even graphs.

A stronger arbitrary-cycle-valuation extension proposal is also FALSE (not Lean
formalized): on K5, assign triangle cost 0, quadrangle cost 1, and pentagon cost
1/2. Every partition has total cost one (two pentagons, or two triangles and one
quadrangle), but no edge weights induce these costs. Averaging over vertex
permutations would give constant edge weights, contradicting the prescribed
triangle and quadrangle costs. This does NOT refute signed UNIT certificates
for rigid graphs. Script `/tmp/graphic_cycle_valuation.py`.

All tripled-tree-plus-matching tests described in the continuation summary
completed. Non-SP cases on the two ten-vertex tree shapes were neither rigid
nor cycle-critical. These finite tests prove no general theorem.

Namespace `Erdos184Work.StarCore`:

- `exists_even_star_core`: Given an even G and v, there is R≤G preserving all edges at v, even, and every cycle of R passes through v. Minimize edges among even subgraphs retaining that star; deleting a cycle avoiding v contradicts minimality.
- `number_degree_bound`: degree(v)≤2*Critical.number G.
- `twice_number_eq_degree_of_cycle_hits`: if G is even and all its cycles pass through v, 2*number G=degree(v).
- `cycle_hits_iff_induce_acyclic`: all cycles pass through v iff G−v is acyclic.
- `low_degree_of_feedback_vertex`: an even graph with a feedback vertex has some vertex of degree≤2 (possibly isolated).
- `EvenMinimal.saturated_vertex`: if G is even-minimal and degree(v)=2*number G, G−v is acyclic and G has a vertex of degree≤2.
- `exists_even_star_core_number`: the extracted star core has optimum exactly degree_G(v)/2.
- `EvenMinimal.degree_gap`: if an even-minimal graph has degree>2 everywhere, then degree(v)+2≤2*number G for every v.
- `EvenMinimal.regular_four_of_number_three`: such a core with optimum 3 must be 4-regular.

The last two are necessary conditions, NOT the missing uniform bound. In particular large optimum/vertex ratio is not ruled out.

## Latest exploratory structural question (UNPROVED)

A stronger possible claim is that every even-minimal simple graph is series-parallel (K4-minor-free). This would imply low degree, but has NOT been proved and must not be assumed. The following finite computations were only attempts to falsify it. None is a Lean proof, and none concerns a counterexample to the original Erdős conjecture.

Completed exact exploratory computations:

- `/tmp/critical4_fast.py`, log `/tmp/critical4_fast.log`: tested all connected simple 4-regular graphs on 8 through 15 vertices for the property that there is no two-cycle decomposition but every cycle can be completed to three cycles. No examples found. At n=15: 805491 graphs, 1386 without two Hamilton cycles, zero tested cycle-critical examples. This tests optimum THREE, not higher optima.
- `/tmp/simple_even_core.cpp`, executable `/tmp/simple_even_core`, log `/tmp/simple_even_core.log`: all Eulerian edge subsets of K8 (2^21 states). Computes minimum cycle-decomposition count and maximum such count over even subgraphs. None of the even-minimal graphs found had a K4 minor. These are computational observations only.
- `/tmp/core_multigraph.py`, log `/tmp/core_multigraph.log`: all labeled loopless 4-regular multigraphs through 7 vertices. No even-minimal example with non-series-parallel support. n=7: 93708 graphs total, 70941 non-SP support. This slow process was stopped before completing n=8.
- `/tmp/weighted_even_core.cpp`, executable `/tmp/weighted_even_core`: all Eulerian multigraphs on five vertices with each pair multiplicity 0..3, and on six vertices with multiplicities 0..2 and 0..3. No even-minimal graph with non-SP support. The last log is `/tmp/weighted_even_core_6_4.log`; it completed with 33554431 nonempty Eulerian states and 358443 even-minimal states. Parallel edges are modeled by 2-cycles as well as longer cycles. This is not a claim about simple graphs' minimum degree.
- `/tmp/simple_core_unlabeled_slow.py` (copy of earlier slow script), log `/tmp/simple_core_unlabeled.log`: all connected simple Eulerian graphs of order 9 tested, 1782 total, no non-SP even-minimal core. Order 10 search was interrupted and replaced with a faster version.

Completed order-10 run (formerly listed as running):

- Former PID 30367, now completed: `sage -python /tmp/simple_core_unlabeled.py`
- Final: 9,545,887 geng graphs, 31,026 connected Eulerian graphs, 30,662 non-SP, 604 unsaturated, zero tested non-SP cycle-critical candidates.
- Log `/tmp/simple_core_unlabeled_fast.log`.
- Current graph checkpoint `/tmp/current_core_graph.txt`.
- It tests connected simple Eulerian graphs on 10 vertices; script stops after n=10. At last check it had passed 4.5 million geng graphs / about 16,600 Eulerian graphs, with no candidate found yet.
- If it finds a non-SP even-minimal graph, it writes `/tmp/nonsp_simple_core.pickle`.
- This version decides two-cycle decomposability by suppressing degree-two paths and testing Hamilton decomposition of a 4-regular multigraph, then uses recursive exact decision for larger cycle counts. It skips saturated non-SP graphs using the mathematical star-core observation.
- Check process/log before starting duplicate searches. Do not interpret absence of a finite example as a proof of the structural claim.

## Useful recent Lean details

- `LongRing.regular_cycle_walk_at` returns `p.toSubgraph = H` (not merely edge-set equality).
- The map-cycle iff is `Walk.map_isCycle_iff_of_injective`, not `isCycle_map_iff`.
- To show an induced walk is a cycle, map it back with `Walk.map_induce` and use that iff. There is no `Walk.IsCycle.induce` lemma.
- `card_edgeFinset_induce_compl_singleton` equates to the edge count of `deleteIncidenceSet`; follow it with `card_edgeFinset_deleteIncidenceSet` to get subtraction by the degree.
- Use `SimpleGraph.edgeFinset_inj.mp`, not `edgeFinset_injective`.
- Lemmas named `StarCore.EvenMinimal.*` do not support dot notation on `EvenCore.EvenMinimal` hypotheses. Use the explicit qualified lemma name.
- Normalize degree/cardinality instances before passing evenness and comparing edge counts, as in the earlier notes.

## Latest integration

`Erdos184Work.StarCharacterization` is integrated and the full Work build passed (exit 0), using only the allowed axioms. Its scratch file has been removed.

- `number_eq_zero_iff`: number G = 0 iff G = bottom.
- `cycle_hits_mono`: a feedback vertex remains a feedback vertex in subgraphs.
- `number_sdiff_add_of_cycle_hits`: for even G with all cycles through v, and even R <= G, number(G \ R) + number R = number G. This is NOT a general additivity theorem.
- `evenMinimal_of_cycle_hits`: such a G is even-minimal.
- `saturated_minimal_iff_feedback_vertex`: for even G, (EvenMinimal G and degree(v) = 2*number G) iff G-v is acyclic.

The unsaturated case remains unresolved. No proof of rigidity, SP support, or bounded minimum degree is available.

## Ongoing restricted order-11 search

- PID 30741, script `/tmp/simple_core_unlabeled_sparse11.py`, log `/tmp/simple_core_unlabeled_sparse11.log`.
- Connected simple Eulerian graphs on 11 vertices, minimum degree 2, maximum degree 6, 15--22 edges.
- At the last check: more than 34,000 Eulerian graphs checked, no non-SP cycle-critical candidate. This is a finite exploratory observation, not a theorem.
- If found, writes `/tmp/nonsp_simple_core_sparse11.pickle`. Check process/log before duplicating.

## Algebraic rigidity obstruction (exploratory, not Lean)

The implication "even-minimal implies all circuit decompositions have the same size" is false for arbitrary binary cycle spaces. `/tmp/binary_core.py` found the zero-sum system on the twelve nonzero vectors encoded by integers 2 through 13 in F2^4. Its circuits have sizes 3, 4, or 5. The full set needs at least three circuits (no two circuits cover twelve elements), and decomposes as

- {2,3,4,5}, {6,7,8,9}, {10,11,12,13}, or
- {2,4,6}, {3,9,10}, {7,11,12}, {5,8,13}.

The exact enumeration reports that every proper zero-sum subset has optimum at most two. Thus it is a minimal core but not rigid. This is NOT a graphical example and does NOT refute the graph-specific rigidity possibility. It does rule out deriving rigidity from the abstract binary zero-sum axioms alone.

The regular non-graphic R10 representation was also checked: columns e_i and e_i+e_(i+1)+e_(i+2) modulo five. Its full support is minimal with optimum two, so even-minimal regular matroids need not be series-parallel. This is not a graph counterexample.

Cographic tests on connected bipartite graphs through nine vertices (at most eighteen edges) found no nonrigid core. This finite absence proves nothing general. Script `/tmp/cographic_core.py`, log `/tmp/cographic_core.log`, completed.

## Extended weighted checks (completed)

`/tmp/weighted_even_core_both.cpp` computes minimum and maximum circuit decomposition counts and minimum-core status for all Eulerian multiplicity vectors. It treats two parallel edges as a circuit and checks both SP support and rigidity.

- Four vertices, multiplicities 0..15: 2,097,151 nonempty Eulerian states, 35,672 minimal cores. No non-SP or nonrigid core. Log `/tmp/weighted_even_core_4_16.log`.
- Five vertices, multiplicities 0..5: 3,779,135 nonempty Eulerian states, 68,702 minimal cores. No non-SP or nonrigid core. Log `/tmp/weighted_even_core_5_6.log`.

These are exploratory finite checks, not Lean proofs. In particular they neither prove rigidity of graphical cores nor the original conjecture.

The restricted order-11 process (PID 30741) was still running at the last check, beyond 77,000 connected Eulerian graphs, with no non-SP cycle-critical candidate found. Check `/tmp/simple_core_unlabeled_sparse11.log` and the PID before restarting it.

No changes have been made to `Spec.lean`; its conjecture still contains `sorry`. No complete proof or disproof has been obtained, and the incomplete file should not be submitted for verification as a solution.

## Completed restricted order-11 and sampled-kernel checks

- The order-11 process completed: 37,648,470 geng graphs considered; 89,591 connected Eulerian graphs in the prescribed degree/edge range; 88,632 non-SP; 6,726 unsaturated; zero non-SP cycle-critical candidates. Final log `/tmp/simple_core_unlabeled_sparse11.log`. No process is still running. This was restricted to maximum degree six and 15--22 edges, NOT all graphs on eleven vertices.
- `/tmp/random_core.cpp` checks all Eulerian edge subsets of each sampled loopless regular multigraph, screening non-SP connected candidates by exact circuit-decomposition number and cycle-criticality, then full minimality if needed.
- 10,000 sampled 4-regular multigraphs on twelve vertices: no non-SP cycle-critical candidate among their Eulerian subgraphs. `/tmp/random_core_12_4.log`.
- 2,000 sampled 6-regular multigraphs on eight vertices: same outcome. `/tmp/random_core_8_6.log`.
- These samples are exploratory and not exhaustive classifications or Lean proofs. Both runs completed.

A different possible compression approach was checked: arbitrary Kelmans neighborhood transfer need NOT preserve or increase the decomposition number, even on edge-critical graphs. A four-vertex path is edge-critical with optimum three, but moving one endpoint's edge to the other endpoint creates a triangle with optimum one. Restricting transfers to adjacent vertices is a distinct question currently being tested in `/tmp/compression_adjacent.py`.

## Adjacent compression obstruction (new Lean verification)

`Submission/Compression.lean` compiled successfully with only allowed axioms and its body was appended to Work. The full integrated build is being checked in `/tmp/work-compression-check.log`, with exit status `/tmp/work-compression-check.exit`. Remove the duplicate scratch file ONLY after that build passes.

Namespace `Erdos184Work.Compression`:
- `transfer`: moves v's neighbors not adjacent to u from v to u, excluding u itself so that uv remains.
- `wheel`: five-vertex wheel, presented on Fin 3 + Fin 2 as K_(3,2) plus the two left edges from the center.
- `transferred_graph`: explicit equality with the compressed eight-edge graph.
- `wheel_number`: optimum four, lower bound from the existing independent-side parity inequality.
- `compressed_number`: optimum three, from an explicit decomposition and the single-edge-addition formula for an even base.
- `wheel_critical`: all edges exposed as singletons in some optimum decomposition, using the wheel's rotations and a four-piece decomposition with both edge orbits exposed.
- `adjacent_transfer_not_monotone`: edge-criticality, adjacency of the transferred pair, and a strict decrease of optimum.

This refutes an auxiliary monotonicity idea, NOT Erdős 184. Graphical even-core rigidity and a uniform linear bound remain unproved.

## Latest integrated status

The full integrated Work build for Compression passed, exit 0. No errors or sorryAx appear in `/tmp/work-compression-check.log`. All printed axioms are permitted. The cached Work.olean is updated. `Submission/Compression.lean` was removed to avoid duplicate declarations. Work now has 11,653 lines. `Spec.lean` is unchanged and still unsolved.

All exploratory processes from this continuation have finished; none is still running.

`/tmp/orthogonal_core.cpp` tested 11,896 midpoint-pairing configurations derived from the octahedral graph L(K4). The base has a decomposition into four star triangles and another into three quadrangles. Its twelve edges have row/column labels from these two decompositions. Pairing midpoints only for edges with different row and column labels preserves both displayed decompositions. Every resulting Eulerian subgraph was screened for non-SP even-minimality by the exact procedure in `/tmp/random_core.cpp`; no candidate was found. Log `/tmp/orthogonal_core.log`. This targeted finite test does NOT establish graphical rigidity or SP support.

Additional failed compression variant: the potential number(G) - (number of odd-degree vertices)/2 is not monotone under adjacent transfers, even on critical trees. Compressing the two internal vertices of a four-vertex path yields a three-edge star: the optimum remains three but the number of odd vertices grows from two to four. This is separate from the verified wheel obstruction.

The next mathematical blocker remains unchanged: a genuine uniform bound for unsaturated even-minimal cores, or a superlinear counterexample family. No unsupported structural hypothesis may be promoted to a proof.


## Weighted fractional bound (new verified development)

`Submission/Weighted.lean` has passed a clean standalone build against the cached
Work module. The body has now been integrated into Work, namespace
`Erdos184Work.Weighted`. A full integrated build is running; see
`/tmp/work-weighted-check.log` and `/tmp/work-weighted-check.exit`.

Key declarations:
- `exists_maximum_weight_path`: maximum total edge weight, with length as a
  lexicographic tie-breaker. Every neighbor of the initial vertex is on the path.
- `walkWeight_rotate`: exact exchange of the chord and predecessor edge.
- `weighted_degree_le_prefix`: rotation maximality bounds the weighted degree
  of the initial vertex by a prefix ending at its furthest neighbor.
- `exists_weighted_degree_le`: nonnegative edge weights, each edge and each
  simple cycle having weight at most t, imply some weighted degree at most t.
- `total_weight_le`: the total nonnegative edge weight is at most t*(n-1), with
  truncated natural subtraction handling empty graphs.
- `signed_total_weight_le`: the same inequality WITHOUT nonnegativity. Apply
  the preceding result to the subgraph retaining nonnegative edges; discarded
  negative edges can only lower the total. All required cycles of that subgraph
  are still cycles of the original graph.
- `functional_full_graph_le`: any linear functional bounded by t on the zero,
  single-edge, and cycle incidence vectors takes value at most t*(n-1) on G.
- `normalized_graph_mem_convexHull`: the incidence vector of G divided by n-1
  is in the convex hull of the zero/cycle/edge atoms (zero convention for n<=1).
  Uses compactness of a finite convex hull and Hahn--Banach separation.
- `exists_fractional_decomposition`: a finite indexed family of valid pieces
  with nonnegative real coefficients, total coefficient sum <=n-1, and coverage
  exactly one on every graph edge and zero elsewhere. Zero atoms are discarded
  by giving a default valid piece coefficient zero; the empty graph is handled
  separately.

The standalone build `/tmp/weighted-final-check.log` is clean. Printed axioms
for both final theorems are exactly the permitted three. There are no sorrys or
admits in Weighted. This is a FRACTIONAL theorem, NOT an integral decomposition.
No constant-factor rounding theorem has been proved. In particular, signed dual
variables are now handled, but the integrality gap remains a genuine blocker.
Do not claim that convex-hull membership gives a disjoint family of pieces.

`Spec.lean` is still unchanged and contains the original sorry. Neither the
conjecture nor its negation has been proved. Do not submit it as a complete proof.

## Weighted integration completed

The full integrated Work build passed, exit 0, with no errors or sorryAx in
`/tmp/work-weighted-check.log`. Both weighted final theorem axiom reports contain
only propext, Classical.choice, and Quot.sound. The cached Work.olean is current.
The duplicate `Submission/Weighted.lean` was removed after the successful build.
Work now has 12,215 lines. No builds or exploratory searches are pending.

The conjecture remains unsolved. The new fractional result does not establish a
constant-factor integral rounding theorem and is not a disproof either. The
unchanged Spec.lean SHA256 is
`509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5`.

## Fractional rounding obstruction (new checked work)

`FractionalGap.lean` and `EvenFractionalBase.lean` passed clean standalone builds
against the cached Work module; their bodies are now appended to Work. The full
integrated build is running in `/tmp/work-fractional-gap-check.log`, with exit
status in `/tmp/work-fractional-gap-check.exit`. Do not delete the scratch files
until this integrated build succeeds.

### Unbounded gap for general graphs — Lean verified

Namespace `Erdos184Work.FractionalGap`:
- For each prime p>=3, vertices are ZMod p + ZMod p, and edges are the three
  matchings y=x+i, i=0,1,2.
- `pairGraph_connected`, `pairGraph_regular`: any two distinct shifts form a
  connected 2-regular graph, using that their difference is a unit modulo p.
- `graph_regular`: the three-shift graph is cubic.
- `piece_cycle`, `fractional_cover`: the three pairs of shifts are valid cycle
  subgraphs, each with coefficient 1/2; every edge is covered exactly once.
- `odd_vertex_lower_bound`: for any all-odd finite graph, |V| <=2*|D| for every
  integral decomposition, from parity of the single-edge subfamily.
- `integral_lower_bound`, `number_lower_bound`: every decomposition of the
  three-shift graph needs at least p pieces.
- `number_upper_bound`: at most 3p pieces, so the family DOES satisfy a linear
  bound in its vertex count. It is NOT an Erdős184 disproof.
- `unbounded_integral_cost_at_fixed_fractional_cost`: for every real B there is
  such a graph whose integral decomposition cost exceeds B*(3/2), despite the
  exact half-integral three-cycle cover.

Thus a universal PURE MULTIPLICATIVE integrality-gap bound is false, not merely
unproved. Any unrestricted rounding route must allow an additive O(n) term or
include extra parity/local constraints. This does NOT exclude a bound restricted
to even graphs, and does NOT contradict the original conjecture.

### Finite even base — Lean verified

Namespace `Erdos184Work.EvenFractionalBase` reuses the 15-vertex 4-regular graph
`ThreeCycleObstruction.exampleGraph`, isomorphic to the line graph of Petersen.
`/tmp/ham_double_cover.py` enumerated its 160 Hamilton cycles and found an exact
four-cycle double cover. This search is NOT used as an axiom; four explicit walks,
their cycle/spanning properties, and edge multiplicities are checked by ordinary
Lean decide in the new module.

Four cycles (each starts and ends at zero):
1. 0,1,5,11,9,4,2,12,3,7,13,6,10,14,8,0
2. 0,7,9,11,4,14,2,3,13,10,6,5,12,1,8,0
3. 0,1,5,11,6,13,10,8,14,4,2,12,3,7,9,0
4. 0,7,13,3,2,14,10,8,1,12,5,6,11,4,9,0

Checked declarations:
- `hamilton_isCycle`, `hamilton_spanning`, `cover_twice`, `fractional_cover`.
- `four_hamilton_fractional_cover`: even degrees, four spanning cycle pieces,
  exact coverage with coefficients 1/2, total cost two.
- `number_eq_three`: combines the existing three-cycle partition and the
  existing kernel-LRAT proof excluding two cycles. This now explicitly proves
  the minimum-number equality, not just the earlier no-two-cycle statement.
- `close_through_fresh_vertex_isCycle`: a simple path avoiding z closes through
  z when its distinct endpoints are both adjacent to z.
- `no_two_path_completion`: two simple paths avoiding vertex zero, with disjoint
  internal edges and disjoint endpoint spokes, cannot complete all edges of the
  base graph. They would close to the forbidden two-cycle partition.

All printed final axioms are propext, Classical.choice, Quot.sound.
Standalone logs: `/tmp/fractional-gap-final-check.log` and
`/tmp/even-fractional-base-final-check.log`.

### Proposed even-gap amplification — NOT formalized

Delete vertex 0 from the above base. The four Hamilton cycles become Hamilton
paths on 14 vertices with endpoint pairs (1,8), (7,8), (1,9), (7,9). Treat
{1,7} as left ports and {8,9} as right ports. Join an even number b of these
blocks cyclically, right port 8 to next left port 1 and right port 9 to next
left port 7. The resulting simple graph should be 4-regular on 14b vertices.

Candidate four-cycle double cover: index cycles by (x,y) in Bool^2. On even
blocks use the path from left port x to right port y; on odd blocks swap x,y.
This matches across boundaries and should give four spanning cycles, hence
fractional cost two. A block lacking any wholly internal piece in a cycle-only
integral decomposition would have its internal edges partitioned into at most
two simple paths by the four boundary edges. `no_two_path_completion` excludes
that. This suggests at least one internal cycle per block, hence integral cost
>=b and an unbounded gap even on Eulerian graphs.

This construction and the restriction-to-paths argument have NOT been proved
in Lean. Do not claim an unbounded even integrality-gap theorem yet. In particular,
there is no Lean definition of the cyclic block family yet. For a future proof,
index the even ring by Fin m x Bool, with successor (j,false)->(j,true) and
(j,true)->(j+1,false), avoiding modular parity complications.

The original conjecture remains unresolved. A pure multiplicative fractional
rounding route for general graphs is now definitively excluded; an additive
Cn bound, a uniform low-degree theorem for minimal even cores, or a genuinely
superlinear counterexample family is still missing. Spec.lean is unchanged.

## Fractional-gap integration completed

The full integrated Work build passed, exit 0. No errors or sorryAx appear in
`/tmp/work-fractional-gap-check.log`; all printed final axioms are allowed.
Work.olean is current. The duplicate FractionalGap.lean and EvenFractionalBase.lean
scratch files were removed after successful integration. Work now has 12,740
lines. All builds and searches from this continuation have finished.

A direct structural check of the proposed even ring was run for 2,4,6,10 blocks:
28,56,84,140 vertices respectively, degree four everywhere, and the four proposed
Hamilton cycles cover every edge twice. This is only a check of those explicit
instances, NOT a Lean theorem for the infinite family and NOT a checked general
integral lower bound. The ring construction remains unformalized.

The original Spec.lean remains byte-for-byte unchanged with its sorry. No complete
proof or disproof of Erdős184 has been obtained. Do not submit the incomplete
Spec as if the auxiliary obstructions settled the original conjecture.

## Block restriction obstruction (new checked development)

`Submission/BlockRestriction.lean` passed its standalone check against the previous
Work cache. It has 437 lines and no placeholders; the printed axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound`. Its body has been appended to
Work. The integrated build is running as PID 37817, with log
`/tmp/work-block-restriction-check.log` and exit status
`/tmp/work-block-restriction-check.exit`. Check completion before removing the
standalone duplicate or using the updated Work cache.

New namespace `Erdos184Work.BlockRestriction`:

- `number_le_sum_of_even_partition`: subadditivity over indexed, edge-disjoint
  even spanning graphs.
- `degree_eq_sum_of_partition`: degree additivity for the same edge partition.
- `number_eq_half_degree_of_feedback_partition`: if each even part has the same
  feedback vertex z, the whole graph has optimum degree(z)/2.
- `base_partition_has_cycle_avoiding_zero`: an even edge partition of the
  15-vertex base must have a part with a cycle avoiding zero.
- `cycle_comap_acyclic_of_missing_vertex`: a proper injective restriction of a
  connected 2-regular subgraph is acyclic.
- `BlockModel G B`: a copy of B-minus-none inside G, with each old neighbor of
  none attached to exactly one external vertex and no other external edges.
- `BlockModel.trace`: localizes a global subgraph to the completed block,
  replacing its boundary edges by the old spokes at none.
- `trace_degree_some`, `trace_even`, `trace_partition`: localization preserves
  the internal degrees and evenness and sends edge partitions to edge partitions.
- `trace_forest_of_not_internal`: a cycle piece which is not wholly internal
  localizes to an even graph with feedback vertex none.
- **`BlockModel.exists_internal_cycle`**: if number(B) > degree_B(none)/2,
  every cycle-only decomposition of G has a piece wholly inside this block.
- **`card_blocks_le_number`**: pairwise vertex-disjoint obstructing blocks in
  an even graph force at least as many pieces as blocks.
- `number_eq_of_iso`: isomorphism invariance of the optimum.
- `completedBase`: the 15-vertex base transferred to Option BaseVertex, where
  BaseVertex is the fourteen nonzero vertices.
- `completedBase_number`, `completedBase_degree_none`, `completedBase_gap`:
  the completed base has optimum three and degree four at none.
- **`card_base_blocks_le_number`**: the block-count lower bound specialized to
  this explicit base.

This closes the *general restriction/lower-bound argument* for the proposed even
ring construction. It does NOT yet define that family in Lean or prove its four
Hamilton-cycle fractional cover. It does NOT provide a superlinear lower bound:
the block models in the theorem have pairwise disjoint vertex sets.

A useful simplification for constructing the four global cycles: combine two
consecutive blocks into one 28-vertex superblock. For cycle label (x,y), its local
Hamilton path is P_xy in the first block followed by P_yx in the second. It starts
at left port x and ends at right port x. Thus each of the four global cycles is a
cyclic concatenation of *identical* 28-vertex Hamilton paths across m superblocks.
This avoids modular parity in the global connectivity argument. Each local edge
and each boundary matching edge is used twice among the four labels.

An exact rational LP calculation on the previously identified non-graphic binary
minimal core (columns 2 through 13 in F_2^4) gives fractional optimum 12/5, versus
integral optimum three. Script `/tmp/core_fractional_exact.py` uses Sage's PPL
solver. This is an exploratory calculation, NOT a new Lean theorem or graph
counterexample. Minimality alone therefore does not force fractional exactness
in abstract binary systems; a graph-specific argument would be needed.

The original conjecture remains unresolved and Spec.lean has not been altered.

### Cyclic-path helper (standalone, checked)

`Submission/CyclicPath.lean` now passes a clean check against Work; see
`/tmp/cyclic-path-check.log`. It has no placeholders and uses only the permitted
axioms. It has NOT been integrated into Work yet.

Namespace `Erdos184Work.CyclicPath`:

- `pairedCycle m` is the ordinary cycle on `28*m` vertices, transported to
  `Fin m × Fin 28` through `finProdFinEquiv`.
- `pairedCycle_connected` and `pairedCycle_regular` hold for `0 < m`.
- `step (i,j)` increments j when j<27; at j=27 it becomes `(i+1,0)`.
- `position_step` proves compatibility with cyclic successor in `Fin (m*28)`.
- `pairedCycle_adj` characterizes adjacency as `step x = y` or `step y = x`.

This supplies the generic connectivity and regularity lemma for the 28-vertex
superblock approach. Still missing: the four explicit local permutations,
identification of their union with the block family, the twice-cover identity,
and construction of its `BlockModel`s. The infinite even fractional-gap theorem
is therefore still NOT proved.

Suggested cycle label order uses the existing h0,h1,h2,h3 walks, with labels
(0,0),(1,0),(0,1),(1,1). In a superblock, the second 14-vertex path swaps labels
1 and 2 and fixes 0 and 3. Delete 0 from the displayed walks and subtract one
from each remaining label to obtain permutations of Fin 14; concatenate the
first path with the swapped-label second path shifted by 14. Define explicit
inverse tables as well, so all later finite checks use ordinary `decide`.
The four global cycle graphs are relabelings of `pairedCycle m` by these local
permutations. Their adjacency can be expressed using just three block-index
relations: a=b, a+1=b, b+1=a. Finite identities can be verified uniformly in the
three Boolean flags (including m=1 and m=2, where flags can overlap).

### Integration completed

The full Work build for BlockRestriction passed with exit status 0. The log
`/tmp/work-block-restriction-check.log` contains no errors or sorryAx; all printed
new axioms are permitted. Work now has 13,178 lines, and its cached olean is
current. The duplicate `Submission/BlockRestriction.lean` was removed after that
successful build. No build remains running.

`Submission/CyclicPath.lean` (90 lines) was also rechecked against the updated Work
cache and compiled to `.lake/build/lib/lean/Submission/CyclicPath.olean`. Its final
log is `/tmp/cyclic-path-final-check.log`. It remains a separate development file.

Spec.lean remains unchanged (SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5).
The original conjecture is still unresolved; do not submit the incomplete file
as a finished solution.

## Infinite even fractional-gap family (completed standalone proof)

`Submission/EvenRing.lean` now has a complete, checked construction. Its clean
standalone log is `/tmp/even-ring-final-check.log` (exit 0); the displayed axioms
are only `propext`, `Classical.choice`, and `Quot.sound`. No native computation or
new axioms were used. Finite permutation and local incidence identities are
verified with ordinary `decide`.

The CyclicPath and EvenRing bodies have been appended to Work, in that order.
The full integrated build is running as PID 39517, with log
`/tmp/work-even-ring-check.log` and exit file `/tmp/work-even-ring-check.exit`.
Do not remove their standalone files until that build succeeds. The old separate
CyclicPath/EvenRing oleans should not be imported after the new Work cache is
installed, since Work now contains their declarations itself.

Namespace `Erdos184Work.EvenRing`:

- Four explicit permutations `order0` through `order3` of Fin 28, with explicit
  inverse tables, combine the old fourteen-vertex Hamilton paths into superblocks.
- `graph m`, for `[NeZero m]`, has vertex type `Fin m × Fin 28`.
- `cycle m i` relabels `CyclicPath.pairedCycle m` by the ith local permutation.
- `local_twice_cover` is a uniform finite identity in three Boolean block-index
  flags. `twice_cover` applies it to equality and cyclic successor of block indices.
- `cycle_le`, `piece_cycle`, `piece_spanning`, **`fractional_cover`**: four spanning
  connected 2-regular subgraphs of coefficient 1/2 cover every graph edge exactly
  once. Fractional cost is two, for every m.
- `slotEquiv` identifies two copies of the fourteen nonzero base vertices with
  Fin 28. `blockEmb`, `blockEmb_disjoint`, `exists_block_vertex` locate the 2m blocks.
- `graph_adj_block`, `graph_internal`, `graph_boundary`, **`blockModel`** verify all
  hypotheses of the general block restriction theorem, including unique external
  neighbors for the four ports.
- `trace_top_eq` is a general helper for block models.
- **`graph_regular`**, `graph_even`, **`graph_connected`**: the graph is connected
  and 4-regular, hence Eulerian.
- **`integral_lower_bound`**: `2*m ≤ Critical.number (graph m)`.
- `graph_edge_count`: exactly `56*m` edges.
- **`integral_upper_bound`**: `3 * Critical.number (graph m) ≤ 56*m`.
  This explicitly confirms that this family has a linear bound in its 28m vertices.
- **`unbounded_even_integral_cost_at_fractional_cost_two`**: for every real B,
  there is a connected 4-regular graph with an exact four-Hamilton-cycle fractional
  decomposition of total cost two, but every integral decomposition costs >2B.

The previously proposed infinite even-gap statement is now fully proved (not
merely checked on finite examples). It rules out pure multiplicative rounding
on even graphs, not just unrestricted graphs. It is NOT a counterexample to
Erdős184, and no part of this proof should be presented as its disproof.

The subsequent structural assessment produced no new theorem bounding arbitrary
minimal even cores. In particular, an unbounded gap in this family does not show
an unbounded gap in minimal cores: the family contains many disjoint internal
cycles, and extraction can discard the Hamilton-cover structure. A bounded gap
on minimal cores, a uniform low-degree theorem for them, or any other uniform
integral bound remains unproved. Spec.lean is still unchanged and unresolved.

### EvenRing integration verified

The integrated Work build passed with exit 0. The final log
`/tmp/work-even-ring-check.log` has no errors or sorryAx. All printed new axioms
are permitted. Work has 13,753 lines and its cached olean is current.

The duplicate CyclicPath.lean and EvenRing.lean source files and their now-stale
separate oleans were removed after successful integration. For further development,
import `Submission.Work`; the CyclicPath and EvenRing namespaces are now in it.
No builds or exploratory searches remain running.

Spec.lean is unchanged, with its original sorry and SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
The original conjecture is NOT settled, and the infinite even-gap theorem is NOT
its negation. No completed submission has been made.

## Additive-rounding reassessment (no new theorem)

The next continuation focused on the original missing integral bound rather than
constructing another obstruction. The checked fractional theorem gives cost at
most n-1. An integral rounding theorem with additive C*n, for any absolute C,
would therefore suffice; the even-gap examples only exclude pure multiplicative
rounding and do not exclude such an additive theorem.

No additive rounding proof was obtained. In particular:
- Clearing fractional denominators gives a multiple edge cover, not an integral
  edge partition of the original simple graph.
- Pairing paths into closed trails does not bound the number of simple cycles
  produced when repeated vertices are split.
- Dropping vertex/star constraints in a fractional cover does not justify
  rounding all incident cycles at constant additive cost.
- The low-degree premise for minimal even cores remains unproved.

This continuation made no changes to Work.lean or Spec.lean and established no
new Lean theorem. Work's previous successful build and cache remain current.
The original conjecture remains unresolved. No jobs were started or left running.

## Even-minimal rainbow-cycle obstruction (new checked work)

`Submission/RainbowCore.lean` (209 lines) has a complete standalone verification
in `/tmp/rainbowcore-final-check.log`. Its three printed theorems depend only on
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry` or native computation
is used. Its body has been appended to Work; the integrated build is running
as PID 40484, log `/tmp/work-rainbow-check.log`, exit file
`/tmp/work-rainbow-check.exit`. Work now has 13,970 lines. Wait for that build
before removing the standalone source and olean.

Namespace `Erdos184Work.RainbowCore`:

- `graph` has seven vertices and eleven edges:
  `01,12,20,03,31,04,41,15,52,16,62`.
- `graph_even`; vertex 1 has degree six.
- Deleting vertex 1 gives a tree on six vertices, checked via explicit paths
  and the tree edge-count characterization.
- `graph_minimal_and_number`: the feedback-vertex characterization proves
  EvenMinimal and optimum exactly three.
- `decomposition` consists of cycles `0-3-1-5-2-0`, `0-1-4-0`, and `1-2-6-1`.
- `triangle` is `0-1-2-0`.
- `triangle_rainbow`, `triangle_nonseparating`: the triangle hits each old
  cycle in one edge and its deletion leaves a connected graph.
- `sparse_union_threshold_is_tight`:
  `m + 2 = D.card + n + triangle.length = 13`.
- `even_minimal_rainbow_obstruction` bundles these properties with the lower
  bound for every cycle-and-edge decomposition.

Thus even-minimality plus a nonseparating rainbow cycle does NOT alone imply
an improvement. The strict inequality in `rainbow_cycle_improves_of_sparse_union`
cannot simply be dropped. This is NOT a counterexample to Erdős184: the
seven-vertex graph needs only three pieces.

Reassessment of core sparsity, additive rounding, and cycle recombination
produced no new uniform bound. No low-degree or bounded-size theorem for
arbitrary minimal even cores has been proved. Spec remains unchanged with its
original sorry; SHA256:
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
Do not submit this incomplete file as a solution to the original conjecture.

### RainbowCore integration verified

The full integrated build passed with exit 0. The final log
`/tmp/work-rainbow-check.log` has no errors or sorryAx. All printed new axioms
are permitted. Work has 13,970 lines and its cached olean is current.

The duplicate RainbowCore source and separate olean were removed. For further
development, import `Submission.Work`; RainbowCore is now in it. No jobs are
running. Spec remains unchanged and unresolved. No proof submission was made.

## Single-edge deletion from even graphs (new verified local result)

`Submission/SingleDeletion.lean` (126 lines) passed standalone verification and
was compiled to its own olean. Log: `/tmp/single-deletion-final-check.log`.
Its four printed theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
The body has been appended to Work (now 14,103 lines). Integrated build PID
40890; log `/tmp/work-single-deletion-check.log`; exit file
`/tmp/work-single-deletion-check.exit`. Remove the duplicate source and olean
only after the integrated build succeeds.

Namespace `Erdos184Work.SingleDeletion`:

- `even_decomposition_edgePieces_three_le`: in an even graph, if a valid
  decomposition has any single-edge piece, it has at least three of them.
  The single-edge subfamily is itself even and nonempty, hence contains a cycle.
- `even_decomposition_with_edge_improves_two`: such a decomposition can be
  improved by at least two pieces. This uses the existing scaled cycle-only
  conversion and the three-edge lower bound.
- `delete_edge_from_even_number`:
  `number G + 1 ≤ number (G.deleteEdges {e.val})` for every edge e of an even G.
  Restore e as a single-edge piece, then apply the two-piece improvement.
- `exists_proper_critical_with_larger_number`: every nonempty even G has a
  proper edge-critical subgraph with strictly larger optimum. Apply the existing
  edge-critical extraction after deleting an edge.

This sharpens local behavior; it is not a linear upper bound. In particular,
"edge-critical" and "even-minimal" are substantially different reductions.
A nonempty even graph is a strict local minimum under single-edge deletion,
although deletion of a whole cycle can move the optimum either way.

This continuation also reconsidered sparse-core preservation, fixed biclique
obstructions, and additive fractional rounding. No valid argument was obtained
for a uniform edge bound or degree bound on arbitrary even-minimal cores. No
assertion about such a bound has been added to Lean. Spec remains unchanged,
with the original sorry and hash
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
The original conjecture remains unresolved. No proof submission was made.

### SingleDeletion integration verified

The full integrated Work build passed (exit 0), with no errors or sorryAx in
`/tmp/work-single-deletion-check.log`. All new printed axioms are permitted.
Work has 14,103 lines; its cached olean is current. The duplicate SingleDeletion
source and olean were removed. Further development should import Submission.Work.
No builds or searches are running. Spec remains unchanged and unresolved.

## Additive-rounding continuation (no new theorem)

The next continuation concentrated on the actual missing conversion rather
than another auxiliary example. The checked fractional theorem has cost at
most n-1, so a uniform additive C*n loss when converting to an integral
edge-disjoint decomposition would suffice. The existing unbounded
multiplicative-gap families do not exclude this additive statement.

No proof of the additive bound was obtained. In particular:
- Clearing denominators only yields a decomposition of a multiple edge cover.
- Local transition pairings can produce closed trails with repeated vertices;
  splitting these into simple cycles has no established O(n) cost bound.
- A proposed vertex-by-vertex rounding must control both the residual coverage
  constraints and the number of new simple cycles. Neither control follows
  from the fractional theorem or ordinary flow integrality.
- No sparse-core preservation argument, bounded-degree theorem for arbitrary
  minimal even cores, or superlinear lower-bound family was established.

No Lean source was changed during this continuation. Work's last successful
build remains `/tmp/work-single-deletion-check.log`, exit 0; its cached olean
is current. No jobs are running. Spec retains its original statement and sorry.
The original conjecture remains unresolved, and no proof was submitted.

## Weighted-path induction reassessment (no new theorem)

This continuation inspected `Weighted.exists_weighted_degree_le` and
`Weighted.total_weight_le` for a possible integral analogue. The induction
removes a vertex of weighted degree at most one; that does not give an
integral constant-cost elimination. For example, uniform edge weight
1/(2r+1) on K_(2r+1) satisfies every cycle-weight constraint and gives
weighted degree below one, whereas ordinary degree is 2r and the existing
vertex-elimination construction pays r pieces. The complete graph itself
has a linear decomposition; this is only a limitation of the proposed
translation of the weighted argument.

The remaining issue is still a valid global rounding or recombination bound,
not an instance mismatch or a missing invocation of the weighted lemma.
No uniform integral bound, sparse-core preservation theorem, or superlinear
counterexample was obtained. No Lean file was changed. The last successful
Work build/cache is still the SingleDeletion integration. No jobs are running.
Spec is unchanged and the original conjecture is unresolved.

## Reference access and cycle-exchange reassessment (no new theorem)

Direct reference access remains unavailable. Attempts to query external DNS
through 1.1.1.1 and dns.google at 8.8.8.8 both timed out. No newer external
result was obtained or used.

The cycle-exchange approach was reconsidered, including whether exposing every
cycle could imply rigidity or a uniform size bound for even-minimal cores.
No proof of either implication was obtained. Individual cycle exposure does
not by itself supply a simultaneous exchange or an augmentation argument.
Neither rigidity, series-parallel support, nor bounded core degree may be
assumed on the basis of the finite exploratory checks.

No Lean source was changed. The last verified Work cache remains current,
there are no active jobs, and Spec still contains the original sorry. The
conjecture is unresolved and no proof was submitted in this continuation.

## Maximum-cycle exchange theorem (new checked development)

`Submission/MaximumCycles.lean` (369 lines) has a clean standalone check in
`/tmp/maximum-cycles-final-check.log`, and a standalone olean. All printed
axioms are permitted. Its body is now appended to Work (14,479 lines).
Integrated build PID 42014; log `/tmp/work-maximum-cycles-check.log`; exit file
`/tmp/work-maximum-cycles-check.exit`. Remove its duplicate source/olean after
that build succeeds.

Namespace `Erdos184Work.MaximumCycles`:

- `regular_two_card_edges`, `two_piece_sdiff`, `two_piece_degree`.
- `two_regular_pieces_intersection_bound_of_feedback`: two edge-disjoint
  connected 2-regular pieces whose union has a specified common feedback
  vertex share at most two vertices. The proof restricts to the union of their
  vertex sets minus that vertex, then uses the strict forest edge bound.
- `liftSubgraph_injective`, `lift_cycle_decomposition_exact`: exact cardinality
  when lifting a cycle decomposition to a larger ambient graph.
- `cycle_extension_exact`: any cycle in an even graph extends to a cycle-only
  decomposition of size `number (G \\ C) + 1`.
- `two_cycles_exchange`: two edge-disjoint cycles sharing at least three
  vertices have an edge partition into at least three cycles. Find a cycle
  avoiding a common vertex, then the residual retains degree four there.
- `cycle_piece_edgeSet_nonempty`, `replace_cycle_subfamily_exact`: exact
  cardinality bookkeeping for arbitrary cycle-family replacement.
- `maximum_decomposition_intersection_le_two`: any MAXIMUM-cardinality
  cycle-only decomposition has pairwise vertex intersections of size at most two.

The last conclusion is NOT a theorem about minimum decompositions. No theorem
identifies the minimum and maximum sizes for even-minimal cores. That remains
an unproved structural possibility. These new results do not settle Erdős184.

### A tested next strengthening fails (exploratory, not Lean)

An exact finite combinatorial check of three-cycle kernels with each pair
intersecting in one or two vertices found a counterexample to the proposed
claim that every such triple without a triple intersection recombines into two.
Script `/tmp/three_cycle_small_intersections.py`, log
`/tmp/three-cycle-small-intersections.log`. This is Python exploration, not a
Lean theorem. No assumption based on the false claim was added to Lean.

The kernel is the triangular prism with its three vertical matching edges
DOUBLED. Label its two triangles `0-3-5-0` and `1-2-4-1`, and double the matching
`01,23,45`. Its three given cycles have junction orders
`(0,1,2,3)`, `(0,1,4,5)`, `(2,3,5,4)`, using different copies of the doubled edges.
Every pair shares exactly two vertices and there is no triple intersection.
No two Hamilton cycles partition the kernel: each Hamilton cycle uses exactly
two vertical edges, but there are six vertical edges to cover. Each simple
Hamilton cycle can use at most one of the two parallel edges in each matching
pair, so it uses at most three vertical edges; the cut parity makes this two.

A simple nine-vertex realization subdivides one copy of each doubled edge,
using new vertices 6,7,8 respectively. The three cycles are
`0-1-2-3-0`, `0-6-1-4-5-0`, and `2-7-3-5-8-4-2`, of lengths 4,5,6.
The graph also has a five-triangle decomposition: the three local triangles
`0-1-6-0`, `2-3-7-2`, `4-5-8-4`, and the two horizontal prism triangles.
It is not even-minimal: the three vertex-disjoint local triangles already
form a proper even subgraph of optimum three. This does not disprove the
original conjecture or the unproved rigidity possibility for minimal cores.

No complete proof or disproof of the conjecture was obtained. Spec is unchanged.

## MaximumCycles integration completed

The full integrated Work build finished successfully (exit 0) in
`/tmp/work-maximum-cycles-check.log`. Work has 14,479 lines and the cached olean
is current. The duplicate `Submission/MaximumCycles.lean` and its standalone
olean have been removed. No uniform integral bound, core-rigidity theorem,
or counterexample to the original conjecture has been obtained. Spec is
unchanged and still contains its original sorry.

## Follow-up assessment after the successful integration

The minimum/maximum distinction was rechecked. Cycle-criticality exposes each
individual cycle in a minimum decomposition, but supplies neither simultaneous
exposure of a family nor inheritance of even-minimality after cycle deletion.
The maximum-decomposition exchange theorem therefore cannot currently be used
to bound the optimum. Neither a uniform low-degree theorem for even-minimal
cores nor an additive fractional-to-integral rounding theorem was established.
No further Lean declarations or assumptions were added. Spec remains unchanged;
no proof or disproof of the original conjecture is available for submission.

## Rigidity and hereditary minimality (new standalone verification)

`Submission/Rigidity.lean` has passed its standalone check without warnings or
errors. Log: `/tmp/rigidity-final-check.log`. All printed axiom dependencies
are permitted. Its body has now been appended to Work; an integrated build is
being launched with log `/tmp/work-rigidity-check.log` and exit file
`/tmp/work-rigidity-check.exit`. Remove the duplicate Rigidity source/olean only
after that integrated build succeeds. Do not import both the new Work and the
old standalone Rigidity module, as their declarations will be duplicated.

Namespace `Erdos184Work.Rigidity`:

- `CycleRigid G`: every cycle-only decomposition has cardinality `number G`.
- `combine_cycles_exact`, `extend_cycles_exact`: exact cardinality when
  combining an even edge partition or extending a cycle decomposition of an
  even subgraph to the ambient even graph.
- `CycleRigid.number_sdiff_add`: `number R + number (G \ R) = number G`
  for even R <= G under the explicit rigidity hypothesis on G.
- `CycleRigid.mono`: rigidity is inherited by even subgraphs.
- `CycleRigid.evenMinimal`: rigidity implies even-minimality.
- `card_le_number_of_hereditary_minimal`: cardinality lower bound obtained by
  adding cycles one at a time; it explicitly assumes minimality of EVERY even
  subgraph, not just of the full graph.
- `rigid_iff_hereditarily_evenMinimal`: an even graph is rigid iff every even
  subgraph is even-minimal.
- `CycleRigid.intersection_le_two`: transfers the maximum-decomposition
  intersection bound to all decompositions under explicit rigidity.
- `minimal_core_rigidity_iff_heredity`: the proposed general inheritance
  statement for even-minimal cores is EQUIVALENT to their proposed rigidity.
  Neither side is proved by this equivalence.

These results identify a logical gap; they do not fill it. No uniform linear
integral bound or counterexample family has been obtained. Spec is unchanged.

## Exact finite follow-up tests (exploratory, NOT Lean proofs)

1. `/tmp/minimal_nonrigid.cpp`, executable `/tmp/minimal_nonrigid`, log
   `/tmp/minimal_nonrigid.log`: all Eulerian edge subsets of K8 were tested.
   There were 398,636 inclusion-minimal nonrigid labeled graphs, all with
   minimum decomposition number two. This is consistent with, but does NOT
   prove, the assertion that every nonrigid even graph contains a two-cycle
   nonrigidity witness. The computation finished; no search is running.

2. `/tmp/triangle_rigidity_kernels.py`, log
   `/tmp/triangle_rigidity_kernels.log`: all 40 three-cycle junction kernels
   with pair-intersection sizes in {1,2} and no triple intersection are
   nonrigid. Their (minimum, maximum) spectra are (2,3), (2,4), or (3,5).
   This retains the earlier prism obstruction: some triples cannot merge into
   two, but they can instead split into more pieces. This finite test has not
   been lifted to a Lean theorem about arbitrary cycle walks.

### A new obstruction to EVEN nonadjacent compression

The earlier wheel counterexample was not Eulerian. A parity-preserving
nonadjacent transfer also fails, as shown by this separate eight-vertex
construction (currently mathematical/Python exploration, not formalized).

Original graph G has edges:
`01,04,41,05,51,23,26,63,27,73,12,30`.
Vertices 0,1,2,3 have degree four, and 4,5,6,7 have degree two.
It is a subdivision of the multigraph consisting of tripled edges 01 and 23,
together with the two edges 12 and 30.

Every cycle partition of G has exactly three pieces: the cut separating
{0,1,4,5} from {2,3,6,7} has exactly the two edges 12 and 30. They must occur
in one cycle, which uses one of the three internally disjoint 0--1 paths and
one of the three 2--3 paths. The remaining two paths on each side form one
cycle each. Thus G is rigid; the newly proved rigidity theorem would imply
EvenMinimal G once this concrete rigidity argument is formalized.

Now transfer the neighbors of 7 to 5. The two moved edges are 27 and 37,
replaced by 25 and 35. The vertices 5 and 7 were nonadjacent, had equal degree
two, and had no common neighbors. The new graph H is still even, with degree
four at 5 and degree zero at 7. It has the two-cycle decomposition
`5-0-1-2-3-5` and `5-1-4-0-3-6-2-5`.
Its optimum is two, certified below by degree four. Exact enumeration reports
spectrum (3,3) for G and (2,4) for H.

This rules out parity-preserving, degree-increasing NONADJACENT compression
as a general monotonicity tool, even on rigid/even-minimal graphs. It does not
settle the distinct proposed restrictions to adjacent transferred vertices,
or to nonadjacent vertices with common neighbors. Those remain unproved.

No result in this section disproves the original O(n) conjecture.

## Rigidity integration completed

The integrated Work build passed, exit 0, with no errors or sorryAx. The
standalone Rigidity source and olean were removed after the successful build.
Work has 14,728 lines, and its cache is current. All finite tests described
above have finished. Spec is unchanged and still contains the original sorry.
No complete proof or disproof is available for submission.

## Parity-preserving compression follow-up (exploratory, not Lean)

The previously untested restrictions have now been examined. No Lean source
was changed in this continuation. The verified Work cache remains current at
14,728 lines. All finite tests below have completed; no jobs are running.

### Adjacent EVEN compression can have unbounded loss

For r >= 3, form G_r from a chain of junctions a_0,...,a_r. Between each
successive pair put four internally disjoint paths: one direct edge and three
length-two paths with fresh internal vertices. Also add two short a_0--a_r
paths: the direct edge a_0 a_r and a length-two path through one new vertex w.
The graph is simple, even, has 4r+2 vertices and 7r+3 edges. Both endpoints
have degree six, internal junctions have degree eight, and all other vertices
have degree two.

Transfer the four private neighbors of a_r to a_0. The vertices are adjacent,
have equal initial degree, and have exactly the common neighbor w. Four edges
are moved, so evenness is preserved. The resulting graph H_r has an r-junction
ring of four parallel paths per side, plus the pendant triangle a_0-a_r-w-a_0.
It has optimum five: four cycles go around the ring, and the pendant triangle
is the fifth. Degree ten at a_0 gives the matching lower bound.

G_r has optimum r+2. Every simple cycle is either local to one four-path
bundle, the short triangle, or a global cycle using one long path from each
bundle and one short path. A decomposition containing the short triangle has
2r+1 pieces. Otherwise its two short paths lie in two separate global cycles;
the two remaining paths per bundle give r local cycles, for r+2 pieces.
Thus these are the only two possible cycle-partition cardinalities. For r>=4,
the adjacent even transfer strictly lowers the optimum, by r-3.

Exact Python checks: `/tmp/even_adjacent_compression.py`, log
`/tmp/even_adjacent_compression.log`. For r=3,4,5 the (minimum,maximum) pairs
are respectively (5,7), (6,9), (7,11) before transfer, and (5,7), (5,9),
(5,11) afterwards. These are exact cycle enumerations, not Lean proofs.
The family is NOT even-minimal: removing the two short paths leaves a proper
even subgraph with optimum 2r. It therefore does not refute a restriction
specifically to even-minimal graphs and adjacent vertices.

### Common neighbors do not rescue NONADJACENT compression, even on cores

A targeted generator of rigid series-parallel cores found a smaller distinct
obstruction. The search script was `/tmp/rigid_common_compression.py`, log
`/tmp/rigid_common_compression.log`. Its first ten-vertex example simplifies to
this nine-vertex graph G (data in `/tmp/rigid_common_compression_small.txt`):

`01,12,20,13,32,14,42,45,52,46,62,07,71,08,81`.

The junction kernel on 0,1,2,4 has tripled paths 01 and 24, doubled paths 12,
and single edges 02 and 14. Each cycle uses exactly two of the paths belonging
to the three multiple bundles (01,12,24). There are eight such paths in total,
so every cycle partition has exactly four pieces. Equivalently, put weight
1/2 along each of these paths and weight zero on 02 and 14: every cycle has
weight one, and total weight is four. Thus G is rigid and hence even-minimal
(the general implication is verified in Rigidity, but the concrete example
has NOT yet been formalized).

Transfer from vertex 4 to vertex 0. Both vertices have degree four, are
nonadjacent, and have common neighbors {1,2}. The private neighbors {5,6}
move from 4 to 0. The result is a subdivision of a triangle with each side
tripled, hence has optimum three (three global triangles; degree six gives
the lower bound). Exact enumeration gives (min,max)=(4,4) for G and (3,4)
for the transferred graph. Thus adding a common-neighbor requirement does
not repair nonadjacent compression, even on rigid/even-minimal graphs.

The separate targeted adjacent-core test `/tmp/rigid_adjacent_compression.py`
finished with 1,652 nontrivial tests on generated rigid cores of optimum four
through seven, with no decrease. This finite absence is NOT a theorem. A
monotonicity statement restricted simultaneously to even-minimal graphs,
adjacency, and parity preservation remains unproved, and no uniform bound
has been derived from it.

These examples all have linear decomposition size in their vertex count.
They refute auxiliary compression rules, NOT the original conjecture.
Spec remains unchanged with its original sorry; no proof was submitted.


## Rigidity base cases (newly verified)

`Submission/BaseRigidity.lean` compiled successfully; log
`/tmp/base-rigidity-check.log`. Its results have been appended to Work. The full integrated build passed
with exit 0 in `/tmp/work-base-rigidity-check.log`, and the duplicate source
and olean have been removed.

New declarations in `Erdos184Work.Rigidity`:

- `twice_card_eq_degree_of_cycle_hits`: any cycle-only decomposition of a graph
  whose cycles all meet v has twice its cardinality equal to degree(v).
- `rigid_of_cycle_hits`: every even graph with a feedback vertex is rigid.
- `rigid_bot` and `cycle_hits_of_single_cycle`.
- `rigid_of_number_le_one`: every even graph of optimum at most one is rigid.
- `rigid_of_evenMinimal_number_le_two`: every even-minimal graph of optimum
  at most two is rigid.
- `rigid_of_saturated_evenMinimal`: saturation degree(v)=2*number(G) gives
  rigidity for an even-minimal graph.

Both printed axiom lists contain only propext, Classical.choice, Quot.sound.
These do NOT prove arbitrary core rigidity or a uniform integral bound.

## Nongraphic regular-matroid experiments (exploratory, not Lean)

`/tmp/r10_fractional.py`, log `/tmp/r10_fractional.log`: R10 represented by
binary columns [1,2,4,8,16,7,14,28,25,19], confirmed isomorphic in Sage to
`matroids.named_matroids.R10()`. Full support is minimal and rigid with
optimum two but exact fractional optimum 5/3. Thus rigidity does not imply
fractional exactness for regular matroids in general. This is not graphical.

`/tmp/r10_two_sum.py`, log `/tmp/r10_two_sum.log`: chains of two-sums:

- 1 block: 10 elements, min/max 2/2, proper support maximum 1, fractional 5/3.
- 2 blocks: 18 elements, min/max 3/3, proper support maximum 2, fractional 9/5.
- 3 blocks: 26 elements, min/max 3/4, proper support maximum 3, fractional 29/15.

The three-block example is NOT minimal. These calculations neither disprove
rigidity of regular-matroid minimal cores nor a bounded fractional gap for
such cores, and say still less about the graph-specific conjecture.


## Unit-cycle weight certificates (new verification)

`Submission/CycleCertificates.lean` passed a clean standalone check. Log:
`/tmp/cycle-certificates-final-check.log`. All printed axioms are among the
permitted three. The module has been appended to Work, and the integrated
build passed with log `/tmp/work-cycle-certificates-check.log` and exit
file `/tmp/work-cycle-certificates-check.exit` equal to 0. The duplicate
scratch source and olean have been removed.

New namespace `Erdos184Work.CycleCertificates`:

- `UnitCycleWeight G w`: every simple cycle has total edge weight exactly one.
  Weights may be signed. Existence for arbitrary rigid graphs is NOT proved.
- `subfamily_weight`, `cycle_edge_weight`, `UnitCycleWeight.piece_weight`,
  `UnitCycleWeight.card_eq_total`, `UnitCycleWeight.number_eq_total`.
- `UnitCycleWeight.rigid`: a unit-cycle weighting forces rigidity of even G.
  The converse is NOT proved.
- `UnitCycleWeight.number_le`: if additionally each edge weight is at most
  one, then number(G) <= |V|-1, by the checked signed weighted dual inequality.
- `UnitCycleWeight.mono`: certificates restrict to graph subgraphs.
- `constant_length_certificate`, `constant_length_rigid_and_bound`: all
  cycles having a fixed positive length gives a bounded unit certificate.
- `feedbackWeight`, `feedbackWeight_total`, `feedbackWeight_certificate`,
  `feedbackWeight_le_one`, `saturated_core_certificate`: half weight on edges
  at a feedback vertex provides a certificate, including saturated cores.
- `markerWeight`: half weight on a specified graph's edge set.
- `marker_certificate_acyclic`: a marker graph whose half-weight function is
  a unit-cycle certificate must be acyclic.
- `marker_certificate_number_bound`: such a marker graph F <= G has
  2*number(G) = |E(F)| <= |V|-1. This is the half-linear special case.
- `even_number_bound_of_core_certificates`,
  `even_half_bound_of_core_marker_certificates`, and
  `asymptotic_of_core_certificates`: conditional reductions with certificate
  existence left as an EXPLICIT UNPROVED HYPOTHESIS.

Strengthened existing cycle-deletion obstruction, namespace `CycleDeletion`:

- `base_cycle_length`: every cycle of the nine-vertex base is a triangle.
- `base_rigid`: the base (three disjoint triangles) is rigid.
- `base_evenMinimal`: the base is even-minimal.
- `cycle_deletion_to_rigid_core`: deleting the displayed cycle from fullGraph
  increases the optimum from two to three even though the remaining graph is
  a rigid minimal core. Thus adjoining a cycle to a rigid core can DECREASE
  its optimum. This refutes that auxiliary monotonicity route, NOT Erdős 184.

The attempt to prove a linear bound from rigidity ALONE did not succeed.
The certificate result is a sufficient condition, not an assertion that
rigid graphs have these certificates. No original conjecture is settled.

### Further theoretical construction (not yet Lean formalized)

For odd r >= 3, r disjoint triangles with ports a_i,b_i can be joined by the
single cycle consisting of matchings a_i--b_(i+1) and a_i--b_(i-1). The result
has a two-cycle decomposition: direct local a_i--b_i edges plus one matching,
and the two-edge local paths through the third vertex plus the other matching.
This gives loss r-2 by adjoining ONE cycle to a rigid core. Indices are modulo r;
the external union is one cycle because gcd(2,r)=1.

A connected version should use a cactus chain of r squares, each square formed
by two two-edge paths between successive junctions a_(i-1),a_i, with ports x_i,y_i.
The same two external matchings give a single added cycle for odd r. Two global
cycles use respectively paths x_i--a_(i-1)--y_i and x_i--a_i--y_i. Each path family
has distinct internal junctions, so the two displayed global cycles are simple.
The base cactus has optimum r and is rigid. This argument is exploratory and
has NOT been checked in Lean; no numerical experiment is offered as proof.
Both constructions still have only linear optimum in their vertex count.


## Failure of diminishing returns (new Lean verification)

`Submission/DiminishingReturns.lean` passed a clean standalone check; log:
`/tmp/diminishing-returns-final-check.log`. Only the permitted three axioms
occur. Its body has been appended to Work. The integrated build passed
with log `/tmp/work-diminishing-returns-check.log` and exit status file
`/tmp/work-diminishing-returns-check.exit` equal to 0. The duplicate source
and olean have been removed.

The intended heredity argument would use submodularity on even subgraphs:
for edge-disjoint even A,B,C,

    number(A+B) + number(A+C) >= number(A) + number(A+B+C).

This inequality is FALSE, even when A is a connected rigid minimal core and
B,C are edge-disjoint triangles. A construction was found algebraically, not
by a blind numerical search, then checked completely in Lean.

On vertices 0,...,6:

- A edges: 01,02,12,03,34,14,05,56,16.
  These are four internally disjoint paths between 0 and 1.
- B edges: 23,35,25.
- C edges: 24,46,26.
- number(A)=number(A+B)=number(A+C)=2; number(A+B+C)=3.
- The upper bounds are explicit simple-cycle partitions.
- The lower bounds are degree certificates: degree(0)=4 in A and A+B;
  degree(2)=6 in the full graph.
- A+C is isomorphic to A+B by swapping 0/1, 3/4, and 5/6, fixing 2.
- A minus vertex 0 is a tree, proving A is rigid and even-minimal.
- The full graph is NOT even-minimal: its degree-six vertex 2 is saturated
  for optimum three, but the cycle 0-3-4-1-0 avoids 2. The verified saturation
  theorem rules out minimality. Consequently the full graph is not rigid.

New namespace `Erdos184Work.DiminishingReturns`:

- `number_le_cycle_family`: generic finite-family upper bound from explicit
  cycle walks, pairwise edge disjointness, and coverage.
- Graph definitions and explicit walks, parity and connectivity results.
- `base_core_and_number`, `withLeft_number`, `withRight_number`, `full_number`.
- `increments_disjoint`, `triangleLeft_graph`, `triangleRight_graph`.
- `strict_failure`: the strict submodular-inequality violation, retaining all
  stated hypotheses on A and both even increments.
- `full_not_evenMinimal`, `full_not_rigid`.

This closes off a possible diminishing-returns proof of hereditary core
minimality. It is NOT a counterexample to core rigidity or Erdős 184. No
new uniform bound for arbitrary minimal cores has been established, and
Spec.lean is unchanged with its original sorry.

### Stronger short-cycle loss construction (mathematical, not yet Lean)

A simpler connected family shows that adjoining a TRIANGLE, not a long cycle,
can lower the optimum by an arbitrarily large amount. This also rules out
bounding the loss solely by the length of the added cycle.

For r >= 3, let A_r be a chain of r squares. The i-th square consists of the
paths a_(i-1)--x_i--a_i and a_(i-1)--y_i--a_i, with all x_i,y_i private and
junctions a_0,...,a_r distinct. Then A_r has 3r+1 vertices and 4r edges.
It is a cactus: its only simple cycles are the r constituent squares, hence
its optimum is r, it is rigid, and every proper even subgraph has smaller
optimum. A marker certificate is the path through all x_i, with half-weight
on its 2r edges.

Choose an interior square, e.g. i=2, and add the triangle on a_0,a_r,x_2.
All three edges are absent from the base when r>=3. The full graph has a
partition into exactly two simple cycles:

- P plus edge a_r--a_0, where P is the a_0--a_r path through all x_i;
- Q plus path a_r--x_2--a_0, where Q is the a_0--a_r path through all y_i.

The cycle lengths are 2r+1 and 2r+2. They are edge-disjoint, and x_2 is not on
Q. Degree four at a_0 proves the matching lower bound two. Thus adding this
single triangle changes the optimum from r to two, a loss of r-2, while the
base is connected and rigid/even-minimal.

The explicit edge-disjointness, coverage, and simple vertex sequences were
checked by Python for r=3,4,5 as a sanity check, but the general construction
and cactus characterization are NOT yet Lean formalized. This is not a
counterexample to Erdős 184: the base optimum is r on 3r+1 vertices.

## Cut characterization of marker certificates (new verification)

`Submission/CutCertificates.lean` passed a standalone Lean check, exit 0,
with log `/tmp/cut-certificates-final-check.log`. Only the allowed axioms occur.
Its body has been appended to Work (now 15,624 lines). The integrated build
passed with log `/tmp/work-cut-certificates-check.log` and exit file
`/tmp/work-cut-certificates-check.exit` equal to 0. Work's cached olean is
current. The duplicate standalone source has been removed.

New `CycleCertificates` lemmas:

- `marker_certificate_complement_acyclic`: the unmarked complement G \\ R
  of a marker certificate is a forest.
- `marker_certificate_edge_bound`: such a G has at most 2*(n-1) edges.
- `markerCount`, `marker_weight_count`, `marker_parity_count`: real and mod-two
  walk weights are expressed through the count of marked edges.
- `marker_certificate_cut`: there is a label V -> ZMod 2 such that
  R.Adj u v iff G.Adj u v and label u != label v.

New generic namespace `CutParity`:

- `weight`: mod-two sum of a symmetric edge function along a walk.
- `close_path_weight_zero`, `weight_bypass`: simple-cycle vanishing implies
  that bypassing repeated vertices preserves weight. The proof uses the
  library's bypass recursion; its removed loops are cycles or backtracks.
- `closed_weight_zero`: vanishing on simple cycles implies vanishing on
  every closed walk.
- `weight_eq_of_endpoints`: walk weight is independent of the walk.
- `exists_label`: any mod-two edge function vanishing on all simple cycles
  has the form w(uv)=label(u)+label(v), for adjacent u,v. Component roots
  are chosen using quotient representatives. No finiteness is required.

These results prove consequences of a certificate, NOT certificate existence
for even-minimal cores. The original conjecture remains unsettled, and Spec
is unchanged with its sorry.

### Additional fractional-gap investigation (not Lean formalized)

The exact R10 attachment-port check finished:
`/tmp/r10_ports.py`, log `/tmp/r10_ports.log`, exit 0.
All nine choices of a second attachment port in a three-block R10 two-sum
had full min/max 3/4, proper-support maximum 3, and 1744 minimal supports
of optimum at least three. Their largest exact fractional gap was 5/3
(integral 3 versus fractional 9/5). This is finite evidence, not a bound.

A proposed universal factor-two gap for arbitrary binary minimal cores is
FALSE. A mathematical counterexample was constructed as follows; its
classification argument has not been formalized in Lean.

Let B_r be the binary code on E(K_r) generated by all cuts and the all-ones
word. For r>=5, all its nonzero proper codewords are minimal supports:
nontrivial cuts are incomparable, their complements are incomparable,
no two nontrivial cuts are disjoint, and two cuts cannot cover K_r (the
four membership classes would have to be independent singletons).
Thus the full word has circuit-partition optimum two.

Take the binary two-sum of two copies of B_r along edge 01. The full support
has optimum exactly three and every proper codeword has optimum at most
two. Indeed a global circuit is either a local circuit avoiding the port
or a union of port circuits with both port copies removed. Full support
requires an odd number of cross-circuits. One cross-circuit leaves a nonempty
local circuit in each block; three pieces are also obtained canonically.
For a proper codeword, at least one of the two underlying block words is
proper (or zero), and the same classification gives at most two pieces.
Consequently this is a binary even-minimal core of optimum three.

There is an explicit fractional cover of total 1+4/(r-2): use the two local
complements of the stars at 0 and 1 in each block, each with coefficient
1/(r-2), and every cross-circuit joining complements of stars at w,z not
in {0,1}, each with coefficient 1/(r-2)^2. Edge-by-edge sums are one.
For r=11 the cost is 13/9, so twice the fractional cost is 26/9<3.

`/tmp/complement_cut_gap.py` checks the base incomparability and all 108 edge
cover equations exactly over rational numbers, without searching. Log:
`/tmp/complement_cut_gap.log`. The minimum/core classification is the
mathematical argument above, NOT a Lean proof. This code is nongraphic;
no original graph counterexample or graph-specific gap obstruction follows.
In particular the bounded-gap question for graphical minimal cores remains
UNPROVED, as do rigidity and bounded-degree assertions for arbitrary cores.

## Continuation status: finite normalization is NOT checked

The third normalization attempt exited 137 (memory exhaustion):
`/tmp/small-order-normalization-check3.exit`. No normalization-completeness
claim follows from `SmallOrderNormalization.lean`; this auxiliary file is
still an unsuccessful development attempt. Do not import an old olean as
verification of the current source.

The separate `FastMarkedOrder.fastNext_eq` result is checked for all orders.
`FourKernelCertificates.lean` also completed successfully (exit 0): it proves
alternatives for 47 explicitly given representatives, not completeness of
those representatives. In particular, the four-, five-, six-, and seven-color
computations do NOT yet exclude arbitrary hypothetical cores of number three.
Even such an exclusion would not itself establish the general conjecture.

A renewed review found no applicable cycle-decomposition bound in Mathlib.
The actual `Subgraph.coe` is a graph on the subtype of subgraph vertices, so
there is no spanning-vertex interpretation counterexample. No new general
mathematical implication was established: minimal-cofactor accessibility,
rigidity of arbitrary minimal graphical cores, a uniform core degree bound,
and the original linear decomposition bound all remain unproved here.
`Spec.lean` has not been changed or resubmitted.

### Structural order normalization now checked (supersedes the failure above)

New modules, with clean principal axiom audits:

- `MarkedOrderCycle.lean`: recursive successor maps are conjugates of full
  cyclic permutations. Insertion of a new marker preserves full cyclicity.
  `Marked.numberedPerm_isCycleOn` is proved for every natural order size.
- `OrderNormalizationTheory.lean`: `raw_injective`, `raw_next`,
  `normalized_valid_all`, `normalized_first_all`,
  `normalized_orientation_all`, and `normalized_support` hold for ALL n.
- `SmallOrderNormalization.lean` has been replaced by corollaries of those
  general theorems and now checks successfully without finite enumeration.

Successful logs: `/tmp/marked-order-cycle-check3.log`,
`/tmp/order-normalization-theory-check2.log`, and
`/tmp/small-order-normalization-structural.log`. All checked principal
axiom lists are exactly subsets of propext, Classical.choice, Quot.sound.

This fixes the normalization subproblem only. The general core bound and the
original conjecture are still unresolved. No change has been made to Spec.

### Further checked modules in the same continuation

- `FourNumericalPatterns.lean`: `classified` proves the nine-orbit numerical
  classification of four-color contact multiplicities. A 50-entry witness
  lookup is checked for all 729 six-tuples by ordinary `decide +kernel`.
  Log `/tmp/four-numerical-patterns-check.log`, exit 0.
- `FourContactPatterns.lean`: `four_contacts_classified` applies this to actual
  four-cycle subfamilies of maximum decompositions under degree <=4 and the
  established three-subfamily minimum bounds. Log
  `/tmp/four-contact-patterns-check2.log`, exit 0.
- `NormalizedKernel.lean`: a color-preserving edge equivalence transports
  arbitrary recursively ordered kernels to ordinary cyclic vertex words.
  Exact full counts, minimality, rigidity, and all color-subfamily minimum
  and maximum bounds are preserved. Log `/tmp/normalized-kernel-check3.log`,
  exit 0. In particular, these statements are not finite experiments.

All principal printed axiom lists use only the permitted three axioms.

### Targeted tests of a possible rank-three reduction (not proofs)

Question tested: must a nonrigid minimal binary core contain one of optimum
three? This remains UNPROVED, and it is not presently available as a step
from the finite optimum-three analysis to the original conjecture.

- `/tmp/first_bad_core_grid_stats.cpp`: all 4095 one-generator extensions of
  the cut code of K_(4,5). No nonrigid minimal cores at all; this particular
  family therefore does not substantively test the desired higher-core step.
- `/tmp/first_bad_core_lifts.cpp`: all 2048 elementary parity lifts of PG(3,2).
  46,244 counted nonrigid minimal supports of optimum three, none above three;
  105 entire lifted codes have no such support.
- `/tmp/first_bad_core_lifts19.cpp`: all 8191 nontrivial hyperplane/parity-lift
  transforms of the known nineteen-element optimum-four core. This run tests
  FULL-support first obstructions: it stops a candidate as soon as any bad
  optimum-three core occurs, and consequently is NOT a test of every possible
  higher subcore in a rejected candidate. There were 708 candidates with no
  bad optimum-three support; no first bad full support was found. Exit 0.

These are exact C++ explorations of nongraphic systems, not Lean theorems and
not searches for counterexamples to Erdos 184. They do not justify assuming
minimal-cofactor accessibility or a rank-three obstruction theorem.

### Canonical pure-kernel reduction now checked

The current chain PairJunctionCoding, JunctionPairCoding, PairSlotMarkers,
CanonicalPairLayout, CanonicalPairKernel, JunctionReindex,
IndexedKernelRestrictions, and CanonicalThreeReduction has successful builds.
`CanonicalThreeReduction.exists_canonical_kernel` encodes a hypothetical
nonrigid even-minimal graph of optimum three by a natural color count l >= 4,
pair multiplicities in Fin 3, sorted marker placements in Fin ((l*l)*2), and
recursive cyclic orders. Its conclusion preserves exact minimality,
nonrigidity, maximum bounds on every color subfamily, and an optimum <=2
bound on every three-color subfamily. It is a reduction, not an exclusion.

The two-incidence APIs use Nat.card, avoiding Fintype-instance mismatches.
Kernel transport modules use an explicit classical DecidableEq instance on
dependent sigma label types. CanonicalPairLayout keeps its support family
abstract and seals successor expressions to avoid elaboration blowups.

The updated combined audit `AxiomCheckCanonicalKernels.lean` passed against
the current sources, including IndexedKernelRestrictions.restrictions and
CanonicalThreeReduction.exists_canonical_kernel. Log:
`/tmp/axiom-check-canonical-kernels-current.log`. All audited results depend
only on propext, Classical.choice, and Quot.sound.

The arbitrary-optimum core bound, and hence Erdos 184, remain unproved.
Spec.lean is unchanged; no partial result has been submitted as a settlement.

### Private-marker and batch series transport now checked

New current modules (all principal axiom checks use only the permitted three):

- SeriesSupportTransport: SupportTransport.refl/trans/ofEmbedding; exact
  partition-spectrum and maximum-bound transport; coordinate duplication via
  a point-code series extension.
- LabelKernelSubdivision: subdivision of any non-loop labelled edge through
  a fresh vertex; exact support transport, spectra, minima, minimality, rigidity.
- LabelKernelSuppression: inverse suppression at a private degree-two vertex,
  excluding the case where suppression would make a loop. Its two incident
  edges may lie in a parallel-edge kernel. Every color-subfamily spectrum is
  preserved if those two edges have the same color.
- WordKernelSuppression: constructs the suppression data for a private marker
  of a cyclic word with at least three markers.
- RestrictedWordKernel: color restriction is an exact support embedding; it
  composes with suppression when the marker is private only in that subfamily.
- CanonicalWordFormat: canonical words enumerate exactly their marker set,
  start at its minimum, and have second < last except for two-marker cycles.
  `private_slot_spectrum` applies restricted suppression directly to canonical
  pair slots when A intersection pairSet p is a singleton.
- FiberSupportTransport: exact transport along nonempty coordinate fibers,
  assuming valid-support saturation and the expansion validity equivalence.
- ParitySeriesCertificate: a batch certificate proves those two hypotheses.
  Parent links through private vertices strictly decrease a natural rank and
  force every valid support to be constant on each fiber. ZMod 2 endpoint
  parity identifies the coarse code. Exact spectra and minimality follow.
- SeriesCertificateData: finite computable certificate data and a decidable
  validity predicate; it uses no native-computation axioms.
- SeriesCertificateExample: an explicit ordinary `decide +kernel` check for
  expanding two parallel edges into two three-edge paths (a six-cycle).

Successful current logs include /tmp/label-kernel-subdivision-check5.log,
/tmp/label-kernel-suppression-check2.log, /tmp/word-kernel-suppression-check2.log,
/tmp/restricted-word-kernel-check.log, /tmp/canonical-word-format-check3.log,
/tmp/fiber-support-transport-check.log, /tmp/parity-series-certificate-check3.log,
/tmp/series-certificate-data-check.log, /tmp/series-certificate-example-check.log.
The combined suppression audit passed at /tmp/axiom-check-kernel-suppression.log
before the final data/example modules were added; those passed individually.

Remaining: repeated suppression has NOT yet been identified with the precise
normalized word obtained by deleting all private markers. Batch certificates
now provide an alternative exact-check route for finite layouts. No four-,
five-, six-, or seven-color completeness theorem has been added in this step.
No arbitrary-optimum core bound was found. Spec is still unchanged and unsolved.

### Additional finite-input interfaces checked

- SmallWordTables.lean: explicit normalized word sets for two through six
  markers, of sizes 1, 1, 3, 12, 60. `complete0` through `complete4`, and
  `complete` for n <= 4, are checked against every recursive Marked.Order by
  ordinary `decide +kernel`. The current build passed at
  /tmp/small-word-tables-check2.log, exit 0.
- CanonicalPairAdmissibility.lean: `counts_numeric` transports the established
  triple contact constraints into pure PairIndex multiplicities.
- CanonicalAdmissibleReduction.lean: `exists_admissible_canonical_kernel`
  strengthens the earlier existence reduction by retaining `Numeric b`, the
  AdmissibleTriple condition on EVERY ordered triple i<j<k. It is still an
  existence result CONDITIONAL on a nonrigid optimum-three graph core, not
  an exclusion. Build /tmp/canonical-admissible-reduction-check.log, exit 0.

The updated suppression audit, including the finite data and example, passed
at /tmp/axiom-check-kernel-suppression-current.log.

### Fast endpoints and first exact four-color exclusion

- FourSingleContactKernel.lean has passed (log
  /tmp/four-single-contact-kernel-check3.log, exit 0). `exists_two` proves
  that the four-color kernel with all six pair multiplicities equal to one
  has a two-circuit partition for EVERY recursive order tuple. Thus
  `not_restrictions` excludes this one numerical pattern. This is not the
  full four-color exclusion.
- FastCanonicalPlace.lean proves `place_eq_fast`. The fast placement filters
  List.finRange by marker membership, preserving order. This avoids an
  ordinary-kernel computation blockage: Finset.sort uses mergeSort, whose
  Acc.rec does not reduce under the attempted `decide +kernel` checks.
  `source_eq_fast` and `target_eq_fast` preserve the original definitions.
  Build /tmp/fast-canonical-place-check.log, exit 0.
- SmallKernelRejection.lean: `RejectionData.sound` checks three rejection
  types: a full partition of size <3; a color-subfamily partition larger
  than its color count; or a three-color subfamily with exact optimum 3,
  obtained from NonAlternate220 by a finite series certificate.
  Build /tmp/small-kernel-rejection-check.log, exit 0.
- FlatCanonicalKernel.lean: `finSigmaFinEquiv` gives computable flat edge
  labels, the fast endpoints are exact, and `rejects` applies any such
  finite rejection certificate to the canonical Restrictions proposition.
  Build /tmp/flat-canonical-kernel-check3.log, exit 0.

Technical warning: write the size as `sum i, (arity b i + 2)` with explicit
parentheses. The earlier unparenthesized version parsed with the +2 outside
the sum. Also Fin.heq_ext_iff needs an explicit equality of the two bounds.

A check of flat endpoint computation for all 16 order tuples in the pure
single-contact case passed: /tmp/check-flat-compute.log.

### Double-square exclusion repaired and kernel-checked

The original pending process 134106 had exited with code 137. Its bulk
order-tuple computation did NOT verify. The revised proof avoids enumerating
all dependent Pi-valued order tuples at the endpoint-transfer stage.

New checked current modules:

- FourDoubleSquareData.lean: 81 independent finite rejection certificates for
  multiplicities (0,2,2,2,2,0), plus the bounded lookup and table_valid. Eighty
  cases use the NonAlternate220 series certificate, and the last has a
  two-cycle partition. All checks use ordinary `decide +kernel`.
  Successful build: /tmp/four-double-square-data3.log and .exit = 0.
- FourDoubleSquareKernel.lean: local_word checks one four-marker word at a
  time. flat_source/flat_target transfer it to the flat canonical labels.
  source_table_row/target_table_row check the inexpensive numeric tables;
  digit_key uses arithmetic to extract the four base-three digits. These
  give witness_valid and not_restrictions for EVERY recursive order tuple.
  Successful build: /tmp/four-double-square-kernel-local2.log and .exit = 0.
  Both principal axiom lists contain only propext, Classical.choice, Quot.sound.

The generator /tmp/generate_four_double_square.py now writes ONLY the Data
file; it must not overwrite the separate structural endpoint bridge. The
current Data source also contains diagnostic progress prints, which do not
occur in the generator output. Scratch DoubleSquareOne and DoubleSquareLocal
were checked independently but are not imported by the finished modules.

Technical fixes: `unfold localIndex` leaves a let binding which prevents
split_ifs; use `dsimp only [localIndex]`. After fin_cases on a Fin index, a
`change` to the concrete arithmetic digit goal avoids opaque constructor
comparisons in `norm_num only`.

This proves only the double-square pattern exclusion, in addition to the
previous all-single-contact exclusion. Full four-color completeness, the
arbitrary-optimum core bound, and the ORIGINAL conjecture remain unproved.
No new global mathematical implication was found in the reassessment of
core inheritance, circuit reconfiguration, matroid methods, or rounding.
Spec.lean remains unchanged with its original sorry; this is not a settlement.

The updated combined canonical audit, including SmallWordTables,
CanonicalAdmissibleReduction, fast placement, rejection soundness, flat
kernels, and BOTH checked four-color exclusions, passed with exit 0:
/tmp/axiom-check-canonical-kernels-double-square.log. Every printed axiom
list uses only the permitted three. No Lean build remains running at this
checkpoint. No incomplete proof was resubmitted.

### Batch coarsening and local alternation interfaces (checked)

The following current sources have successful individual builds and principal
axiom audits using only propext, Classical.choice, Quot.sound:

- SeriesCertificateAssembly: sigma assembly of local series certificates,
  allowing retained vertices to overlap between pieces while private link
  vertices avoid all other pieces.
- CyclicSeriesData: computable suppression of indexed cycles; validity for
  ALL selected subsets on cycles of length two through six. No all-length
  validity theorem is asserted.
- CyclicWordCoarsening: exact partition spectra, counts, minimality, rigidity,
  and color-subfamily spectra under simultaneous deletion of private markers.
- CanonicalSubsetCoarsening: retained markers are precisely contacts with
  other selected colors; removed markers are automatically private.
- StableCanonicalCoarsening: coarse label lengths depend on counts and colors,
  not the recursive order tuple. Exact partition spectra are preserved.
- LocalCanonicalRows: each coarse row depends only on its own order.
- FilteredCyclicWord: coarse rows literally equal filtered cyclic lists,
  expressed using getD to avoid dependent lookup-bound computations.
- TripleAlternation220: every nonalternating (2,2,0) kernel has exact optimum
  three, for arbitrary rotations/orientations of the three local words.
- TripleAlternationKernels: every nonalternating (2,2,1) kernel has a partition
  of size four, again allowing arbitrary local rotations/orientations.
- FourCanonicalCounts: all nine numerical representative patterns have local
  word lengths two through six; Alternating is equivalent to the forward
  adjacent-position predicate ForwardAlternating.

Build logs respectively include /tmp/series-certificate-assembly2.log,
/tmp/cyclic-series-data2.log, /tmp/cyclic-word-coarsening.log,
/tmp/canonical-subset-coarsening2.log, /tmp/stable-canonical-coarsening.log,
/tmp/local-canonical-rows4.log, /tmp/filtered-cyclic-word2.log,
/tmp/triple-alternation-2202.log, /tmp/triple-alternation-kernels3.log,
/tmp/four-canonical-counts.log.

The FIRST concrete application FourForkExample is still being debugged.
Profiles 4 and 5 reached the final forced declaration after checking the
endpoint embedding; they were stopped while elaboration was stuck in the
permutation coercion. Neither run verified the final theorem. Profile 6
adds explicit endpoint simplification and applies the forward predicate
pointwise to avoid the coercion bottleneck.

/tmp/generate_four_forks.py now generates FourFork00 through FourFork17 from
/tmp/four-forks.json. These 18 files are UNVERIFIED templates at this point.
They are not imported into the audited chain. The intended constraints are
independent per row, reducing the full-order finite classification to 652
tuples across nine representative numerical patterns. Those counts still
come from external exact data, NOT a Lean completeness theorem.

The original conjecture and its arbitrary-optimum core bound remain OPEN
in this development. No statement modification, new conjecture counterexample,
or general implication was found. Spec.lean is unchanged with its sorry.

### First fork and first additional representative pattern verified

FourForkExample.forced first passed with a clean axiom list at
/tmp/four-fork-example-clean.log (exit 0). The current strengthened version
also passed at /tmp/FourForkExample-check.log: forced_of_upper needs only
an upper bound of three on the chosen three-color support. The forced
corollary takes the original Restrictions hypothesis.

Crucial repairs:
- After rewriting oneOrder_self and placeC/A/Z, add rfl to close the explicit
  numerical-arity normalization equality. Earlier diagnostic runs had
  recovered from these unsolved goals with sorryAx and were NOT proofs.
- In endpoint proofs, fin_cases produces Fin.mk indices; simplify with
  Matrix.cons_val_zero' and Matrix.cons_val_succ' before applying row lemmas.
  Matrix.cons_val alone does not normalize those constructor indices.
- Apply the forward alternation equivalence pointwise, then simplify
  Equiv.ofBijective_apply. Avoid a bulk comparison of coerced permutations.
- The weakened local-bound statement must use Classical.decEq on the FULL
  sigma-label type, not just the coarse label type, to match transport APIs.
- In the generalized generator, peripheral pullback maps use the order of
  phi's reference markers, NOT the sorted retained marker set. These differ
  when the peripheral-to-peripheral contact comes earlier numerically.

CanonicalLocalBounds.lean passed. It isolates maximum bounds for every color
subfamily and upper bounds of two on every three-color subfamily, with no
full-support minimality hypothesis, and transports the full maximum to flat
labels.

FourRows1.lean, FourData1.lean, FourKernel1.lean all passed. The finite local
filters leave 16 tuples for multiplicities (0,2,2,2,2,1), every one with a
checked five-circuit partition. The main consequences are catalogue,
exists_two (under inconsistent local bounds here), and not_restrictions.
All audited axioms are permitted. Logs: /tmp/FourRows1-check.log,
/tmp/FourData1-check.log, /tmp/FourKernel1-check.log, all exit 0.

The repaired remaining fork modules are being built sequentially. The
remaining eight representative-pattern row/data/kernel modules are GENERATED
but NOT YET VERIFIED at this checkpoint. Their queued audit is
AxiomCheckLocalFour.lean; it must not be described as passed until its build
actually succeeds.

Generators and exact input data:
- /tmp/generate_four_forks.py
- /tmp/four_row_catalogue.py and /tmp/four-row-catalogue.json
- /tmp/generate_four_rows.py
- /tmp/generate_four_row_data.py
The catalogue script completed exactly all 652 independently row-filtered
representative tuples, retaining 30 possible max-four indices. This external
calculation is not itself a Lean completeness theorem.

Still no arbitrary-optimum reduction or unconditional global bound. The
original Spec.lean remains unchanged and UNSOLVED.

### All representative-pattern four-color modules now checked

All 18 FourFork00--FourFork17 modules have now passed. Their weakened
forced_of_upper / forced_of_lower statements require only the relevant
selected triple bound, not full-support minimality. All principal axiom
lists are clean. The two batch logs are /tmp/four-forks-build.log and
/tmp/four-rows-first-build.log; the latter completed with exit 0.

All nine triples FourRows{k}, FourData{k}, FourKernel{k}, for k=0,...,8,
now have successful current builds (individual /tmp/NAME-check.exit = 0).
Thus the independent row filters and ALL 652 partition certificates are
kernel-checked. Each pattern's LocalBounds implies its key belongs to its
good catalogue and that its canonical kernel has a two-circuit partition.
It follows that NONE of the nine representative patterns satisfies full
Restrictions. The retained good-catalogue sizes are 1,0,1,7,12,0,9,0,0,
for a total of 30. These are necessary catalogues, not a claim that every
catalogued tuple extends to a larger admissible family.

Important distinction: this covers all nine NUMERICAL REPRESENTATIVES.
The transport for arbitrary color labellings / actual four-cycle graph
families is still a separate theorem. FourRepresentativeKernels.lean
aggregates the nine conclusions, adds exists_two_of_eq and the necessary
numerical allowed set {0,2,3,4,6}; it is queued for checking after the
combined audit. Do not yet describe that aggregate as verified.

Pending structural sources, currently UNVERIFIED:
- CanonicalLocalExtraction.lean: transports local maximum/three-color
  bounds through the existing actual path-family extraction and normalized
  canonical code, and sends a two-circuit partition back to a graph bound.
- FourGraphFamily.lean: applies numerical color permutation BEFORE the
  actual canonical extraction. Its intended main result number_and_contacts
  gives both number<=2 and an allowed numerical representative for any
  degree<=4 graph with a maximum four-cycle decomposition whose triples
  have number<=2. It also contains lower_subfamily, the corresponding
  subfamily_number_le_two consequence, and three_core_maximum_ge_five.

At this precise checkpoint AxiomCheckLocalFour.lean is running. After it,
FourRepresentativeKernels, CanonicalLocalExtraction and FourGraphFamily are
queued sequentially. Watch the .exit files and errors before claiming any
of these additional checks have succeeded.

No new global mathematical implication was obtained from the reassessment
of arbitrary minimal cores, circuit exchanges, fractional rounding or
rank-three accessibility. Even full optimum-three rigidity would still
need a general reduction. Original Spec.lean is unchanged and UNSOLVED.

### Four-color graph transport and strengthened reduction verified

The combined representative audit passed at /tmp/axiom-check-local-four.log
(exit 0). FourRepresentativeKernels.lean passed at
/tmp/FourRepresentativeKernels-check.log (exit 0), including allowed_of_bounds,
exists_two, exists_two_of_eq, allowed_of_eq, and not_restrictions.

CanonicalLocalExtraction.lean now passed at
/tmp/CanonicalLocalExtraction-check3.log (exit 0). The earlier failures were
missing `include` declarations for section hypotheses used only in proofs.
The final file includes hC, hd, F, hsrc, hdst, hpiece, hcover explicitly and
uses an explicitly typed sigma lambda in the raw-kernel `change` step.

FourGraphFamily.lean passed at /tmp/FourGraphFamily-check4.log (exit 0).
Checked results:
- lower_subfamily: every subfamily of a lowered family lifts to an original
  subfamily with identical cardinality and edge-union graph.
- number_and_contacts: for a degree<=4 graph with a maximum four-cycle
  decomposition and number<=2 on every three-cycle subfamily, the whole
  graph has number<=2 and its contact counts have a representative in
  {0,2,3,4,6}.
- subfamily_number_le_two: the same two-cycle bound for any four-cycle
  subfamily of a larger maximum family under those local conditions.
- three_core_maximum_ge_five: EVERY maximum family of a hypothetical
  nonrigid even-minimal graph of optimum three has at least FIVE cycles.
The last mismatch was only the finite-degree witness on lowered pieces;
normalizing IsRegularOfDegree through Nat.card fixed it.

AxiomCheckFourGraph.lean passed, /tmp/axiom-check-four-graph.exit = 0.
Every printed list uses only propext, Classical.choice, Quot.sound.

CanonicalFiveLowerReduction.lean also passed at
/tmp/CanonicalFiveLowerReduction-check2.log (exit 0). Its theorem
CanonicalThreeReduction.exists_admissible_canonical_kernel_ge_five upgrades
the strongest earlier pure-kernel existence reduction from l>=4 to l>=5,
retaining Restrictions and Numeric. It does NOT exclude all such kernels.

Import warning: CanonicalLocalBounds and the OLD CanonicalAdmissibleReduction
use independently autogenerated local-instance names in the SAME namespace.
Importing both produces a declaration-name collision. The new
CanonicalFiveLowerReduction imports CanonicalPairAdmissibility (which is all
its copied proof needs), not CanonicalAdmissibleReduction, and gives its own
local instance the explicit name canonicalFiveLowerDecEq. Do not combine
the two incompatible auxiliary branches without renaming/rebuilding an
instance, or consolidating source bodies in one file.

AllowedFourCounts.lean is the next pure numerical follow-up: zero-opposite
and no-three-doubles properties of the five allowed representatives, and
positivity on five distinct colors. Check its build status separately; it
was just queued when this checkpoint was written.

The ORIGINAL Erdős 184 proposition remains UNSOLVED. No arbitrary-optimum
bound or reduction to optimum three is available. Spec remains untouched.

### Positive-contact kernel and four-double bound verified

Current successful builds, all with permitted axiom lists:
- AllowedFourCounts.lean: all_positive, using at least five colors and the
  triple contact lower bound plus the allowed four-color patterns.
- FourSubfamilyPatterns.lean: core_pattern, core_pair_contact_pos,
  core_no_three_doubles; transport to arbitrary selected graph subfamilies.
- FewDoubleContacts.lean: doubled_card_le_two and
  core_selected_contacts_bound. Any K selected cycles in a hypothetical
  nonrigid even-minimal optimum-three core have at most |K|+1 markers per row.
- CanonicalPositiveReduction.lean: exists_positive_canonical_kernel gives
  l>=5, Restrictions, Numeric, positive pair counts, and <=l+1 row markers.
- AllowedFourDoubleBound.lean: doublePairs_le and core_double_pairs_bound;
  every four selected cycles have at most two doubled contact pairs.
  /tmp/AllowedFourDoubleBound-check.exit = 0, its two axiom lists are clean.

AxiomCheckPositiveKernel.lean is a NEW combined audit; check its separate
log before describing the combined import as passed.

The ORIGINAL proposition still has no proof or disproof. In particular no
arbitrary-optimum core bound or reduction to optimum three has been found.
The finite classification branch does NOT by itself settle Erdős 184.

Combined AxiomCheckPositiveKernel passed (exit 0):
/tmp/axiom-check-positive-kernel.log. All listed axioms are permitted.
The general structural reassessment has not closed the arbitrary-optimum gap.

### Five-color numerical classification now verified

New modules with successful current oleans and clean axiom audits:
- FiveNumericalPatterns.lean (/tmp/FiveNumericalPatterns-check2.exit=0):
  classified; omit_double_card. Exactly 86 Boolean double-contact masks
  satisfy at most two doubles on each four-subset. The five representatives
  in pair order (01,02,03,04,12,13,14,23,24,34) have doubled sets
    {}, {01}, {01,02}, {01,23}, {01,02,34}.
  Their labeled orbit sizes are 1,10,30,15,30. The 120 permutations and
  normalization witnesses are checked by ordinary `decide +kernel`.
  Generator: /tmp/generate_five_numerical.py.
- FiveSubfamilyPatterns.lean (/tmp/FiveSubfamilyPatterns-check.exit=0):
  FiveNumericalPatterns.classified_nat, pattern_of_counts; and
  FiveSubfamilyPatterns.core_pattern on any injectively selected five-cycle
  subfamily of a hypothetical nonrigid even-minimal optimum-three core.
- FiveCanonicalCounts.lean (/tmp/FiveCanonicalCounts-check.exit=0):
  canonical counts and marker_lower (>=4), marker_upper (<=6), arity_bound
  (<=4), Orders. This fits the already verified coarsening range exactly.

New generic transport:
- CanonicalColoredCoarsening.lean passed
  /tmp/CanonicalColoredCoarsening-check3.exit=0, all four printed audits clean.
  WordKernel.restriction_color_spectrum; canonical and stable color_spectrum;
  StableCanonicalCoarsening.local_upper and local_three preserve ALL selected
  subfamily bounds after suppression, not just full-family spectra.
  Note: the initially attempted polymorphic local `have hf {I : Type*}`
  failed to rewrite at concrete Fin types (universe/instance inference).
  Explicit hlarge/hlocal equalities of color-label finsets work.
- ColoredEmbeddingBounds.lean is NEW and its SECOND build is pending at
  /tmp/ColoredEmbeddingBounds-check2.log/.exit. It adds colorLabels_map for
  color-preserving sigma equivalences and localBounds pulled back through a
  kernel embedding into a coarsened family. The first attempt merely lacked
  `include hr T M hmap`; do not claim success until checking build2.

Planned next finite step (not yet implemented):
For each of the 5 numerical five-color patterns and each omitted color,
choose a permutation of the remaining four colors matching FourCanonicalCounts
pattern 2 (all single), 3 (one double), 4 (two adjacent doubles), or 6 (two
 disjoint doubles). Build a kernel embedding from that canonical four-color
kernel into StableCanonicalCoarsening of the five-color family. Its row
order depends on only one input row, so all endpoint and injectivity tables
can be checked row-by-row on at most 120 recursive orders. Vertex map:
map the USED four-color pair slots to corresponding five-color slots and
complete arbitrarily to an injective Fin32 -> Fin50 table.

For each input row q, filter its normalized five-color word to retained
markers, pull back marker names through the slot map, then rotate/reverse
into the normalized four-color word. Encode the latter as Marked.Order by
removing the highest numbered marker recursively; its predecessor is the
insertion position. Edge map is the permutation matching unordered adjacent
pairs of that small normalized word to adjacent pairs of the filtered large
word. Existing LocalCanonicalRows.stableWord_local and
FilteredCyclicWord.word_eq_getD support row-local finite endpoint proofs.
Then ColoredEmbeddingBounds.localBounds gives FourRows{k}.catalogue on each
four-subset, pruning the five-row tuple space before full partition checks.

Unfiltered normalized five-row tuple counts are 243,3888,77760,62208,1244160.
In the two patterns with adjacent doubles, the center row has the checked
221 alternation restriction; this cuts its 60 words to 20. Resulting
independent-row counts should be 243,3888,25920,62208,414720 (sum 506979).
Those counts are mathematical planning, not yet a new completeness proof.
The existing external five-local enumeration reports 8311 survivors and
656 max-five survivors; new formal coverage still needs to be established.

The latest general reconsideration (minimum-core heredity, square cofactor
accessibility, regular-matroid/fractional rounding, or rank-three reduction)
produced NO missing theorem. Much of it duplicates earlier investigations;
do not promote these ideas to facts. Spec is STILL UNCHANGED and UNSOLVED.

ColoredEmbeddingBounds second build PASSED (exit 0); both printed axiom
lists are permitted. Combined AxiomCheckFiveNumerical.lean is now queued at
/tmp/axiom-check-five-numerical.log/.exit. Check that result before using
its combined-import audit.

Implementation refinements for the next four-subset transport:
- CanonicalPairKernel.source/target ALREADY use the normalized word, so no
  extra NormalizedKernel transport is needed on the small four-color side.
- Marked.Order n for a word of length n+2 is encoded recursively by deleting
  highest marker n+1 and pairing the remaining Order(n-1) with that marker's
  predecessor in the original word, encoded in Marked.Marker(n-1).
  A numbered marker j in Marker t is recursively Sum.inl unless j=t+1,
  when it is Sum.inr (). Base Marker0 is Fin2. This gives explicit small
  order values; ordinary finite endpoint checks will validate them.
- Use LocalCanonicalRows.stableWord_local to reduce an arbitrary large-row
  word to oneOrder at its color, and the existing FourFork row_eq_fast proof
  pattern to replace suppression by FilteredWord.filtered ... .getD.
- For each normalized full-row word, generate the small canonical order and
  an edge permutation matching UNORDERED adjacent pairs to the large filtered
  word. Endpoints have at least three markers in positive four-subsets, so
  the edge match is unique. The sigma equivalence combines the chosen color
  equivalence Fin4≃A and these row permutations.
- ColoredEmbeddingBounds.colorLabels_map proves the required all-subfamily
  support map from a color-preserving sigma equivalence. localBounds then
  pulls large LocalBounds back through the embedding, yielding the existing
  FourRows{k}.catalogue on that chosen four-subset.

### Combined five-numerical audit passed; projection prototype pending

/tmp/axiom-check-five-numerical.exit=0. Every listed theorem uses only the
permitted axioms. External reference access was retried with curl and remains
unavailable (DNS failure), so no newer result has been obtained from the web.

New generator: /tmp/generate_five_projections.py. It can generate all 25
five-to-four projection modules, but ONLY FiveProjection04.lean has been
written so far. Its THIRD build is currently pending:
  /tmp/FiveProjection04-check3.log / .exit
The first attempt failed on unannotated numerals of Marked.Marker0 and on
Fin addition under a dependent CycleData.size. Fixed by `(j : Fin 2)` at
the base marker and explicit `(1 : Fin m)` in normalized vertex successors.
The second attempt was deliberately stopped after several minutes to replace
repeated small fastPlace evaluation in finite endpoint certificates by literal
smallMarkers tables. The third version includes smallPlace equalities and
#check progress lines after each row. It has not yet been observed to pass.
Do NOT use its conclusions until a successful build and clean audit.

Projection generator details:
- chooses the first numerical color permutation into one of reps 2,3,4,6;
- completes the used slot relabeling to an injective Fin32 -> Fin50 table;
- for every normalized large-row word, recursively encodes the normalized
  small word as a Marked.Order and tabulates the edge permutation;
- finite checks validate each row's edge bijection and unordered endpoints;
- combines these by Equiv.sigmaCongr, then pulls back LocalBounds and obtains
  the already checked FourRows{k}.catalogue.
The final sigma embedding and LocalBounds steps are still UNVERIFIED in
this prototype; fixing them may be necessary.

New external exact data (NOT Lean completeness proofs):
- /tmp/five_projected_catalogue.py, /tmp/five-projected-catalogue.json,
  /tmp/five-projected-catalogue.log. All raw normalized five-row tuples were
  filtered through the CURRENT checked four-representative catalogues,
  with the same color and slot relabeling as the new projection generator.
  Runtime ~3.5 seconds. Surviving counts by five-pattern index 0..4:
    243, 1944, 2052, 3312, 760; total 8311.
  Thus the older reported 8311 count is now independently reproduced.
- /tmp/five_partition_cert.cpp, executable /tmp/five_partition_cert;
  /tmp/five_partition_catalogue.py. Generated a circuit partition for each
  survivor, using two circuits if its maximum is <=5, otherwise >5 circuits.
  Python independently checked each explicit circuit's distinct vertices,
  edge incidences and exact edge partition. Runtime ~37 seconds.
  /tmp/five-partition-catalogue.json is 5.4 MiB, log
  /tmp/five-partition-catalogue.log ends DONE 8311.
  Maximum-count histograms by pattern:
    0: {5:156, 6:87}
    1: {5:396, 6:1530, 7:18}
    2: {5:80, 6:1972}
    3: {5:24, 6:3184, 7:104}
    4: {6:672, 7:88}
  Total max-five survivors: 656, agreeing with older data. New Lean data
  modules and the five-row completeness filters have NOT yet been generated.

Spec.lean remains untouched and UNSOLVED. No new general mathematical step
has been found. The finite optimum-three work remains separate from the
unproved arbitrary-optimum reduction needed for the original conjecture.

### Projection prototype debugging update

The earlier FiveProjection04 builds 2 and 3 were intentionally terminated,
not verified. The delayed diagnostics were caused by buffering. Profiling
build4 exposed the real issue: `fin_cases` cannot construct a DATA-valued
function (smallOrders or rowEquiv), because its List.Mem eliminator is Prop-
only. The following dependent definitions must use nested Fin.cases terms,
not tactic fin_cases. The generator has now been fixed accordingly.

Current pending build is FIFTH:
  /tmp/FiveProjection04-check5.log/.exit
  launched with -Dprofiler=true. Source regenerated cleanly (no debugging
  run_cmd commands; the failed IO progress commands from build4 are gone).
The small-marker literal-table optimization remains, and the finite row
certificates reached their #check lines in build4. Final sigma embedding,
LocalBounds pullback, and catalogue still require a successful final build.

The previous queued all-single batch (parent PIDs 155409,155410) was cancelled
before stopping build3. It is NOT now running or queued. NEW generated files:
  FiveRows0.lean (234 lines), FiveData0.lean (4503), FiveKernel0.lean (63).
Generated by /tmp/generate_five_all_single.py, adapting the checked four-row
and four-data generators to all 243 all-single five-row tuples. These files
are currently UNVERIFIED and need sequential builds after the prototype.
The first case needs no four-subset filtering, since all 243 tuples survive.
The generator uses /tmp/five-all-single-catalogue.json extracted from the
new full certificate data. It currently prints the inherited 'nine modules'
status line, but actually generates ONLY the three index-zero modules.

### Projection prototype now verified

FiveProjection04Base (build9) and FiveProjection04 (build16) are both checked.
The latter's embedding, localBounds, catalogue audits contain only the permitted
axioms. Build12 failed at a dependent rewrite; build14 timed out rewriting the
computed sigma index; build15 used congrArg but timed out unfolding row sources.
Build16 succeeded by explicitly changing the literal index, using Eq.trans with
congrArg on edge_apply, then simp only on fastSource/fastTarget, stable source/
target, smallOrders, and Fin.cases before the final row change.

Generator /tmp/generate_five_projections.py now emits Base + Theory modules
consistently, preserving the prototype's assembly fix. Cases (0,0) and (4,2)
have been generated; their builds are queued behind the all-single modules.
Current sequential batch: FiveRows0, FiveData0, FiveKernel0, FiveProjection00Base,
FiveProjection00, FiveProjection42Base, FiveProjection42. Each log/exit uses
/tmp/{module}-check.log/.exit. Results not yet observed. It stops on first error.

The original Spec.lean remains unchanged and UNSOLVED. No new arbitrary-core
bound or rank-three reduction has been established. Do not conflate finite
projection verification with the original conjecture.

All-single five-color modules now VERIFIED: FiveRows0, FiveData0, FiveKernel0;
all three /tmp/{module}-check.exit files are 0 and principal audits are clean.
This checks all 243 all-single row tuples and their explicit partitions.
FiveRows0.catalogue, exists_two, not_restrictions are now available. This is
only the all-single numerical five-color pattern, not all five patterns.

FiveProjection00Base and FiveProjection00 also passed with permitted axioms.
FiveProjection42Base passed. FiveProjection42 failed at the rfl in edge_apply1
under the 200000 heartbeat limit. Its second build raises that limit to
1500000, with log/exit /tmp/FiveProjection42-check2.log/.exit; pending at this
note update. The sequential batch has otherwise completed/stopped cleanly.

FiveProjection42 second build PASSED, exit 0, with permitted axioms for
embedding/localBounds/catalogue. The issue was only the lower heartbeat cap;
new generated theory modules now use 1500000. All remaining 22 projection
Base/Theory pairs have now been generated by the updated split generator.
They are queued sequentially in /tmp/build_remaining_five.sh; progress is
/tmp/remaining-five-progress, failures /tmp/remaining-five-failures, individual
logs/exits /tmp/{module}-check.log/.exit. Only one Lean process at a time.
Existing verified cases (0,0), (0,4), (4,2) are skipped and not overwritten.

/tmp/generate_five_raw_rows.py generates FiveRows1,...,FiveRows4 from the
five-partition JSON. These use ALL normalized raw row orders, no fork pruning;
their raw key bound is the PRODUCT of row sizes, not survivor-list length.
They are queued after the projection builds. They have NOT yet been checked.
FiveRows0 remains the already verified all-single file and is not regenerated.

Implementation plan for five-row completeness (NOT yet implemented):
- For each projection, tabulate the encoded four-row key for every raw large
  row order. Use 0 for an invalid projected four-row word, index+1 otherwise.
- FourRows{k}.chosen{i} on the transported LocalBounds excludes invalid words.
  Small finite row checks (<=120 orders) can then identify these table codes
  with actual projected four-row keys+1. FourRows catalogue implies the tuple
  belongs to a finite allowed encoded-key set.
- Five such necessary conditions filter the raw mixed-radix row key. Prove
  coverage of the external 8311 survivor list, potentially using chunked
  ordinary kernel decide on the finite tuple space.
- Avoid a giant raw-key match returning certificates. Define cases Fin M
  indexing survivors and prove raw key belongs to their image. Choose its
  case index noncomputably, preserving exact row digits; certificates and
  source/target tables are then indexed only by Fin M.
- Remaining data sizes are 1944,2052,3312,760 records. Split certificate files
  into manageable chunks (~200 cases). The verified FiveData0 has 243 cases,
  12 MiB olean, and compiled in about four minutes.

All this remains finite optimum-three work. No arbitrary-optimum core bound,
no rank-three obstruction theorem, and no proof/disproof of Spec.lean has been
found. Spec is still unchanged with its original sorry.

New auxiliary generic modules VERIFIED:
- FiniteCaseLookup.lean: balanced Table, lookup, recursively decidable Correct,
  lookup_sound and exists_of_isSome. /tmp/finite-case-lookup-check2.exit=0;
  principal axioms only propext.
- FiniteIntervals.lean: Covers, of_fin, merge for assembling interval-sized
  finite checks. /tmp/finite-intervals-check.exit=0; allowed axiom lists.
Both import only small Mathlib components, avoiding the graph-heavy branch.

/tmp/generate_five_projection_codes.py generated 25 UNVERIFIED code modules
FiveProjectionCode{k}{v}.lean. These encode the projected four-row normalized
word by index+1 (zero marks invalid). A finite row implication is conditional
on the projected FourRows chosen-word theorem, so invalid four-row words are
not silently admitted. They derive Compatible from transported LocalBounds.
Their batch builds have been appended AFTER the existing projection/raw-row
batch; the code batch stops on first failure. Data also saved in
/tmp/five-code-constraints.json. No code module has been checked yet.

A pure numerical filter prototype is under development, independent of the
large graph branch: /tmp/generate_pure_five_filter.py currently generated only
PureFiveFilter1 and PureFiveFilter1Prototype (first 1000 raw keys). It duplicates
the computable projection-code constraints; graph transport still must connect
these definitions once both sides are checked. Balanced Table lookup maps a
surviving raw key to Fin M, while Correct proves caseKey i equals that raw key.
The first attempt crashed in the Matrix vector macro on the 1944-entry caseKey
vector (deep interpreter recursion). The second replaces caseKey by a balanced
index-comparison tree, avoiding deep vectors and reducing lookup evaluation
cost. Its logs/exits are /tmp/PureFiveFilter1-check2.* and
/tmp/PureFiveFilter1Prototype-check2.*; pending at this note update. These small
imports can build alongside the serialized graph branch without loading Work.

/tmp/generate_pure_five_complete.py now generates interval certificate modules:
1000 raw keys per lemma, ten lemmas per module; balanced FiniteIntervals.merge
assembles full coverage. Only pattern 1 has been generated so far:
PureFiveComplete1_000.lean (four chunks) and PureFiveComplete1.lean. These are
UNVERIFIED and NOT yet queued. /tmp/pure-five-complete-modules lists them.
The pure filter second build is still pending. Its balanced caseKey avoids the
previous vector macro stack overflow. Memory was about 2 GiB total cgroup while
it ran concurrently with one graph projection build, safely below 10 GiB.

PureFiveFilter1 second build PASSED (exit 0, audit only propext), and
PureFiveFilter1Prototype second build PASSED (first 1000 keys, audit propext
and Quot.sound). The balanced lookup construction is therefore checked on
this prototype. No graph-to-pure-filter connection has yet been checked.

PureFiveFilter2/3/4 and all interval completeness modules for patterns 1..4
have now been generated. A separate SMALL-IMPORT sequential batch is running:
/tmp/build_pure_five.sh, progress /tmp/pure-five-progress, failure file
/tmp/pure-five-failures. It first completes pattern 1, then builds each pure
filter data module and its complete chunks/assembly, stopping on any error.
Individual logs/exits /tmp/{module}-check.log/.exit. The complete-module list
is /tmp/pure-five-complete-modules. Chunk counts: pattern1=4, pattern2=78,
pattern3=63, pattern4=1245 (1000 keys each, last partial); ten chunks/module.
This batch imports only small utilities/numeric data, not Work, and can safely
run alongside the one graph-heavy projection process. Continue monitoring
cgroup memory, and avoid starting a SECOND graph-heavy build.

/tmp/generate_five_certificates.py now generates a compressed-index certificate
interface and chunked circuit data. ONLY pattern 1 has been generated so far:
FiveCertificates1Base, FiveCertificates1_000,...,_009, FiveCertificates1, and
FiveCaseSelection1. All are UNVERIFIED and NOT yet queued. The generated module
list is /tmp/five-certificate-modules.
- Base: Cases/caseKey aliases to PureFiveFilter1, checked bound placeholder via
  ordinary decide, raw-key good finset (Fin 3888), caseSource/Target, Certificate.
- Each 200-case chunk: explicit cycle partitions and Valid checks, local lookup,
  row-table identities using caseKey, size<=5 implies size=2 and raw key in good,
  then a Covers CertificateAt interval. No large global certificate lookup.
- Assembly merges intervals and chooses one PartitionData per case, exposing
  data_valid/data_size.
- FiveCaseSelection1 connects the five computed projection-code predicates to
  PureFiveFilter1.Compatible at the raw key, invokes pure completeness, and
  selects its case index with exact index_key. This is currently unverified.
A new FiveKernel1 is still needed to combine selected data with flat_src/dst,
prove catalogue, exists_two and not_restrictions. Similar generators can then
handle patterns 2,3,4. Do not overwrite the already verified all-single files.

/tmp/generate_five_compressed_kernel.py has generated an UNVERIFIED FiveKernel1
combining certificate data with the selected case. It proves witness_valid by
index_key and existing flat_src/dst, obtains the size<=5 bound from LocalBounds,
and derives raw-key catalogue, exists_two, not_restrictions. It has not been
queued, and depends on the unverified certificate/selection modules.

Latest observed progress: every completed projection through (2,0) passed;
FiveProjection21Base was running. Pure pattern 1 FULL completeness is now
VERIFIED (PureFiveComplete1_000 and PureFiveComplete1 exit 0). PureFiveFilter2
also passed, and its first interval module was running. All observed audits
are permitted. Cgroup memory with both jobs was about 4.9 GiB, below 10 GiB.

The pattern-1 certificate module list and FiveKernel1 have now been appended
to /tmp/build_remaining_five.sh AFTER all projection-code builds. This phase
stops on first error. At present /tmp/five-certificate-modules contains ONLY
pattern 1; do not regenerate that list to other patterns while the running
batch is about to read it unless intentionally expanding the queue.

Projection (2,1) FAILED under 1.5M heartbeats at the last rfl in edge_apply2.
No olean was written. The subsequent printed sorryAx is Lean's provisional
error recovery, NOT a usable theorem. All successful modules remain clean.
Generator and not-yet-verified theory files (21..24,30..34,40,41,43,44) now
add `dsimp only [Matrix.vecCons,Fin.cons,Fin.cases]` after the explicit raw
DFunLike coercion reduction, before rfl. This fix is UNVERIFIED so far.
Case22 may already have been read by its running build, so its current result
may still reflect the old version. A retry phase has been inserted into the
running batch AFTER raw-row builds but BEFORE projection-code modules. It
retries recorded failures with the new source and stops if any still fails;
logs /tmp/{module}-check2.*. This prevents the code phase from depending on a
failed projection. The original failure list will be archived as
/tmp/remaining-five-initial-failures when that retry phase starts.

Pure pattern2 first 10,000-key interval module PASSED, clean audit. Its second
module was running. Peak cgroup usage observed about 6.8 GiB with both jobs,
falling after the pure module completed. Continue monitoring memory.

The added dsimp did NOT resolve all cases: FiveProjection23 failed at the last
rfl of edge_apply3. Cases21/22/23 are currently failures without oleans.
The graph batch has now been SIGSTOP-paused at its parent PID saved in
/tmp/paused-graph-batch-pid; its current child FiveProjection24 is allowed to
finish. A diagnostic job waits for that child, then runs
Submission/FiveProjection21Inspect.lean, tracing the remaining edge_apply2 goal
before rfl under a smaller heartbeat cap. Log/exit:
/tmp/FiveProjection21Inspect-check.log/.exit. This is a scratch diagnostic, not
a verified module. After repairing the helper, RESUME the graph batch with
`kill -CONT $(cat /tmp/paused-graph-batch-pid)`. Do not forget the paused parent.
The pure numeric batch remains running independently.

Memory precaution: pure pattern2 module003 reached about 7 GiB RSS and total
cgroup usage about 8 GiB while the graph batch was paused. Future pure patterns
3 and 4 have now been regenerated with 200 keys per lemma, ten lemmas/module
(2000 keys/module), to reduce peak reduction memory. They were not yet started,
so no verified files were overwritten. New chunk/module counts: pattern3
312 chunks/32 modules; pattern4 6221 chunks/623 modules. The list
/tmp/pure-five-complete-modules now preserves pattern1/2 entries and uses these
new pattern3/4 entries; the running script will read them at those future
pattern loops. Pattern2's current eight-module loop is unchanged.

Diagnostic update: explicit successor indices solve the row-equivalence lemma:
`change rowEquiv o ((0 : Fin 2).succ.succ) = edgeEquiv2 (o 0)` followed by
`simp only [rowEquiv,Fin.cases_zero,Fin.cases_succ]`. Mere primed simp lemmas
on a numeral index did not reduce the dependent Fin.cases expression.
A generic sigma application lemma is rfl. The remaining diagnostic timeout
is transporting that row equality to the sigma second component via congrArg
on E.toFun. Build7 increases the scratch diagnostic cap to 1.5M heartbeats;
/tmp/FiveProjection21Inspect-check7.* is pending. Graph parent remains PAUSED.

Pure pattern2 module004 peaked at about 9.1 GiB TOTAL cgroup memory, then GC
reduced usage to ~4.1 GiB without failure. Future pattern2 modules005/006/007
have been refined in place using /tmp/refine_pure_intervals.py: each old
1000-key interval is assembled from <=200-key decide lemmas, preserving the
old interval_chunk names and module queue. Those modules had not yet started.
Pattern3/4 already use <=200-key checks. This should reduce reduction peaks.

DEPENDENT PROJECTION FIX VERIFIED: diagnostic build9 passed, then full
FiveProjection21 build3 passed with clean embedding/localBounds/catalogue
axioms. The successful helper construction is now in the generator and all
remaining unverified projection theories:
1. generic edge_apply_generic on variable sigma index, by rfl;
2. row_apply{i}: explicitly change numeral i to iterated Fin.succ of zero,
   then simp only rowEquiv/Fin.cases_zero/Fin.cases_succ;
3. use Sigma.ext for the final edge equality, heq_of_eq on the second component;
4. raw DFunLike coercion reduction, then
   `have hh := congrArg Equiv.toFun (row_apply{i} o)`;
   `dsimp only [edgeEquiv{i},Equiv.ofBijective] at hh`;
   `exact congrFun hh j`.
The 1.5M cap is still used. Do not revert to a monolithic rfl on the dependent
sigma expression. Case21 was removed from the current failure queue because
build3 is verified; old failure logs remain as history. Cases22/23/24 still
need their queued retry with the fixed source.

FiniteCases.lean is also now VERIFIED (second build), with explicit
`Fin.cases (motive := M)` in small numeral-indexed reduction lemmas. Its audits
use only propext. This utility is not needed by the current successful helper.

The graph parent remains paused TEMPORARILY while a smoke batch runs:
/tmp/five-smoke-before-resume.sh builds FiveProjectionCode00, FiveRows1,
FiveProjectionCode12 (individual default -check logs/exits). If all pass it
writes /tmp/five-smoke-success and automatically CONT-resumes the graph parent.
If one fails it writes /tmp/five-smoke-failure and leaves the parent paused.
The main batch now skips already verified up-to-date raw-row/code modules,
so these smoke builds will not be duplicated. Check this smoke status first.

Further pure pattern4 optimization generated (UNVERIFIED):
/tmp/generate_factor_five4.py replaces the 6221 raw-interval lemmas by 60
factored checks, one per distinguished q0:Fin60. For each q0 it quantifies
q3,q4,q1, tests the omit-2 constraint, and only then quantifies q2 and tests
omit-1 and the other three constraints. This exploits actual independence of
the omitted row; it does not omit any compatible tuple. RowKey_digits and
an assembly lemma recover the identical `complete` / `exists_case_of_compatible`
API for every raw key <1244160. Files PureFiveComplete4Base, _000.._059 and
PureFiveComplete4 have been regenerated; none had started in the main pure
batch. /tmp/pure-five-complete-modules now lists this new pattern4 sequence.
Old unused pattern4 interval files >059 are not imported or queued.

An independent small-import prototype batch is checking PureFiveFilter4,
PureFiveComplete4Base, PureFiveComplete4_000, using /tmp/{module}-prototype.*
logs/exits. Only this one factored row case is being tested for now. Monitor
memory with the ongoing graph smoke and pure pattern2 batch; data4 has only
760 cases and imports no graph branch. The main pure batch will rebuild these
three when it reaches pattern4, harmlessly, if the prototype passes.

Smoke tests PASSED: FiveProjectionCode00, FiveRows1, FiveProjectionCode12 all
have clean audits. The smoke script automatically resumed the graph parent;
it is NO LONGER PAUSED. New-helper projections30/31/32 passed, with roughly
30-second theory builds. Main graph batch continues as scheduled.

PureFiveFilter4 data prototype PASSED (clean audit). Factored Base prototype
failed only at rowKey_digits: `unfold` left Fin.val projections opaque to omega.
Changed that line to `dsimp only [rowKey,digit0,...,digit4]`. Base + first ordered
case are now being rechecked with /tmp/{module}-prototype2.log/.exit. No usable
Base/ordered theorem yet; the failed rowKey_digits printed sorryAx provisionally.

Factored pattern4 prototype PASSED: PureFiveComplete4Base prototype2 and
PureFiveComplete4_000 prototype2 both exit 0, with allowed axioms. In particular
rowKey_digits is now verified after the dsimp fix, and the entire distinguished
q0=0 slice passed the early-pruning finite check. All sixty slices and the
assembly are still required; the remaining 59 are queued in the main pure batch
when it reaches pattern4. No full pattern4 coverage is claimed yet.


# Latest continuation: all five projections checked; compressed certificates pending

See the newest LiveStatus.md entry for current process IDs and precise logs.
Every five-to-four projection Base/Theory and projection-code module passed.
All raw FiveRows1..4 passed. Pure pattern2 coverage passed. Pure pattern3 data
was repaired by splitting its 3312-entry lookup into 32 named balanced blocks;
its corrected kernel check passed, and interval coverage is running.

FiveCertificates1Base and FiveCaseSelection1 passed. The first 200-certificate
chunk initially failed ONLY at its final interval wrapper, after the individual
certificate, row transport, and size declarations elaborated. Explicitly fixing
(P := CertificateAt) in FiniteIntervals.of_fin avoids the unwanted inference.
The full chunk is being rechecked; no successful chunk result is yet asserted.
All remaining five certificate files, representative wrapper, and graph-family
transport were generated and queued but are still UNVERIFIED.

Mathematical investigations of core absorption, LP rounding with additive rank
loss, splitting-off, and product amplification yielded NO missing general bound.
Neither weak cofactor existence nor finite optimum-three rigidity implies the
arbitrary-core conclusion by itself. No such inference is used in Lean.

For future six-color transport: CyclicSeries.valid currently assumes arity<=4
(up to six positions). Six-color rows with two doubles can have seven positions.
CyclicSeriesData validity is checked only over retained position subsets, NOT
all row permutations, so extending finite checks to arity5/6 should be small.
That extension is not written or proved in this continuation.

Spec.lean is unchanged, SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5,
and still has the original sorry. No proof/disproof has been submitted.


# Further checkpoint: pure pattern3 complete and five-word orbit data prepared

PureFiveComplete3 and all 32 component intervals passed check2, clean axioms.
FiveCertificates1 chunks000..003 passed check2, certifying the first 800 of
1944 pattern1 cases. Graph batch is checking _004; pure batch has moved to
the factored pattern4 slices. No current failure in either batch.

New exact Python orbit reduction /tmp/five_word_orbits.py enumerates all
color automorphisms of each five-count pattern and both labelings of every
doubled contact. Every edge and vertex bijection to the selected minimum-key
representative is checked directly against endpoint arrays. The 656 max-five
keys form 32 layout orbits: 4,20,6,2 in patterns0,1,2,3. Data and log:
/tmp/five-word-orbits.json, /tmp/five-word-orbits.log. This is not a Lean proof.

The corresponding FiveWordOrbits0..3 modules were generated (generator:
/tmp/generate_five_word_orbits.py) and queued, but NOT CHECKED. Each uses the
verified good-key catalogue for coverage, explicit inverse checks rather than
quadratic injectivity checks, and an endpoint/color-preserving kernel embedding.
CyclicSeriesLarger and LargerColoredCoarsening were also generated and queued,
so the earlier note saying no arity extension was written is now superseded;
the extension is still UNVERIFIED.

No new general mathematical theorem emerged. In particular, these finite
representatives do not justify reducing an arbitrary-optimum bad core to
optimum three. The original conjecture remains unsolved.


# Latest checked continuation: orbit and larger-row smoke tests passed

PureFiveComplete4 passed all60 factored slices and the final assembly, with
permitted axioms. Pure five coverage for patterns1..4 is now complete.
FiveWordOrbits0 passed:156 all-single good keys reduce to4 representatives,
with edge/vertex inverse, endpoint and color identities. CyclicSeriesLarger
(valid5/valid6/valid_le_six) and LargerColoredCoarsening's arity<=6 APIs passed.
Temporary smoke parent173954 successfully resumed graph parent168723.

PureSixDoubleBase also passed, checking its720 color permutations and pair
coordinates. Its first check00 was intentionally canceled (143) for memory.
All32 check modules were split into4 subchecks of256 Boolean assignments each;
checks00..12 have since passed check2 and the batch continues. Orbit1's
quantified checks were split into4 blocks of<=100 cases, still UNVERIFIED.

Generated and queued, still UNVERIFIED: PureSixDoubleTransfer (natural counts
from the Boolean classification under explicit FiveBound), AllowedFiveCounts
(actual five-family bounds and six-pattern reduction), SixCanonicalCounts
(canonical marker/arity bounds), and FiveWordOrbitColors (color permutations).
See LiveStatus.md for current process IDs, generators, failure logs, and queues.

No new arbitrary-core mathematical step has been obtained. Spec.lean remains
unchanged with its original sorry. No submission was made.

# Resumed continuation: small six-regular Hamilton-factor test (not Lean)

Spec remains unchanged and unsolved. No new arbitrary-core argument resulted.

Exact exploratory test, outside Lean:
- /tmp/hamilton_factor_server.cpp implements exhaustive edge-color assignment
  into k Hamilton cycles, with degree and union-find subtour pruning. Unused
  colors are symmetry-equivalent. A positive result means all edge colors are
  assigned, every color has degree2 at every vertex, and no proper subtour.
- /tmp/regular6_order11.py: all266 unlabeled 4-regular graphs on11 vertices,
  including disconnected complements, complemented to six-regular graphs.
  Every one has a decomposition into3 Hamilton cycles. Log
  /tmp/regular6-order11.log; exit0;6395 search nodes.
- /tmp/regular6_order12.py: analogous all7849 unlabeled 5-regular graphs on12
  vertices, complemented to six-regular graphs. Every one has a decomposition
  into3 Hamilton cycles. Log /tmp/regular6-order12.log; exit0;129990 search nodes.
- Consequently these finite regular classes contain no optimum-four candidate
  for the stronger core-rigidity investigation. This is not a theorem in Lean,
  does not address nonregular graphs, and gives no asymptotic conclusion.

Theoretical reconsideration of single-cycle extensions of rigid cores did not
produce a proof. Even a proved extension theorem would still require a valid
minimal-cofactor accessibility argument. Do not silently assume either.

## Seven-color completion — 2026-08-28 23:05 UTC

The entire six/seven classification and graph-transport chain has now passed.
Final logs/exits:
- /tmp/SevenCaseCompatibility-check.log, exit0
- /tmp/SevenKernelExclusion-check.log, exit0
- /tmp/SevenGraphFamily-check.log, exit0 (22:56:22)
- /tmp/SmallCoreRigidity-check.log, exit0

Verified theorem SevenGraphFamily.three_core_rigid: every even-minimal graph
whose minimum cycle-and-edge decomposition number is three is cycle-rigid.
The new SmallCoreRigidity module combines this with the earlier cases <=2:
rigid_of_number_le_three, number_ge_four_of_nonrigid,
hereditary_of_number_le_three, degree_two_of_number_le_three.
All printed axiom lists contain only propext, Classical.choice, Quot.sound.
The maximum-family local hypotheses are transported from actual graphs; the
seven-color result is no longer only a numerical or conditional classification.

THIS DOES NOT SETTLE SPEC. No arbitrary-optimum reduction was obtained.
Reconsidered approaches included extension of a rigid (k-1)-core, simultaneous
cycle exposure, square accessibility, and additive fractional rounding. None
provided the necessary implication. In particular, cycle deletion does not
preserve minimality, and the <=3 theorem cannot be inductively applied to a
cofactor merely because its optimum is k-1. The directed/TU and abstract binary
obstructions already recorded remain relevant; they do not refute graphical
rigidity or the original conjecture.

The reference-site request failed DNS again (/tmp/erdos184-current.err).
All old build queues are finished. Spec.lean is unchanged and still contains
its original sorry; no new submission was made.

## Targeted doubled-Petersen and weighted-R10 checks — 2026-08-28 23:30 UTC

Spec is STILL UNSOLVED and unchanged. The following are exact finite C++
calculations, not yet Lean theorems.

- /tmp/double_petersen_core.cpp, /tmp/double-petersen-core.log, exit0:
  multiplicities0..2 on the15 Petersen edges; 53,567 nonzero even supports.
  Full doubled Petersen has min5, max15. Deleting ANY circuit leaves min4,
  yet it is NOT even-minimal (proper even supports have min as large as9).
  All minimal supports in this finite system are rigid. In particular the
  full graph is a graphical obstruction to replacing EvenMinimal by merely
  CycleCritical. Subdivision gives a simple-graph realization, but that
  transport and the full obstruction theorem are not yet Lean checked.
  A min5 lower-bound interpretation: four nontrivial cycles in a cubic cycle
  double cover give a3-edge-coloring; Petersen is not3-edge-colorable. A
  parallel2-cycle in a four-piece cover is excluded by30 total edges and
  maximum ordinary cycle length9. This argument is not yet formalized.
- /tmp/weighted_binary_core.cpp tested all R10 multiplicities0..3 and0..4.
  Logs /tmp/weighted-R10-core4.log and core5.log, both exit0. No nonrigid
  minimal core. Full0..3 box has32767 nonzero even states; full triple-R10
  count5/max12. Full0..4 box has312792 nonzero even states; quadruple-R10
  count7/max20. This is NOT a general regular-matroid theorem.

Important scope distinction reconsidered: the DIRECTED four-vertex example
blocks a nested-difference/TU argument, but directed balanced0/1 supports
are NOT closed under symmetric difference. It therefore does NOT refute a
BINARY first-bad-core reduction to optimum3. Such a binary reduction remains
unproved; the earlier hyperplane/lift tests do not establish it. It must not
be silently used with the now verified graphical <=3 theorem.

Current auxiliary Lean work: PetersenBaseData.lean PASSED (all57 cycle
certificates), FinsetMask.lean PASSED (generic finite-set mask surjectivity).
PetersenBase.lean's original exhaustive Circuit quantifier crashed twice
with stack overflow; neither is a valid proof. Catalogue is being replaced
by32 finite support-containment checks, avoiding nested Circuit enumeration.
Only the first1024-word check is currently running. Final CycleCritical/not-
EvenMinimal graph theorem is NOT YET PROVED. No changes to Spec or submission.

## Doubled-Petersen simple-graph obstruction VERIFIED — 2026-08-29 00:10 UTC

DoublePetersenGraph.lean now PASSED (/tmp/DoublePetersenGraph-check.log, exit0).
Its theorem counterexample proves a simple even graph is CycleCritical, has
Critical.number=5, and is NOT EvenMinimal. All principal axiom lists contain
only propext, Classical.choice, Quot.sound. This is an auxiliary obstruction,
NOT a disproof of Erdős184. Spec.lean is still unchanged and UNSOLVED.

The complete kernel/certificate chain also passed: PetersenBaseData, all32
PetersenCatalogueChecks, PetersenBase, ParallelLabels, ParallelFlip,
PetersenWeights, DoublePetersenLower, DoublePetersenCertificates,
DoublePetersenCore, LabelKernelRealization, PathKernelDifference.
The graph is the simple subdivision of the doubled Petersen labelled kernel.

Transport fix: Code depends on its DecidableEq parameter, so a homogeneous
code equality between native and classical instances is ill-typed. Instead
prove Prop-level iff lemmas (valid_eq, number_iff, minimal_iff, circuit_iff).
Explicit @HasNumber/@Circuit/@MinimalCore use the classical edge instance;
rw with Subsingleton.elim replaces it by the native product/Fin instances.
For SupportTransport projections, use explicit @...lift/@...circuit_iff:
edge labels use Classical.decEq, but target Sym2 uses its STRUCTURAL equality
instance over classical vertex equality, NOT Classical.decEq (Sym2 Vertex).
Set local DecidableEq Vertex to classical before graph circuit transport.
Finally rewrite native finset-difference equality instances before using
expandGraph_sdiff. No mathematical strengthening beyond the obstruction.

## Unconditional maximum-family triple threshold VERIFIED — 2026-08-29 00:10 UTC

MaximumTripleThreshold.lean PASSED (/tmp/MaximumTripleThreshold-check.log,
exit0). Principal axioms are only propext, Classical.choice, Quot.sound.
- degree_le_four: if every three-piece subfamily of a maximum cycle family
  has optimum<=2, the whole graph has degree<=4. Otherwise choose three
  pieces through one vertex, whose union has degree6 and optimum>=3.
- pair_contact_positive: under those triple bounds and family size>=5,
  every pair has positive contact. Uses generic maximum_triple_admissible,
  not a minimal-core specialization.
- number_le_two: the same triple bounds imply optimum<=2 for ANY graph
  with a maximum cycle family; the four-through-seven classification applies.
- exists_rigid_triple: if optimum>=3, EVERY maximum cycle family contains
  a three-piece subfamily whose union is rigid (and has optimum3).

This strengthens the small-core result by removing global minimality.
It STILL DOES NOT SETTLE SPEC or supply arbitrary-optimum rigidity. In
particular, extending a chosen rigid subfamily to an optimal full partition
is not established. Spec remains unchanged with the original sorry.

## Further reduction diagnostics (exact computations, NOT Lean proofs)

- /tmp/direct_threshold.py checks all152 balanced supports of the complete
  symmetric directed graph on4 vertices and all176 maximum partitions.
  The triple-threshold property holds throughout this directed system,
  although full support is a nonrigid minimal core of optimum4/max6.
  Thus the checked graphical triple threshold cannot ALONE justify an
  abstract nested-difference-system induction. Binary XOR closure is absent
  in this directed example; a binary/graphical induction remains unproved.
- /tmp/first_bad_core_contract19.cpp, /tmp/first-bad-contract19.log, exit0:
  all5036 projections contracting at most4 coordinates of the known19-label
  binary optimum4 core were checked. 636 retained a bad optimum3 subcore;
  4400 had none. No contracted FULL support gave a first bad core above3.
  This tests that specific family, NOT a general binary reduction. Contracting
  can increase the optimum (new singleton circuits can appear), so no monotonic
  contraction principle follows. No proof jobs remain running.

## Targeted six-regular near-simple kernels — 2026-08-29 00:45 UTC

Original Spec remains UNSOLVED and unchanged. No new core-density theorem.
Exact exploratory enumeration /tmp/regular6_few_doubles.py checked six-regular
loopless multigraphs on7..10 vertices with multiplicities<=2 and at most3 doubled
pairs. It enumerates missing simple graphs up to isomorphism and every compatible
doubled-edge completion; repetitions are harmless. All8551 generated instances
have a partition into3 Hamilton cycles (148680 branch-and-bound nodes total).
Log /tmp/regular6-few-doubles-7-10.log, exit0, runtime~2s. No optimum4 candidate
arose. This is not a Lean theorem, not an exhaustive test beyond that class,
and does not establish the original asymptotic bound or core rigidity.

/tmp/graph_threshold_core_server.cpp was prepared to extract the first valid
support of optimum4 if a candidate failed Hamilton3. No such invocation arose
in this run. Its correctness has NOT been verified by Lean. All jobs completed.

## Continuation — 2026-08-29 01:00 UTC: affine first-bad-core diagnostic

Original Spec is STILL UNSOLVED and unchanged. No new Lean theorem or final
submission was obtained. Reconsideration of globally edge-minimal cores,
minimal-cofactor accessibility, additive fractional rounding, and a binary
first-bad reduction did not establish any missing unconditional implication.
In particular EdgeCritical is only a one-edge-deletion condition, and neither
that condition nor small-optimum rigidity may be upgraded to full heredity.

New EXACT EXPLORATORY C++ result (NOT Lean verified):
- /tmp/affine20_firstbad.cpp, executable /tmp/affine20_firstbad
- /tmp/affine20-firstbad.log, /tmp/affine20-firstbad.progress, exit file0.
- Enumerates the complements of zero-sum twelve-element subsets of F2^5;
  adds a leading1 to obtain twenty distinct affine columns in F2^6.
- Computed affine orbits under translation, cyclic coordinate permutation,
  and an elementary shear: six orbits, with sizes8680,208320,3333120,13888,
  833280,2666496; total7063784 supports. This count also agrees with the
  weight12 coefficient of the extended Hamming code:
  (choose(32,12)+31*choose(16,6))/32 =7063784.
- For every representative the full support has minimum4, maximum5, and
  proper-support maximum3, so it is a nonrigid minimal core of optimum4.
  EVERY representative also contains nonrigid minimal cores of optimum3
  (counts189,173,169,165,165,165 respectively). Hence none is a first bad
  core above3. This is finite evidence only, NOT a proof of the missing
  binary reduction and NOT a graphical counterexample to Erdős184.
- The DP enumerates all16384 kernel words per representative in increasing
  support-mask order and computes minimum/maximum circuit partitions and
  the maximum minimum over all proper valid supports.

Also /tmp/direct_threshold.py now prints all cofactors in the directed K4
obstruction. Some four-arc-cycle cofactors are rigid minimal cores of optimum3;
thus this example does have weak minimal-cofactor accessibility, despite its
full support being a nonrigid minimal core of optimum4. Directed balanced
supports remain non-XOR-closed, so this is not a binary counterexample.

No jobs remain running. Spec retains its original sorry and SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Continuation — 2026-08-29 01:20 UTC: weaker square accessibility is FALSE

Original Spec is STILL UNSOLVED and unchanged. Three new auxiliary modules
have PASSED, with only propext, Classical.choice, Quot.sound in their audits:

- PetersenSquareLower.lean, namespace DoublePetersen.SquareLower:
  For each Petersen base edge e choose an adjacent edge nextEdge(e). After
  deleting both doubled pairs, an integer weight certificate gives minimum
  circuit count at least4. The weight marks the remaining doubled bridge
  at the common endpoint and all three doubled edges at an untouched vertex.
  Total weight is8; every remaining circuit has weight at most2. Finite
  checks use the existing57-cycle catalogue and ordinary decide +kernel.
  Lemmas lower, no_critical_pair_cofactor; /tmp/PetersenSquareLower-check.log,
  exit0, current olean.
- PathKernelCritical.lean: generic Family.critical_cofactor transports
  CycleCritical of an expanded graph to the exact one-circuit deletion
  equation for labelled supports. /tmp/PathKernelCritical-check.log, exit0.
- PetersenSquareGraph.lean: pair_cofactor_not_critical, expand_card,
  cycle_labels, square_labels, no_square_critical_cofactor, and
  square_critical_obstruction. /tmp/PetersenSquareGraph-check.log, exit0.
  The last theorem asserts graph even + CycleCritical + number5 + contains
  a square + EVERY square cofactor is NOT CycleCritical. An explicit square
  walk is supplied, so the statement is not vacuous. All axioms permitted.

This REFUTES replacing EvenMinimal by CycleCritical in the square-accessibility
route. It does NOT refute SquareCoreReduction.SquareAccessible for genuinely
minimal cores: this graph is already known not to be EvenMinimal. It is NOT
a counterexample to Erdős184 and yields no unconditional linear bound.

Transport details: Finset.sdiff's classical DecidableEq can fail to rewrite
via a named Classical.decEq equality because elaborated instance expressions
differ. An explicitly typed @sdiff equality proved by extensionality fixes
this. Set local DecidableEq Vertex to Classical.decEq for expansion edge-card
calculations, to match structural Sym2 equality over classical vertex equality.
For the explicit square walk, give full `show graph.Adj ...` endpoint types;
constructor named-argument inference did not determine the intermediate sums.

Further consideration of simultaneous square exposure, minimal-core density,
rigid-base augmentation, and additive rounding supplied NO missing general
implication. All proof jobs finished. Spec SHA256 is still
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Continuation — 2026-08-29 01:30 UTC: directed-obstruction splitting test

Original Spec is STILL UNSOLVED and unchanged. No new Lean theorem in this
continuation. Reconsideration of binary zero-sum factorization, minimal-cofactor
accessibility, and rigid-base single-cycle augmentation did not establish the
missing arbitrary-optimum induction. No binary first-bad reduction is available.

New structured EXACT C++ diagnostic (NOT Lean verified):
/tmp/split_directed_core.cpp, executable /tmp/split_directed_core,
/tmp/split-directed-core.log, exit0. Start from all12 arcs of symmetric directed
K4, forget directions after splitting s vertices into input/output vertices,
and put c parallel connectors between each split pair. Checked s=0..4 and
c=1 or3; each split choice is equivalent by symmetry. Every even support in
each resulting labelled undirected multigraph is checked, not just the full
support. Largest code dimension17 (131072 states); largest circuit catalogue
2200. All minimal cores encountered were rigid; none is a graph counterexample.

Full (minimum,maximum), ordered s=0,1,2,3,4:
 c=1: (3,6),(3,5),(3,5),(3,4),(2,4).
 c=3: (3,6),(3,6),(3,7),(4,7),(4,8).
No full support was minimal. With c=3 the maximum optimum among proper supports
was3,4,5,6,6 respectively. (The program's `propermaximum` field is computed
as the maximum over ALL supports including full; since none of these full
supports is minimal, it equals the proper maximum in this run.)

Motivation: three split vertices with three connectors each force a hypothetical
three-cycle decomposition to act like a directed Hamilton decomposition, so
minimum4 is plausible and confirmed by the exact DP. But the connectors create
proper rigid cores with optimum up to6. Thus orientation forcing does NOT
transfer the directed K4 minimality obstruction to a graphical one.

No pending jobs. Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Continuation — bounded-codegree / vertex-elimination reconsideration

Spec remains UNSOLVED. No new Lean result or finite diagnostic in this
continuation. The checked bounded-common-neighbor estimate has coefficient
2*Nat.clog 2 (2*r)+5. The smallest-counterexample reductions supply high
minimum degree and high edge-connectivity but NO universal upper bound on r.
Consequently these results cannot currently be combined into an absolute
linear constant. No valid large-codegree elimination step was established.
Reconsidering regular-factor decompositions or expander-style recursive bounds
also yielded no absorption/rounding theorem removing the unbounded overhead.
No change to Spec and no submission; no pending jobs.

## Continuation — monotone-hull matroid shortcut is FALSE

Spec is STILL UNSOLVED. No new Lean theorem in this continuation. A proposed
binary bridge was examined: on a maximum cycle family D, define M(A) as the
maximum minimum decomposition number over even subgraphs of the union of A.
It is NOT generally a submodular/matroid rank function, even in a graph all
of whose minimal even cores are rigid. Thus that rank-based argument cannot
justify arbitrary-optimum rigidity from the verified optimum-three theorem.

Exact small Python diagnostic (NOT Lean verified):
/tmp/core_hull_submodularity.py, /tmp/core-hull-submodularity.log.
Four edge-disjoint triangles on vertices0..6:
 A=(0,1,2), B=(0,3,4), C=(1,3,5), D=(2,4,6).
Their full union has12 edges, so this four-triangle family is maximum.
All64 even supports were examined; all their minimal cores are rigid.
Results (minimum,maximum,max_subnumber):
 AB=(2,2,2); ABC=(2,3,2); ABD=(2,3,2);
 ACD=(3,3,3); BCD=(3,3,3); ABCD=(2,4,3).
Hence M(ABC)+M(ABD)=4 <5=M(AB)+M(ABCD), violating submodularity.
The rigid-subfamily independence complex also fails circuit elimination:
ABC and ABD are minimally nonrigid, whereas ACD and BCD are rigid.

This does NOT refute the separate binary first-bad-core reduction; that
reduction remains unproved. No original conjecture proof/disproof, no Spec
edit, no submission, and no pending jobs.

## Continuation — local even replacement is also FALSE (exact diagnostic only)

Spec is STILL UNSOLVED and unchanged. No new Lean theorem was proved and no
submission was made. The arbitrary-optimum maximum-family representation,
minimal-cofactor accessibility, and minimal rigid-base extension implications
remain unproved. In particular, none was obtained from the small-optimum result.

The earlier Petersen-line-graph local two-cycle obstruction was strengthened by
an exact finite diagnostic, not a Lean proof:
- /tmp/local_even_replacement.py
- /tmp/local-even-replacement.log
- /tmp/local-even-replacement-certificates.json

Let G be the Petersen line graph (15 vertices, 30 edges) in the ordering in
/tmp/line_petersen_data.pickle. Let H be the union of the two cycles with edge
masks 140509184 and 394473289. H has 18 edges, 11 simple cycles, cycle-space
dimension four, minimum partition size two and maximum partition size three.
The full graph G has minimum three (no two-cycle partition and an explicit
three-cycle partition). EVERY nonempty even edge subset S of H satisfies
number(G minus S) <= 2. All 15 such S were checked, with explicit partitions
saved in JSON. The XOR closure has size 16, matching the independently computed
cycle-space dimension, so all even subsets of H are included.

Thus the proposed LOCAL replacement principle is false even if removal of a
whole even subgraph, rather than just one cycle, is allowed: a nonrigid two-cycle
union need not admit a proper even replacement preserving the ambient optimum.
G is not an EvenMinimal graph. This neither disproves core rigidity nor settles
Erdos 184. A valid global exchange argument would need additional reasoning.

No jobs are left running. Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Continuation — critical saturation and degree-two identification VERIFIED

The original Spec is STILL UNSOLVED and unchanged. No complete proof/disproof
has been submitted. A uniform sparsity bound for arbitrary cycle-critical
simple graphs was reconsidered as a weaker sufficient target, but no such
bound was proved or assumed. In particular, the unsaturated case remains open.

### New checked general module

Submission/CriticalSaturation.lean (imports Submission.TightDual), namespace
Erdos184Work.CriticalSaturation, passed with current olean and permitted axioms.
Log /tmp/CriticalSaturation-check.log; exit file is 0.

- cycle_hits_saturated: if G is CycleCritical and degree(v)=2*number(G),
  every cycle contains v. EvenMinimal is NOT needed.
- saturated_iff_feedback: for even cycle-critical G, saturation at v is
  equivalent to G induced away from v being acyclic.
- saturated_rigid_and_sparse: under that saturation hypothesis, even G is
  rigid, has at most 2*|V| edges, and 2*number(G) < |V|.
- degree_gap_of_nonrigid: an even nonrigid cycle-critical graph satisfies
  degree(v)+2 <= 2*number(G) for every v.

These results give no uniform bound on the optimum in the unsaturated case.

### Exact identification diagnostic (not itself a Lean proof)

Files:
- /tmp/even_cycle_factor_server.cpp and compiled server
- /tmp/petersen_pair_identification.py
- /tmp/petersen-pair-identification.log
- /tmp/petersen-pair-identification-certificates.jsonl

Starting with the checked 40-vertex doubled-Petersen realization, match each
private vertex for label (e,false) to a private vertex (perm(e),true), where
the two base Petersen edges are vertex-disjoint. The quotient is simple on
25 vertices with 60 edges: ten vertices have degree six and fifteen have
 degree four. Fifty selected permutations were checked, not all permutations.
EVERY selected quotient has an explicit three-cycle partition, independently
checked in Python for edge coverage and connected 2-regularity. Degree six
then gives minimum exactly three. A surviving square avoids a degree-six
vertex, so none of these quotients is cycle-critical. This is a failed way
to produce a dense critical graph, not evidence sufficient for a general bound.
The unmerged reference was also rejected by the exact 3-cycle search; its
stronger optimum-five statement was already proved in Lean.

### One quotient and its provenance now formally checked

Submission/PetersenIdentificationData.lean and
Submission/PetersenIdentification.lean both PASSED, exit0/current oleans.
Namespace Erdos184Work.PetersenIdentification.
Logs /tmp/PetersenIdentificationData-check.log and
/tmp/PetersenIdentification-check.log; all four final principal audits contain
only propext, Classical.choice, Quot.sound. Harmless linter warnings remain.

The first diagnostic permutation is used. Verified results include:
- explicit graph, degree_table, even, degree_lower, edge_card=60;
- three explicit 20-edge cycles, number_upper and number_three;
- an explicit square avoiding vertex0, not_critical, not_minimal;
- quotient : DoublePetersenGraph.Vertex -> Fin25;
- quotient_surjective, quotient_hom, quotient_edge_surjective;
- private_degree, identified_private, identified_degree_two;
- obstruction, combining source cycle-criticality/optimum5 with the target's
  evenness, minimum degree4, 60 edges, optimum3, and failure of cycle-criticality.

The map takes edges onto the target edges, so the target is genuinely the
specified vertex quotient, not an arbitrary graph with extra edges. Distinct
identified vertices both have degree two in the original graph. This refutes
preservation of cycle-criticality under such degree-two identifications.
It does NOT refute the original conjecture or the critical sparsity target.

Verification lessons:
- Monolithic finite degree/cardinality/edge-coverage checks consumed excessive
  memory. Splitting finite quantifiers with fin_cases made the checks practical.
- Compute edge-cardinality via the explicit edge list, an extensional
  edge_finset equality, and List.toFinset_card_of_nodup, rather than blindly
  reducing graph.edgeFinset.card. The list nodup proof uses simp.
- Long cycle proofs work with simp on Walk.isCycle_def/isTrail_def.
- Native and classical neighbor-set Fintype instances cause displayed-identical
  degree expressions not to rewrite. Normalize via card_neighborSet_eq_degree
  and Nat.card_eq_fintype_card before rewriting or using the evenness theorem.
- Data and assembly were separated to cache the checked finite data. The final
  assembly check used -M9000 and stayed below the cgroup limit. No new OOM kill.
- /tmp/make_petersen_identification.py is the INITIAL generator; its output was
  subsequently repaired and split. Do NOT rerun it over the checked modules.
- Submission/PetersenIdentificationProbe.lean and its earlier logs are scratch
  diagnostics with obsolete failures. The final Data/assembly exit0 logs and
  oleans are authoritative; no failed proof was promoted to a theorem.

No jobs remain running. Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Continuation: arbitrary-edge monotone hull and adjacent compression

Spec remains UNSOLVED and unchanged. No new Lean theorem or complete submission.
The revisited quantity is h(G) = max { Critical.number H | H ≤ G }, allowing
ALL edge-subgraphs, unlike the earlier even-support hull. A potential route
would be monotonicity of h under adjacent Kelmans transfer, followed by a
valid extremal compression argument. Neither step has been proved.

Exact finite diagnostic only (NOT Lean verified):
- /tmp/compression_hull.cpp and /tmp/compression_hull
- /tmp/compression-hull6.log and /tmp/compression-hull7.log
The program computes the minimum cycle-and-single-edge partition number for
all edge subsets of K_n by a least-edge partition recurrence. It then computes
the maximum over subgraphs using immediate-subset maxima, and tests every
ordered adjacent transfer on every graph. No decrease of the hull was found
for n=6 or n=7. These two bounded-order absences do NOT imply monotonicity.
No larger enumeration was launched, and no jobs remain running.

This direction also does NOT justify a sparsity claim for globally edge-minimal
graphs. The existing split-graph examples rule out a universal n-piece bound
for arbitrary graphs, and global edge minimality must not be confused with
single-edge criticality. The missing arbitrary-order linear bound remains.

## Continuation: edge-hull infrastructure verified; conjecture still unsolved

NEW CHECKED module: Submission/EdgeHull.lean, importing Submission.Work.
/tmp/edge-hull-check.exit is 0, /tmp/edge-hull-check.log contains four permitted
axiom audits, and .lake/build/lib/lean/Submission/EdgeHull.olean is current.

Erdos184Work.EdgeHull defines value G = max {number R | R ≤ G}, over ALL
edge-subgraphs, and Minimal G = strict decrease on every proper edge-subgraph.
Verified: number_le_value, le_value, value_le_iff, monotone, exists_maximizer,
exists_minimal_maximizer, Minimal.edgeCritical. In Compression, transfer_self,
transfer_adj_pair/left/right/away and transfer_mono are verified. transfer_mono
is inclusion monotonicity of the graph operation, NOT decomposition-number
monotonicity.

The conditional transfer_value_le_of_minimal and
adjacent_transfer_value_le_of_minimal precisely expose the missing hypothesis:
  ∀ R, Minimal R → ∀ u v,
    number R ≤ value (transfer R u v ⊔ edge u v).
The joining edge may be absent from the extracted minimal R even when it is
present in G. Its inclusion in this condition is important. No proof of that
condition, no extremal compression conclusion, and no linear bound was obtained.

### Exact finite diagnostics, NOT Lean theorems

/tmp/edge_hull_unlabelled.py computes exact minima and hulls up to isomorphism,
using every single-edge deletion for the hull recurrence and every cycle
through a fixed edge for the minimum recurrence. All recursive subgraphs are
canonically labelled with Sage. The order-eight run completed:
  12346 isomorphism classes; value(K8)=8, number(K8)=7;
  79 globally edge-minimal graphs, of which 4 have a cyclic component;
  all 4424 ordered-pair transfer-plus-joining-edge tests on minimal cores passed.
Log /tmp/edge-hull-unlabelled8.log, data /tmp/edge-hull-minimal-8.pickle.
The four cyclic cores (including isolated vertices) have graph6 strings:
  G?@zz{  optimum7, 15edges: K3 join I4 plus an isolated vertex;
  G?@z~{  optimum8, 16edges: leaf attached to the clique side;
  G?`zz{  optimum8, 16edges: leaf attached to the independent side;
  G?B~v{  optimum8, 17edges: K3,5 plus two adjacent edges on the three-side.
The last is nonchordal, so global edge-minimality does NOT imply chordality.
These computations do not prove any arbitrary-order compression statement.

The order-nine version was launched and is STILL RUNNING at this note update:
PID in /tmp/edge-hull-unlabelled9.pid (361212), log
/tmp/edge-hull-unlabelled9.log. Latest observed progress was over209000 states.
Do not claim its conclusion before the final FULL/NO_CORE_COUNTEREXAMPLE lines.
It uses modest memory (~250 MB RSS) and will save minimal cores on completion.

A separate exact test rejected a proposed edge-critical singles/cycles ratio:
/tmp/critical_single_fraction.cpp, /tmp/critical-single-fraction7.log.
K2,5 is edge-critical with optimum4 and maximum optimal single-edge count2.
More generally K2,(2t+1) has optimum t+2 and exactly2 single-edge pieces in
any optimum (all cycles have length4). Thus there is no positive fixed lower
bound on the fraction of singleton pieces in optimal edge-critical graphs.
This is an obstruction to an auxiliary route, not a disproof of Erdős184.

A further mathematical observation (NOT newly Lean formalized): the existing
odd-independent-side parity lower certificates survive adjacent compression
at the level of the hull. If both transferred vertices lie outside the odd
independent set B, its degrees and the total degree on the other side are
preserved. Otherwise take the receiver outside B (the opposite receiver gives
an isomorphic transfer). Moving r private neighbours of v∈B adds r to the
other-side degree sum and subtracts r from degree(v). If r is odd, delete the
retained joining edge: B has odd degrees again and the other-side sum changes
by r-1≥0. If r is even, no deletion is needed. This explains some finite
examples, but no assertion that all cores have such certificates is proved.

Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
It still has the original sorry. No complete proof/disproof or submission.

## Latest continuation: parity preservation and adjacent-only extremal reduction

Spec remains UNSOLVED and unchanged; its original sorry is retained. No complete
proof/disproof has been obtained or submitted. SHA256:
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

### NEW VERIFIED modules (current oleans, successful exit-zero checks)

- EdgeHullParityBase.lean imports EdgeHull. Includes the former degree and
  private-neighbor lemmas, plus delete_edge_neighbors_left,
  delete_edge_degree_left/right/other.
  Log /tmp/edge-hull-parity-base-check.log and .exit.
- EdgeHullParity.lean now imports EdgeHullParityBase, without duplicating its
  definitions. Log /tmp/edge-hull-parity-check.log and .exit (0).
  Checked transfer_left_sum, delete_cross_edge_left_sum,
  transfer_right_independent, transfer_preserves_odd_independent_certificate,
  transfer_hull_parity_lower. All principal audits permitted.
  For a graph on A ⊕ B with B independent and all its degrees odd, adjacent
  transfer from b∈B to a∈A has a subgraph R (the transfer itself, or with ab
  deleted) with B still odd and independent and the A-degree sum not decreased.
  Consequently its hull satisfies the original independent-side lower bound.
  This is ONLY a lower-certificate preservation theorem; no assertion that
  all minimal graphs possess such certificates has been proved.
- EdgeHullExtremal.lean imports EdgeHullParity.
  Log /tmp/edge-hull-extremal-check.log and .exit (0).
  exists_global_extremizer: choose maximum number over ALL graphs on V,
  minimum edge count among those, then maximum prescribed natural potential.
  It is Minimal. number_eq_of_hull_at_global_minimizer: an edge-count-preserving
  operation with hull at least this global optimum must itself have that
  optimum, because a proper maximizing subgraph would violate minimal edge count.
  bound_of_adjacent_minimal_compression: conditional extremal reduction.
- EdgeHullPotential.lean imports EdgeHullExtremal.
  Log /tmp/edge-hull-potential-check.log and .exit (0).
  Checked sum_exchange_two, transfer_edge_card, degreePotential,
  transfer_potential_lt, NestedAlongEdges, exists_improving_transfer,
  NestedAlongEdges.exists_universal, bound_of_compression_and_nested.
  degreePotential is the sum of squared degrees, using Nat.card neighborSet
  to avoid Fintype-instance mismatches. Transferring private neighbors from
  a lower/equal-degree sender to a higher-degree receiver strictly increases it.
  NestedAlongEdges says the lower-degree endpoint of each edge has no private
  neighbor apart from the other endpoint. In a connected such graph, a vertex
  of maximum degree is universal (checked by propagation along walks).
  All four final audits contain only propext, Classical.choice, Quot.sound.

IMPORTANT REFINEMENT: The global extremal route needs ONLY
  ∀ G, Minimal G → ∀ u v, G.Adj u v → number G ≤ value (transfer G u v).
The earlier sufficient condition including nonadjacent pairs plus a joining
edge is stronger than necessary for this route. Neither is proved.

The latest conditional reduction requires exactly:
1. The above adjacent-only minimal-core compression inequality; and
2. A bound for graphs satisfying NestedAlongEdges.
There is NO arbitrary-order proof of (1) and NO verified linear bound in (2).
Universal-vertex structure alone is not a decomposition bound. One possible
mathematical route to (2) is all-odd path decomposition (Lovasz); that theorem
and the requisite parity/assembly reductions are NOT formalized here.

### Completed external diagnostics, NOT Lean theorems

Order-nine unlabelled hull computation finished successfully:
/tmp/edge-hull-unlabelled9.log
/tmp/edge-hull-minimal-9.pickle
274668 isomorphism classes; number(K9)=4; value(K9)=9.
168 nonempty globally minimal graphs, 16 with a cyclic component.
12096 transfer-plus-joining-edge tests on minimal cores: no counterexample.
Cyclic cores (key, minimum, edges):
H??@x{~ 7 15
H??@x|~ 8 16
H?@@x{~ 8 16
H_?@x{~ 8 16
H??Bzx~ 8 17
H??@x~~ 9 17
H??@z}~ 9 17
H?@@x}~ 9 17
H?B@x{~ 9 17
H?Q@x{~ 9 17
H_?@x|~ 9 17
H_@@x{~ 9 17
H??Bzz~ 9 18
H??Bz~| 9 18
H?ABzx~ 9 18
H??F~z| 9 19

A narrower two-choice claim was tested:
  number G ≤ max(number (transfer G u v ⊔ edge u v),
                 number ((transfer G u v).deleteEdges {uv})).
/tmp/edge_hull_two_choice.py, /tmp/edge-hull-two-choice9.log.
It FAILS for nonadjacent u,v even when G is globally minimal. Example:
G graph6 H?@@x{~, minimum8, u1 v2 nonadjacent; the two target minima are6 and5.
This source is K3 join I4 with a leaf attached to the independent side, plus
an isolated vertex. It is not a counterexample to the hull inequality.
The script stopped after eight such nonadjacent failures.

The adjacent-only variant /tmp/edge_hull_two_choice_adj.py completed:
/tmp/edge-hull-two-choice-adj9.log; 272 unordered adjacent tests on the 16
cyclic minimal cores, no two-choice failure. This is finite evidence only.
No arbitrary-order two-choice theorem has been proved or assumed.

All background computations in this continuation have FINISHED. There are no
active Lean or Sage jobs. Failed scratch probes remain separate from final
exit-zero logs; never use recovery declarations containing sorryAx.

Lean lessons: use explicit Finset.sum_add_distrib (not in default simp);
Finset.sum_erase_add has an explicit finset argument; normalize all relevant
cardinalities, including multiplicative coefficients, with
  [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
and for edges [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card].
A generic Classical DecidableEq V can differ from Sum's synthesized instance;
a local noncomputable DecidableEq (A ⊕ B) := Classical.decEq _ helped, but
let-bound graphs still required Nat.card normalization. Huge defeq searches
were instance mismatches, not difficult mathematics; heartbeat-limited probes
localized them. Some older failed probes hit Lean's memory limit, but the
successful module checks use -M7000 and have only permitted audits.

## Further continuation: odd-forest reduction; terminal simplification fails

Spec remains UNSOLVED, unchanged, and retains the original sorry. No complete
proof/disproof has been obtained or submitted.

NEW VERIFIED module: Submission/OddForestReduction.lean
imports Submission.EdgeHullPotential.
Log /tmp/odd-forest-reduction-check.log, exit file0, current olean.
All three final audits use only propext, Classical.choice, Quot.sound.
Namespace Erdos184Work.Vertex:
- exists_forest_same_parity: every finite graph has an acyclic edge-subgraph
  with the same degree parities and at most n edges.
- exists_parity_forest: an even terminal set in a preconnected graph can be
  realized as the odd-degree set of a forest.
- exists_odd_complement_forest_except: for any specified r in a preconnected
  graph, delete a forest with fewer than n edges so every vertex other than r
  has odd degree.
- odd_at_exception_of_even_order: handshaking supplies odd degree at r too
  when the order is even.
- exists_odd_complement_forest: for positive even order, the residual can
  therefore have all degrees odd.
These supply parity correction only. There is NO all-odd path-partition theorem
or resulting terminal cycle-and-edge bound in this module.

The contemplated terminal route uses the known Lovasz path-decomposition theorem
for all-odd graphs. It is absent from Mathlib and the installed Sage sources,
and no complete proof was reconstructed in this continuation. Do not silently
assume it or replace simple paths by Euler trails: repeated internal vertices
would make closing through the universal vertex fail the 2-regularity condition.
The general minimal-core compression hypothesis is also still unproved.

### Exact targeted diagnostic, NOT a Lean theorem

/tmp/edge_hull_double_split.py
/tmp/edge-hull-double-split.log
/tmp/edge-hull-double-split.pickle
The source is two K3 join I4 graphs sharing a clique edge, on12 vertices and
29 edges: universal vertices0,1; other clique vertices2,3; leaves4..7 adjacent
to0,1,2 and leaves8..11 adjacent to0,1,3.
The computation FINISHED in about701 seconds:
  260584 canonical subgraph states;
  source minimum12, hull12, maximum over proper subgraphs12;
  source is NOT globally minimal;
  1033 nonempty globally minimal subgraph types, 68 with a cyclic component.

Among the proper minimal cores is graph6 I???~B~~w on10 vertices,23 edges,
minimum10. It is K2 joined to two disjoint K1,3 stars. It is connected,
2-connected, and NestedAlongEdges, but it is NOT K_a join I_b (and not even a
split graph: two independent leaf-child edges form an induced2K2).
In the saved12-vertex data its canonical representative, with two isolates, is
  K?????FM@~f~.
Thus the proposed shortcut "globally minimal terminal blocks are complete split
graphs" fails in this exact external computation. No Lean minimality certificate
for this example was produced; do not report it as kernel-verified.

Two other new minimal source subgraphs, order12/27 edges/minimum12:
  K?????N{F}^~  (degrees 3x8,5,5,9,11)
  K?????N{F}~|  (degrees 3x8,5,5,10,10)
They are not NestedAlongEdges. No new transfer tests on these were launched.

A mathematical observation, NOT newly formalized: stronger degree/parity lower
certificates can account for the10-vertex example. Let A be any nonempty vertex
set of size a, let b be the size of an independent set of odd-degree vertices,
and let o be the number of odd-degree vertices outside A. Every decomposition
of size k satisfies
  sum_{v in A} degree(v) + (2a-2)*b + o <= 2a*k.
Reason: its singleton graph has at least b edges and degree at least1 at every
odd vertex; cycle contributions on A are at most2a per cycle. For the example,
A is the two universal vertices, b=6 (leaves), o=8, degree sum18, giving
  18+2*6+8=38 <=4k, hence k>=10.
This strengthens the earlier complementary independent-side certificate, but
no certificate characterization of arbitrary minimal graphs has been proved.

The earlier line-Petersen diagnostic was rerun (/tmp/test_line_petersen.py):
it has7514 cycles and a non-exposable8-cycle, so it is NOT cycle-critical. This
was only checking an auxiliary possibility, not a new result or a source of a
uniform bound. Its /tmp/line_petersen_data.pickle was regenerated identically.

All background jobs in this continuation have FINISHED; no Lean or Sage jobs
are running. Last resource check was about58h56m used /37h04m remaining.
Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## New checked modules: enhanced parity certificates and transfer correction

ParityDegreeLower.lean, NestedDoubleStar.lean, and ParityCorrectedTransfer.lean
have exit-zero checks and current oleans. Their main axiom audits use only
propext, Classical.choice, Quot.sound. The first gives
sum_A degrees + (2|A|-2)|B| + |O| ≤ 2|A| number
for nonempty A, odd independent B, and odd O disjoint from A. A and B need
not be disjoint. The second verifies minimum=10 and nested neighborhoods
for K2 joined to two disjoint K1,3 graphs; GLOBAL MINIMALITY IS NOT CHECKED.
The third proves parity-corrected adjacent transfer preserves all degree
parities and does not lower degrees away from the sender; it preserves the
certificate when sender is outside A and receiver outside B. This is NOT
number/hull compression, and certificate completeness remains unproved.

Spec remains unchanged with sorry. No complete proof/disproof obtained.

## Latest checked continuation: complete disjoint-certificate transfer

Submission/AdjacentCertificateTransfer.lean PASSED; current olean and exit0:
/tmp/adjacent-certificate-transfer-check.log and .exit. Principal axiom audits
contain only propext, Classical.choice, Quot.sound.

Namespaces/results:
- EdgeHull.value_le_of_iso, value_eq_of_iso: hull invariance across vertex types.
- Compression.transfer_swap_adj, transferSwapIso, transfer_value_swap:
  opposite transfer orientations are isomorphic by swapping the endpoints.
- transfer_degree_sum_of_mem: when both endpoints belong to A, the raw transfer
  preserves its degree sum. transfer_preserves_internal_certificate additionally
  preserves oddness on B and O when these sets are disjoint from A.
- transfer_certificate_oriented: combines raw internal transfer with the earlier
  parity-corrected transfer when the sender lies outside A.
- transfer_certificate_bound: for ANY adjacent transfer and nonempty A disjoint
  from odd independent B and odd O, the original enhanced certificate numerator
  is at most 2|A| times the TARGET HULL. Orient away from B and either toward A
  or internally in A, then transport the hull through the swap isomorphism.
- transfer_hull_ge_of_certificate: if that numerator is strictly greater than
  2|A|(k-1), then k ≤ target hull. Certificate existence is an EXPLICIT assumption.

This does NOT establish number/hull compression for arbitrary minimal graphs.
It also does not establish the terminal linear bound or settle Spec.

### Exact catalogue diagnostic (external, NOT Lean verified)
/tmp/check_parity_certificates.py; /tmp/parity-certificates.log.
For each graph maximize the enhanced global certificate using an odd independent
set of maximum size b, q=number-of-odd-vertices/2, and the sorted floor(degree/2)
list. For an A of size a, the optimized bound is
  b + ceil((sum of top a floor(degree/2) + q - b)/a).
This formula permits A to overlap B (as does ParityDegreeLower); the newly
checked arbitrary-transfer theorem requires A and B to be disjoint.

The single global certificate misses 7 of 15 connected cyclic order9 catalogue
cores and 34 of 55 connected cyclic double-split catalogue cores. All misses
have pendant tree structure. Summing optimized certificates over biconnected
blocks (a single edge contributes1) attains the stored exact minimum on ALL
168 order9 cores and ALL1033 double-split cores. This is finite evidence for a
BLOCKWISE tightness conjecture, not a theorem for arbitrary graphs. We have
not proved completeness or preservation of arbitrary blockwise certificates.

Spec unchanged with original sorry. No complete proof/disproof, no submission.

## Latest continuation: minimal cores have nonseparating cycle deletions

NEW VERIFIED Submission/MinimalCycleConnectivity.lean; current olean, exit0:
/tmp/minimal-cycle-connectivity-check.log and .exit. Axiom audits contain only
propext, Classical.choice, Quot.sound.

- Critical.number_delete_bridge: deleting a bridge lowers number by exactly1.
- EdgeHull.Minimal.cycleCritical: global edge-minimality implies every simple
  cycle deletion lowers number by1, WITHOUT any evenness assumption.
- Minimal.cycle_edge_reachable: after deleting a cycle, the endpoints of every
  removed edge remain reachable. Otherwise adding that edge back gives a bridge
  and a proper subgraph with the original number, contradicting global minimality.
- Minimal.delete_cycle_reachable: deleting any simple cycle preserves ALL
  original reachability relations.
- Minimal.delete_cycle_connected: connectedness is therefore preserved.
- Minimal.cycle_vertex_degree: every vertex on a cycle has degree at least3.
- Minimal.degree_two_not_on_cycle and Minimal.bridge_of_degree_le_two:
  every edge incident to a vertex of degree at most2 is a bridge.

These are necessary structural properties, NOT a compression theorem or an
upper bound. Reconsideration of universal/nested terminal graphs did NOT yield
an all-odd simple-path decomposition or a terminal linear bound.

### Exact finite tests, NOT Lean theorems

1. Two-choice compression on EDGE-CRITICAL graphs (not globally minimal):
   /tmp/two_choice_edgecritical.cpp and /tmp/two-choice-edgecritical.log
   checks all labelled order7 graphs and finds no counterexample.
   /tmp/edgecritical_twochoice_unlabelled.py generated all12346 order8 graph
   values and481 edge-critical isomorphism types. Saved data (avoid rebuilding):
   /tmp/edgecritical-values8.pickle = (number_table, edgecritical_rows).
   Its first counterexample printer failed because Sage EdgesView is not JSON
   serializable; the completed table was already saved. The corrected cached
   test /tmp/edgecritical_twochoice_cached.py confirms the counterexample in
   /tmp/edgecritical-twochoice8-cached.log.

   Graph6 G?oxnc, source number6, transfer receiver4/sender5 number5,
   joining-edge-deleted transfer number4. Edges:
   04 07 14 17 25 26 27 35 36 37 45 56 67.
   Every one-edge deletion has number5. It is connected, so a spanning tree
   with7 edges proves it is NOT globally minimal. This does not refute the
   main minimal-core two-choice/hull conjecture.

   /tmp/edgecritical_counter_summary.py; /tmp/edgecritical-counter-summary.log:
   all two-choice failures total8 unordered-edge tests across two isomorphism
   types. The other is GLqBG{, also number6, active order8, minimum degree3,
   vertex/edge connectivity3. It too has a spanning-tree subgraph of number7.

2. /tmp/edgecritical_nonseparating.py; /tmp/edgecritical-nonseparating.log:
   among481 order8 edge-critical types,195 have a raw-transfer drop;35 of
   these have EVERY cycle deletion preserving reachability. Hence the new
   necessary nonseparation property does NOT rescue RAW number monotonicity.
   In all35, the joining-edge-deleted target restores the source number.
   Both two-choice-failure graphs have separating cycles (explicit cycles in
   the log), so there is no order8 counterexample to the stronger auxiliary
   two-choice claim under edge-criticality + nonseparating cycle deletions.
   This is finite evidence only. No general theorem of this kind is proved.

3. /tmp/edge_and_cycle_critical.py; /tmp/edge-and-cycle-critical8.log:
   requiring BOTH one-edge deletion and one-cycle deletion to lower number
   does NOT imply global minimality. Among481 edge-critical types,117 meet
   the additional cycle-critical condition, and38 of these are nonminimal.
   K3,5 is a simple example (number7 on8 vertices, spanning-tree number7).

No jobs remain running. Spec still unchanged with original sorry and hash
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No complete proof/disproof or submission has been made in this continuation.

## Latest continuation: multi-cycle bridge restoration bound checked

NEW VERIFIED Submission/MinimalBridgeRestoration.lean, with current olean and
exit0 at /tmp/minimal-bridge-restoration-check.log and .exit. Main axiom audits
contain only propext, Classical.choice, Quot.sound.

- Critical.number_delete_bridges: if every edge of a finite set F is a bridge
  of G, number G = number (G.deleteEdges F) + |F|.
- Critical.number_sdiff_add_le: number G ≤ number(G\E)+number E for E≤G.
- BridgeExtension.exists_extension: for any R≤G there is a finite set of new
  edges N⊂E(G)\E(R) such that all N-edges are bridges in R+N and R+N has the
  same reachability relation as G. Proof: choose a spanning maximal forest T
  of R and extend T to a spanning maximal forest F of G; use N=E(F)\E(R).
  The existing R connections cannot destroy the bridge property, because T
  already realizes all R reachability and is contained in F.
- EdgeHull.Minimal.bridge_restoration_lt: for globally minimal G, any nonempty
  even E≤G, and a bridge-only restoration N⊂E after deleting E, |N|<number E.
  Otherwise the restored proper subgraph has number at least number G.
- Minimal.exists_small_bridge_restoration: combines the previous results to
  produce such a restoration of full original reachability, with |N|<number E.
  In particular a union of q edge-disjoint cycles can be reconnected using at
  most q-1 restored edges. The cofactor is NOT assumed or proved minimal.

This is a stronger NECESSARY constraint on minimal graphs, not an upper bound.
Further examination of rank/excess, maximal cycle families, parity forests,
and universal-vertex arguments did not yield the missing arbitrary-order step.
No certificate-completeness, compression, terminal linear bound, or original
conjecture proof/disproof has been obtained. No new exact searches were launched.

Spec remains unchanged with original sorry and SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No jobs remain running and no complete submission was made.

## Latest continuation: hereditary terminal structure checked; still no settlement

NEW VERIFIED `Submission/NestedHereditary.lean`, importing
`Submission.EdgeHullPotential`. Current olean, exit-zero check:
`/tmp/nested-hereditary-check.log` and `.exit`.
Principal axiom audits use only propext, Classical.choice, Quot.sound.

In namespace Erdos184Work.Compression:
- `closedNeighbors`, `mem_closedNeighbors`, `card_closedNeighbors`;
- `NestedAlongEdges.closed_subset`;
- `nestedAlongEdges_iff_closed_comparable`: the degree-oriented terminal
  condition is equivalent to inclusion-comparability of closed neighborhoods
  at each adjacent pair;
- `NestedAlongEdges.induce`: the condition is inherited by induced subgraphs.
  The proof uses closed-neighborhood inclusion, rather than incorrectly
  assuming induced degrees preserve their original comparisons;
- `NestedAlongEdges.induce_exists_universal`: every connected induced
  subgraph of a terminal graph has a universal vertex;
- `NestedAlongEdges.no_two_private_neighbors`: adjacent endpoints cannot both
  have private neighbors. This excludes induced P4 and C4 configurations.

These are structural lemmas ONLY. No terminal linear bound, all-odd simple-path
partition theorem, arbitrary minimal-core compression, or certificate exactness
was proved. Reconsideration of all-odd path decomposition and fractional dual
exactness did not close either missing general step. Trails cannot replace
simple paths in the contemplated cone construction.

### Tensor-product analysis from the preceding continuation (not Lean formalized)

A proposed multiplicative lower bound for the minimum decomposition number
under categorical graph products is false. For G=K_(3,10), existing checked
bipartite lower bounds give number(G)>=14. The categorical product G x G is
the disjoint union K_(9,100) + K_(30,30). Existing bipartite constructions give
upper bounds 150 and15 for these components, hence a total upper bound165,
strictly below196<=number(G)^2. The product isomorphism and combined upper
bound were NOT assembled as a Lean theorem. This is an obstruction to that
auxiliary amplification proposal, not a counterexample to Erdős184.
Tensor powers of a complete bipartite graph likewise split into complete
bipartite components, so this family cannot produce superlinear ratios via
that operation. No valid amplification argument was obtained.

Spec.lean is unchanged, still with its original sorry; SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No proof/disproof was submitted, and no background jobs remain running.

## Latest continuation: fixed vertex-connectivity reduction VERIFIED

Original Spec remains UNSOLVED. NEW checked module:
`Submission/VertexSeparatorReduction.lean` (imports MinimalBridgeRestoration).
Current olean; `/tmp/vertex-separator-reduction-check.exit` is0 and its log
contains only permitted-axiom audits for all principal new results.

Namespace `Erdos184Work.VertexSeparators`:
- `NoSmallSeparator G k`: every cover A union B=univ by two proper vertex sets
  with |A intersection B|<=k has an edge between the two exclusive sides.
- `DeletionConnected G k`: deleting any set of at most k vertices leaves a
  PRECONNECTED induced graph. Small complete graphs are included; the empty
  residual is preconnected, so this avoids small-order connectivity conventions.
- `noSmallSeparator_iff_deletionConnected`: equivalence of these definitions.
- `number_spanning_le`, `number_induce_support`: adding isolated vertices or
  discarding vertices outside the support does not increase the required bound.
- `split_number`: for a genuine separation A,B, there is a graph H on B with
  number(G)<=number(G.induce A)+number(H). Assign all overlap edges to A and
  delete them from H; do not double-count them or assume H remains induced.
- `number_le_square` and `split_budget`: elementary finite-order base and
  natural-number accounting for the separator induction.
- `number_bound_of_minimal_no_small_separator`:
    if every globally edge-minimal G with NoSmallSeparator G k satisfies
    number(G)<=B*|V|, then every graph satisfies
    number(G)<=((2*k+1)^2+(k+1)*B)*|V|.
  Proof uses potential |V|-k for orders >k, a square-size base up to2k+1,
  and the fact that the child orders sum to at most |V|+k. Small child orders
  are paid for by a square bound. It first extracts a globally minimal hull
  maximizer and THEN performs the separator split; connectivity is NOT
  asserted to survive that extraction.
- `number_bound_of_no_small_separator`: same reduction without minimality in
  the terminal hypothesis.
- `number_bound_of_deletion_connected` and
  `number_bound_of_minimal_deletion_connected`: deletion-connectivity versions.
- `asymptotic_iff_fixed_vertex_connectivity`: exact equivalence of the original
  asymptotic proposition and a uniform real-coefficient bound restricted to
  DeletionConnected G k, for each FIXED natural k.
- `asymptotic_iff_minimal_fixed_vertex_connectivity`: equivalent natural-number
  bound restricted simultaneously to EdgeHull.Minimal G and
  DeletionConnected G k, again for each fixed k.

These are CONDITIONAL reductions, not a bound for the highly vertex-connected
class. No endpoint-routing theorem, terminal compression bound, core sparsity,
certificate exactness, or original proof/disproof was obtained. Fixed vertex
connectivity alone does not justify short edge-disjoint routes for an arbitrary
large collection of paired terminals. No new finite graph search was launched.

Technical details:
- Write `Nat.card (A intersection B : Set V)` with the explicit set type; the
  unannotated intersection can elaborate as an attempted intersection of Types.
  Likewise use `(S complement : Set V)` when it appears in a binder's type.
- To combine ncard and Fintype arithmetic, first `change` a set-cardinality
  identity to Nat.card of the subtype sets, then normalize Fintype cards.
- `nlinarith` needs `Nat.sub_add_cancel` explicitly when treating n-k as an atom.
- `open scoped Classical` does not make simp prove arbitrary disjunctions of
  excluded-middle form; `tauto` finishes the relevant set-cover identity.

No jobs remain running. Spec unchanged, still with original sorry; SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No complete submission. Latest resources: $611.39 used/$388.61 left;
60h56m used/35h04m left.

## Odd path extraction and two cycle absorption moves (verified)
`OddPathExtraction.lean` extracts edge-disjoint simple paths pairing precisely
all odd vertices, leaving an even residual. Thus in the all-odd case there are
exactly n/2 paths with unique endpoints, BUT the residual need not be empty.
For forests it is empty and the path partition theorem is checked.
`TwoPathCycleAbsorption.lean` is now fully checked, including `absorb_clean_cons`.
It proves two-path cycle absorption (1) when the paths are vertex-disjoint,
(2) when one meets the cycle only at its endpoint and that endpoint is absent
from the other path. Axiom audits use only the permitted three axioms.
Logs: /tmp/odd-path-extraction-check.log and
/tmp/two-path-cycle-absorption-check.log (both exit0; current oleans).
Neither move is automatically applicable to every extraction. In K3 join I3,
with triangle 0-1-2 left over and paths 0-4-1-3, 1-5-2-4, 2-3-0-5, both local
hypotheses fail. A general rearrangement argument is missing. Subcubic all-odd
absorption seems attainable but does not settle the original conjecture.
The independent general adjacent-minimal-core compression gap remains.

## Maximal endpoint path packings (verified; original still unsolved)
`EndpointPathMaximality.lean` imports TwoPathCycleAbsorption and checks cleanly,
with current olean and /tmp/endpoint-path-maximality-check.exit =0.
`Admissible L` requires edge nodup, endpoint nodup, and all vertices as endpoints.
`Maximal L` maximizes covered edge count among all admissible families.
`exists_maximal` proves existence for all-odd finite graphs, via the checked
extraction and a bounded natural maximum (no finiteness of walk types assumed).
`admissible_exchange`, `Maximal.no_exchange`, and `Maximal.no_two_exchange`
formalize exact list-permutation exchanges retaining endpoints and adding edges.
Permutation transport and `two_at_front` allow selecting arbitrary distinct
pieces from a family. `Maximal.pair_not_disjoint` and
`Maximal.pair_clean_blocked` turn the two verified absorption moves into
necessary obstructions for any unused cycle. They do NOT show the unused
residual is empty, and do not prove the all-odd simple-path partition theorem.
All principal axiom audits use propext, Classical.choice, Quot.sound only.

## Covered-path parity and maximal even residual (verified)
`CoveredPathParity.lean` imports EndpointPathMaximality and is fully checked:
/tmp/covered-path-parity-check.exit =0, current olean. All principal axioms are
propext, Classical.choice, Quot.sound. It defines `coveredGraph L` as the union
of path graphs, proves exact edge membership and degree addition, and proves
`coveredGraph_degree_mod_two`: for an edge-disjoint path family, the covered
degree modulo2 equals the endpoint occurrence count modulo2. Thus an admissible
family in an all-odd graph leaves an even residual; it has exactly n/2 paths.
`exists_maximal_even_residual` packages a maximal family, an even residual,
exact disjoint edge coverage, and the path count. Its residual is NOT shown to
be empty. The earlier K3 join I3 example only blocks the two moves for a
particular initial extraction; it is not asserted to be a maximal packing.

The central gaps are unchanged: no general all-odd simple-path partition
proof, no uniform terminal nested bound, no minimal-core adjacent compression,
and no unconditional arbitrary-order cycle bound. Spec unchanged with original
sorry and SHA256 509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No complete submission was made. No background jobs were launched.

## All-odd subcubic simple-path theorem VERIFIED
Two new modules are checked, with current oleans and permitted axioms only:
- EndpointPathReversal.lean: `Piece.reverse`, maximal-packing transport under
  edge/endpoint permutations, reversal of either of the first two paths,
  `exists_terminal_head`, `exists_initial_second`, endpoint uniqueness.
  Log /tmp/endpoint-path-reversal-check.log, exit0.
- SubcubicOddPaths.lean: `subcubic_all_odd_path_partition` proves that every finite
  all-odd graph of maximum degree <=3 has an edge partition into exactly n/2
  nonclosed SIMPLE paths, with every vertex an endpoint exactly once.
  Log /tmp/subcubic-odd-paths-check.log, exit0.

Proof: Take a maximal covered-edge endpoint packing. At a vertex on an unused
cycle, covered degree is odd and at most1 (two incident edges are reserved by
that cycle), hence exactly1. Paths therefore meet that cycle only at their
endpoints, and distinct paths cannot share a cycle vertex. If an endpoint path
has its other endpoint outside the cycle, the clean absorption move applies,
contradicting maximality. Thus all relevant paths have both endpoints on the
cycle. Two different such paths cannot intersect outside it either: that
would require degree at least4. A cycle vertex has a neighbor not equal to its
partner endpoint, giving two vertex-disjoint endpoint paths and the first
absorption move. Therefore the residual is acyclic; it is also even, so empty.

Checked declarations include:
`Admissible.covered_degree_one_on_unused_cycle`,
`Admissible.path_meets_unused_cycle_at_ends`,
`Admissible.paths_separate_on_unused_cycle`,
`Admissible.cycle_ended_paths_disjoint`,
`Maximal.head_other_end_on_unused_cycle`,
`Maximal.path_endpoints_on_unused_cycle`,
`Maximal.no_unused_cycle_subcubic`,
`Maximal.residual_acyclic_subcubic`, `Maximal.covers_subcubic`.

This does NOT prove the arbitrary-degree all-odd path theorem, the terminal
nested-graph bound, adjacent minimal-core compression, or the original
conjecture. Degree5 permits an internal path at a residual-cycle vertex or an
intersection of two paths away from the residual cycle, so the proof's crucial
degree-one/disjointness assertions cannot just be reused in that case.
Reviewing fractional/minimal-core rounding supplied no new general theorem.
Spec remains unchanged with its original sorry. No complete proof submitted.

Technical lessons: `Set.ncard_pos` has an explicit default finiteness argument,
so use `(Set.ncard_pos (s := S)).mp`, not `Set.ncard_pos.mp`. To pass degree
parity through `acyclic_even_eq_bot`, normalize `card_neighborSet_eq_degree` and
`Nat.card_eq_fintype_card`; direct instance comparison caused a timeout.
For list flatMap of cons pieces, use right-associated append expressions.

## One-generator binary hull diagnostic — still no settlement

Spec is unchanged and UNSOLVED. No new Lean theorem was proved in this
continuation, and no final proof/disproof was submitted.

The proposed auxiliary inequality is:

    h(C0) <= h(span(C0,z)) + 1,

where h(C) is the maximum, over codeword supports, of the minimum number of
pairwise-disjoint minimal nonzero codewords partitioning the support. The codes
here are genuinely binary linear (XOR-closed), not merely the weaker abstract
`Erdos184Serial.Code` interface. This inequality remains UNPROVED.

Exact exploratory diagnostics (Python integer masks, NOT Lean verified):

* `/tmp/code_extension_hull.py`, log `/tmp/code-extension-hull.log`: 100000
  random-basis attempts, lengths 5..18 and generated dimension at most 10.
  Dependent extensions are skipped. Every word in each tested code is examined.
  No counterexample. These mostly have low hull values, so this is weak evidence.
* `/tmp/code_extension_partitioned.py`, log
  `/tmp/code-extension-partitioned.log`: start with 4..7 disjoint blocks of
  length 3..5, add 0..4 extra generators, then one further generator. Completed
  5992 independent extensions (6000 attempts). Counts for h(C0)-h(C1):
  0:3522, 1:2183, -1:239, -2:44, -3:4. No drop greater than one.
* `/tmp/signed_hull_test.py`, log `/tmp/signed-hull-test.log`: exhausts all 127
  hyperplanes of the octahedral graph's 7-dimensional cycle code and all 1023
  hyperplanes of K6's 10-dimensional cycle code. Both ambient hulls are 2;
  the maximum hull among hyperplanes is 3 in both cases. No counterexample.
* `/tmp/code_extension_structured.py`, log
  `/tmp/code-extension-structured.log`: larger repeated-column examples,
  lengths 12..22, dimensions at most 15. The run was intentionally stopped
  after its progress entry at trial 700; it is NOT a completed 2000-trial run.
  No failure was reported before stopping. Do not claim complete coverage.

A limited elementary observation (mathematical, NOT Lean formalized): if C0
is exactly the span of disjoint block supports A1,...,Ak, then the inequality
holds. If z is partial on any block Aj, every new coset word meets Aj, so the
union of the other k-1 blocks has unchanged partition number k-1. If z is
constant on every block, either it lies in C0 or it has a nonzero coordinate
outside their union, in which case the whole old support is unchanged. This
explains some of the positive diagnostics; it does NOT extend to arbitrary C0.

Even an arbitrary-code proof would not yet settle the graph conjecture:
contraction creates parallel edges, and an exact contraction code cannot be
identified with the simple-graph transfer that drops duplicate edges. No
uniform bound controlling this loss or completing the nested-graph reduction
was obtained. The all-odd arbitrary-degree path augmentation also remains
unproved; the previously checked subcubic theorem was not generalized.

No background computations remain. Spec SHA256 is still
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## One-generator and contraction hull routes REFUTED (new kernel-checked results)

The original Erdős 184 proposition is STILL UNSOLVED. Spec.lean is unchanged,
with its original sorry. No original proof/disproof was submitted. This entry
supersedes the preceding tentative one-generator direction: the unrestricted
inequality is FALSE, with unbounded additive loss. The finite diagnostics had
missed a simple structured family.

### New verified modules

1. `Submission/BinaryExtensionHull.lean`, namespace
   `Erdos184Serial.BinaryExtension`.
   - `HullBound C n`: every valid support has a circuit partition of size <=n.
   - `SeriesPair C a b`: all source words agree at coordinates a,b.
   - `ExtensionBy C B z`: B's words are C's words and their coset by z.
   - `XorClosed` and the actual `extend` code constructor.
   - `AgreeOn.circuit_iff`, `.partition_iff`, `.hasNumber_iff`.
   - `hullBound_of_broken_seriesPair`: loss <=1 IF the added generator breaks
     a source series pair. Remove one source circuit containing that pair;
     the extension agrees with the source on the remaining support.
   - `preserves_seriesPairs_of_failure`: any failure must preserve all source
     series pairs. This remains true, but does not imply the unrestricted rule.
   Check `/tmp/binary-extension-hull-check.log`, exit file0, current olean.

2. `Submission/TripleBundleCode.lean`, namespace
   `Erdos184Serial.TripleBundle`.
   Ground set `Edge A = Fin 3 × A`. `count s i` counts row i.
   - `source`: even cardinality in each row independently.
   - `target`: the three row cardinalities have equal parity.
   - Both are XOR-closed genuine binary codes.
   - `target_extension a`: target is the extension of source by the triple
     containing `(i,a i)` for each i.
   - Source circuits all have size2, within a single row;
     `source_partition_card`: every source partition satisfies 2|D|=|s|.
   - `target_partition`: if k is a least populated row of a target word s,
     there is a partition with 2|D|+count(s,k)=|s|. Construct triangles until
     row k is exhausted, then pair edges in the other two rows.
   - `target_hullBound`: target hull <= card A.
   - `target_full_hasNumber`: the full target support has minimum card A,
     so this hull bound is EXACT. All target circuits have size <=3.
   - For A=Fin(2r), source full support is rigid/minimal with number3r,
     and source hull is exactly3r; target hull is2r.
   - `extension_hull_counterexample`: explicit width4 case, source hull6,
     target hull4, hence failure of the proposed loss-at-most-one rule.
   - `unbounded_extension_hull_loss c`: uses r=c+1 and proves loss >c,
     even with a rigid minimal source core.
   Check `/tmp/triple-bundle-code-check.log`, exit file0, current olean.

3. `Submission/TripleBundlePort.lean`, namespace
   `Erdos184Serial.TripleBundle.Port`.
   Ground set `Option (Edge A)` with none as a distinguished closing edge.
   - `code`: each row's parity equals the indicator of the closing edge.
   - `code_xorClosed`: genuine binary closure.
   - Every circuit avoiding none has size2; every circuit containing none
     has size4 (one edge in each row, plus the closing edge).
   - `partition_card_of_mem`: if none belongs to a partitioned support s,
     then 2|D|+2=|s|.
   - Width2r+1 full support is rigid/minimal with number3r+1.
   - `projection_valid_iff`: erasing none from valid words gives EXACTLY
     `TripleBundle.target`, the circuit-code puncturing/contraction operation.
   - `unbounded_contraction_hull_loss c`: for r=c+1, a rigid minimal source
     of number3r+1 projects to a code of hull2r+1, a drop r>c.
     Its type includes XOR closure of both codes.
   Check `/tmp/triple-bundle-port-check.log`, exit file0, current olean.

Every principal audit in all three final checks lists only propext,
Classical.choice, Quot.sound. The generic proofs do not rely on the numerical
searches. The one finite `decide +kernel` check is the width4 source validity.

### Graph interpretation (mathematical; NOT newly Lean-transported)

The plain source is the cycle code of a chain of three bundles of 2r parallel
edges. Identify the chain's ends to obtain the triangle of three bundles,
whose code is the target. Subdividing all labelled edges once makes both
source and target simple; no duplicate edges need be dropped during this
vertex identification.

The port construction is particularly relevant to the proposed contraction
route. Take junctions 0,1,2,3; between each successive pair put 2r+1 internally
disjoint paths of length2; add the single closing edge 0--3. This is a simple
even graph on 6r+7 vertices with 12r+7 edges. Every full cycle partition has
3r+1 pieces: exactly one cycle uses the closing edge, and the remaining edges
pair locally within the bundles. It is an even-minimal rigid core. Contract
0--3 (whose endpoints have no common neighbors) to obtain a simple triangle
of bundles; the target's even-support hull is2r+1. Thus loss r is unbounded
WITHOUT a parallel-edge duplication issue. r=1 recovers the old 13-vertex
NegativeCertificate family member; r=2 already gives source7 vs target hull5.

The code counts and minimality above ARE kernel-checked. The explicit graph
realizations, their equality to the implementation's `contract`, and transport
of the ALL-even-support hull have NOT been newly formalized in this entry.
Do not claim that a Lean graph-contraction theorem was submitted.

Crucial limits:
- This is NOT a disproof of Erdős184: all these graph counts are linear in
  their orders (indeed source number is about half its vertex count).
- `EvenMinimal` is NOT `EdgeHull.Minimal` over arbitrary edge subgraphs.
  These nonempty even examples are not globally edge-minimal (single-edge
  deletion increases their cycle-and-edge optimum). Thus the previously
  unproved adjacent *global* minimal-core compression route is NOT refuted
  by this construction, and is also not proved.
- There is no general all-odd path theorem or terminal nested-graph bound in
  this new work. The earlier subcubic result remains the checked special case.

No background jobs remain. Original Spec SHA256 is unchanged:
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Global-core parity-certificate continuation — no settlement

Spec remains unchanged and UNSOLVED. No new Lean theorem was proved in this
continuation. The global-minimal parity-certificate completeness hypothesis,
adjacent minimal-core compression, and the general all-odd path theorem remain
unproved. The previous binary/port counterexamples do not address GLOBAL
EdgeHull.Minimal graphs.

### A structured two-port candidate fails global minimality (external exact witnesses)

Take two copies of H_b = K3 join I_b and identify two independent-side vertices.
The resulting graph has 2b+4 vertices. A proper subgraph is obtained by deleting
the three right-side edges incident with one of the two shared vertices. It is
a one-vertex sum of H_b and H_(b-1). The existing degree/parity lower certificates
for those two blocks give a lower bound for this proper subgraph.

Files:
- `/tmp/two_port_split.py`: an initial GLPK minimum search was STOPPED after a
  few minutes on b=4. It did not report an optimum. Do not cite it as completed.
- `/tmp/two_port_split_upper.py`: completed explicit greedy cycle packings.
- `/tmp/two-port-split-upper.log`, `/tmp/two-port-split-upper.json`: final
  edge lists, pairwise edge-disjoint simple cycles, and remaining singleton
  edges. These are external exact integer witnesses, NOT Lean-verified here.

Results (whole-graph upper bound, proper-subgraph lower bound):
  b=4:  (12,12), 4175 cycles in the catalogue;
  b=6:  (13,17), 25865 cycles;
  b=12: (29,33), 544199 cycles.
Thus none is globally minimal. The whole-graph values are UPPER bounds only;
no minimum claim is made. This does not establish certificate completeness.
The first JSON write failed on a Sage EdgesView; the corrected rerun completed
and wrote all three final results. No jobs are left running.

### Other reconsiderations, NOT new theorems

All stored minimal cores need not be chordal: for example G?B~v{ is
K1 join K_(2,5), on8 vertices,17 edges, stored minimum8. Checking the existing
catalogues found 1,5,6 nonchordal cyclic entries respectively in the order8,
order9, and double-split catalogues. These were reused data, not a new
exhaustive search. Do not assume a chordal characterization.

A possible structured family for future analysis (UNTESTED for its optimum
or global minimality): four vertices A with just the edge 0--1; for each i in A,
add m independent degree-three vertices with neighborhood A minus {i}.
It has 4m+4 vertices and12m+1 edges. The known enhanced certificate with degree
set A and all4m independent odd vertices gives number >=5m+1. For m=3 this is
16 on16 vertices, above a spanning tree's15; neither equality nor global
minimality has been established. Different neighborhood types can create an
induced gem, so this may test stronger structural shortcuts if it is minimal.
No computation for this family was started. Do not treat it as a counterexample
to any currently stated theorem.

Further thought about constant-factor tensor amplification and additive
rank-sized fractional rounding yielded no proved inequality. The already
recorded raw tensor obstruction remains valid. No amplification hypothesis
has been added to Lean.

Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Low-degree hull reductions verified — original STILL UNSOLVED

`Submission/LowDegreeHull.lean` imports MinimalBridgeRestoration and contains:

- `EdgeHull.bridge_replacement_le`: if R <= G and e is a bridge of R but
  not of G, then number R <= value (G.deleteEdges {e}). The proof deletes e,
  restores ambient reachability using a nonempty bridge-only extension, and
  applies the exact bridge deletion formula for the decomposition number.
- `EdgeHull.value_delete_nonbridge_of_degree_le_two`: deleting a non-bridge
  s(v,w) with degree(v)<=2 preserves the arbitrary-edge hull. The adjacency
  assumption is unnecessary and has been removed; an absent edge is harmless.
  This uses a globally minimal maximizer, NOT an even-minimal core.
- `EdgeHull.value_delete_bridge`: if e is a bridge of G, then
  value G = value (G.deleteEdges {e}) + 1.
- `EdgeHull.Minimal.delete_bridge`: global minimality passes to deletion of
  a bridge. The helper bridge_extension_data adds the bridge back to any
  edge subgraph of the deleted graph.

Final check: `/tmp/low-degree-hull-check.log`, exit file0; current olean.
All four principal audits list only propext, Classical.choice, Quot.sound.
No finite core computation or new compression inequality was obtained from
these reductions. In particular the four-neighborhood candidate remains
untested, and general certificate completeness remains unproved.

Spec.lean is UNCHANGED with its original sorry; SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No settlement was submitted. No background jobs remain.

## Chain/ring continuation — ORIGINAL STILL UNSOLVED

Spec.lean remains unchanged with its original sorry. No proof or disproof of
Erdos184.erdos_184 has been found. Do not present the following auxiliary work
as a settlement or submit the unchanged file as a complete proof.

New checked modules (current oleans; principal audits use only permitted axioms):
- HullForestReduction: forest-bound witnesses and restoration of ambient bridges.
- CycleForestCertificate: finite cycle/edge partition plus rank-parent forest
  certificates imply ForestBound. Current Data includes a parent field.
- ChainRingDefinitions, ChainRingNormalization, ChainRingHullReduction: three
  K3,6 blocks with hub sets {0,4,1},{1,5,2},{2,6,3}, closed by edge 0--3;
  adjacent transfer 0<-3 yields the ring with last hub set {2,6,0} and leaf3.
  The host hull bounds <=24 are conditional on all canonical certificates.
- ChainRingBlocks, ChainRingParity, ChainRingPieces: localization of pieces
  avoiding the closing edge; a piece containing it uses <=4 edges per block
  and even degrees at all independent-side vertices.
- ChainRingResidualBounds: rowResidual_number_ge_eight is now VERIFIED.
  The remaining >=14 edges and six odd independent-side vertices give the
  lower bound via ParityDegreeLower.independent_odd_degree_bound.
- ChainRingLower: source_number_ge_twenty_five is now VERIFIED. The other
  pieces localize to the three blocks and require at least24 pieces; adding
  the closing-edge piece gives25. Logs /tmp/chain-ring-lower-check.log and
  /tmp/chain-ring-residual-bounds-check.log; both corresponding exit files0.

Arithmetic fix: `dsimp only [deg] at hd hs hev hr` before omega; in the final
residual inequality use `dsimp only [deg, R] at hl hsum hc hb`.

Finite certificate batch is INCOMPLETE. Seven certificates per file, 98 files,
ChainRingCertificates0..97. Progress /tmp/chain-ring-certificates-build.log;
per-file logs/exits /tmp/chain-ring-certificates-K.log/.exit. Inspect those
files to identify the last successful part. Parent378169 was deliberately
SIGSTOP-paused during this checkpoint; its current child may finish normally.
Watcher381828 (/tmp/finish_chain_ring_certificates.sh) was stopped deliberately.
No claim is made that all686 certificates have passed.

Generated but UNVERIFIED aggregation modules:
- ChainRingCertificateGroup{0,1}_{0..6}.lean
- ChainRingHullBounds.lean
The generator normalizes a : Fin3 -> Fin7 to ![a0,a1,a2], then uses343 cases
per Boolean ring value. Check these only after the certificate batch passes.
Do not import ChainRingOneCertificate together with bulk file97: duplicate names.

Still missing for the AUXILIARY counterexample: finish certificate batch,
check aggregation and hull bounds, then choose a minimal maximizer R<=source.
Number R>=25 forces the closing edge into R (base hull<=24); transfer R lies
in target (hull<=24), refuting arbitrary global-minimal adjacent compression.
This would NOT refute original Erdos184, since the example's number is linear
in its25 vertices. No general uniform bound or superlinear family is known here.

Original Spec SHA256:
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Matching-deletion continuation — original STILL UNSOLVED

New VERIFIED module Submission/MatchingDeletion.lean (243 lines), current olean,
/tmp/matching-deletion-check.log and .exit=0. All principal audits contain only
propext, Classical.choice, Quot.sound.
- cycle_outside_matching_two: every simple cycle has at least2 edges outside
  any degree-at-most-one graph M.
- even_number_outside_matching: for even G and degree(M)<=1,
  2*number G <= edgeCard(G minus M).
- matching_edges_le_singletons: if M<=G is a matching and G is even, every
  decomposition of G minus M has at least edgeCard(M) singleton pieces.
- delete_matching_number: 2*number G + edgeCard(M) <= 2*number(G minus M).
- hull_matching_boost: 2*number G + edgeCard(M) <= 2*EdgeHull.value G.
- minimal_even_matching_gap: for proper even E<=G with G globally minimal,
  M<=E matching, 2*number E + edgeCard(M)+2 <= 2*number G.
The graph-degree hypotheses use Nat.card neighborSet, avoiding Fintype mismatch.
Proof: in a minimum partition of G minus M, let F be the singleton union and
K the cycle union. F+M is even, and each of its cycles uses at least2 F edges.
Thus it needs <=|F|/2 cycles. Parity gives |F|>=|M|. Combine with K.
This is NOT a uniform upper bound. Matching size <=n/2 only supplies an additive
increase of order n, not a fixed fraction of a potentially superlinear optimum.

### Structured four-neighborhood candidate — EXTERNAL witnesses only
/tmp/four_neighborhood_certificates.py and /tmp/four-neighborhood-certificates.log
/tmp/four-neighborhood-certificates.json contain exact explicit decompositions.
Graph: four hubs0..3, a_i<=3 independent vertices of type i adjacent to all hubs
except i; optionally edge0--1. Ambient order16. For each of512 active cases,
cycle templates on the four hubs are expanded with distinct independent vertices.
The 13 templates are six digons, four triangles, three quadrilaterals; at most
three templates are used, with a small exact matching of edge slots to vertex types.
All511 cases except full a=(3,3,3,3) plus edge have a partition costing no more
than an explicit contained spanning forest. The full case has upper16 and forest15.
The known parity certificate gives lower16 for the full graph. Combined with the
low-degree bridge-restoration reduction, these witnesses SHOULD prove that it
is globally minimal; this has NOT been formalized in Lean. In particular don't
claim a new Lean minimality/3-connectivity theorem. The full graph is expected
3-connected and has cycles among its odd-degree vertices; it still has an exact
single parity certificate, so it does NOT refute certificate completeness.

### Chain/ring batch status
Parent378169 is RUNNING again. Parts0..51 were confirmed successful at last read,
part52 was then running. Inspect /tmp/chain-ring-certificates-build.log for current
status. Restarted finisher PID382040 waits for part97 exit0, then compiles groups
and ChainRingHullBounds. Groups0_0..0_4 have already independently PASSED; the
finisher currently repeats those harmlessly. Original watcher381828 is stopped.
Submission/ChainRingCompressionObstruction.lean has been WRITTEN but NOT CHECKED;
it imports pending HullBounds plus checked Lower. Once HullBounds passes, compile
that final assembly and audit it. Its intended theorem only refutes arbitrary
GLOBAL-minimal adjacent compression, NOT Erdős184.
A -M3000 trial of part97 failed immediately at imports (memory threshold); it did
not pass, and no ordinary part97 exit flag was written. Keep one heavy Lean job
at a time. The successful batch is unaffected. Memory-test files use distinct
/tmp/chain-ring-certificates-97-memory-test.* names.

### Unproved ideas reconsidered; do not silently assume
- Compression restricted to globally minimal highly vertex-connected graphs
  might avoid the chain obstruction, but NO theorem or evidence sufficient for
  that hypothesis was obtained.
- A possible sufficient target is existence of a vertex whose deletion drops
  number by at most2 in every globally minimal graph. It is UNPROVED.
- A fixed relative boost value(E)>=(1+epsilon)*number(E) on even graphs would
  imply an O(n) bound using the singleton forest of a globally minimal graph.
  Only the additive matching boost above is proved, not relative amplification.
- Bounding cycle pieces by singleton pieces in a globally minimal minimum
  decomposition is UNPROVED; the older edge-critical version was already
  refuted by K2,(2t+1). Do not confuse global minimality with edge criticality.
- General all-odd Lovasz path decomposition, arbitrary minimal-core rigidity,
  additive rank-sized fractional rounding, and product amplification remain
  unproved. No new original-proof bridge emerged from revisiting them.

Spec remains unchanged with original sorry, SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No complete proof/disproof was submitted. Last resources ~65h30m used /30h30m left,
$659.72 used/$340.28 remaining.

## Star-forest deletion and support boost — original STILL UNSOLVED

New VERIFIED modules, current oleans:
- StarDeletion.lean: generic `delete_with_repair`, `even_number_outside_two`,
  `independent_cover_degree_sum`, `cycle_outside_stars_two`,
  `delete_stars_number`, `hull_stars_boost`.
  /tmp/star-deletion-check.log and .exit=0.
- StarHullBoost.lean: `exists_leaf_stars`, `independent_hull_boost`,
  `exists_maximal_matching`, `matching_support_card`, `supported_order_boost`,
  `relative_boost_of_support_bound`.
  /tmp/star-hull-boost-check.log and .exit=0.
All final principal audits list only propext, Classical.choice, Quot.sound.

The new unconditional inequality is
  6*number G + G.support.ncard <= 6*EdgeHull.value G
for even G. Proof: choose a maximal matching M, with m edges. Its uncovered
supported vertices B form an independent set, and |support G|=2m+|B|.
The earlier matching boost gives 2*k+m<=2*h. Attach each vertex in B to one
neighbor, forming a star forest with independent leaves. Every cycle uses at
least two edges outside this forest; deleting it forces at least |B| singleton
pieces. The same repair argument gives 2*k+|B|<=2*h. Twice the former plus the
latter gives the displayed factor-six inequality.

This is only ADDITIVE in supported vertex count. It does not bound k by n and
does not prove a fixed relative boost. Conversely, the checked pointwise lemma
`relative_boost_of_support_bound` says a hypothesis k<=C*|support G| implies
(6C+1)*k<=6C*h. This makes the relative-boost target no easier merely by restating it.

PENDING modules, not yet verified at this checkpoint:
- MinimalSingletons.lean: intended |support G|+6<=8*singletonCount for every
  optimal decomposition of a nonempty GLOBAL-minimal graph, and the stronger
  |support(cycle union)|+6<=6*singletonCount. These concern vertices, NOT a
  fixed fraction of the total number of pieces.
- RelativeHullCriterion.lean: intended equivalence of original asymptotic
  proposition with existence of fixed natural t such that every even G obeys
  (t+1)*number G <= t*value G. Neither side is claimed unconditionally.
They are queued in /tmp/check_chain_sequence.sh, wrapper
/tmp/singleton-relative-wrapper.log; per-module /tmp/MODULE-check.log/.exit.
Check these before reporting them as proved.

### Parameterized chain/ring contraction analysis — partly checked

New VERIFIED arithmetic-only module ChainRingArithmetic.lean, current olean:
/tmp/chain-ring-arithmetic-check.log and .exit=0; axioms propext and Quot.sound.
It proves the packing-cost arithmetic for arbitrary b=6q>=6, including
`ring_excess_bound` and `chain_excess_bound`. It does NOT transport the packing
to arbitrary-size graphs.

External deterministic witness generator /tmp/chain_ring_general.py extends
old b=6 construction to arbitrary b divisible by six. Complete tests:
- b=12: 2197 cases per Boolean ring value, max cost-minus-forest-rank 6(chain),
  4(ring). /tmp/chain-ring-general-12.log; explicit witnesses also saved in
  /tmp/chain-ring-general-12.json.
- b=24: 15625 cases per Boolean, max excess18(chain),12(ring).
  /tmp/chain-ring-general-24.log (no saved JSON for this larger run).
These are external verifications, NOT Lean graph theorems.

Mathematical parameterized argument (generic Lean graph transport NOT DONE):
Use three K_(3,b) blocks with hub triples {0,4,1},{1,5,2},{2,6,3}, close0--3,
and transfer0<-3. There are3b+7 vertices. The source lower proof generalizes:
a piece containing the closing edge removes <=4 edges per block, leaving all
b leaf degrees odd. The degree/parity lower bound gives >=4b/3 pieces per
residual block, hence source number>=4b+1. Without the closing edge the base
hull is <=4b. The ring target hull is <=11b/3+2. Thus a globally minimal source
maximizer retaining the closing edge loses at least b/3-1 under transfer.
The closing edge has no common neighbors; the transferred sender is a leaf.
Ordinary simple contraction removes that leaf edge, giving an expected hull
loss at least b/3. Therefore the construction mathematically also obstructs
ANY fixed additive loss bound for ALL minimal-core adjacent contractions,
not just loss0. Do NOT call this arbitrary-b statement kernel-verified.

Packing arithmetic: localExcess(a)=2 if a=1, otherwise ceil(a/3), from C4/C6
packings of K_(3,a). For active counts a_i<=b in the ring, let m=min a_i and
use t=ceil(m/2) global cycles. Each uses one or two leaves per row. Consume
all m in a minimum row and choose the other consumptions in[t,2t], avoiding
one leftover leaf. Each other row has remaining localExcess <=ceil((b-2t)/3).
For b=6q, t+2*ceil((b-2t)/3)<=4q+1. The all-positive active ring has hub rank5;
one/two active rows have hub rank2/4. Thus cost <= contained forest rank+
(4q-4). The chain analog has excess <=6q-6. Bridge restoration in a minimal
host subgraph would extend these bounds to the whole host, exactly as in b=6.
No amplification to a superlinear family follows: source count remains linear
in its order.

### Build status at this checkpoint
Main chain certificate batch378169 progressed through81;82 was running when
SIGSTOP-paused by the singleton/relative sequence. It resumes automatically.
Finisher382040 waits for97, then groups and HullBounds. Additional watcher
387448 (/tmp/finish_chain_ring_obstruction.sh) waits for HullBounds exit0 and
then compiles ChainRingCompressionObstruction. Watcher log:
/tmp/chain-ring-obstruction-finish.log. Check actual logs for current state.
Spec unchanged with original sorry; no settlement or completed submission.

### Singleton consequences now VERIFIED
MinimalSingletons.lean PASSED, /tmp/MinimalSingletons-check.log and .exit=0,
current olean. Its principal audits use only the permitted three axioms.
- `proper_hull_lt` for a proper subgraph of a globally minimal graph.
- `even_support_gap`: 6*number E+|support E|+6 <=6*number G for proper even E.
- `minimum_split`: an optimal decomposition splits exactly into its even cycle
  union and singleton forest union, with additive minimum counts.
- `singleton_count_supported`: |support G|+6 <=8*singletonCount in every
  optimum of nonempty globally minimal G.
- `singleton_count_cycle_support`: |support(cycle union)|+6 <=6*singletonCount.
Again these are fractions of VERTEX count, not of decomposition piece count.
RelativeHullCriterion's first attempt FAILED with a whnf/kernel timeout in the
support-restriction lemma. It has been rewritten with an explicit subtype
Fintype and direct lifting of the induced decomposition. A recheck is pending
in /tmp/relative-hull-wrapper.log and /tmp/RelativeHullCriterion-check.*.
Do not use a failed recovery declaration/axiom audit as a proof.

### Relative criterion now VERIFIED
RelativeHullCriterion.lean PASSED, current olean,
/tmp/RelativeHullCriterion-check.log and .exit=0. The final iff audit uses only
propext, Classical.choice, Quot.sound. Its `asymptotic_iff_relative_hull_boost`
proves the original Work-version proposition equivalent to
  exists t : Nat, forall even G, (t+1)*number G <= t*EdgeHull.value G.
Forward direction restricts a uniform bound to the support and applies the
new support boost; t=6*ceil(C). Reverse direction takes a global-minimal hull
maximizer, splits its optimum into an even union and <=n singleton edges,
and obtains number G<=(t+1)*n. This is an EQUIVALENCE ONLY, not a settlement.

The kernel timeout was avoided by explicitly setting the subtype Fintype and
lifting the induced decomposition directly via
`Vertex.lift_decomposition_induce_support`; do not use the earlier failed
`number_induce_support` proof/recovery declaration. ProbeRelative is scratch,
failed/irrelevant, and is not imported by any verified module.
Main certificate batch last confirmed through87,88 running; all passed so far.

## Chain/ring compression obstruction COMPLETED — original STILL UNSOLVED

All98 certificate parts0..97 PASSED (686 explicit finite certificates), all14
ChainRingCertificateGroup{0,1}_{0..6} aggregation modules PASSED, and both final
modules now PASSED with current oleans:
- ChainRingHullBounds.lean, /tmp/chain-ring-hull-bounds-check.log/.exit=0.
  base_hull_le_twenty_four and target_hull_le_twenty_four are VERIFIED.
- ChainRingCompressionObstruction.lean,
  /tmp/chain-ring-compression-obstruction-check.log/.exit=0.
  minimal_compression_obstruction and not_minimal_adjacent_compression VERIFIED.
All final audits use only propext, Classical.choice, Quot.sound.
The small assembly file passed without any substantive changes from the
previous draft (the temporary hm.1 edit was reverted before checking).

The checked counterexample is an existential globally minimal R<=source on25
vertices. Its number is>=25, it retains edge0--3, and the hull of transfer0<-3
is<=24. This conclusively refutes the auxiliary universal adjacent-compression
rule even on GLOBAL-minimal graphs. It is NOT a disproof of Erdős184.
The arbitrary-b unbounded-loss construction is still only mathematical/external
plus verified arithmetic; do not upgrade its graph transport to checked status.

All background Lean/check/batch/watcher jobs have completed. Remaining process
entries named check_chain_* are zombies only, not active computations. No
pending build needs resuming. The old helper scripts target completed parent
378169 and should not be treated as an active batch controller.

Original Spec is STILL UNCHANGED with its original sorry. SHA256:
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No complete proof/disproof of the original proposition was obtained or submitted.
Last budget check:66h47m used,29h12m remaining; $671.44 used,$328.56 remaining.
New verified general results from this continuation are StarDeletion,
StarHullBoost, MinimalSingletons, RelativeHullCriterion, ChainRingArithmetic.
See their entries above for precise scope and logs. The relative criterion is
an equivalence, not a proof of the conjecture. The singleton bound is in vertex
count, not a fixed fraction of the optimum piece count. No new mathematical
bridge closing the remaining uniform O(n) upper bound was found.

## Exact edge-deletion identity VERIFIED — 2026-08-29 13:12 UTC

Original Spec STILL UNSOLVED and unchanged. New module:
`Submission/ExactEdgeDeletion.lean` (237 lines), current olean, clean build:
`/tmp/exact-edge-deletion-check.log`, `.exit=0`.
All four principal printed axiom audits contain only propext,
Classical.choice, Quot.sound. No sorry, debug IO, or new axiom in the module.

Namespace `Erdos184Work.ExactEdgeDeletion`:
- `cycle_upper_bound`: for ANY graph G and simple cycle p containing edge ab,
  number(G-ab)+1 <= number(G-p)+p.length.
- `attaining_cycle`: for even G and actual edge ab, there is a simple cycle
  p containing ab with equality in the preceding bound.
Together these prove the mathematical formula
  kappa(G-e) = min_{simple cycles C containing e}(kappa(G-C)+|C|-1).
The Lean formulation uses a universal bound plus an attaining witness,
not a newly defined minimum or girth function.
- `shortest_attaining_cycle`: if G is cycle-critical, the attaining cycle is
  shortest among cycles CONTAINING THE SPECIFIED EDGE and
  number(G-e)+2 = number(G)+p.length.
- `shortest_cycle_formula`: every edge-local shortest cycle satisfies that
  identity under evenness and CycleCritical.
- `even_minimal_shortest_cycle_formula`: same under EvenMinimal, using its
  already-verified implication to CycleCritical.

Proof of attainment: split an optimal decomposition of G-e into its cycle
union K and singleton forest F. Restore e to F. The result T=F+e is even,
and T-F has exactly one edge. The feedback-edge decomposition bound says T
has at most one cycle piece; it is nonempty, hence exactly one cycle p.
K=G-p and |p|=|F|+1 give the equality by optimal-subfamily additivity.

IMPORTANT: this does not strengthen CycleCritical into EvenMinimal, does not
establish hereditary minimality or arbitrary rigidity, and gives NO uniform
linear bound. The edge-local shortest cycle must not be confused with girth
of the entire graph. No new bridge to the original O(n) assertion was found.

Elaboration lesson: an initial proof defined the cycle-only subfamily property
and applied cycle_subfamily_even; this triggered a huge whnf/instance reduction.
The working proof avoids that bottleneck and uses edgePieces_degree_parity,
degree_sdiff_add, and Vertex.degree_sup_inf exactly as StarDeletion does.
Final full check takes about 7.6 seconds. All temporary IO marker tactics and
profiling options were removed. An unused scratch ProbeDeletion remains;
it contains only an independent upper-bound check, not an original settlement.

No background jobs remain. Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
Budget at latest check:67h18m42s used,28h41m18s remaining; $321.80 remaining.
No complete proof/disproof of Erdős184 was obtained or submitted.

## Further structural reassessment — original STILL UNSOLVED

No new Lean theorem or original settlement in this continuation. The general
minimal-even heredity, bounded-degree, square accessibility, and selective
compression steps remain unproved. The exact deletion identity does not
supply those implications.

A specific proposed necessary condition was checked and rejected: even-degree
vertices of a globally minimal graph need NOT be independent, even when only
non-bridge edges are considered. Exact diagnostic (NOT Lean-verified):
`/tmp/check_even_even_critical.py`, `/tmp/check-even-even-critical.log`.
It reuses `/tmp/edgecritical-values8.pickle` and recursively computes proper
hulls to distinguish global minimality from mere single-edge criticality.
Among 481 stored edge-critical types, 79 are globally minimal; three of those
have an even-even non-bridge edge. Simplest is graph6 `G?@zz{`, K3 join I4
plus one isolated vertex, number7, 15 edges. The clique vertices all have
degree6 and their three edges are non-bridges. The other two examples attach
one pendant edge to this graph (to a clique or independent-side vertex).
This is NOT an original-conjecture counterexample.

Diagnostic correction: the initial script used Sage G.bridges on disconnected
graphs and incorrectly included some forest edges in the non-bridge list.
It was corrected to test the connected-component count before/after each
edge deletion. ONLY the final overwritten log with counts143(edge-critical)
and3(global-minimal) is the corrected output. No Lean proof uses this data.

No jobs remain running. Spec is unchanged with its original sorry and SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No proof/disproof of Erdős184 has been obtained or submitted.

## Even-minimal hull upper gap VERIFIED — 2026-08-29 13:30 UTC

Original Spec remains UNSOLVED. New `Submission/EvenCoreHullGap.lean` (71 lines)
has a current olean and successful check:
`/tmp/even-core-hull-gap-check.log`, `.exit=0`. All four principal axiom audits
contain only propext, Classical.choice, Quot.sound.

Namespace `Erdos184Work.EvenCoreHullGap`:
- `proper_subgraph_bound`: EvenMinimal G and proper R<=G imply
    number R + 2 <= number G + Fintype.card V.
  Split a minimum decomposition of R into even cycle union E and singleton
  forest. Minimality gives number E <= number G-1; the forest has <=n-1 edges.
- `hull_le_number_add_order_sub_two`:
    value G <= number G + (Fintype.card V - 2)
  whenever EvenMinimal G. This actually does not need evenness of G separately.
- `number_bound_of_relative_gain`: if also
    (t+1)*number G <= t*value G,
  then number G <= t*(Fintype.card V-2).
- `gap_sandwich`: for even, even-minimal G,
    |support G| <=6*(value G-number G),
    value G-number G <=n-2.

These are NOT uniform decomposition bounds. They show that the proposed fixed
relative hull boost on minimal even cores already entails the missing linear
bound on those cores; the earlier additive matching/star repair inequalities
cannot simply be promoted to a proportional increase.

The remaining all-odd simple-path theorem / nested terminal route was
reconsidered. No arbitrary-degree path absorption proof was obtained. Existing
SubcubicOddPaths remains restricted to degree<=3. Splitting high-degree vertices
into subcubic gadgets does NOT automatically give simple paths after merging:
paths can revisit the merged vertex. No contraction/merging lemma was assumed.
Even a terminal bound would not repair the refuted universal adjacent-compression
hypothesis; a valid selective compression argument is still missing.

No jobs remain. Spec unchanged with original sorry and SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
Latest resource check:67h33m33s used,28h26m27s remaining; $318.92 remaining.
No original proof/disproof was obtained or submitted.

## Path-absorption reassessment — no new theorem

The all-odd arbitrary-degree simple-path absorption step remains unproved in
this workspace. Re-read the existing TwoPathCycleAbsorption,
EndpointPathMaximality, EndpointPathReversal, and SubcubicOddPaths proofs.
The exact obstruction to reusing the subcubic argument is still present:
on an unused cycle, the covered degree need not be one, endpoint paths can
meet that cycle internally, and two endpoint paths can overlap away from it.
Thus neither of the two checked absorption moves is automatically applicable.
No many-path exchange, general path-partition theorem, or terminal bound was
obtained in this continuation. Orientation or subcubic-splitting heuristics
were not promoted to theorems; directed trails or merged paths can repeat
vertices. No new external computation or background job was started.

Original Spec remains unchanged with its sorry, and no original settlement
has been submitted. The newest checked general auxiliary module is still
EvenCoreHullGap, not an arbitrary-degree path-absorption result.

## Square deletion with re-extraction — remaining gap identified

Original remains UNSOLVED; no new Lean theorem in this continuation.
Investigated bypassing SquareAccessible by deleting a square and extracting an
even-minimal subgraph of its cofactor with the same number. This extraction is
available, but the selected squares are NOT thereby proved to be an optimal
family in their union. The SquarePieces counting bound requires that
optimality (or an adequate replacement), which is still missing.

A mathematical obstruction to weakening the INITIAL hypothesis to CycleCritical:
start with the checked doubled-Petersen example, number5. Choose any base
5-cycle and a base edge e on it. Delete the doubled pair at e (an expanded
square). The cofactor has number4. It contains the doubled four-edge path
formed by the other edges of the chosen 5-cycle; this is a rigid minimal core
of number4, since a forest base admits only doubled-pair circuits. Extract that
core, then delete its four pair squares successively (all subsequent cofactors
are rigid minimal cores). The five selected squares together are the doubled
5-cycle, whose minimum is TWO, not five: take its two global cycles using the
two copies consistently. In the simple expansion these have length10 each,
whereas the five selected local squares have length4 each. Thus even this
re-extraction chain, with all later cores minimal, need not yield an optimal
selected family when the initial graph is only CycleCritical.

The general doubled-Petersen criticality/number result is already Lean-checked;
the particular five-cycle chain observation was NOT newly formalized. It is
not a counterexample to the version starting from EvenMinimal, and is not a
disproof of Erdős184. No inference of full heredity, square accessibility, or
selected-family optimality has been made. No new jobs are running; Spec is
unchanged with its original sorry. No original settlement was submitted.

## Contraction reassessment — previously refuted route recognized

No new theorem. The contemplated uniform-loss contraction rule for the EVEN
hull was already refuted by TripleBundlePort.unbounded_contraction_hull_loss.
Its code-level assertion is verified, with a rigid minimal source; the simple
graph realization and exact graph transport remain as described in the older
entry. No uniform contraction law was assumed, and no suitable existential
edge-selection law was obtained. Added RouteStatus.md as a concise index to
avoid retrying already-refuted universal implications. Original remains
unsolved, Spec unchanged, no jobs or settlement submission.

## Fractional/minimal-core rounding reassessment — no new theorem

Revisited TightDual, the checked fractional existence/dual bounds, and the
recorded R10 and even-ring gap examples. No bounded rounding theorem for
arbitrary even-minimal graphical cores was established. Exact duality remains
an explicit hypothesis that would force rigidity; it is not a consequence of
minimality in the available proofs. Pure multiplicative rounding for arbitrary
even graphs is already refuted by the checked fixed-fractional-cost family.
Neither bounded multiplicative rounding ON CORES nor additive O(n) rounding
has been proved or disproved here.

Potential parity/XOR decompositions of a multiple cycle cover cannot be assumed
to yield an edge-disjoint partition with the same number of cycles. Likewise,
regular-matroid/TU heuristics do not supply exactness: the recorded R10 examples
already obstruct that stronger assertion outside graphs. No such shortcut was
used in Lean. No new source theorem or background job in this continuation;
Spec unchanged and original Erdős184 still unsolved. No settlement submitted.

## Vertex-splitting reassessment — original still unresolved

No new Lean theorem or settlement in this continuation. Rechecked the earlier
Petersen-line-graph diagnostic: all its simple nonadjacent-neighbor smoothings
lower the optimum from three to two. This refutes an unrestricted
optimum-preserving smoothing rule, but not a rule restricted to EvenMinimal
cores. Full vertex splitting, or a suitably chosen split with bounded total
loss, remains unproved. One must separately handle repeated visits to the
split vertex when lifting cycles and parallel shortcut edges; suppressing
these issues is not a valid reduction to simple graphs.

The nested-terminal/all-odd-path route was also reconsidered. It still has
TWO independent missing steps: arbitrary-degree simple-path absorption (or
another terminal bound), and a valid selective compression theorem. Neither
was established. No new computation or background job was started.

Spec.lean is unchanged with its original sorry. No proof or disproof of the
original proposition was obtained or submitted.

## Clean endpoint-cycle absorption VERIFIED — original still unresolved

Three new checked modules (653 lines total), each with a current olean:

1. FourSpokeCycleAbsorption.lean (200 lines), importing EndpointPathMaximality.
   Namespace OddPaths.Absorption: four_spoke_paths, absorb_four_spokes,
   no_four_spokes_in_maximal, intersecting_paths_exchange. These construct a
   four-spoke exchange under explicit rim-separation and clean-support
   hypotheses. The last extracts the arms from two actual paths having a
   unique interior intersection. This was an intermediate local move.

2. CleanEndpointCycleAbsorption.lean (266 lines), importing
   EndpointPathMaximality and RigidSwitching. The stronger main theorem is
   OddPaths.Absorption.absorb_clean_cycle_ended:
   TWO simple paths with FOUR distinct endpoints on a simple cycle can absorb
   that cycle into TWO simple paths with the SAME endpoint multiset, provided
   each old path meets the cycle only at its endpoints. Their intersections
   OUTSIDE the cycle are COMPLETELY UNRESTRICTED. Edge lists are related by
   an exact permutation. No degree bound is assumed. All cyclic orders are
   covered, not just alternating ones.
   Proof: split the cycle between the first path's endpoints. If the second
   path's endpoints lie on opposite arcs, extend both ends of each old path
   using appropriate rim segments. If they lie on the same arc, orient them
   in order and extend each old path with one complementary rim path.
   Each new path uses only ONE old path, so outside intersections are harmless.

3. CleanCycleMaximality.lean (187 lines), importing the preceding stronger
   module and EndpointPathReversal. Defines CleanOn, proves transport under
   list permutation and reversal, and gives clean-preserving endpoint selection.
   Main results in OddPaths:
   - Maximal.no_clean_unused_cycle
   - Maximal.unused_cycle_internal_contact
   Thus ANY unused simple cycle of a maximal admissible endpoint-path packing
   meets SOME packed path at a genuinely INTERNAL vertex. Outside-cycle
   intersections alone cannot block absorption. The proof first shows that,
   under CleanOn, a path with one endpoint on the cycle has its other endpoint
   there too, using the earlier clean absorption move. Then the new two-clean-
   cycle-ended-path theorem contradicts maximality.

Logs/exit files, all exit 0 and all printed axiom audits limited to propext,
Classical.choice, Quot.sound:
  /tmp/four-spoke-cycle-absorption-check.{log,exit}
  /tmp/clean-endpoint-cycle-absorption-check.{log,exit}
  /tmp/clean-cycle-maximality-check.{log,exit}
No sorry, new axioms, or native-computation tactics occur in these sources.

IMPORTANT UPDATE TO EARLIER PATH-GAP NOTES: intersections of cycle-ended paths
outside the unused cycle are NO LONGER an obstacle when those paths are clean
on the cycle. The remaining general absorption/normalization problem is to
handle INTERNAL contacts with unused cycles. Nothing here proves those
contacts absent or removable at arbitrary degree. The all-odd arbitrary-degree
simple-path theorem, terminal linear bound, and selective compression step
remain unproved. These auxiliary results do NOT settle Erdős184.

Spec.lean is unchanged with its original sorry and SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No complete proof/disproof submitted and no jobs remain running.
Latest resource check: 68h28m58s used /27h31m02s left; $308.35 left.

## Endpoint escape counting VERIFIED — original still unresolved

New `Submission/EndpointEscape.lean`, importing SubcubicOddPaths, has a current
olean and an exit-zero check at /tmp/endpoint-escape-check.{log,exit}. Both
principal axiom audits contain only propext, Classical.choice, Quot.sound.

Namespace OddPaths:
- Piece.degree_add_endpoint_count and covered_degree_add_endpoint_count give
  the exact identity
    degree(coveredGraph L,v) + count(endpoints L,v)
      = 2 * number of packed paths containing v.
- touchingPaths / touchingEndpoints record paths through v and their endpoints.
- For Admissible L, the touching-endpoint set has size coveredDegree(v)+1 and
  contains v. Simplicity therefore bounds the number of graph neighbors in
  that set by coveredDegree(v).
- Admissible.residual_degree_le_escaping_neighbors:
    degree(G minus coveredGraph L,v)
      <= |neighbors_G(v) minus touchingEndpoints(L,v)|.
- Admissible.endpoint_path_avoids_of_not_touching supplies the endpoint path
  of every vertex outside that endpoint set; it avoids v.
- Admissible.two_escaping_neighbors_on_unused_cycle gives TWO distinct
  neighbors of any vertex v on an unused cycle, each being an endpoint of a
  packed path which avoids v. These neighbors may be the two endpoints of
  the SAME path. No claim that their incident edges are unused is made.

This is only a counting/selection constraint. A valid multi-path exchange
which absorbs internal contacts remains missing. A proposed finite fan based
on the neighbor toward each endpoint along its path was considered, but no
branch-map transport or terminating augmentation was proved. Do not infer
absorption merely from the existence of the two escaping neighbors.

No arbitrary-degree all-odd path theorem, nested terminal bound, selective
compression theorem, or original conjecture settlement was obtained.
Spec.lean remains unchanged with its sorry. No jobs are running and no complete
proof/disproof was submitted. ProbeEndpointEscape.lean is only a development
probe and contains failed identifier checks; it is not a verified module.

## Endpoint rotations and actual branch fans VERIFIED — latest continuation

Original Spec STILL UNSOLVED, unchanged, with original sorry and SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No proof/disproof of the original conjecture was obtained or submitted.

Four new checked modules, all with current oleans and only the permitted three
axioms in their principal audits:

1. `EndpointRotation.lean` (71 lines; imports EndpointEscape)
   Namespace `Erdos184Work.OddPaths.Rotation`.
   `split_before`, `support_perm`, `isPath`, `edge_perm`, `exists_rotation`.
   For a simple path from a to b passing through v, with edge av, reverse the
   prefix before the predecessor w of v, replace wv by av, and get a simple
   path from w to b with EXACTLY THE SAME vertex set.  The edge identity is
     new.edges ++ [wv] ~ old.edges ++ [av].
   No unused-edge hypothesis is needed for this local identity.
   `/tmp/endpoint-rotation-check.log`, `.exit=0`.

2. `EndpointBranches.lean` (118 lines; imports EndpointRotation)
   Namespace `Erdos184Work.OddPaths`.
   `edge_owner_unique`, `dart_ne_symm_in_trail`, `Branch`, `Branch.covered`,
   `Branch.endpoint_unique`, `exists_branch`, `branchMap`, `branchMap_spec`,
   `branchMap_injective`, `Admissible.branchMap_bijective`.
   `Branch L v a w` records the ACTUAL incident branch towards endpoint a:
   for a path oriented src->dst, incoming dart wv corresponds to src and
   outgoing dart vw to dst.  Opposite darts cannot coexist in a trail.
   The map from touching endpoints other than v to covered neighbors of v
   is a bijection.  This closes the branch-bijection gap noted previously.
   `/tmp/endpoint-branches-check.log`, `.exit=0`.

3. `PartialInjectionFan.lean` (99 lines; imports EndpointBranches)
   Namespace `Erdos184Work.PartialInjectionFan`.
   `exists_exit`, `first_exit_injective`, `exists_first_exit`,
   `meeting_implies_same_start`.
   An injective partial map on a finite set S, started outside its image,
   exits S after at most |S| steps.  The entire sequence, including its
   terminal point, is injective.  Fans from different starts outside the
   image cannot meet.  The exit proof uses the finite reachable set: an
   injective self-map there would be surjective, contradicting the start's
   absence from the original image.
   `/tmp/partial-injection-fan-check.log`, `.exit=0`.

4. `EndpointFans.lean` (99 lines; imports PartialInjectionFan)
   Namespace `Erdos184Work.OddPaths`.
   `fanStep`, `fanStep_branch`, `fanStep_injective`,
   `Admissible.fanDomain_card`, `Admissible.fanStep_image`,
   `Admissible.exists_endpoint_fan`, `Admissible.endpoint_fans_disjoint`.
   Every unused incident edge vx begins an actual branch fan at v.  All fan
   vertices are neighbors of v.  The terminal vertex is the endpoint of a
   packed path avoiding v.  The fan length is at most the covered degree of
   v.  Distinct unused neighbors give disjoint fans, including their ends.
   `/tmp/endpoint-fans-check.log`, `.exit=0`.

IMPORTANT LIMITATIONS:
- The general simultaneous rotation/reassembly of an entire fan has NOT been
  formalized.  The local rotation and the actual branch fan are checked
  separately.  Their combination must still preserve other branches and
  track duplicated/missing endpoints during the rotation sequence.
- Two terminal endpoints can belong to the SAME path.  Distinct terminal
  paths can intersect outside the center.  Fan disjointness concerns the
  sequence of neighboring endpoints, NOT their packed path supports.
- No well-founded cycle-absorption sequence has been proved.  In particular,
  the arbitrary-degree all-odd path theorem is still missing.
- Even that theorem would not repair the independent selective-compression
  gap in the original route.  No original O(n) bound follows from these fans.

Mathematical observation (NOT newly Lean formalized): rotating all branches
along one fan should preserve each old path's vertex set and exchange the
initial unused edge with the terminal incident edge, replacing the initial
endpoint by the terminal endpoint in the endpoint multiset.  Two such fans
from an unused cycle would absorb it if their terminal paths were distinct
and vertex-disjoint.  Neither condition is automatic.  Joining two intersecting
paths through the center can create MULTIPLE residual cycles, not necessarily
one; a chain of two parallel branches between junctions with a new cycle at
one junction illustrates this.  Do not assume a universal one-path/one-cycle
reassembly theorem.

Development probe `ProbeEndpointFan.lean` has one failed #check
(`Function.iterate_map`); it is not a verified module and is not imported.
All four actual modules contain no sorry, axioms, native computation or debug IO.
No active compilation or other background job remains at this update.
Latest resources: $301.99 remaining; 27h02m09s remaining.

## Global-core reassessment — original still UNSOLVED

Revisited arbitrary even-minimal rigidity, a possible first-bad binary-core
reduction to optimum three, exact-dual/unit-cycle certificates, global extremal
compression, and the weaker core edge-excess target.  No new implication closing
any of these gaps was established.  No new Lean theorem is claimed in this
continuation, and no external graph search or background job was launched.

Important correction to keep explicit: the original assertion is O(n), NOT an
n-piece bound.  The split-graph constructions already in Work give more than n
pieces for sufficiently large independent sides.  Thus a compression fallback
of the form max(n, target hull) must not be treated as a plausible sufficient
rule without separately checking its terminal bound.  A larger fixed linear
fallback remains unproved, not supplied by the chain/ring obstruction.

The binary first-bad-core reduction remains unproved.  The nongraphic examples
of higher-optimum nonrigid cores containing optimum-three bad cores are only
finite evidence.  The verified graphical optimum<=3 rigidity theorem cannot
be promoted to arbitrary optimum from that evidence.  Likewise, no minimal
cofactor or bounded rigid-core-gap theorem was obtained.

No Spec modification, no original proof/disproof, and no new submission.
Spec still has SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
Latest actual verified additions remain the four endpoint rotation/branch/fan
modules described in the preceding entry.  No jobs remain running.

## Actual simultaneous fan rotation and conditional absorption VERIFIED

Original Spec remains UNSOLVED and unchanged with its original sorry.  This
continuation now closes the previously missing SIMULTANEOUS REASSEMBLY of the
branch fans, but NOT the terminating absorption or original-compression gaps.

Six new modules (753 lines total), each with a successful standalone compilation,
a current olean, and principal audits using only propext, Classical.choice,
Quot.sound:

1. `EndpointFanRotation.lean` (140 lines; imports EndpointFans)
   - `Branch.fanStep_eq`: any actual branch agrees with the selected fan map.
   - `movedEndpoint`, `markedEdge`.
   - In `OddPaths.FanRotation`: `move_arm`, `arms_inter`,
     `move_piece_through`.
   Either or BOTH endpoints of a path through v can be rotated at once.
   Each arm keeps its vertex set; hence the two arms remain internally disjoint.
   The new path is simple and has the same length and vertex set as the old.
   All changed edges and endpoints are tracked exactly.
   `/tmp/endpoint-fan-rotation-check.{log,exit}`, exit0.

2. `EndpointFamilyRotation.lean` (143 lines; imports EndpointFanRotation)
   - `endpoint_owner_unique`, `Admissible.touching_endpoint_iff`.
   - `FanRotation.PieceMove`, `exists_move_piece`, `movePiece`, `movePiece_spec`.
   - `addedStar`, `removedStar`, `list_endpoint_eq`, `list_edge_perm`.
   - `moveFamily`, `moveFamily_endpoints`, `moveFamily_edges`,
     `moveFamily_unchanged`, `moveFamily_avoiding`.
   Rotates an arbitrary eligible endpoint set in the whole family.  A path
   with neither endpoint selected is literally unchanged.  In particular,
   every original path avoiding v remains in the resulting list.
   `/tmp/endpoint-family-rotation-check.{log,exit}`, exit0.

3. `EndpointFanAccounting.lean` (136 lines; imports EndpointFamilyRotation)
   - `selected_endpoints_perm`, `endpoint_map_account`, `addedStar_perm`,
     `removedStar_perm`, `list_rotation`, `iterate_prefix_perm`,
     `cancel_fan_accounting` (plus elementary flatMap helpers).
   For a nodup eligible endpoint list A, rotation gives M with
     edges(M) ++ star(fanStep(A)) ~ edges(L) ++ star(A),
     ends(M) ++ A ~ ends(L) ++ fanStep(A).
   The iterate-prefix identity telescopes these lists at a fan's endpoints.
   `/tmp/endpoint-fan-accounting-check.{log,exit}`, exit0.

4. `TwoEndpointFanRotation.lean` (123 lines; imports EndpointFanAccounting)
   - `cancel_lists_accounting`, `fanPrefix`, `mem_fanPrefix`, `fanPrefix_nodup`.
   - `Admissible.rotate_two_endpoint_fans`.
   For distinct unused neighbors x,y of v, supplies distinct terminal endpoints
   t,z and an actual path family M such that
     edges(M) ++ [vt,vz] ~ edges(L) ++ [vx,vy],
     ends(M) ++ [x,y] ~ ends(L) ++ [t,z].
   The first list is NODUP, so M is edge-disjoint and vt,vz really are unused.
   Both t,z are outside touchingEndpoints(L,v); their endpoint paths avoid v.
   All old paths avoiding v occur unchanged in M.
   NOTE: M need NOT have distinct endpoints.  The two list identities explicitly
   track the temporary missing endpoints x,y and duplicated endpoints t,z.
   `/tmp/two-endpoint-fan-rotation-check.{log,exit}`, exit0.

5. `FanCycleAbsorption.lean` (132 lines; imports TwoEndpointFanRotation)
   - `Piece.ending_at`, `Piece.starting_at` reorient selected endpoint paths.
   - `FanAbsorption.join_endpoint_paths` joins two VERTEX-DISJOINT paths via v.
   - `FanAbsorption.no_disjoint_terminal_paths`.
   With the preceding rotation identities around an unused cycle, disjoint
   terminal paths can be joined through v and the original cycle's rim becomes
   the second new path.  Exact permutations establish a genuine admissible
   augmentation, contradicting maximality.  No endpoint-nodup assumption on M
   is smuggled in: its endpoint defect is canceled explicitly.
   `/tmp/fan-cycle-absorption-check.{log,exit}`, exit0.

6. `FanCycleMaximality.lean` (79 lines; imports FanCycleAbsorption)
   - `FanAbsorption.cycle_as_rim` cuts an arbitrary simple cycle at a vertex.
   - `Maximal.unused_cycle_escaping_paths_meet`.
   For EVERY vertex v of ANY unused simple cycle of a maximal admissible L,
   there are distinct neighbors t,z and packed endpoint paths p,q avoiding v,
   and a vertex w != v in BOTH path supports.  This is obtained from actual fan
   rotation and conditional absorption, not just endpoint counting.
   `/tmp/fan-cycle-maximality-check.{log,exit}`, exit0.

The new maximum-packing obstruction does NOT assert p != q, nor that w lies
on the unused cycle, nor that vt or vz were originally unused.  It does not
supply a strictly improving potential or terminate a many-path absorption.
The arbitrary-degree all-odd simple-path theorem remains unproved.  Even that
result would leave the independent selective-compression step for Erdos184.

All six modules are free of sorry, new axioms, native computation and debug IO.
There are a few harmless unused-variable/simp warnings.  All builds have exited;
no job remains active.  Spec SHA256 is still
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No original proof/disproof was obtained or submitted.
Latest resources: $293.67 remaining; 26h32m37s remaining.

## Single-fan clean-endpoint absorption VERIFIED — original still UNSOLVED

The unfinished OneEndpointFanRotation draft has been completely replaced.
Three modules now compile with principal axiom audits containing only propext,
Classical.choice, and Quot.sound:

- OneEndpointFanRotation.lean (80 lines):
  Admissible.rotate_endpoint_fan gives a fixed actual one-fan move M, with
  edges(M)+[vt] ~ edges(L)+[vx] and ends(M)+[x] ~ ends(L)+[t].
  The extended edge list is Nodup. Paths avoiding v are retained unchanged.
  Every original piece has a transformed member with the same support and
  with any endpoint at v unchanged. There is no explicit Nat.find in its type.
  /tmp/one-endpoint-fan-rotation-check.{log,exit}, exit 0.

- OneFanCycleAbsorption.lean (104 lines):
  FanAbsorption.extend_clean_pair extends one path along a cycle rim and
  another across the escaping terminal edge. Intersections between the two
  paths outside the rim are unrestricted. FanAbsorption.no_clean_endpoint
  proves that a maximal packing cannot have an endpoint path whose only
  contact with an unused cycle is that endpoint. The original cycle is
  genuinely added, with exact endpoints preserved.
  /tmp/one-fan-cycle-absorption-check.{log,exit}, exit 0.

- EndpointOwnedCycleContact.lean (101 lines):
  Maximal.endpoint_path_meets_unused_cycle_again handles arbitrary cycle
  roots and orientations. Maximal.clean_endpoint_path_both_ends_on_cycle
  needs cleanliness only for the specified path, not all packed paths.
  Maximal.unused_cycle_endpoint_owned_internal_contact proves an unused
  cycle has an internal contact with a packed path whose OWN endpoint lies
  on the cycle. It combines one-fan absorption with the previously checked
  two-clean-cycle-ended-path absorption.
  /tmp/endpoint-owned-cycle-contact-check.{log,exit}, exit 0.

This closes the proposed one-clean-endpoint augmentation from the previous
checkpoint. It does NOT close general cycle absorption: internally contacting
endpoint paths still require a terminating argument. The independent selective
compression / original O(n) bridge also remains unproved. No original proof or
disproof was obtained or submitted. Spec.lean remains unchanged with its sorry.
No active compilation job remains.

## Global-gap continuation after one-fan absorption — no new settlement

Reviewed SquareCoreReduction, EvenCoreHullGap, RelativeHullCriterion,
SmallCoreRigidity, TightDual, and the prior regular/binary obstructions.
No new implication proving the original uniform bound was found.

The square route still lacks minimality of a suitable square cofactor.
Deleting a square from an even-minimal graph gives optimum k-1, but extraction
of a minimal core inside that cofactor may discard additional even edges.
A sequence of selected disjoint squares therefore cannot simply be regarded
as part of an optimum decomposition of the initial graph, so the checked
square-subfamily cardinal bound cannot be applied to that sequence.

A proposed localization to the at-most-four pieces meeting a square likewise
does not transport the initial graph's minimality to their union/cofactor.
No such localization or heredity lemma was asserted. The verified optimum<=3
rigidity result has not been promoted to arbitrary optimum. Binary/regular
heuristics do not repair this: general binary bounded core rounding is already
refuted in the earlier notes, and graph-specific rounding remains unproved.

Other reconsidered but unproved ideas: bounded-density minimal cores,
vertex-splitting with bounded total lift loss, normalization of an optimal
cycle family's intersections, and a binary first-bad-core reduction to optimum
three. None was added as an assumption or a claimed theorem.

Spec remains unchanged with its original sorry. No original proof/disproof,
no new submission, and no active background job. Latest actual checked results
remain the three single-fan/endpoint-owned-contact modules above.

## Same-terminal relocation and arbitrary distinct-terminal reassembly VERIFIED

Original Spec is still UNSOLVED and unchanged. Two new modules compile with
current oleans and principal axiom audits restricted to propext,
Classical.choice, and Quot.sound:

1. SameTerminalCycleRelocation.lean (188 lines), imports FanCycleMaximality.
   - Piece.oriented_between and Piece.cycle_through_new_vertex orient a path
     by two distinct endpoints and close it through a new vertex, with exact
     edge permutation, support membership, and length = path length + 2.
   - FanRelocation.same_terminal_path handles two-fan terminals that belong
     to ONE path. Replaces that path by the original cycle rim. Returns an
     admissible family N and an unused simple cycle D, with
       edges(N) ++ edges(D) ~ edges(L) ++ edges(C),
       ends(N) ~ ends(L),
     and Nodup of the complete new edge list. D has exactly the old terminal
     path's vertices plus the center. No endpoint uniqueness is assumed of
     the intermediate fan-rotated family M; the defect is explicitly canceled.
   - FanRelocation.Maximal.relocated_cycle_not_shorter: in a maximal packing
     such a replacement necessarily has length(D) >= length(C). It is NOT
     a strict augmentation or a proved terminating operation.
   - Maximal.unused_cycle_relocation_or_distinct_contact connects the move
     directly to the actual two-fan construction. Either an actual relocation
     of this form exists, or two DISTINCT escaping endpoint paths intersect.
   Check: /tmp/same-terminal-cycle-relocation-check.{log,exit}, exit 0.

2. IntersectingTerminalExchange.lean, imports SameTerminalCycleRelocation.
   - FanRelocation.join_by_bypass joins two distinct original endpoint paths
     through the center, then uses Walk.bypass to obtain a simple path with
     the required other endpoints. No vertex-disjointness is assumed.
   - FanRelocation.distinct_terminal_exchange combines this path with the
     original unused cycle rim and the retained family. It restores EXACT
     endpoint multiplicities and proves Admissible for the new family N.
     Its edge list is a SUBSET of edges(L) ++ edges(C), not necessarily all
     those edges. The explicit quantitative bound is
       |edges(L)| + |C| <= |edges(N)| + |P| + |Q| + 1.
   - FanRelocation.Maximal.distinct_terminal_length_bound therefore proves
       |C| <= |P| + |Q| + 1
     for any such two-fan terminals in a maximal packing. If this fails, the
     checked exchange is a genuine augmentation even when P and Q intersect.
   Check: /tmp/intersecting-terminal-exchange-check.{log,exit}, exit 0.

The general intersecting case now has an actual reassembly with an explicit
loss bound. It does NOT have full absorption: bypassed edges can contain
multiple residual cycles. No strictly improving global measure or arbitrary-
degree all-odd path theorem was obtained. The independent bridge from the
path route to the original O(n) cycle-and-edge assertion also remains open.
No original proof/disproof was submitted, and no jobs remain active.

## Two-fan relocation alone has a local trap — Lean VERIFIED

Two new modules are checked; current oleans and clean principal axiom audits:

- FanRelocationTrap.lean (257 lines), imports IntersectingTerminalExchange.
  G on Fin 6 is K3 joined with an independent triple: adjacency is u!=v and
  (u<3 or v<3). all_odd is checked. Initial admissible paths are
    0-4-1-3, 1-5-2-4, 2-3-0-5,
  covering nine edges, with unused cycle 0-1-2-0. An explicit admissible full
  cover is
    0-4-1-5-2-3, 4-2-0-3-1, 5-0-1-2.
  Thus not_maximal is proved directly, without the unproved all-odd theorem.
  Every initial packed path has an internal contact with the unused triangle.

  The actual branch steps and iterates are checked. Writing v=0,1,2 cyclically,
  the fan from next(v) exits immediately at next(v); the fan from prev(v) goes
  prev(v) -> v+3 -> next(v)+3 and exits. These are opposite endpoints of the
  one path starting at next(v), of length three. all_fan_exits_same_path is
  independent of the existential lengths chosen by the fan theorem.
  outside_touching also shows the two possible escaping endpoints exactly.

  losing_relocation_exists invokes the ACTUAL generic two-fan rotation and
  same-terminal reassembly at every triangle vertex. It constructs an
  admissible N and a simple cycle D, with exact full edge/end-point accounting,
  D.length=5 and |edges(N)|=7. every_same_path_relocation_loses_two proves the
  loss for any same-path relocation satisfying the exact accounting.

  This refutes a proposed NONDECREASING-COVERAGE ALGORITHM using only the
  current two-fan relocations, even though a full cover exists. The original
  family is NOT globally maximal; this does not refute any theorem conditional
  on Maximal L, nor the original conjecture. Other exchanges can escape it.
  Log/exit: /tmp/fan-relocation-trap-check.{log,exit}, exit 0.

- RelocationMaximality.lean (36 lines), imports SameTerminalCycleRelocation.
  maximal_iff_equal_cycle_length: for an exact one-cycle relocation of a
  maximal packing to an admissible family N, N is maximal iff the two cycle
  lengths agree. strict_cycle_growth_loses_coverage records the strict loss.
  Log/exit: /tmp/relocation-maximality-check.{log,exit}, exit 0.

A possible ADDITIONAL move, not newly Lean formalized: replace initial path
0-4-1-3 by 0-2-1-3 and unused triangle 0-1-2 by 0-4-1. This exchanges two
length-two arcs and preserves nine covered edges. Thus the checked local trap
must not be oversold as an obstruction to ALL nondecreasing rearrangements.
A general two-contact path/cycle segment switch would add this missing move.
No complete termination argument was derived, and the independent original
O(n) bridge remains unproved. Spec is unchanged with its original sorry; no
settlement submitted, no active background jobs.

Technical note: concrete finite walks' IsPath decidability uses equality
transport and did not reduce with bare decide. Rewriting Walk.isPath_def
first allowed ordinary decide. For fanStep on Fin 6, its definition uses
classical DecidableEq for Finset.erase; set a local Classical.decEq instance
before splitting the conditional and applying Finset.mem_erase, rather than
assuming it is definitionally equal to Fin's computational instance.

## ARBITRARY-DEGREE ALL-ODD PATH THEOREM NOW VERIFIED

The one-endpoint-defect idea works. New checked modules:
- OccurrenceFanBranches: choose ONE owner occurrence per endpoint label;
  selected branch step is injective assuming only edge-list Nodup.
- OccurrencePieceRotation: independent arm rotations with general endpoint map.
- OccurrenceFamilyRotation: selected occurrence labels form exactly the fan
  prefix, even when surrounding endpoint labels repeat; exact accounting.
- OccurrenceFanRotation.rotate_endpoint_fan: general edge-Nodup family, exact
  one-edge/one-endpoint defect; unchanged pieces avoiding the center.
- EndpointDefectStep.edge_step: an unused edge either adds one covered edge
  moving the endpoint defect to the center, or preserves coverage and moves
  the defect to an endpoint label absent from the original family.
- EndpointDefectAbsorption.no_defect_trail / no_unused_cycle: propagate along
  the remaining unused trail. A missing-endpoint exit restores admissibility;
  otherwise the closed walk closes the defect. Both contradict maximality.
- AllOddPaths.all_odd_path_partition: every finite all-odd graph has an
  edge-disjoint simple-path partition with unique endpoints and exactly n/2
  paths. NO MAXIMUM-DEGREE RESTRICTION remains.

All principal theorem axiom checks: [propext, Classical.choice, Quot.sound].
Logs /tmp/{occurrence-fan-branches,occurrence-piece-rotation,
occurrence-family-rotation,occurrence-fan-rotation,endpoint-defect-step,
endpoint-defect-absorption,all-odd-paths}-check.log (successful latest builds).
Current oleans are in .lake/build/lib/lean/Submission.

This supersedes previous claims that the all-odd theorem remains unproved.
It does NOT settle Erdős184: the independent selective-compression / O(n)
cycle-and-edge bridge is still missing. Spec is unchanged with original sorry.
Resource check: 70h47m used,25h13m remaining;$278.55 remaining. No active jobs.

## Terminal nested class NOW BOUNDED; generalized endpoint completion VERIFIED

New checked modules after AllOddPaths:
- UniversalEvenCycles.universal_even_bound: even graph with a universal
  vertex has 2*number(G) <= |V|-1, by closing all-odd paths after vertex deletion.
- NestedEvenBound.nested_even_bound: even NestedAlongEdges graphs satisfy
  2*number(G) <= |V| (component assembly).
- PrescribedEndpointPaths.complete: any existing edge-disjoint simple-path
  family whose endpoint multiset covers every vertex and has the degree
  parities of G can be completed to an exact edge partition of G, preserving
  that entire endpoint multiset and path count. Endpoint labels need not be
  unique. Only positivity/coverage is required for the missing-endpoint exit.
- CyclePackBudget.cycle_pack_budget: cycle packing plus residual edge budget.
- CloseAvoidingPaths.Avoiding.packing_bound: closes a common-apex-avoiding path
  packing, counting uncovered edges explicitly.
- LeafPathRemoval.remove_leaf_path: all-odd family with a leaf at v; erase its
  unique endpoint path. Remaining paths all avoid v, cover endpoints except
  v and one t, and omit fewer than |V| original edges.
- AttachLeaf: singleton apex-edge attachment to an induced-type base; exact
  degree formula and all-odd result for one even exception.
- EmbeddingPathFamily: injective graph-map transport of Piece lists.
- UniversalParityBudget: after forest parity correction in the connected base,
  either close all odd-base paths directly or use the apex as a temporary leaf
  at the single even exception. The deleted leaf path is charged as single
  edges; no hidden path-to-cycle conversion is assumed.
- UniversalConnectedBase.universal_connected_base_bound: if deleting a
  universal vertex v leaves a connected graph, number(G) <= 3*(|V|-1).
- UniversalBound.universal_bound: same bound for ALL graphs with a universal
  vertex. Splits at v when the base is disconnected, using exact budget
  |A|+|B|=|V|+1. No evenness or base connectivity restriction.
- FinitePartitionBound.number_le_sum_partition: arbitrary finite edge partition
  subadditivity (not restricted to even graphs).
- NestedBound.nested_bound: every NestedAlongEdges graph satisfies
  number(G) <= 3*|V|, by the universal-vertex theorem on each component.

All principal axiom audits: propext, Classical.choice, Quot.sound only.
Latest successful logs /tmp/{universal-even-cycles,nested-even-bound,
prescribed-endpoint-paths,cycle-pack-budget,close-avoiding-paths,
leaf-path-removal,attach-leaf,embedding-path-family,universal-parity-budget,
universal-connected-base,universal-bound,finite-partition-bound,nested-bound}-check.log.
Current oleans exist for all named modules.

TECHNICAL: induced-subtype Fintype instances often differ (classical predicate
versus constructed membership). UniversalBound defines canonicalNumber using
Fintype.ofFinite and proves number_fintype_normalize. Rewriting to that named
constant, plus Nat.card, avoids arithmetic treating instance-dependent counts
as different variables. A lemma directly rewriting to @number with a canonical
instance LOOPED under simp; the opaque-to-simp named definition fixes it.

SUPERSEDES former gaps: both arbitrary-degree all-odd paths and the terminal
NestedAlongEdges linear bound are now proved. The remaining selective/global
compression step is NOT proved. Universal adjacent compression on all Minimal
G is already disproved (ChainRingCompressionObstruction), so do not invoke the
old sufficient condition as if it were available. Spec is unchanged, UNSOLVED,
with original sorry. No original settlement submission; no active jobs.

## Secondary-optimal singleton forest VERIFIED — original STILL UNSOLVED

New modules (both compile, oleans current, principal audits permitted only):
- `SingletonCycleExchange.lean`
- `OptimalSingletonForest.lean`
Logs: `/tmp/singleton-cycle-exchange-check.log`,
`/tmp/optimal-singleton-forest-check.log`.

Namespace `Erdos184Work.SingletonExchange`:
- `cycle_exchange_bound`: E even; C a simple cycle meeting E in precisely an
  edge M. Then number((E-M) union (C-M))+1 <= number(E)+|C-M|.
  Proof: choose an optimal cycle of E containing M, retain other cycles, and
  apply the acyclic-feedback-edge bound to that old cycle minus M together
  with C-M. The old cycle minus one edge is acyclic.
- `Optimal G F`: F<=G, G-F even, number(G-F)+|F|=number(G).
- `Best G F`: Optimal, and |F| minimum among all Optimal splits.
- `exists_best`: every finite graph has such an F.
- `Optimal.acyclic`: F is a forest.
- `Best.no_one_edge_cycle`: no simple cycle of G has precisely one edge outside F.
- `Best.reachable_induced`: F.Reachable a b and G.Adj a b imply F.Adj a b.
  Thus every component of this secondary-optimal singleton forest is induced.

Exchange proof for Best: if C-M<=F and M is outside F, replace F by
(F-(C-M)) union M, and replace the even part by its symmetric difference with C.
The total optimum does not increase by cycle_exchange_bound, but |F| falls by
|C-M|-1>=1, contradiction.

IMPORTANT: None of these results settles Erdős184. Spec.lean is unchanged with
its original sorry. No settlement has been submitted.

### Exact finite diagnostics (NOT Lean proofs)

`/tmp/singleton_compression.cpp` computes exact minimum count, secondary minimum
singleton count, arbitrary-edge hull, and global edge-minimality for all labeled
simple graphs of a specified order. An edge e occurs as a singleton in some
secondary-optimal decomposition iff
  number(G-e)+1=number(G), singles(G-e)+1=singles(G).
It found NO counterexample to
  number(G) <= value(transfer G u v)
for such an edge uv, even without Minimal G, on all graphs up to 8 vertices.
Logs `/tmp/singleton_compression.log` (7), `/tmp/singleton_compression8.log` (8).
This remains an UNPROVED general compression hypothesis, not a theorem.

A tempting one-private-edge shift variant is FALSE:
G=K3 join I4 (clique 0,1,2; independent 3,4,5,6) has number=7 and is Minimal;
shift edge 0-4 to 3-4 along edge 0-3. The target hull is 6.
Exact diagnostic `/tmp/one_edge_compression7.log` (not Lean-certified here).
Receiver 3 originally has degree3, sender0 degree6.

Requiring the receiver to have at least sender degree is ALSO insufficient
for a universal Minimal rule, by a structural padding argument (mathematical,
not newly Lean-formalized): attach three pendant edges at vertex3. Both source
number and target hull increase by3, Minimality is preserved, and the two
endpoint degrees are now equal6. The one-edge shift strictly increases squared
-degree potential but drops the hull. Exact exhaustive tests up to order8
miss this ten-vertex padded counterexample; their logs
`/tmp/improving_edge_compression7.log`, `/tmp/improving_edge_compression8.log`
correctly say NONE within those tested orders. Do NOT infer a universal rule.
The padded graph need not be a maximum over ALL ten-vertex graphs, so this does
not refute a rule stated only at full vertex-order global extremizers.

### New possible continuation (all substantial claims UNPROVED)

If the UNPROVED full-transfer rule on edges of Best F held, a degree-potential
maximal global extremizer would have nested neighborhoods along those F edges.
Combining nestedness with the newly proved induced-forest property forces F
components to be stars: at each F edge the lower-degree endpoint can have no
other F neighbor, since domination plus inducedness would make an F triangle.
The leaves are odd vertices of G, dominated by their F-neighbor/root.
This elementary structural consequence has not yet been written in Lean.

A possible next target is a bounded HULL deletion loss for a dominated leaf of
Best F, or for all leaves of this star forest. For example, a bound of the form
number(G)<=value(G-L)+C*|L| could allow induction. This is NOT established.
Cautions:
- A bound with actual number(G-L), rather than the hull, fails for complete
  even-order graphs: K6 has best singleton matching, but number(K6)=5 and
  number(K5)=2 (gap3 for a single dominated matching leaf).
- A bound for an arbitrary dominated vertex fails even for Minimal graphs:
  K3 join I_m has clique vertices dominated by each other, and deleting one
  has unbounded loss. Those clique-clique edges are not singleton edges in a
  secondary-optimal decomposition when m is large.
- A bounded deletion inequality for the ENTIRE hull of arbitrary host graphs
  would already imply the original conjecture on complete hosts. Do not use it
  as an easy generic fact.

No active jobs at this note. Use -M7000 for Lean builds: -M6000/-M6500 can fail
loading this dependency closure before emitting useful diagnostics. Only one
large Lean job at a time. Degree hypotheses at graph-operation lets must be
passed using explicit graph parameters AND `simpa only [← card_neighborSet_eq_degree,
← Nat.card_eq_fintype_card]`; otherwise unification can consume 1.6M heartbeats.

### Singleton-star structural consequences are now VERIFIED

`SingletonStarStructure.lean` compiles (current olean, permitted axiom audits).
It defines `NestedSingletons G F` (nestedness only along F edges) and proves:
- `Best.dominated_leaf`, `.dominated_leaf_degree`;
- `Optimal.odd_of_forest_leaf`;
- `Best.lower_endpoint_leaf` and `.no_three_edge_path`;
- `global_extremizer_nested_singletons`, conditional on the explicitly UNPROVED
  full-transfer hull inequality along Best F edges.
This does NOT provide a bound for the weaker terminal class NestedSingletons;
that class must not be confused with fully NestedAlongEdges.
Log `/tmp/singleton-star-structure-check.log`.

### New path-pairing investigation (UNPROVED; external diagnostics only)

An unrestricted fixed-pair absorption rule is FALSE even when the demand graph
is a spanning tree. Small explicit counterexample (6 vertices):
D = {01,12,03,05,34}, H = D union {24,25,45}.
Initial paths are the five D edges; the unused triangle is 245. There is no
edge partition of H into simple paths with these same five endpoint pairs.
Exact exhaustive path-cover diagnostics:
`/tmp/connected_demand_extension6.log`, `/tmp/connected_linkage_extension6.log`.
A hand obstruction: vertices1 and3 have degree2 and demand endpoint multiplicity2.
Rerouting either pair of their incident demands requires at least four extra
edges, but the whole residual has only three. Thus the four arm edges remain
single paths; the remaining 0-5 path cannot also cover the triangle at5.
Attaching dense demand/host blocks at articulation vertices shows that merely
raising endpoint multiplicities does not repair a general fixed-pair rule.
No Lean formalization of this diagnostic has been added.

A NARROWER rule relevant to cycle packing remains untested in general:
- D is a spanning tree of demanded pairs on ALL host vertices;
- every D edge is ABSENT from host H;
- H has an edge-disjoint simple path routing of D;
- the unused edges are even (equivalently degree H parity equals degree D).
Question: can that routing be extended to cover H, preserving endpoint pairs?
In the cycle setting, D consists of one marker edge in each selected cycle;
H is the original graph minus those marker edges. Full routing would close
back into one cycle per tree edge. The absence of demand edges and coverage
of ALL vertices are essential additional hypotheses not present in the
six-vertex counterexample. Subdividing that example's seed edges removes demand
edges from H, but then the new internal vertices are NOT demand vertices, so
it does not refute the narrower rule.

External exact script `/tmp/disjoint_linkage_extension.py` enumerates tree demand
shapes and host graphs in the appropriate parity class, disjoint from demand
edges; it searches all simple-path routings. Order8 found no counterexample
(373 nontrivial dense candidates after necessary degree/edge-count pruning),
log `/tmp/disjoint_linkage_extension8.log`. An order9 diagnostic has just been
launched, log `/tmp/disjoint_linkage_extension9.log`; check job before any next
heavy operation. This hypothesis remains entirely UNPROVED. Even if true, a
rainbow-spanning-tree reduction from a hypothetical smallest counterexample
would also need formalization (matroid-intersection/rainbow-tree partition
criterion). Do not claim that the all-odd theorem preserves prescribed pairs.

### Final status of this continuation

The order9 disjoint-linkage diagnostic was stopped before completing its first
(tree-demand) shape. Its partial log is NOT a positive test through order9 and
contains no settled counterexample. No active proof-development jobs remain.
The original conjecture is still UNSOLVED; Spec.lean retains the original sorry
and unchanged SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No complete proof or disproof was obtained in this continuation.

## Continuation: the disjoint-demand spanning-tree absorption shortcut is FALSE

The original Erdős184 conjecture remains UNSOLVED. Spec.lean is unchanged.
This update is a structural mathematical obstruction plus an exact external
check, NOT a newly Lean-certified theorem and NOT an original disproof.

Files:
- /tmp/disjoint_tree_gadget_obstruction.py
- /tmp/disjoint-tree-gadget-obstruction.log
- /tmp/disjoint-tree-gadget-obstruction.json

Start with the earlier six-vertex host consisting of the demand tree
D0={01,12,03,05,34} plus triangle245. Replace each of the five host tree edges
with a separate gadget, retaining the original demanded pair. Orient the
replacements (root a, external terminal b) as
  (0,1), (2,1), (0,3), (5,0), (4,3).
Each gadget has local vertices0,...,7 with local0 identified with a, seven new
vertices, and an extra host bridge local7--b. Add the seven demanded edges
of the local path0-1-2-3-4-5-6-7. Its seven host routing paths are
  0-3-1, 1-4-2, 2-5-3, 3-6-4, 4-7-5, 5-1-6, 6-2-7.
Add the host edge local0--local7, so the original demand a--b has routing
  a--local7--b.
All 16 host edges of a gadget are covered by these eight initial paths.

The resulting graph has41 vertices and83 host edges; its demand tree has40
edges. Every demand edge is absent from the host. The40 initial simple paths
are edge-disjoint, cover80 host edges, and leave exactly triangle245 unused.
All host/demand degree parities agree. The saturated vertices, with equal
host degree and demanded endpoint count, are exactly0,1,3. In any full routing
these vertices cannot occur internally on a path.

The added internal demands must remain in their own gadgets: the other
external terminal b is saturated, and leaving/returning through the sole
remaining attachment a would repeat a vertex. Original demand12 must use
its gadget bridge at1, since its alternative exit reaches saturated0;
similarly demand34 must use its gadget bridge at3. The bridges are then
unavailable to demands01 and03. Demand05 must use its own bridge at0.
Consequently none of the demanded paths can cover any edge of triangle245.
This is the same underlying forced-path obstruction as in the six-vertex
example, but now every demanded pair is a host nonedge and the demand tree
spans ALL vertices.

The script independently enumerates all simple paths after excluding saturated
internal vertices, computes the edges forced to each demand, and excludes
those edges from other demands. It terminates with all three triangle edges
having no possible owner. It checks the initial routing, tree property,
nonedge condition, degree parities and saturated set by exact arithmetic.

Therefore do NOT invoke the narrowed fixed-pair absorption hypothesis from the
previous notes. A route allowing changes to the marker tree or allowing cycles
to use multiple markers would need a genuinely different theorem; none has
been proved here. No new Lean module or original settlement was obtained.

## New checked continuation: reachability of hull maximizers and forest deletion

Original Erdős184 remains UNSOLVED. Spec.lean is unchanged with its original
sorry. No original settlement has been submitted.

Two new modules compile with current oleans and principal axiom audits using
only propext, Classical.choice, Quot.sound:

1. Submission/MaximizerReachability.lean
   Namespace Erdos184Work.EdgeHull.
   - maximizer_reachable: R<=G and number R=value G imply
     R.Reachable=G.Reachable. BridgeExtension supplies bridge-only restoration;
     any nonempty restoration would increase number beyond value G.
   - maximizer_connected.
   - exists_minimal_maximizer_all: removes the old positivity restriction by
     treating hull zero with the bottom graph.
   - exists_minimal_maximizer_reachable.
   - Minimal.cycle_cofactor_hull: a cycle cofactor of a globally minimal graph
     is hull-tight, although it need NOT itself be globally minimal.
   - Minimal.cycle_descent: for every simple cycle C of globally Minimal G,
     there exists Minimal R<=G-C with number R+1=number G and exactly the same
     reachability as G. This does NOT bound the number of descent steps.
   Log /tmp/maximizer-reachability-check.log.

2. Submission/AcyclicDeletion.lean
   Namespace Erdos184Work.AcyclicDeletion.
   - number_le_delete_forest: for even G and ANY acyclic M,
       number G <= number (G-M).
     M need not be a subgraph of G. Split an optimum of G-M into even E and
     singleton forest F. The repair G-E is even and its edges outside M are
     contained in F. The feedback-forest cycle bound gives number(G-E)<=|F|.
   - even_subgraph_le_deleted_hull: R<=G even and M acyclic imply
       number R <= EdgeHull.value (G-M).
   - incidence_forest.
   - number_le_delete_vertex, number_le_induce_compl_vertex:
       even G -> number G <= number (G.induce {v}^c).
     The residual need NOT be even, so this is NOT a zero-cost induction
     establishing a linear bound.
   Log /tmp/acyclic-deletion-check.log.

Technical: passing operation-graph degree hypotheses without explicitly
normalizing neighborSet cardinality again caused 1M-heartbeat failures.
The fix at even_feedback_decomposition is `by simpa only
[← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hNe`.
The induced-vertex corollary also needed Fintype-instance normalization;
AcyclicDeletion defines private stableNumber/number_stable rather than loading
UniversalBound only for its equivalent normalization helper.

Further mathematical consideration did not prove either the full-transfer rule
along Best singleton edges or a bounded dominated-leaf deletion loss. These
remain hypotheses, not consequences of the two new modules. In particular,
odd/even degree changes prevent iterating the forest-deletion lemma as a
cost-free deletion argument for arbitrary graphs.

No substantial build or diagnostic is running at this update.

## Continuation: parity-corrected forest deletion checked; original still UNSOLVED

`Submission/ParityForestDeletion.lean` compiles with a current olean.
Log: `/tmp/parity-forest-deletion-check.log`.
Principal axiom audits contain only propext, Classical.choice, Quot.sound.
Namespace Erdos184Work.AcyclicDeletion:
- `number_le_delete_forest_add`: if T<=G, T<=M, M is acyclic, and G-T
  has even degrees, then number(G)<=number(G-M)+Nat.card(T.edgeSet).
  Apply the even forest-deletion lemma to G-T, observe (G-T)-M=G-M,
  and restore T as singleton edges.
- `optimal_forest_extension`: the same inequality when T is the singleton
  forest of an optimal split and M is any forest extending it.
This does NOT control the correction cost over repeated deletions and does
NOT prove the original uniform O(n) estimate.

A contemplated odd-neighbor deletion shortcut is FALSE without further
hypotheses: subdivide every edge of a d-arm star once. The center has no
odd-degree neighbors. The graph is a tree with decomposition number 2d;
after deleting the center the remaining matching has number d. Thus a
bound on deletion loss solely by the number of odd neighbors plus a
universal constant is impossible, even for globally minimal trees.
This elementary obstruction has not been separately formalized in Lean.

The dominated Best-singleton leaf deletion bound and full Best-edge transfer
rule remain UNPROVED. No original proof/disproof has been obtained.
Spec.lean is unchanged, still containing its original sorry; SHA256:
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No substantial development job is running and no original settlement was submitted.

## New checked continuation: general endpoint-bounded SIMPLE-path partitions

Original Erdős184 is still UNSOLVED; Spec.lean is unchanged and retains its
original sorry. No settlement has been submitted.

Five new modules (596 lines total) compile with current oleans. Their principal
axiom audits use only propext, Classical.choice, Quot.sound:

- EndpointSupportCompletion.lean: split_piece_at, split_family_at,
  split_at_missing_endpoint, fill_endpoint_set, fill_supported_endpoints.
  A full simple-path partition can be split once at each supported vertex
  with zero endpoint occurrences. All positive multiplicities stay unchanged.
  Edge lists are preserved up to permutation. Log:
  /tmp/endpoint-support-completion-check.log.
- PruneLeafPaths.lean: transfer_family and prune_leaf_edge. Deleting a leaf
  edge from a path packing deletes exactly that edge, preserves simple paths,
  and increases endpoint multiplicity only at its neighbor, by at most one.
  Log /tmp/prune-leaf-paths-check.log.
- OptionPathProjection.lean: transports path families from G embedded on the
  some-vertices of Option V back to G. The extra isolated none-vertex cannot
  lie on a nonempty path. Log /tmp/option-path-projection-check.log.
- OptionLeafParity.lean: optionLeaf G v attaches a leaf; at an even v, this
  decreases evenCount by exactly one, including isolated vertices. Degree
  identities use Nat.card neighborSet to avoid Fintype instability.
  Log /tmp/option-leaf-parity-check.log.
- BoundedEndpointPaths.lean, namespace Erdos184Work.OddPaths:
  * bounded_endpoint_partition: a full simple-path edge partition with at most
    one endpoint at every odd vertex and at most two at every even vertex.
  * exact_endpoint_partition: one endpoint at each odd vertex, two at each
    supported even vertex, zero at each isolated vertex; path count <= |V|.
  Log /tmp/bounded-endpoint-paths-check.log.

Proof: strong induction on evenCount across vertex types. Attach a leaf to
an even vertex, apply induction, prune its leaf edge, project back to G.
The base is the checked arbitrary-degree all-odd path theorem. Finally split
paths at missing supported endpoints, and use degree parity and endpoint
counting. The Euler-tour approach considered earlier was NOT needed.
This is a PATH result. It must NOT be substituted for a cycle-and-single-edge
partition. No valid O(n)-cost path-to-cycle conversion has been obtained.

Technical: Option V's structural BEq versus the generic classical BEq caused
List.count type mismatches. In BoundedEndpointPaths, explicitly install
  letI : DecidableEq (Option W) := Classical.decEq _
  letI : BEq (Option W) := instBEqOfDecidableEq
before invoking the generic induction hypothesis and pruning lemma. This
solved the mismatch. Rewrite optionLeaf_delete in the goal before applying
prune_leaf_edge, rather than asking simp to rewrite the dependent existential.
The ProbeEndpointSplit, ProbePathPrune, ProbeLeafParity, ProbeCountNormalize
files contain failed #check probes; they are not imported or verified modules.

### New possible route, entirely UNPROVED: cycles hitting a spanning tree

Question: if G is even and T is a specified spanning tree contained in G,
does G admit a simple-cycle edge partition in which every cycle meets T?
This would imply at most |E(T)|=n-1 cycles and would suffice for the original
O(n) conjecture after parity correction. It is a stronger hypothesis, not a
consequence of the new path theorem or previous fixed-pair results.

Exact EXTERNAL diagnostic, not a Lean proof:
/tmp/tree_hitting_cycles.cpp, executable /tmp/tree_hitting_cycles.
For each unlabeled tree shape on n vertices, it tests every labeled even
supergraph containing that tree, using an exact dynamic program over the
binary cycle space. Cycles are allowed only when they meet the tree.
No counterexample on orders 2 through 8. Logs:
/tmp/tree-hitting-cycles{2,3,4,5,6,7,8}.log.
Order7: 11 tree shapes; order8: 23 tree shapes. The order8 star has no even
supergraph (its universal center has odd degree7), so that case is vacuous.
No order9 test was run. These finite checks do NOT prove the general claim.

The central obstacle persists: cutting tree edges gives paths, and joining
those paths gives closed trails, but refining trails into simple cycles can
create cycles containing no tree edge. No termination or charging argument
preventing this has been established.

Further caution: even fixed-pair absorption for an unrestricted spanning PATH
of demands is false, not just for branching demand trees. Let D be the path
0-1-2-3-4-5-6 and H=D union triangle036. Start with the six single-edge
D paths; the triangle is unused. Vertices1,2,4,5 are saturated (host degree =
demand endpoint multiplicity =2), so they cannot be internal on any full
routing. This forces demands01,23,34,56 to use their own edges. Then demands
12 and45 are forced as well, leaving triangle036 uncovered. This is elementary
mathematical reasoning, not a new Lean-certified obstruction. Here D edges ARE
host edges; this is not a counterexample to a nonedge-demand spanning-PATH
variant. The earlier nonedge-demand spanning-TREE variant already has its
separate 41-vertex obstruction. Neither observation refutes tree-HITTING
cycle decompositions, which allow cycles containing multiple marker edges.

No substantial build or diagnostic is running. Spec SHA256 remains:
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

### Latest external diagnostic: universal all-odd prescribed endpoint PAIRS

UNPROVED candidate: every all-odd simple graph with a universal vertex admits
an edge partition into simple paths with any specified perfect matching of its
vertices as endpoint pairs. This is stronger than Prescribed.complete, which
only preserves endpoint multiplicities.
/tmp/universal_prescribed_paths.cpp and its executable exhaustively checked the
32768 labeled all-odd universal graphs on 8 vertices (universal vertex 0,
matching 01,23,45,67). All passed; log /tmp/universal-prescribed-paths8.log.
Relabeling fixes the universal vertex and covers every matching. Universal degree
7 and four paths force every path to contain the universal vertex, which the
exact search uses. This finite test is NOT a proof. No general proof, structural
counterexample, or completed reduction to the original conjecture is available.
No job is running. Spec remains unchanged and UNSOLVED.

### Further continuation: two-color endpoint diagnostics (no settlement)

New UNPROVED candidate: if every vertex of G has odd degree and vertices are
colored with two colors, each color occurring evenly in each connected component,
then G has a full simple-path partition with one endpoint at every vertex and
with both endpoints of each path the same color.
This is weaker than arbitrary prescribed endpoint pairs. An initial monochromatic
packing can be obtained mathematically from a red T-join and its complement,
leaving cycles; the missing issue is colored cycle absorption with simple paths.
The current Prescribed.complete theorem does NOT preserve endpoint colors.
Exact external diagnostic /tmp/two_color_paths.cpp, using nauty graph shapes:
- order8: all 243 unlabeled all-odd graphs, 14888 admissible two-colorings;
  no failure. /tmp/two-color-paths8.log, /tmp/allodd8_masks.txt.
- order10: all 91 connected all-odd subcubic graphs, 23296 colorings;
  no failure. /tmp/two-color-subcubic10.log, /tmp/allodd_subcubic10_masks.txt.
These finite checks are not a proof. A possible connection is to a two-center
marked spanning tree, but no complete reduction or general theorem is proved.

The separate universal-vertex prescribed-pair proposal was tested on a structured
order10 family: add a universal vertex to every even graph on 9 vertices with
maximum degree <=4, and test ALL 945 perfect matchings. All 404 unlabeled base
graphs and 381780 matchings passed. Exact source and log:
/tmp/universal_prescribed_shapes.cpp, /tmp/universal-prescribed-subquartic10.log.
This extends finite evidence only; no general pairing theorem is available.

Elementary warning, not Lean formalized: arbitrary prescribed perfect matchings
fail even in all-odd simple graphs. Take a cycle and attach one pendant leaf at
each cycle vertex. Match each leaf to its own neighbor. Each corresponding
simple path is forced to be that pendant edge, so no path can cover the cycle.
Thus endpoint uniqueness alone is insufficient to preserve prescribed pairs.
(The universal-vertex hypothesis excludes this obstruction.)

Spec.lean remains unchanged and UNSOLVED. No genuine proof/disproof obtained;
no settlement submitted. No Lean or diagnostic process is running.

## New continuation: common matching with an odd spanning tree is FALSE

Original Spec is still unchanged and UNSOLVED. The following refutes another
auxiliary bridge only; it does not refute tree-hitting cycles or the conjecture.

Tempting claim: a connected all-odd simple graph H and an all-odd spanning tree T
on the same vertices, even with disjoint edge sets, have full simple-path
partitions with the SAME perfect matching of endpoints. It would allow closing
paired H and T paths, every resulting cycle meeting T. This claim is FALSE.

Structural warning: let H be a k-cycle with a pendant leaf at each vertex.
It is connected and all-odd, on 2k vertices. Its full endpoint path partitions
have at most 3^k endpoint matchings (three choices at each cubic vertex).
An all-odd subcubic tree has k-1 cubic vertices, hence 3^(k-1) endpoint matchings.
Averaging over relabelings of a fixed such tree gives expected number of common
matchings at most 3^(2k-1)/(2k-1)!!. For k=11 this is <1, already disproving the
claim if edge-disjointness is not required. This is mathematical reasoning,
not Lean-formalized. The more precise disjoint obstruction below is exact.

Small explicit DISJOINT obstruction on 12 vertices:
H = cycle 0-1-2-3-4-5-0 plus pendant edges i-(i+6), i=0,...,5.
T = {04,15,24,27,2-11,37,48,59,5-10,6-10,7-10}.
T is an odd subcubic tree (internal path 5-10-7-2-4); H is connected all-odd,
and H and T are edge-disjoint. H has 686 realizable full endpoint matchings;
T has 243. Their intersection is empty.

Exact discovery source /tmp/odd_tree_corona_small.py and certificate
/tmp/odd-tree-corona-obstruction-12.json; log
/tmp/odd-tree-corona-obstruction12.log. The source derives H matchings directly
by choosing the active cycle vertices and their two local directions, and T
matchings by propagating one unmatched endpoint along its internal caterpillar.
Independent verification /tmp/check_odd_tree_corona.py instead constructs every
T transition pairing and enumerates all simple H paths for those endpoint pairs.
It confirms zero realizable pairings. Log /tmp/check-odd-tree-corona.log.
This is an external exhaustive certificate, NOT a kernel-checked Lean theorem.

The SAME even graph G=H union T has this valid THREE-cycle tree-hitting partition:
[0,6,10,4,8,2,11,5,9,3,7,1],
[0,5,10,7,2,3,4],
[1,5,4,2].
Thus the common-matching obstruction must NOT be promoted to an obstruction to
red-tree-hitting cycles, much less to an original disproof.

For comparison, exhaustive testing had found no common-matching obstruction
on order8: all 224 connected all-odd graph shapes against all 5888 labeled odd
trees (overlap allowed), 105 possible endpoint matchings. Source and log
/tmp/common_odd_tree_paths.cpp, /tmp/common-odd-tree-paths8.log. This is another
example of finite low-order evidence missing a genuine larger obstruction.
Additional disjoint corona/caterpillar examples exist on orders14,16,18,22;
no example was found in the fixed 20000 order10 relabeling trials. None of this
settles the original. No development process is running.

## Continuation: another singleton-degree deletion shortcut is refuted

Original Spec.lean remains unchanged and UNSOLVED. No new Lean theorem or
settlement was obtained in this continuation.

The proposed separating-cycle criterion for connected nonempty even-minimal
cores remains UNPROVED. It would suffice for an even bound number(G)<=n-c:
reduce to an even-minimal core, delete a separating cycle (unit number loss),
and induct on its residual components. This is a conditional mathematical
observation only, not an established structural theorem.

A different tempting shortcut is FALSE:
  number(G) <= value(G-v) + degree_F(v)
for a best optimal singleton forest F. Exact exhaustive diagnostic
/tmp/singleton_vertex_loss.cpp computes number, secondary singleton count,
minimum singleton degree at vertex0 (both over all optima and over best optima),
and the arbitrary-edge hull for every labeled graph on seven vertices.
Log /tmp/singleton-vertex-loss7.log: 9980 failures, maximum excess two.

The larger displayed obstruction is the already known K3 join I4, with clique
{0,1,2} and independent set {3,4,5,6}. Its number is7, it is globally minimal,
and its best singleton count is4. Some best singleton forest avoids vertex0,
yet the hull after deleting0 is5. Thus even the proposed variant with an
additional constant1 fails at singleton degree0. The earlier displayed
wheel-on-five-vertices obstruction has number4, deleted hull3, and best
singleton degree0. These new diagnostic certificates are external, not Lean.

IMPORTANT SCOPE: this does NOT refute a deletion bound specifically for a
DOMINATED LEAF of a best singleton forest. Vertex0 has singleton degree0,
not1. Nor does it refute the original conjecture or tree-hitting cycles.

An attempted current-status check of erdosproblems.com/184 failed due to DNS
unavailability; no new published result was obtained from it.
Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No Lean or diagnostic process is running. No proof/disproof submitted.

## New checked component-count reduction; original still UNSOLVED

Two auxiliary modules now compile with current oleans and permitted-axiom audits:

1. Submission/SeparatingCycleReduction.lean (144 lines), namespace
   Erdos184Work.SeparatingCycleReduction. It imports Work only.
   - HasSeparatingCycle G means some simple cycle deletion STRICTLY increases
     Nat.card G.ConnectedComponent, counting isolated vertices too. This
     formulation applies also to disconnected graphs.
   - component_count_lt_of_lost_reachability: a subgraph that loses an original
     reachability relation has strictly more components.
   - separating_of_cycle_degree_two and separating_of_even_degree_two.
   - component_bound_of_separating_cores: under the EXPLICIT UNPROVED assertion
     that every nonempty even-minimal even graph has a separating cycle,
       number G + Nat.card G.ConnectedComponent <= Fintype.card V
     for every even G.
   - asymptotic_of_separating_cores: that same uniform hypothesis implies the
     exact original asymptotic proposition.
   Proof uses edge-count induction, extraction of an even-minimal core with
   unchanged number, component-count monotonicity, and the unit cycle loss.
   This avoids assuming that a cofactor is itself minimal.
   Build/audit: /tmp/separating-cycle-reduction-check.log, -M7000.

2. Submission/SmallSeparatingCores.lean (73 lines), same namespace; imports
   SeparatingCycleReduction and SmallCoreRigidity.
   - separating_of_small_core verifies the criterion for number<=3 using the
     previously checked degree-two theorem.
   - no_separating_core_number_ge_four.
   - no_separating_cycle_preserves_reachability: without any separating cycle,
     EVERY cycle deletion preserves all reachability (not only connectedness).
   - no_separating_even_degree_ge_four: all supported vertices have degree>=4.
   - obstruction_of_asymptotic_failure: a hypothetical failure of the original
     conjecture would yield a nonempty even-minimal graph with number>=4, all
     supported degrees>=4, and every cycle deletion preserving reachability.
     This is conditional; existence of such a graph is NOT asserted.
   Build/audit: /tmp/small-separating-cores-check.log. Its large import closure
   exceeded -M7000; it compiled successfully with -M8500, one Lean process only.

The universal separating-cycle hypothesis has NOT been proved or refuted.
The connected-core-only formulation discussed informally would additionally
use transport of minimality to connected components; the checked theorem uses
HasSeparatingCycle for ALL nonempty even-minimal cores directly.
No result here settles the original. Spec.lean is unchanged with its sorry,
SHA256 509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No proof/disproof submitted. No development process running at this update.

## Twin blowups: nonseparation alone does not give degree-optimal decompositions

External mathematical observation (not a Lean theorem): if B is bridgeless
with minimum degree at least3, its two-fold independent blowup G has NO cycle
whose edge deletion increases component count. Indeed, a cut contained in a
simple cycle has cut-degree <=2 at each vertex. A split twin pair has total
cut-degree 2*degree_B(v)>=6, impossible. Thus twin pairs are unsplit. Every
crossing base edge supplies a whole K2,2 subcycle of the proposed cycle; the
cycle must equal this square, making the base cut a single bridge.

The Petersen blowup diagnostic has been repaired: /tmp/twin_blowup_hamilton_decomp.py
now converts Sage EdgesView/integers to JSON-safe lists/ints. Rerun succeeded,
producing /tmp/twin-blowup-petersen-hamilton.json with three Hamilton cycles
partitioning the 20-vertex6-regular blowup. Coverage/degrees/connectivity checked
by the script. The earlier truncated JSON should no longer be used.

The stronger proposed bridge 'no separating cycle => number=Delta/2' is FALSE.
Construct a5-regular bridgeless base on32 vertices: two central vertices a,b,
and five disjoint copies of K6 minus one edge xy; attach a to x and b to y
in each copy. Its twin blowup is10-regular on64 vertices and has no separating
cycle by the preceding argument. Removing the four central twins leaves FIVE
components, so it has no Hamilton cycle. A five-cycle decomposition of a
10-regular graph would force every cycle through every vertex, hence would be
a Hamilton decomposition. Thus number>5=Delta/2. External construction and
separator checks: /tmp/twin_blowup_separator.py and /tmp/twin-blowup-separator.json.
This is NOT an even-minimal example, not a refutation of the separating-CORE
hypothesis, and not a counterexample to the original conjecture.

## Further obstruction to a path-count shortcut

Mathematical observation, not Lean-formalized: even for simple even graphs
having no separating cycle, cycle number cannot be bounded by a constant
multiple of minimum simple-path partition size. Take a chain of m copies of
K5, consecutive copies meeting in a single vertex, with distinct left/right
attachment vertices within each block. Every simple cycle stays in one block.
Each K5 needs and admits two cycles, hence the chain needs2m cycles. Deleting
any cycle keeps its K5 connected (cycle lengths3,4,5 checked directly), so the
whole chain has no separating cycle. Each K5 with specified distinct ports
u,v admits four edge-disjoint u-v simple paths: uv, u-a-b-v, u-b-c-v,
u-c-a-v, where a,b,c are the other vertices. Concatenating these four paths
blockwise covers the entire chain. For m>=2 its minimum path count is4,
by degree8 at a joint. None of these chains is even-minimal: in each K5,
two triangles sharing one vertex give a proper even subgraph with number2.
Thus this does not refute the separating-cycle hypothesis for even-minimal
cores, nor the original conjecture.

## Connected separating-core reduction and edge connectivity VERIFIED

The original conjecture is still UNSOLVED; Spec.lean unchanged. Four new
auxiliary modules compile, with current oleans and permitted-axiom audits:

1. NonseparatingEdgeConnectivity.lean (103 lines), imports only the previous
   SeparatingCycleReduction. In an even graph with no separating cycle,
   deleting ANY set of at most3 edges preserves all original reachability.
   Thus a connected such graph is4-edge-connected (Mathlib IsEdgeConnected4).
   Proof: fix a cycle partition. If the deleted set is a transversal, its
   deletion preserves reachability. Otherwise some cycle contains at least
   two of the three edges; delete the whole cycle using nonseparation, then
   delete at most one residual edge using evenness. No minimality assumed.
   Log /tmp/nonseparating-edge-connectivity.log; -M7000.

2. SpanningEvenCoreTransport.lean (93 lines), imports GraphCircuitCode and
   CircuitTransport. Adding isolated ambient vertices to an even graph
   preserves its cycle number and even-minimality (spanning_number,
   spanning_minimal_iff). Transport is through injective edge-coordinate
   maps of circuit codes; spanning_code_valid proves validity equivalence.
   Log /tmp/spanning-even-core-transport.log; -M7000.

3. ComponentSeparatingCores.lean (about150 lines), imports the above modules
   and GraphVertexSeparation. Proves component_even_minimal and
   no_separation_component. Consequently the sufficient separating-core
   hypothesis may now be restricted to CONNECTED nonempty even-minimal
   graphs: asymptotic_of_connected_separating_cores is checked. This closes
   the previously recorded component-transport gap, NOT the structural
   separating-cycle hypothesis itself.
   Log /tmp/component-separating-cores.log; -M7000.

4. ConnectedCoreObstruction.lean (about43 lines), imports ComponentSeparatingCores
   and SmallSeparatingCores. connected_obstruction_of_asymptotic_failure
   packages hypothetical original failure into a CONNECTED, nonempty,
   even-minimal graph with number>=4, no separating cycle,4-edge-connectivity,
   supported degrees>=4, and reachability preserved by every cycle deletion.
   No existence or exclusion of such a core is asserted.
   Log /tmp/connected-core-obstruction.log; -M8500.

All principal axiom prints contain only propext, Classical.choice, Quot.sound.
Technical fixes: normalize degree assumptions at operation-graph lets by
`simpa only [<- card_neighborSet_eq_degree, <- Nat.card_eq_fintype_card]`;
normalize edgeFinset instances with `[SimpleGraph.edgeFinset, <- Set.toFinite_toFinset]`.
In the dependent existential for a component use an explicit Fintype C with
Classical membership, rather than synthesizing Fintype C.supp (its decidable
membership instance differs). Only one Lean process was run at a time.

## Continuation: arbitrary parity-correction support bound VERIFIED

Submission/MinimalParityCorrection.lean now compiles with -M7000, current olean,
log /tmp/minimal-parity-correction.log. Both principal axiom audits use only
propext, Classical.choice, Quot.sound. For nonempty globally Minimal G and
T<=G such that G\\T is even, it proves:
- support(G\\T).ncard + 6 <= 6 * Nat.card T.edgeSet;
- support(G).ncard + 6 <= 8 * Nat.card T.edgeSet;
- T is nonempty.
This concerns EVERY parity correction, not just an optimal singleton forest.
It does NOT bound the decomposition number, so Spec remains UNSOLVED.

The exact external C++ parity diagnostic has completed with exit0:
/tmp/minimal-parity-forest8.log
DONE n=8 graphs=268435456 cores=564355 failures=40320 coreFailures=0 worst=1
Order7 had no failures at all (2097152 graphs). At order8, best optimal
singleton count need not be minimum parity-correction size, but none of the
failures is globally minimal. The first failure has number4, bestSingles3,
minParity2 and edges 01,02,06,07,13,15,17,24,26,34,35. Odd vertices2,3 have
parity-correcting path2-4-3. No claim of a general theorem follows from these
finite diagnostics. The restricted equality for globally minimal graphs is
still UNPROVED. No active compilation or exact calculation remains.

## New exact obstruction: fixed MATCHING completion is false even in all-odd graphs

External exact diagnostic /tmp/matching_completion.cpp, compiled executable
/tmp/matching_completion; /tmp/matching-completion8.log found a counterexample
on the sixth all-odd order8 shape (not an exhaustive completed run).
Graph edges: 05,06,07,16,27,37,47,67. Degrees are all odd. Matching demands:
05,16,23,47. Initial edge-disjoint paths are 05,16,2-7-3,47; triangle0-6-7
is unused. No full fixed-pair partition exists: leaf5 paired with its neighbor0
forces edge05 as the entire path, likewise16 and47. The remaining pair23
must use2-7-3, since both endpoints are leaves attached to7. Thus all four
paths are forced and none can cover the triangle. This refutes feasible-to-full
fixed PERFECT-MATCHING completion, not only earlier higher multiplicities.
It does NOT refute the two-color endpoint grouping claim, the universal-vertex
fixed-pair claim, or tree-HITTING cycle decompositions (the marker matching
is disconnected). No new Lean theorem here. Spec remains unchanged/UNSOLVED.

The cycle-space parity diagnostic also completed (exit0):
/tmp/core_parity_cycle_space.cpp, /tmp/catalogue-core-parity.log.
It examined 1201 catalogue entries: the168 order9 global-minimal types and
1033 entries in the old restricted double-split catalogue. No failure of
bestSingletonCount=minParityCorrection appeared. The latter catalogue is NOT
an exhaustive order12 catalogue. The diagnostic enumerates every even support
via a spanning-forest fundamental-cycle basis, computes its exact cycle number,
and minimizes cycleNumber(E)+|G-E|, secondarily |G-E|. Parity correction is
minimized independently. This is external finite evidence only. Spec unchanged.

## Best-singleton raw two-choice compression: unrestricted claim REFUTED

/tmp/best_singleton_twochoice.cpp, /tmp/best-singleton-twochoice7.log completed.
The order7 globally minimal restriction had no failure. The unrestricted test
stopped at G with edges 01,02,05,06,13,14,16,23,25,34, number4 and best singleton
count1. Edge23 is a singleton in a Best optimum. Transfer sender3 to receiver2:
target number3, joining-edge-deleted number2, but target hull6. Thus the raw
two-choice inequality fails even for a Best singleton edge. Source is NOT
globally minimal; its spanning tree already costs6>4. This does not refute
Best-edge HULL compression or the global-minimal raw two-choice variant.
The source consists of triangles025,016,134 plus edge23. The transfer folds
it into the triangle-of-three-triangles core plus a pendant edge. No new Lean
proof of this auxiliary obstruction has been added. Spec remains UNSOLVED.

## New verified two-color INITIAL packing

Submission/TwoColorInitialPacking.lean compiled with -M7000, current olean,
log /tmp/two-color-initial-packing.log. The principal audits use only propext,
Classical.choice, Quot.sound. Namespace Erdos184Work.OddPaths.TwoColor.
- Monochromatic S L means each path's two endpoints both lie in S or both outside.
- exists_initial: if G is Preconnected and all degrees odd, and |S| is even,
  there is an Admissible monochromatic path packing (each vertex endpoint once).
- ColorMaximal and exists_color_maximal maximize edge coverage within this class.
- Such a maximum has n/2 paths and an even residual.
Proof: choose a parity forest F with odd set S; partition F into paths. Extract
paths from G\\F, whose odd set is the complement of S. Map and concatenate the
families. Disjoint endpoint classes and disjoint graph edge sets give Admissible.
This does NOT prove full coverage, nor any original cycle-and-edge bound.

Completed exact external two-color test on connected order10 graphs of maximum
degree<=5: all8860 all-odd shapes,2268160 admissible colorings passed. Generator
nauty-geng -cq -d1 -D5 10 filtered1156842 graph6 strings by degree parity.
Files /tmp/filter_allodd_g6.cpp, /tmp/allodd_maxdegree5_10_masks.txt,
/tmp/two-color-maxdegree5-10.log and .exit (0). Larger-degree checks and any
general color-preserving absorption theorem are not certified by this result.

## New verified full path theorem with ONE even vertex

Submission/OneEvenPaths.lean compiles with -M7000; current olean;
/tmp/one-even-paths.log. Main theorem full_partition has only the permitted
axioms. For a finite graph G, distinguished z of even degree, and every v!=z
of odd degree, it gives a FULL simple-path edge partition, each v!=z used once
as an endpoint and z never as an endpoint, with 2*pathCount+1=|V|. No connectivity
assumption is needed. An isolated z is allowed; all other vertices are odd.

Proof: maximize edge coverage over endpoint-distinct path families with exactly
one missing endpoint, whose identity may vary. At a missing vertex, the fan
step cannot exit to any different missing vertex; hence a maximum has no unused
incident edge there, and that vertex must have even degree in the host. Unique
possible evenness forces it to be z. The unused-trail defect argument extends
with terminal alternatives t=x or t=z, both closing into an allowed family.
In the initial cycle step, relocation to a new missing endpoint x gives another
maximum, contradicting odd host degree at x. Thus the residual is acyclic; its
parity is even, so it is empty. This is NOT a cycle-and-single-edge bound for
arbitrary graphs. The generic Maximal.residual_acyclic lemma here still assumes
all other vertices odd; no hypothesis has silently been dropped.

## New verified rooted closure and almost-universal cycle bound

- Submission/CloseAdjacentEndpoints.lean (namespace RootedClosure), compiled
  /tmp/close-adjacent-endpoints.log, -M7000. packing_bound closes a path family
  avoiding v, with unique endpoints ALL ADJACENT to v, and charges leftover
  edges separately. Unlike the older interface, v need not be universal.
- Submission/AlmostUniversalEvenCycles.lean, compiled
  /tmp/almost-universal-even-cycles.log, -M7000. almost_universal_even_bound:
  for even G with v!=w, vw a nonedge, and v adjacent to every other vertex,
    2*number G <= |V|-2.
  Delete v: w is the sole even-degree vertex of the base. Apply OneEvenPaths,
  map the paths back, and close them through v using RootedClosure.

All principal axiom audits are permitted only. These are special-case results,
not a settlement. Spec.lean is unchanged with its original sorry.

## Completed external two-color checks in this continuation

/tmp/two-color-degree7-10.log and .exit (0): all21953 connected all-odd order10
shapes of maximum degree EXACTLY7 passed all5619968 colorings. Combined with
the degree<=5 run, this covers all connected all-odd order10 graphs WITHOUT a
universal vertex. Degree9/universal cases have NOT been fully checked here.
Filter source /tmp/filter_allodd_degree7_g6.cpp; nauty-geng -cq -d1 -D7 10;
9532717 input graph6 shapes filtered. /tmp/two_color_paths_progress.cpp is the
same exact solver with progress reporting.

/tmp/two-color-subcubic12.log and .exit (0): all509 connected all-odd subcubic
order12 shapes passed all521216 colorings. /tmp/two_color_graph6.cpp uses
compressed present-edge coordinates (the old complete-graph 64-bit masks would
overflow at12 vertices). Input nauty-geng -cq -d1 -D3 12 is connected, as the
solver's single component parity check assumes. No general completion theorem
follows. The full two-color path theorem and its original-conjecture bridge
remain unproved. No original proof or disproof has been submitted.

## Further continuation: unrestricted Best-leaf deletion has UNBOUNDED loss

This is a mathematical construction with exact external base checks, NOT a
new Lean theorem and NOT a disproof of Erdős184. Spec remains unchanged.

Let B=K3 join I4, clique vertices 0,1,2 and independent vertices 3,4,5,6.
An optimum with minimum singleton count has singleton forest
  F={13,14,25,26}
and cycles
  0-1-2-0, 0-3-2-4-0, 0-5-1-6-0.
Thus number(B)=7, Best singleton count=4, and degree_F(0)=0. The lower bound
7 is already checked in Work.lean; at least four singleton edges are needed
because the four odd independent vertices cannot share singleton edges.
The hull of B-0 is5. An exact independent present-edge DP additionally
checks that every immediate edge-deleted B has hull6, so B is globally
Minimal. Artifacts:
  /tmp/best_leaf_wedge_certificate.py
  /tmp/best-leaf-wedge-certificate.json
These external calculations are not Lean certificates.

Take m copies of B, identify their vertex0 to a single vertex v, and attach
one new pendant edge vz. Every simple cycle stays within one block; number
and arbitrary-edge hull add across one-vertex sums. Thus this graph G_m has
  |V|=6m+2,
  number(G_m)=7m+1,
  value(G_m-v)=5m.
The union of the displayed singleton forests and {vz} is Best: it has
4m+1 singleton edges, which is the lower bound from the 4m original odd
independent vertices and the new pendant vertex. Crucially degree_F(v)=1.
Therefore deleting a leaf OF A BEST SINGLETON FOREST can lose 2m+1 in the
hull, with no universal additive bound. The base global minimality and
one-vertex additivity also give global minimality of G_m.
This refutes unrestricted Best-leaf deletion even under global minimality.
It does NOT refute dominated Best-leaf deletion: v is not dominated by its
singleton neighbor z (z has degree1). It also does not refute a rule that
chooses some suitable leaf rather than allowing every leaf.
The family has only constant number/order ratio, so it is not an original
counterexample.

A distinct exact order8 diagnostic is running at this update:
  /tmp/best_leaf_vertex_loss.cpp
  /tmp/best-leaf-vertex-loss8.log and .exit
It distinguishes degree_F=0, degree_F=1, degree_F>=2, and domination by the
unique singleton neighbor. Its early records include loss3 at a Best leaf
(the m=1 example above) and loss2 at a dominated Best leaf (K3 join I4 with
an isolated eighth vertex). Do not report the exhaustive run as complete
until its DONE line and exit file appear.

The classified order8 run above has now COMPLETED with exit0, examining all
268435456 labeled graphs. In the degree_F classes0,1,>=2 the maxima
of number(G)-hull(G-v)-minimum_Best_degree_F(v) were2,2,1 respectively. For dominated Best leaves
the maximum loss was2. These bounded-order checks do NOT prove the dominated
Best-leaf bound. The source retains unused legacy counters in its DONE line;
the appended CLASSIFIED SUMMARY is computed from the actual record lines,
not from those unused counters. No diagnostic process remains active.
No original proof/disproof, no new Lean theorem, and no settlement submission
in this continuation. Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## New checked compression structure: TransferSingletonForest

Submission/TransferSingletonForest.lean (206 lines) compiles, with current
olean and log /tmp/transfer-singleton-forest.log. The three principal axiom
audits contain only propext, Classical.choice, Quot.sound. No sorry/admit or
new axiom occurs in this module. Only one substantial Lean job ran at a time;
-M7000 sufficed. Harmless unused-variable/section-variable warnings remain.

Namespace Compression, checked:
- transfer_reachable: an adjacent full transfer preserves the ENTIRE
  reachability relation.
- transfer_connected and transfer_tree.
- transfer_acyclic: adjacent full transfer of a forest is still a forest.
  Proof extends the forest to a spanning tree; the transferred tree stays
  connected with the same edge count, hence is a tree; use transfer_mono.

Namespace SingletonExchange, for Best G F and F.Adj u v, checked:
- Best.singleton_neighbor_private: every other F-neighbor of v is a private
  G-neighbor relative to u. Inducedness of Best components would otherwise
  give a triangle in F. The symmetric fact also holds at u.
- Best.transfer_even_remainder:
    transfer G u v \\ transfer F u v = transfer (G \\ F) u v.
- Best.transfer_split: the two transferred graphs on the right are disjoint
  and their union is transfer G u v.
- Best.transferred_sender_leaf: the transferred singleton forest has exactly
  {u} as the sender v's neighbor set.
- Best.transferred_forest: it lies in the transferred host, is acyclic, has
  the original F edge count, and degree1 at v.

IMPORTANT: transfer(G\\F) need NOT remain even; transfer can change parity
at u and v. The transferred singleton forest is NOT proved Optimal or Best
for the target. There is still NO decomposition-number or hull comparison,
so these structural transport results do not settle the original conjecture.

A proposed shortcut using JUST the parity-corrected target number is false,
even on a globally minimal tree and even with degree(receiver)>=degree(sender).
The path with edges01,03,12, transfer sender1 to receiver0, has number3 and
transfers to the three-edge star of number3. One edge is moved; removing the
joining edge01 as the parity correction leaves number2. The corrected graph
has the original degree parities, which therefore do not suffice to preserve
number. Exact external diagnostic /tmp/best_parity_transfer.cpp and
/tmp/best-parity-transfer7.log; this does not refute the two-choice comparison
or the Best-edge hull comparison. No new large diagnostic remains running.

Original Spec remains unchanged/UNSOLVED, SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No original proof/disproof or settlement submission in this continuation.

## Reassessment: exact edge deletion does not supply global minimality

No new Lean theorem or original settlement in this continuation. Revisited
ExactEdgeDeletion together with MinimalParityCorrection and the connected
nonseparating even-core reduction. The tempting inference
  EvenMinimal G => EdgeHull.Minimal (G-e)
is false. Two triangles meeting in one vertex give a simple example: G is
rigid/even-minimal with number2; deleting one edge gives number3, whereas
further deleting an edge in the other triangle gives a four-edge spanning
tree of number4. Thus the globally minimal singleton/support inequalities
cannot be applied directly to G-e merely from even-minimality of G.
The example has separating cycles and does NOT refute a statement additionally
assuming no separating cycle. No proof of that narrower statement was found.

For comparison, if G-e really is globally Minimal, deleting C-e from G-e
for any cycle C containing e is a parity correction. The already checked
correction_support_bound would then constrain its support by 8*(|C|-1)-6.
Evenness means deleting e does not remove supported vertices. This conditional
observation is mathematical reasoning here, not a newly checked Lean lemma,
and it supplies no bound without the missing global-minimality hypothesis.
Extracting a globally minimal hull maximizer R<=G-e changes its odd vertices
and singleton forest; one may not retain the shortest-path description from
the exact single-edge-deletion formula after that extraction.

Spec remains unchanged and UNSOLVED, with its original sorry. No proof or
disproof submitted. No active development or diagnostic jobs at this update.

## Further reassessment: bounded degree does not close the global gap

No new theorem or settlement in this continuation. Reviewed the maximum-family
intersection machinery and the maximum-degree-four case. In that case every
vertex belongs to at most two displayed cycles, but excluding such cores would
not by itself give the needed arbitrary-degree reduction. Indeed bounded-degree
even graphs already have a linear bound just from edge counting (at degree4,
there are at most2n edges and each cycle uses at least3). The existing triple
threshold is not a theorem reducing arbitrary even-minimal cores to degree4.
No such implication has been added or assumed. Original Spec unchanged with
its sorry; no proof/disproof submitted and no active jobs.

## Amplification reassessment: no superlinear family obtained

No new Lean theorem or original settlement. Revisited the verified fractional-
gap constructions, one-vertex/serial gluing, and degree-parity lower bounds.
The bounded-degree even-gap family has an explicit linear integral upper
bound and is not a counterexample. One-vertex sums preserve additivity but
also add order minus one, so iterating a fixed collection of components
cannot yield an unbounded number/order ratio. Reusing larger interfaces can
allow cycles to cross multiple gadgets; additivity cannot simply be retained.
No valid efficient overlapping-gadget amplification was established.
Spec remains unchanged with its sorry; no proof/disproof submitted and no
active computational jobs at this update.

## Continuation: parity gap remains; dominated edge-amalgam does not amplify

Original Spec remains unchanged and UNSOLVED. No general parity-correction,
compression, dominated-leaf, or separating-core theorem has been obtained.
In particular, global minimality does not justify subtracting a whole parity
forest's size from the number after its deletion. The existing one-cycle
critical identity cannot be iterated without additional hypotheses.

A targeted attempt to amplify the dominated Best-leaf loss-two example was
examined by hand. Take m copies of K3 join I4 and identify their edges uv,
where u is a clique vertex and v an independent vertex. In copy i name the
other clique vertices x_i,y_i and the other independent vertices a_i,b_i,c_i.
There are n=5m+2 vertices and 14m+1 edges. For m>=2 there is an explicit
partition with n-1 pieces:
- singleton edges uv and u-a_i,u-b_i,u-c_i (3m+1 in total);
- triangles x_i-y_i-c_i-x_i (m cycles);
- cycles u-x_i-a_i-y_i-v-x_(i+1)-b_(i+1)-y_(i+1)-u (m cycles), with indices
  modulo m.
The two block indices differ, so each last cycle is simple. Every edge occurs
exactly once. Thus number(G)<=5m+1=n-1. Since G is connected and cyclic, a
proper spanning tree has number n-1, and G is NOT globally Minimal for m>=2.
This explains why sharing the domination edge cannot yield the hoped-for
minimal-core amplification: mixed cycles invalidate blockwise additivity.
It neither proves nor refutes the dominated Best-leaf bound in general.

The explicit partitions were externally checked for m=2,...,20 by
/tmp/dominated_edge_amalgam_certificate.py; log:
/tmp/dominated-edge-amalgam-certificate.log. This is a direct certificate
check, NOT a Lean theorem or an exact optimality computation. No new Lean
module has been compiled in this continuation. No settlement was submitted.

## New verified inheritance rules: OptimalSingletonDeletion

Submission/OptimalSingletonDeletion.lean compiles with -M7000; current olean.
Log /tmp/optimal-singleton-deletion.log. Principal axiom audits use only
propext, Classical.choice, Quot.sound. Namespace SingletonExchange:

- Optimal.extend_even: if C<=G is even and number(G-C)+number(C)=number(G),
  every Optimal (G-C) T lifts to Optimal G T.
- Best.singleton_count_le_cofactor: consequently, every optimal singleton
  split of that cofactor has at least the singleton count of a Best split
  of G.
- Best.delete_even: if C<=G-F is even and additive inside the optimal even
  remainder, then Best G F implies Best (G-C) F. This applies to an even
  subfamily of the chosen minimum cycle decomposition, not arbitrary even C.
- Best.singleton_count_le_delete_cycle: for CycleCritical G, deleting any
  cycle gives the singleton-count comparison, even when C meets F. It does
  NOT assert that F remains optimal or even contained in the cofactor.
- Best.singleton_count_le_minimal_delete_cycle: the global Minimal corollary.

No uniform linear bound follows yet. In particular, neither global minimality
nor the singleton-count comparison has been transported through a subsequent
arbitrary hull-maximizing core extraction. Do not iterate them without a proof.
Full Best-edge transfer and dominated Best-leaf deletion remain UNPROVED.

A constant support-minimum-degree bound for globally Minimal graphs was also
considered, not proved. The saved 79 order-eight, 168 order-nine, and 1033
restricted double-split catalogue entries all have support-minimum-degree
one or three. This is only a property of those finite catalogues, not a general
theorem; it supplies no justification for the proposed structural bound.

Original Spec remains unchanged and UNSOLVED, with its original sorry. No
proof/disproof of the conjecture has been obtained or submitted.

## Continuation: hull-saturated parity support bounds VERIFIED

New file Submission/HullSaturatedParity.lean compiles with -M7000, current olean.
Log /tmp/hull-saturated-parity.log. Principal axiom audits use only propext,
Classical.choice, Quot.sound. For value(G)=number(G) and ANY parity correction
T<=G (G-T even), it proves:
- support(G-T).ncard <= 6*|E(T)|;
- support(G).ncard <= 8*|E(T)|.
The cycle-cofactor corollary uses the previously verified
Minimal.cycle_cofactor_hull in MaximizerReachability. That hull-saturation
identity is not new. The strict Minimal bounds with the additional +6 remain
stronger; the new statements weaken the graph hypothesis.

These are support bounds, not decomposition-number bounds, and do not prove
Best singleton count equals minimum parity-correction size. That equality was
reconsidered for ALL hull-saturated graphs, not just Minimal graphs; it remains
UNPROVED. The difficulty is equal-number pruning of an even subgraph: extending
an optimum by the deleted cycles costs additional pieces, so the checked
Optimal.extend_even lemma cannot be applied when its additivity hypothesis fails.

Two finite binary-matroid model checks (not Lean proofs and not evidence of a
graph-theoretic uniform bound) found no failure of the proposed hull-saturated
parity equality in any subset of five specified column configurations:
- PG(3,2), 15 columns, 32768 subsets;
- doubled Fano, 14 columns, 16384 subsets;
- AG(4,2), 16 columns, 65536 subsets;
- all weight-three rank-five columns, 10 columns, 1024 subsets;
- columns 1,...,11,16,17,18,20,24, 16 columns, 65536 subsets.
Scripts /tmp/binary_hull_parity_check.py and
/tmp/binary_hull_parity_structured.py; logs /tmp/binary-hull-parity-check.log
and /tmp/binary-hull-parity-structured.log. Both processes finished. The second
script repeats the first two checks when importing its helper. No claim of a
general binary-matroid theorem follows from these finite checks.

The two-color path route was also revisited. Existing endpoint-fan rotations
preserve endpoint multisets, not monochromatic endpoint PAIRS; hence they do
not directly prove ColorMaximal completion. Independently, monochromatic
completion alone has not been shown to imply the original linear cycle-and-edge
bound. Reassembling paths through tree markers can leave marker-free cycles;
no valid argument controlling those cycles was obtained.

Spec remains unchanged with its original sorry. No proof/disproof of the
conjecture was obtained or submitted. No active development jobs remain.

## Continuation: relative-hull route reassessed; no new settlement

Revisited whether the proposed equality between Best singleton count and the
minimum parity-correction size would close RelativeHullCriterion. No valid
implication was obtained: even if that equality holds, it does not by itself
bound the number of cycles in the even remainder by a fixed multiple of the
singleton count. Charging cycle occurrences to singleton-supported vertices
would require an additional uniform incidence/exchange theorem; no such theorem
was proved.

The existing independent-star and matching deletion estimates give additive
support-sized hull gains. They cannot simply be summed across repeated deletions:
after the first deletion the residual generally is not even, so the repair
hypothesis needed by those estimates is absent. No fixed relative gain was
established by this reassessment. No new Lean declarations or external
computations were added in this continuation, and no jobs are active.

Original Spec is unchanged and UNSOLVED. Latest verified auxiliary modules
remain OptimalSingletonDeletion and HullSaturatedParity. No conjecture proof or
disproof was obtained or submitted.

## Continuation: transferred parity forest VERIFIED; original still unsolved

New module Submission/TransferParitySplit.lean compiles with -M7500; current
olean. Log /tmp/transfer-parity-split.log. All three principal axiom audits
contain only propext, Classical.choice, Quot.sound.
Namespace Erdos184Work.SingletonExchange:

- sdiff_delete_pair_delete: the graph identity for restoring a singleton edge
  from the forest to the cofactor, then deleting that edge from the cofactor.
- transfer_even_of_even_private: transferring an even graph across distinct
  vertices stays even if the number of moved private neighbors is even.
- Best.transfer_delete_pair_even: write E=G-F, T=transfer G u v and
  J=transfer F u v. If F.Adj u v and the number of moved private neighbors
  of E is odd, then T-(J-uv) is even. Thus the joining edge is incorporated
  into the transferred even remainder rather than kept as a singleton.
- Best.transferred_delete_pair_size: deleting uv from J reduces its edge
  count by exactly one and isolates sender v in that forest.
- Best.exists_transferred_parity_forest: there is J'<=transfer F<=transfer G,
  acyclic, with even cofactor in transfer G, at most |E(F)| edges, and sender
  forest degree at most one. It is J in the even-private case and J-uv in
  the odd-private case.

IMPORTANT: This is only a parity-corrected split. J' is NOT proved Optimal
or Best, and its even cofactor's decomposition number is NOT bounded in the
required direction. Neither full-transfer hull comparison nor the dominated
Best-leaf deletion bound has been obtained. Do not infer either from the
smaller forest alone.

The square-accessibility route was also reconsidered. The existing verified
SquareMarginal example already shows that a rigid two-cycle base can absorb
a square at no increase of minimum count. Its final graph is not EvenMinimal.
Thus local path completion or small-core rigidity alone does not establish
accessibility of genuine minimal cores. No new square accessibility theorem
or counterexample was obtained.

Technical: avoid rewriting a Set singleton to a coerced Finset singleton
inside graph.edgeFinset.card; dependent decidability prevents the rewrite.
For the exact deleted-edge count, use Nat.card edgeSet, edgeSet_deleteEdges,
Nat.card_coe_set_eq, and Set.ncard_diff_singleton_add_one instead.

Spec remains unchanged and UNSOLVED with its original sorry, SHA256
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No original proof/disproof was obtained or submitted. No active job remains.

## Continuation: low-degree global-core route remains unproved

Reassessed the sufficient assertion that every nonempty globally Minimal graph
has a supported vertex of degree at most three. No general proof or disproof
was found. The existing LowDegreeHull theorems concern bridges and degree<=2
nonbridge deletion; they do not give the required existence theorem.

A cheap inspection of the EXISTING saved catalogues (not a new exhaustive graph
search, not Lean-certified evidence) found every entry is 3-degenerate:
- order8 catalogue: 75 entries of degeneracy1 and 4 of degeneracy3;
- order9 catalogue: 152 entries of degeneracy1 and 16 of degeneracy3;
- restricted double-split catalogue: 965 entries of degeneracy1 and 68 of
  degeneracy3.
These finite observations prove neither the stronger degeneracy assertion nor
the weaker minimum-degree assertion. Most catalogue entries are forests.

The possible use of odd path partitions and parity corrections does not close
this gap: they do not convert the remaining paths into a uniformly bounded
number of cycles and single edges. No new Lean declaration was added in this
continuation. Latest verified new module remains TransferParitySplit.lean.
Spec remains unchanged and UNSOLVED, with its original sorry; no settlement
was obtained or submitted. No active jobs remain.

## Continuation: minimum parity forests and quarter-order hull gain VERIFIED

Original Spec remains unchanged and UNSOLVED. Two new modules compile with
-M7500 and have current oleans. All principal audits use only propext,
Classical.choice, Quot.sound:
- Submission/MinimumParityForest.lean, log /tmp/minimum-parity-forest.log;
- Submission/PerfectForestHull.lean, log /tmp/perfect-forest-hull.log.
Namespace Erdos184Work.MinimumParity.

Minimum G F means F<=G and F has the fewest edges among subgraphs of G with
F's degree parities. This is NOT SingletonExchange.Best: no decomposition
optimality is part of the new definition.

Checked results:
- exists_minimum: a minimum correction exists in every realizable parity class.
- Minimum.even_balance: for every even C<=G,
    |E(F intersect C)| <= |E(C minus F)|.
  Proof flips C by symmetric difference and compares edge counts.
- Minimum.acyclic and Minimum.reachable_induced: minimum parity corrections
  are forests and each of their connected components is induced in the host.
- exists_perfect_forest: every finite preconnected graph of even order has
  such a forest with every vertex odd. Empty order is harmless and vacuous.
- Minimum.cycle_outside_two: each cycle of any subgraph H<=G has at least
  two edges outside a minimum parity forest F of G.
- Minimum.even_repair_bound: for any even H<=G,
    2*number H <= |E(H minus F)|.
- perfect_forest_hull_boost: for preconnected even G of EVEN order n,
    4*number G + n <= 4*EdgeHull.value G.
  Use the perfect forest, then the existing StarDeletion.delete_with_repair.
  Its deletion makes all vertices odd, so every singleton split has >=n/2
  singleton edges. This supplies the claimed quarter-order additive gain.

This last result sharpens the former support/6 estimate on that particular
class. It remains ADDITIVE in the vertex order. No fixed relative hull gain,
Best=minParity equality, arbitrary-core edge-excess estimate, or original
linear bound follows from it. Do not omit preconnectedness or even order.
The edge-excess reassessment found no way to extend the verified rigid triple
in a maximum cycle family to a sufficiently large rigid subfamily.

A brief inspection of the old catalogues also rules out the tempting assertion
that cyclic globally Minimal graphs cannot have exactly one supported even
vertex: e.g. stored graph6 H??F~z| has number9 and degrees
3,3,3,3,3,3,6,7,7. This is reused external catalogue data, not a new Lean
counterexample. No general near-perfect-matching assertion was proved.

No original proof/disproof was obtained or submitted. Spec SHA256 is still
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No active jobs remain.

## Continuation: parity-optimality induction reassessed, still unproved

No new Lean theorem or original settlement in this continuation.
Considered whether the new minimum-parity exchange inequality closes the
candidate that every hull-saturated graph has a Best singleton forest of
minimum parity-correction size. It does not yet do so.

A precise mathematical descent observation (not newly formalized): if a
globally Minimal G has Best F and a strictly smaller parity correction T,
then G-T is nonempty and even (otherwise G=T and |F|<=|T|). Choose a cycle
C in G-T. The cofactor H=G-C is hull-saturated with number k-1. T remains a
parity correction in H, while every Best singleton forest of H has at least
|F| edges by OptimalSingletonDeletion. Hence H also violates the candidate.
The cofactor need NOT be globally Minimal. Consequently this observation
cannot be iterated on the global-Minimal class, and no analogous valid
step was obtained for arbitrary hull-saturated hosts. Saturation alone does
not justify Optimal.extend_even when its required additivity equality is
absent, nor does equal-number pruning preserve the original parity forest.

No Best=minParity theorem, relative hull gain, or uniform cycle bound was
obtained. Latest verified modules remain MinimumParityForest and
PerfectForestHull. Spec is unchanged and UNSOLVED, retaining its original
sorry. No proof/disproof was submitted and no active jobs remain.

## Continuation: arbitrary minimum parity corrections need not be optimal, even at saturation

Original Spec is still unchanged and UNSOLVED. No new Lean theorem or original
settlement in this continuation. Reassessing the perfect-forest iteration did
not produce an amortized bound: deletion changes even degrees to odd degrees,
and the cost of returning to an even remainder is still uncontrolled.

A new precise obstruction to a STRONGER parity shortcut was checked externally
(not Lean-formalized). Let G = K3 join I6 on 0,...,8, hubs 0,1,2. Exact DP over
all 2^21 edge-subgraphs gives number(G)=value(G)=9, Best singleton count=6,
and minimum parity-correction size=6. The host is saturated, not Minimal.
The correction T consisting of all six edges from hub0 to the independent
vertices is minimum: each of those six odd vertices requires an incident
correction edge, and no two independent vertices are adjacent. But G-T has
number4, so this particular minimum correction costs 6+4=10 > value(G).
Its cofactor consists of eight internally disjoint 1--2 paths (six through
vertices3,...,8, one through0, and the direct edge12). Four cycles suffice,
and degree8 at vertices1 and2 proves that four are necessary.

A different minimum correction IS optimal: singleton edges
03,04,15,16,27,28 plus cycles (0,1,2), (0,7,1,3,2,5), (0,8,1,4,2,6)
give nine pieces. Hence this example does NOT refute the previously unproved
existential candidate Best singleton count = minimum parity-correction size
on saturated graphs. It refutes the universal claim that EVERY minimum
correction is optimal there, and the stronger bound
  value(G) >= number(G-T) + |E(T)|
for every minimum correction T. Do not use either universal statement.

Exact diagnostic source /tmp/three_hub_parity_hull.cpp, executable with same
basename, log /tmp/three-hub-parity-hull9.log. This is external evidence, not
a Lean proof or an original-conjecture counterexample. Separately,
/tmp/parity_first_hull.cpp and /tmp/parity-first-hull7.log checked all 2^21
order7 graphs: the minimum total cost among minimum-cardinality parity
corrections never exceeded the hull. The same existential-cost inequality
held on all subgraphs of the specified three-hub host. These finite checks
supply no general theorem and no original linear bound.

Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No Lean compilation or diagnostic job is active. No proof/disproof was obtained
or submitted. Latest verified modules remain MinimumParityForest,
PerfectForestHull, and TransferParitySplit.

## Continuation: square re-extraction amortization still lacks a charge

Revisited the precise square-deletion chain from EvenMinimal cores rather
than assuming SquareAccessible. No new Lean theorem or original settlement.
If Gi loses a square Ci and the cofactor is pruned to Ri of equal number,
the discarded remainder Ji is even. The exact number decrement is one,
but Ji can be nonempty without a proved loss of supported vertices or a
proved increase of connected-component count. Thus neither its edge count
nor its decomposition number has an established telescoping vertex budget.
For a complete chain, subadditivity gives only
  number(initial) <= number(union selected squares)
                     + number(union discards) + number(final core).
Combined with the unit decrements, this controls the selected-family
optimality defect by the discard cost, not by O(n). It does not make the
selected squares an optimum family or permit invoking SquarePieces.

The old doubled-Petersen chain obstruction still has only a CycleCritical
initial graph; it is not a counterexample to the initial-EvenMinimal version.
No such stronger obstruction or general amortization proof was obtained.
SquareMarginal refutes unrestricted diminishing returns but its full graph
is not EvenMinimal, as already checked. No statement about arbitrary cores
was inferred from it.

Spec remains unchanged and UNSOLVED, with the original sorry. No proof or
disproof was submitted. No compilation or diagnostic job was started in
this continuation, and no job is active.

## Continuation: dominated-singleton structure and RAW deletion obstruction VERIFIED

Original Spec remains unchanged and UNSOLVED. Two new auxiliary modules have
current oleans and principal axiom audits using only propext, Classical.choice,
Quot.sound. Both compiled with -M7500, one substantial Lean process at a time.

1. Submission/DominatedSingletonRemainder.lean (131 lines), imports
TransferParitySplit. Log /tmp/dominated-singleton-remainder.log.
Namespace SingletonExchange. For Best G F, F.Adj u v, and v dominated by u:
- dominated_neighbor_even: every G-neighbor w of v other than u is adjacent
  to BOTH v and u in E=G-F, not merely in G.
- dominated_even_neighborhood: E.neighborSet v=G.neighborSet v minus {u},
  and E.neighborSet v is contained in E.neighborSet u.
- doubleStar and its neighborhood/evenness lemmas define K_{2,S} with hubs
  u,v and S=E.neighborSet v.
- dominated_doubleStar: this M is contained in E, is even, and E-M is even.
No optimality, number additivity, transfer monotonicity, or bounded vertex
loss is asserted for M or its complement.

2. Submission/DominatedRawDeletionObstruction.lean (about160 lines), imports
that module and PerfectForestHull. Log /tmp/dominated-raw-deletion-obstruction.log.
It verifies a six-vertex graph with edges
  01,02,03,04,05,12,13,14,15,25,34,
and Best singleton matching F={01,25,34}. Its number is5, its even remainder
has number2, vertex0 is a forest leaf dominated by1, and deleting vertex0
leaves two triangles with number2. Thus RAW deletion loss two is false even
at a dominated Best leaf. This is NOT a hull-loss obstruction and NOT an
original-conjecture disproof. Global Minimality is not asserted (in fact the
five-edge star at0 is a proper spanning tree with the same number5).
The lower certificate combines all-odd singleton count>=3 with the two-hub
degree/parity bound; all upper bounds have explicit cycle partitions.

External exact diagnostics used during this reassessment:
- /tmp/dominated_raw_loss.cpp, /tmp/dominated-raw-loss7.log;
- /tmp/dominated_general_hull_loss.cpp, /tmp/dominated-general-hull-loss7.log.
Both finished over all order7 graphs. The former supplied the six-vertex
obstruction now verified in Lean. The latter found maximum dominated raw-
source versus deleted-hull loss2 at this bounded order, even without the
Best-edge restriction. No general domination-only rule follows; domination
without Best-leaf control must not be substituted for the intended hypothesis.

The original sufficient full-transfer hull comparison along Best singleton
edges and the dominated Best-leaf bounded hull-deletion loss remain UNPROVED.
No proof/disproof of Spec was obtained or submitted. No job remains active.
Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Continuation: targeted terminal profiles and cloning reassessment — UNSOLVED

No new Lean theorem or settlement of Spec was obtained in this continuation.
Spec remains unchanged with its original sorry. No proof was submitted.

The previously completed /tmp/chain_best_profiles.cpp calculation is external
exact evidence only: over all edge subgraphs of K3,6, with hubs0,2 as terminals,
only the full graph has number8 and minimum terminal-path-deletion number8.
Both its Best singleton count and the path-minimizing cofactor singleton count
are6. The explicit source chain-ring partition described in the continuation
summary (seven cycles plus18 singleton edges) was not Lean-formalized. In
particular, do not use the closing edge of that source as a Best singleton edge.

New external exact checks (NOT Lean proofs):
- /tmp/saturated_terminal_profiles.cpp, /tmp/saturated-terminal-profiles7.log:
  all order7 graphs, fixing terminals0,1. Among92337 hull-saturated nonempty
  graphs,215 have minimum path-cofactor number equal to the original number;
 60 of these have a higher minimum cofactor singleton count (gap1). Thus that
  local profile is possible; saturation does NOT forbid it.
- /tmp/best_block_ring_profiles.cpp, /tmp/best-block-ring-profiles.log:
  B=K3 join I4 minus edge03, terminals0,3. number(B)=value(B)=6, BestSingles=3;
  min terminal-path cofactor profile=(6,4). Minimum cofactor after deleting
  two edge-disjoint terminal paths has number4. Among number6 subgraphs,
  only full B has one-path cost6. Two proper subgraphs have one-path cost5
  and no pair of edge-disjoint terminal paths; other number6 subgraphs have
  one-path cost<=4. These proper subgraphs obstruct the attempted chain-block
  counterexample to Best-edge HULL comparison: raw target savings do not by
  themselves bound its hull.
- /tmp/minimal_dominated_best_degree.cpp,
  /tmp/minimal-dominated-best-degree7.log: among order7 globally Minimal graphs,
  a dominated endpoint of a Best singleton edge has maximum degree3. This is
  ONLY bounded-order evidence and no uniform degree assertion was proved.
  Inspecting the old order8/9 catalogues likewise supplies no general result.
- /tmp/zykov_hull.cpp, /tmp/zykov-hull7.log: unrestricted nonadjacent two-choice
  cloning fails on globally Minimal graphs. A five-vertex path with edges
  02,04,12,13 has number4, but cloning0 onto1 or1 onto0 produces hull3 (one
  vertex becomes isolated). The seven-vertex tree 02,05,06,12,13,14 has number6
  and both clone hulls4. Thus unrestricted Zykov symmetrization cannot be used.
  No biconnected-restricted cloning theorem or original bound was proved.

Further theoretical reconsideration did not prove Best-edge full transfer,
bounded dominated Best-leaf hull deletion, arbitrary even-core rigidity, or
another global O(n) bridge. No new background job remains active.

## Continuation: saturated singleton-pruning diagnostic and a structured obstruction

Original Spec remains unchanged and UNSOLVED. No new Lean theorem or original
settlement was obtained or submitted. All finite computations in this entry
are EXTERNAL diagnostics, not Lean verification.

The previously pending /tmp/saturated_singleton_pruning.cpp order7 run finished
successfully: /tmp/saturated-singleton-pruning7.log ends
  DONE fails=0 existsFails=0 oneFails=0 worst=0
and the .exit file contains0. This is bounded-order evidence ONLY. In particular,
the stronger one-edge assertion is FALSE in general, as the following structured
construction shows (mathematical block argument with an externally checked base).

Base B is K3 join I4 minus03, hubs0,1,2 and terminals a=0,b=3.
The exact recurrence over its16384 edge-subgraphs verifies:
  number(B)=value(B)=6; BestSingles(B)=3;
  min over simple a--b paths P of (number(B-P),BestSingles(B-P))=(6,4).
Every number6 subgraph is connected on all7 vertices. This also follows from
maximizer_reachable, already proved generally in Lean, since value(B)=6.
New independent base checker:
  /tmp/singleton_pruning_chain_certificate.py
  /tmp/singleton-pruning-chain-certificate.log
  /tmp/singleton-pruning-chain-certificate.json
It checks cycle/single-edge partitions and exact edge coverage, and prints an
explicit optimum base partition and optimum cofactor for path0--1--3.

For m>=1 chain m copies of B by identifying b_i with a_(i+1), and join the
outer terminals by a new two-edge path through a new vertex z. Call this G_m;
let H_m delete the first of the two new edges. Then, mathematically:
  |V(G_m)|=6m+2,
  number(G_m)=value(G_m)=6m+1,
  BestSingles(G_m)=4m,
  number(H_m)=value(H_m)=6m+1,
  BestSingles(H_m)=3m+1.
Reason for the exact numbers and singleton counts: a decomposition either uses
both new path edges as singleton pieces (cost at least6m+2), or has exactly one
cycle through z. The latter cycle uses one terminal path in each block; all
remaining cycles are block-local. Each cofactor costs at least6 with at least4
singletons. The displayed base cofactor attains these bounds. H_m is simply the
chain plus a pendant edge, so its counts add as6m+1 and3m+1.

For hull saturation, consider any edge-subgraph R of G_m. If a new path edge
is missing, blockwise upper bounds give number(R)<=6m+1. If both are present
and all block terminal pairs remain connected, remove one outer cycle;
each remaining block subgraph has number<=6, giving the same bound. Otherwise,
some block fails terminal reachability, hence has number<=5 (a number6
maximizer would preserve the full base's reachability). Decomposing the two
new edges separately again gives number(R)<=6m+1. Thus the upper hull bound
is valid for all subgraphs, not merely for the full chain.

For m=2 the script prints and independently checks a30-edge14-vertex graph
partition with profile(13,8), and its29-edge one-edge deletion with profile
(13,7). Consequently equal-number one-edge deletion can DECREASE minimum
singleton count on saturated graphs, by m-1 without a uniform bound.
The original minimal-CORE monotonicity claims remain UNPROVED and are NOT
refuted by this construction: every minimal equal-number core of G_m is a
spanning tree, since it is connected and its number equals |V|-1. Such a core
has6m+1 singleton pieces, larger than4m. Do not confuse this obstruction with
a counterexample to either minimal-core claim or to Erdős184.

Also preserved from the preceding continuation: /tmp/chain_even_fractional.py
and /tmp/chain-even-fractional.log found fractional cycle optimum7, attained
integrally, on the25-vertex37-edge chosen even remainder of the three-block
chain-ring. The signed dual is -1/2 on03 and +1/2 on the15 edges printed in
the log; this certificate has NOT been Lean-checked. It does not prove
fractional exactness for arbitrary Best remainders or globally Minimal graphs.

A new network check again failed DNS resolution for erdosproblems.com. No
literature update was retrieved. No Lean build or background diagnostic is
active. Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Continuation: a uniform DEGENERACY/sparsity bound for global cores is false

Original Spec remains unchanged and UNSOLVED. The following is a mathematical
argument, with small explicit grouping certificates checked externally; it has
NOT been formalized in Lean. It is an obstruction to auxiliary structural
shortcuts, not to the original O(n) conjecture.

For every a>=1, K_(a,a) has an explicit partition with
  (3a-1)/2 pieces if a is odd, and a/2 pieces if a is even.
Use cyclic-offset perfect matchings. For even a, pair offsets(0,1),(2,3),...;
for odd a, leave offset0 as a singleton matching and pair(1,2),(3,4),....
Each consecutive-offset pair is a Hamilton cycle since the offset difference
is1. External direct checks for a=1,...,31 (no graph search):
  /tmp/degenerate_bipartite_group_certificates.py
  /tmp/degenerate-bipartite-group-certificates.log.

CONCRETE NON-3-DEGENERATE MINIMAL CORE EXISTENCE:
Let G=K_(5,1560). Each of its1560 vertices on the large side has odd degree5,
so every cycle/edge partition has at least1560 singleton edges. Every cycle
has length<=10. With7800 edges this forces number(G)>=2184.

For any3-degenerate H<=K_(5,t), at most15 large-side vertices have degree>=4.
Indeed choose a3-degeneracy deletion ordering. Such a vertex cannot precede
all its hub-neighbors, and assign it to its first earlier hub-neighbor. It is
still present when that hub is removed; each of the5 hubs has at most3 later
neighbors, so at most15 vertices are assigned.
Decompose the remaining leaves by their exact hub neighborhood:
- degree1: one singleton per leaf;
- degree2: pair leaves of each of the10 pair types, using a K2,2 cycle;
  a type of size b costs<=b/2+3/2;
- degree3: group leaves of each of the10 triple types in threes, using
  K3,3 = one six-cycle plus three singletons; a type of size a costs
  <=4a/3+10/3;
- the h<=15 high-degree leaves use at most5h singleton edges.
All groups are edge-disjoint, even if they share hubs. Consequently
  number(H) <= (4t+310)/3.
For t=1560, this is6550/3<2184. An existing minimal hull maximizer of G
therefore cannot be3-degenerate: its number is at least2184. This refutes
upgrading the old small-catalogue3-degeneracy observation to a general theorem.

GENERALIZATION (same mathematical grouping argument, not Lean checked):
Globally Minimal graphs have neither uniformly bounded degeneracy nor a
uniform bound |E|<=C|V|. Fix any odd r>=3 and let G=K_(r,t), with t large.
Every decomposition of G has at least t singleton edges and cycles of length
at most2r, hence number(G)>=(3/2-1/(2r))*t = alpha_r*t.
For any H<=G, group leaves with equal hub neighborhoods S, of size a, in
batches of a. The K_(a,a) certificates above yield cost alpha_a per leaf,
where alpha_a=3/2-1/(2a) for odd a and alpha_a=1/2 for positive even a
(and alpha_0=0). Unbatched leftovers cost a constant C_r depending only on r,
not t. Thus
  number(H) <= sum_(large-side v) alpha_(degree_H(v)) + C_r.
For odd r, alpha_r is strictly larger than every alpha_a with0<=a<r.
Any hull maximizer R, in particular any globally Minimal one, has
number(R)>=alpha_r*t. Hence all but a bounded number (depending on r only)
of its t large-side vertices have degree r. It follows that
  |E(R)|/(r+t) >= r*(t-O_r(1))/(r+t),
which tends to r as t grows. Letting odd r grow refutes both uniform edge
density and uniform degeneracy bounds for globally Minimal graphs.

IMPORTANT SCOPE: this does NOT refute the weaker assertion that every globally
Minimal graph has SOME vertex of bounded positive degree. A bounded number of
exceptional low-degree leaves could remain in each example. Global minimality
is not hereditary to arbitrary induced subgraphs (the clique triangle inside
K3 join I4 already demonstrates that distinction). Thus one must not infer a
counterexample to the weak minimum-degree route from this argument. No original
linear decomposition bound or disproof follows.

The two-color endpoint route was revisited but still has no established
path-to-cycle conversion. The minimum-degree vertex hull-loss route also
remains unproved. A direct DNS-over-HTTPS attempt timed out; no current
literature was retrieved. A targeted binary Best-remainder fractional diagnostic
was launched at /tmp/binary-best-remainder-fractional.log/.exit; its result is
not assumed in this entry and must be read before reporting any conclusion.

## Continuation: Best-remainder fractional EXACTNESS fails for general binary systems

Original Spec remains unchanged and UNSOLVED. No Lean proof/disproof of the
original conjecture, and no new Lean module, was produced in this continuation.
The statements below concern binary column circuit systems, NOT simple graphs.
All their finite checks are external and must not be treated as Lean results.

The first targeted check /tmp/binary_best_remainder_fractional.py finished at
/tmp/binary-best-remainder-fractional.log and .exit(0). R10, its two-sum, the
six-pair extension of R10, the rank-five extension, and AG(4,2) had NO qualifying
globally Minimal supports with at least2 cycles in a Best remainder. Thus those
passes are vacuous for the proposed nontrivial exactness claim. The graphical
K3 join I4 did have a qualifying core and21 tested Best remainders, all exact.

A subsequent structured family gave a nongraphic counterexample. Consider
rank-four binary projective geometry PG(3,2), represented by columns1,...,15
in (F2)^4, and delete column1. Let X={2,...,15}. Its circuits are the minimal
nonempty xor-zero subsets. Exact subset DP on all16384 subsets proves:
  number(X)=5; Best singleton count=2; hull(X)=5; proper hull maximum=4.
Thus X is globally Minimal in this binary circuit-and-singleton system.
Its total xor is1, so any two-singleton parity correction must be one of the
seven pairs {a,a+1}, a=2,4,...,14. Each is Best: its12-element xor-zero
complement has minimum circuit partition number3, and an explicit3-piece
partition is printed in the final certificate log.

For EACH of these seven Best remainders there are48 five-element circuits,
and every element is in exactly20 of them. Giving each circuit coefficient
1/20 is therefore an exact rational fractional cover of cost48/20=12/5.
No circuit can exceed5 elements in rank4, so12/5 is also the fractional
optimum. It is strictly smaller than the integral optimum3. Hence even the
EXISTENTIAL claim 'some Best remainder of every globally Minimal binary
support is fractionally exact' is false.

Final independent exact certificate (no floating-point inference):
  /tmp/projective_best_gap_certificate.py
  /tmp/projective-best-gap-certificate.log
The source is nongraphic: a simple rank4 graphic matroid has at most10 elements,
whereas X is simple with14. This does NOT refute fractional exactness for
Best remainders of globally Minimal SIMPLE GRAPHS, nor any bounded-rounding
version, nor Erdős184. It shows that a pure binary-circuit argument cannot
establish that exactness claim without using additional structure.

Discovery diagnostics, all finished with exit0:
- /tmp/binary_translation_pair_core.cpp; executable with same basename;
  /tmp/binary-translation-pair-core{0,1,2}.log;
  /tmp/binary-translation-pair-cores.exit.
  These use22 columns comprising11 translation pairs in PG(4,2), with three
  choices of the four omitted quotient points. All three full supports have
  number=hull6, BestSingles2, proper hull6: SATURATED BUT NOT MINIMAL.
  The full-support fractional gaps must not be substituted for a minimal-core
  counterexample. The actual14/15-element minimal cores they exposed supply it.
- /tmp/binary_translation_fractional.py;
  /tmp/binary-translation-fractional.log/.exit;
  /tmp/binary-translation-fractional-certificates.json.
  All33 full-support Best remainders have rationally verified covers below4.
- /tmp/check_translation_actual_cores.py;
  /tmp/translation-actual-core-fractional.log/.exit.
  These smaller extracted cores genuinely fail the existential exactness test.
  The final PG(3,2)-minus-one certificate above isolates the simplest case and
  replaces floating LP outputs by the uniform rational48-cycle certificate.

No diagnostic or Lean build remains active. Main unresolved bridges include
GRAPH-specific Best-remainder rounding/exactness, valid selective compression,
and an existential bounded-cost vertex/core reduction. Neither the new binary
obstruction nor unbounded degeneracy/sparsity of global cores settles the
original conjecture. Spec SHA256 is still
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Continuation: a SATURATED Best/minimum-parity gap, and symmetry-reduced profiles

Original Spec is unchanged and UNSOLVED. No Lean proof/disproof of the original
conjecture was obtained. The following are mathematical arguments with external
exact checks, NOT new Lean theorems.

### The existential Best = minimum-parity shortcut is FALSE at saturation

This follows from the previously checked chain family G_m (m copies of
B=K3 join I4 minus03, terminals0,3, chained and closed by a two-edge path
through a new vertex). The established block argument gives
  number(G_m)=value(G_m)=6m+1; BestSingles(G_m)=4m; |V|=6m+2.
Take, in each block, the three singleton edges04,05,06 of its displayed
optimal partition, and also take BOTH edges of the new closing path. This
is a parity correction T of size3m+2. Its even complement is the disjoint
union, edgewise and across articulation blocks, of three cycles per block.
Thus this particular split costs (3m+2)+3m=6m+2, one more than optimal.
For m>=3 its correction has size3m+2<4m=BestSingles(G_m).
Consequently NO minimum-cardinality parity correction is optimal on G_m.
This refutes the EXISTENTIAL equality on arbitrary hull-saturated graphs,
not merely the older universal claim that every minimum correction is optimal.

In fact the exact minimum correction size is min(3m+2,4m): parity at the new
vertex forces a correction to use either both closing edges or neither.
In the former case each block has the base parity {0,4,5,6}, requiring at
least3 local edges; in the latter, parity propagates along the articulation
chain so each block has parity {3,4,5,6}, requiring at least4 local edges.
These bounds are attained by the base three-edge stars or four-edge stars
at hub1 respectively. For m>=2 the minimum is3m+2, so the Best-minus-minimum
parity gap is m-2, unbounded additively.

External certificate /tmp/saturated_parity_gap_certificate.py and log
/tmp/saturated-parity-gap-certificate.log check exact edge coverage and parity
for m=1,2,3,4,10,30, using the independently rechecked base recurrence. The log
prints the full20-vertex44-edge m=3 graph, its19-piece/12-singleton optimum
certificate, and an11-edge parity correction. The arbitrary-m lower/hull
arguments are the mathematical block arguments above, not a Lean check.

SCOPE: G_m is NOT globally Minimal (its number is |V|-1). Its minimal hull
maximizers are spanning trees. Thus the version restricted to globally
Minimal graphs remains unproved and unrefuted, as does minimal-core singleton
monotonicity. This does NOT disprove the original Erdős184 statement.

### Exact three-hub orbit recurrence (external, finished)

/tmp/three_hub_orbit_profiles.cpp, executable of the same basename, and log
/tmp/three-hub-orbit-profiles.log (exit file0) compute exact profiles using
seven independent-side neighborhood counts and the three possible hub edges.
A simple cycle uses two or three hubs; its connections are direct hub edges
or paths through distinct leaves. The resulting42 cycle signatures cover
all possibilities. Singleton and cycle removal give the minimum recurrence;
all one-edge deletions give the hull and min/max Best-singleton counts among
minimal hull maximizers. A separate eight-state parity DP computes minimum
parity-correction size. This is a finite exact diagnostic, not Lean verification.

The run covered1,961,256 orbit states with at most16 independent-side vertices,
and21,207 globally Minimal states. None had Best larger than minimum parity.
No arbitrary-order conclusion follows from that absence.
For B_t=K3 join I_t minus03, the relevant completed profiles include:
  B4: number=hull6, Best3, path-cofactor(6,4), minimal-core singles6;
  B7: number=hull10, Best6, path-cofactor(10,7), minimal-core singles7;
  B10: number=hull14, Best9, path-cofactor(14,10), minimal-core singles10;
  B13: number=hull18, Best12, path-cofactor(18,13), minimal-core singles13;
  B16: number=hull22, Best15, path-cofactor(22,16), minimal-core singles16.
Thus the higher saturated bases examined do NOT immediately turn the chain
into a counterexample to minimal-core singleton monotonicity. Do not infer
that adding a forest preserves Best or that saturation implies Minimality.

### Other investigations, no general bridge

The graphical even-ring fractional gap was reviewed. A Best forest has
components independent in its even remainder. If a connected globally Minimal
non-tree has n vertices, its number is at least n (a proper spanning tree has
number n-1). Thus if a Best forest has a components and its remainder has c
cycles in an optimum, necessarily c>=a>=chromatic_number(remainder). This
excludes some small fractional gadgets but does NOT exclude the ring family
or prove the required fractional rounding/exactness. Adding cross-block forest
edges changes the boundary structure, so the ring's old local lower argument
cannot simply be reused to assert that an added forest is Best.

/tmp/simple_binary_best_contraction.cpp and log
/tmp/simple-binary-best-contraction.log checked80,460 instances in subsets of
PG(3,2) of the conditional inequality
  number(S)<=hull(S/e)+1 when e is singleton in a Best partition.
There was no failure in that finite test. This is NOT a general matroid or
graph theorem, and no selective-transfer proof followed. General binary
arguments must also distinguish simple systems from parallel-element systems.

No Lean build or diagnostic remains active. The main original O(n) bridge is
still missing. Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Continuation: strict singleton-growth descent is FALSE — Lean checked

Original Spec remains unchanged and UNSOLVED. Two new standalone modules
compile successfully with permitted axiom audits:
  Submission/ThreeHubMinimalLeaves.lean
  Submission/StrictSingletonDescent.lean
Logs:
  /tmp/three-hub-minimal-leaves.log
  /tmp/strict-singleton-descent.log
Current oleans are installed for both. There are harmless linter warnings,
no proof placeholders, and all final principal axioms are propext,
Classical.choice, Quot.sound. No rebuild of Work was needed.

Namespace Erdos184Work.ThreeHubMinimalLeaves:
- degree_right and degree_right_full: exact neighbor cardinality formulas
  for a subgraph of a complete bipartite graph.
- degree_two_card_le: for globally Minimal G <= K_(3,B), at most two B-side
  vertices have degree two. Proof: restrict to the three hubs and those
  vertices; any cycle would contradict Minimal.cycle_vertex_degree. The
  resulting forest has at least twice as many edges as B-side vertices and
  strictly fewer edges than its three-plus-B-side vertex count.
- optimal_singleton_lower: if G is also connected and F is ANY Optimal
  singleton split, then |B| <= |F|+2. All B-side vertices have degrees1..3;
  those not of degree two are odd and independent, so force distinct
  singleton edges. This is a general theorem, not a bounded-order check.

Namespace Erdos184Work.StrictSingletonDescent:
- bestForest and singles choose a Best forest and its unique minimum
  optimal-singleton count; singles_eq and singles_le are verified.
- Property H is the hypothetical rule: every connected cyclic globally
  Minimal G <= H has some R <= G, also globally Minimal and connected,
  with number(R)+1=number(G) and singles(G)<singles(R). It allows arbitrary
  smaller cores, not just a prescribed cycle deletion.
- potential_bound: Property H would imply
    number(G)+singles(G) <= 2*(|V|-1)
  for every connected Minimal G<=H, by induction on number.
- host is K_(3,19), on22 vertices. host_connected and host_number_lower
  (number(host)>=26) are verified using the independent-odd degree bound.
- exists_excess_core: some connected globally Minimal hull maximizer G of
  this host has number(G)>=26 and singles(G)>=17, hence their sum exceeds42.
- not_property: therefore Property host is FALSE.

This conclusively rules out a STRICT increase of Best singleton count at
every chosen unit cycle/core reduction. It does NOT refute either the
non-strict minimal-core singleton monotonicity assertion or the original
Erdős184 conjecture. In particular the new theorem is not a Spec disproof.

Mathematical interpretation: a connected minimal core of K_(3,t) has at least
t-2 singleton edges, whereas a terminal spanning tree has t+2. Only four
strict increases are possible, but for t>=19 the number lower bound forces
more than four unit descents before reaching a tree. This explains why a
singleton-only amortization cannot work even on this simple graphical family.

An additional bridge-count budget could address some constant-singleton
steps: edges already bridges remain bridges when subgraphs preserve
reachability. However no theorem ensuring a positive combined singleton/
bridge charge per step, or any other uniform amortization, has been obtained.
Do not treat that further proposal as a proved reduction.

No Lean build or diagnostic remains active. Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No original proof/disproof was obtained or submitted.

## Continuation: combined singleton/bridge charge requires SELECTION — unresolved

Original Spec remains unchanged and UNSOLVED. No new Lean theorem or original
settlement was obtained in this continuation.

The proposed potential is BestSingles(G)+number_of_bridges(G). Old bridges
persist under subgraph reductions preserving reachability (the existing
bridge_mem_of_reachable_eq and IsBridge.anti_of_mem_edgeSet suffice). This
bounded budget alone does not prove any positive charge per unit descent.

An exact symmetry-reduced diagnostic was run:
 /tmp/three_hub_bridge_potential.cpp
 /tmp/three-hub-bridge-potential.log and .exit(0)
It extends the preceding three-hub orbit recurrence by tracking the MAXIMUM
potential among minimal hull maximizers and computing bridges by exact DFS.
For every valid cycle signature of a Minimal state it checks the cofactor
hull equals source number minus one, then tests the available core potential.
The completed run covered1,961,256 orbit states and21,207 Minimal states,
of which4,225 were cyclic. There were325 failures of the EVERY-cycle strict
charge, and no failure of the EXISTS-a-cycle variant in this bounded family.
The latter absence is not a general theorem; three-hub examples contain
low-degree cyclic vertices that are unavailable in a general reduction.

The simplest EVERY-cycle obstruction is explicit:
 G=K3 join I7, number=hull11, BestSingles7, bridges0, globally Minimal;
 C=the triangle on its three hubs;
 G-C=K3,7, number=hull10, BestSingles7, bridges0, globally Minimal.
Its maximum core potential is7, the same as the source, so selecting a
minimal cofactor core cannot rescue this particular cycle choice.
A separate completed exact orbit certificate prints the proper-hull maxima
(10 and9 respectively):
 /tmp/three_hub_bridge_potential_certificate.cpp
 /tmp/three-hub-bridge-potential-certificate.log
These finite checks are EXTERNAL diagnostics, not Lean-verified theorems.
They do NOT refute a selective combined-potential rule, nor Erdős184.

No general proof of that selective rule, no uniform amortized charge, and
no alternative original linear bound was found. A fresh attempt to retrieve
current literature from erdosproblems.com and export.arxiv.org again failed
with DNS resolution errors; no new literature claim was used.
No background job remains. Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Continuation: positive-bound audit completed without settlement

Original Spec remains unchanged and UNSOLVED. No new Lean proof was obtained.
The audit of the positive quantitative results did not uncover an unconditional
consequence sufficient for Spec:
- universal_bound concerns number(G), not the edge-subgraph hull;
- nested_bound requires NestedAlongEdges, and likewise bounds number(G);
- the irreducible, separating-cycle, square-accessibility, and rigidity routes
  retain their explicit structural hypotheses.
The possible uniform bound on SOME positive degree in every globally Minimal
nonempty graph remains unproved/unrefuted here. Unbounded degeneracy does not
refute that assertion, and it must not be used as a theorem in a deletion/core
induction. No new numerical diagnostic or compilation was launched.
Neither the strict-singleton-descent obstruction nor the saturated parity gap
is a negation of Erdős184. No original settlement has been submitted.

## Continuation: raw Best-edge transfer obstruction VERIFIED; Spec unsolved

The original Spec is unchanged and UNSOLVED. The new result below is an
auxiliary obstruction, NOT an original-conjecture disproof.

### New Lean result

Current modules:
  Submission/BestTransferRawData.lean
  Submission/BestTransferRawLower.lean
  Submission/BestTransferRawUpper.lean
  Submission/BestTransferRawObstruction.lean
Namespace Erdos184Work.BestTransferRaw.
Logs /tmp/best-transfer-raw-{data,lower,upper,obstruction}.log and .exit.
All four passed; the last file was recompiled after adding a module docstring.
Principal audits contain only propext, Classical.choice, Quot.sound.

The source has13 vertices. Take two copies of B=K3 join I4 minus edge03,
identify terminal3 of the first with terminal0 of the second, and close the
outer terminals by ONE edge (not the two-edge closing path in earlier notes).
Explicit labels: first copy0..6, second copy[3,7,8,9,10,11,12], closing edge09.
The singleton forest is {04,05,06,09,3-10,3-11,3-12}.
Verified:
- source_number: number(source)=13;
- forest_best: this seven-edge forest is Best;
- transfer_eq: full transfer0<-9 is the explicitly defined target;
- target_upper: number(target)<=11;
- raw_transfer_loss: Best source forest, forest.Adj0 9, and
    number(transfer source0 9)+1 < number(source).
Global Minimality of this source is NOT asserted in the Lean theorem.

The source lower proof is structural, not a graph catalogue. Every piece
avoiding the closing edge is confined to one block. For a cycle containing
that edge, parity makes the degree removed at each block port exactly one.
Each residual block then has three hub degrees>=4 and four independent odd
vertices; the degree/parity certificate forces at least6 pieces. If the closing
piece is a singleton, the untouched block likewise needs6 pieces. Erasing the
closing piece from any decomposition leaves at least6+6 pieces.
Seven independent odd vertices force at least7 singleton edges in every
optimal split. Explicit six-cycle and four-cycle partitions certify the source
and target even-remainder upper bounds.

A first attempt to verify CycleForestCertificate.PieceValid for all explicit
cycles by direct connectivity decision exceeded memory. Basic finite data were
split off, and explicit cycle walks were used with number_le_cycle_family.
The final successful proofs do not use native_decide or untrusted axioms.
For disjointness, simp [Finset.disjoint_left,List.mem_toFinset] avoided the
classical-vs-computable DecidableEq instances embedded in toFinset.

IMPORTANT CORRECTION to an intermediate commentary: this family does NOT
refute optimality of the natural transferred singleton forest. Longer pairs
of terminal paths were initially overlooked. They leave one cycle per block;
in the two-block example the transferred even remainder has an explicit
four-cycle partition, and the same seven-edge forest is optimal. The only
new Lean obstruction is to RAW-number monotonicity, not hull monotonicity or
transferred-forest optimality.

### Exact external block/ring profiles (NOT Lean theorems)

Artifacts:
 /tmp/best_transfer_ring_profiles.py
 /tmp/best-transfer-ring-profiles.log
 /tmp/best_transfer_ring_partitions.py
 /tmp/best-transfer-ring-partitions.log

For each of all2^14 edge subgraphs S of B, compute t_q(S), q=0,1,2,
where t_q is the minimum number after deleting q edge-disjoint simple
terminal0-to3 paths (infinity if unavailable). Pareto-maximal profiles are:
 (5,infinity,infinity), (6,5,infinity), (6,6,4).
The last profile occurs only for full B. The middle profile is attained by
B minus either edge incident to terminal3. These computations use exact
cycle/singleton recurrences and enumerate34 terminal paths and73 pair-unions.

Consequences via the elementary block argument, for m>=2:
- One-edge-closed chain G_m has n=6m+1, number6m+1, BestSingles3m+1.
- It is globally Minimal MATHEMATICALLY from the finite base profiles:
  every proper subgraph either has a block of number<=5, or a proper block
  of number6 with a path cofactor of number<=5; in either case total<=6m.
  This global-Minimality argument is not newly Lean-formalized.
- Transferring along its closing edge produces a ring plus a pendant edge.
  Raw number is4m+3, but arbitrary-edge hull remains6m+1.
- One ring block with profile(6,5,infinity) blocks all q>=2 crossing cycles,
  so the hull fully rescues the comparison. This family does NOT refute the
  sufficient Best-edge transfer HULL inequality.
- The natural transferred forest still has3m+1 edges; its even cofactor has
  m+2 cycles. It is optimal and Best, rather than an optimality obstruction.
The script's m=1 ring arithmetic is only abstract profile arithmetic; endpoint
identification can create parallel edges there. Use m>=2 for these simple
chain/ring interpretations.

### Restricted terminal-cut diagnostic (NOT a theorem)

Artifacts /tmp/terminal_singleton_barrier.cpp and executable; logs
 /tmp/terminal-singleton-barrier7.log
 /tmp/terminal-singleton-barrier8.log and .exit(0).
For saturated simple B with nonadjacent terminals a,b, all terminal-path
cofactors have the same number k=number(B), and their best singleton count
is strictly above BestSingles(B), test existence of R<=B with number(R)=k,
some edge separating a,b, and min terminal-path cofactor number>=k-1.
Order7:1,048,576 states,20 eligible, no failure.
Order8:134,217,728 states,1,050 eligible, no failure.
No general bridge-subgraph lemma follows. That claim is stronger than the
contraction inequality actually needed, and it remains unproved. The strict
path-number branch of the code cannot occur under saturation, so its zero
count is tautological, not extra evidence.

### Best-edge contraction is FALSE for multigraph/binary parallel systems

This supersedes any temptation to infer a general matroid theorem from the
older simple PG(3,2) finite pass. The distinction from simple graphs is essential.
Take four junctions in a chain, with2r parallel edges in each of its three
bundles, plus one closing edge e between the chain ends. Two parallel edges
are allowed as a circuit in this MULTIGRAPH model.
- Full source has number3r+1, BestSingles1, and e is a Best singleton.
- Every proper edge-subgraph has number<=3r: the source is globally Minimal.
- Contracting e yields three bundles around a triangle. Its arbitrary-edge
  hull is2r+1, witnessed by row counts(1,2r,2r). Thus loss r is unbounded,
  even on a globally Minimal source and along a Best singleton edge.
For counts(a,b,c), the target minimum is
 min_{0<=q<=min(a,b,c)} [q+sum_i ceil((a_i-q)/2)].
Choosing q=min counts bounds this by2r+1, and the displayed witness attains it.
Source has only local two-circuits or one closing four-circuit, so its formulas
and Best singleton count follow directly. Exact count checks for r=1..12:
 /tmp/parallel_best_contraction_certificate.py
 /tmp/parallel-best-contraction-certificate.log
These are mathematical/external results, not new Lean code theorems.
Subdividing the parallel edges makes the graphs simple but adds enough
vertices that spanning-tree subgraphs destroy source saturation/minimality;
it does NOT transport this to a simple-graph obstruction or to Spec.

Bounded attempts to fetch the cited paper and Erdős184 page via direct IP
resolution timed out. No new literature claim was used.
No proof or disproof of the original conjecture was obtained or submitted.

## Continuation: selective vertex-hull loss reduction VERIFIED; Spec unsolved

New module Submission/VertexHullLossReduction.lean compiles successfully, with
current .lake/build/lib/lean/Submission/VertexHullLossReduction.olean.
Log /tmp/vertex-hull-loss-reduction.log; exit file is 0. Principal axiom audits
use only propext, Classical.choice, Quot.sound.
Namespace Erdos184Work.VertexHullLoss:
- Property C asks that every nonempty globally Minimal graph admit SOME vertex v
  with number(G) <= value(G.induce({v}^c)) + C.
- uniform_of_property derives number(G) <= C*|V| from that explicit hypothesis,
  using order induction and extraction of a globally minimal hull maximizer.
- asymptotic_of_property transfers this to the original asymptotic proposition.
- obstruction_of_asymptotic_failure proves that ORIGINAL FAILURE would force,
  for EVERY natural C, a globally Minimal nonempty graph with
    value(G.induce({v}^c)) + C < number(G)
  for EVERY vertex v simultaneously.
This is a necessary obstruction and a CONDITIONAL route, not a proof of
Property C, not a proof that such obstructions exist, and not a settlement.
It must not be confused with the already-refuted arbitrary Best-leaf bound.

A fresh reference fetch failed with DNS resolution unavailable. The positive
bound audit still found only explicit hypotheses or restricted graph classes.
Spec.lean is unchanged and retains its original sorry. The earlier submission
of the unchanged file was rejected by verification, as the user reported.
No further submission was made and no background Lean process remains.

## Continuation: two parity-exchange shortcuts refuted externally

No original settlement or new Lean theorem in this continuation. Spec unchanged.
The following are exact EXTERNAL computations, not kernel-verified theorems.

1. Hull submodularity fails even along a minimum parity forest of a globally
Minimal graph. Let G=K3 join I4, hubs0,1,2, independent vertices3,4,5,6.
Let F={03,04,05,06}, a minimum parity correction and also Best; choose e=03,f=04.
The four hull values at G,G-e,G-f,G-e-f are 7,6,6,6, so
 h(G)+h(G-e-f)=13 >12=h(G-e)+h(G-f).
The raw numbers are instead7,6,6,5. The even base G-F has raw number3 but hull6.
Artifacts /tmp/minimum_parity_forest_submodularity.py,
 /tmp/minimum-parity-forest-submodularity.log and .json.
All32768 edge subsets of the15-edge host and all103 cycles were considered.
The full graph has proper-hull maximum6, confirming global Minimality externally.
This does not refute Best=minParity on globally Minimal graphs.

2. EVERY minimum parity correction being optimal is FALSE even on globally
Minimal graphs. G=K3,10 has number=hull14, proper-hull maximum13, BestSingles10,
minimum parity correction size10. The star F containing all ten edges at one
hub is a minimum parity correction (each of ten independent odd vertices
forces an edge), but G-F=K2,10 has number5. Thus this particular correction
has total cost10+5=15 >14. Another minimum correction is optimal (BestSingles10).
Artifacts /tmp/minimum_parity_not_every_optimal.cpp and executable,
 /tmp/minimum-parity-not-every-optimal.log.
This reused the exact three-hub orbit recurrence, checking19448 orbit states.
For the graphs K2,10 plus a star with a edges at the third hub, a=0..10,
raw numbers are5,6,7,8,8,9,10,11,12,13,14. Thus raw submodularity restricted to
this minimum forest also fails (at a=3,4,5), despite global Minimality of the
full host. No such universal submodularity rule may be used to prove the
still-UNPROVED EXISTENTIAL statement BestSingles=minParity on Minimal graphs.

A separate mathematical obstruction (not newly Lean-verified): a simple-path
packing pairing the four odd vertices of K7,4 cannot leave even residual
components each containing at most two odd vertices. There are only two
paths; their endpoints are on the four-vertex side, so each has length<=6,
and they cover<=12 edges. The claimed residual condition would force each
of the seven opposite vertices to have residual degree<=2, requiring the
paths to cover>=14 edges. This refutes an unrestricted partial-terminal
residual-separation shortcut, not the conjecture or a suitable selective rule.

The only new Lean-verified module in the recent continuation remains
VertexHullLossReduction. All parity tests above are external diagnostics.
No background job remains, and no further proof submission was made.

## Continuation: optimal-singleton subset deletion VERIFIED; Spec still unsolved

New module Submission/SingletonSubsetDeletion.lean compiles successfully,
with current .lake/build/lib/lean/Submission/SingletonSubsetDeletion.olean.
Log /tmp/singleton-subset-deletion.log; exit file contains 0. All four
principal axiom audits use only propext, Classical.choice, Quot.sound.
Namespace Erdos184Work.SingletonExchange:

- Optimal.delete_subset: for Optimal G F and T<=F, the cofactor G-T has
  Optimal (G-T) (F-T), and number(G-T)+|E(T)|=number(G).
- Optimal.extend_singletons: when singleton restoration has additive number,
  any optimal cofactor forest R lifts to R union T in the source.
- Best.delete_subset: secondary optimality also survives arbitrary deletion
  T<=F. No global minimality or saturation hypothesis is needed.
- Best.single_deletion_saturated: if G is globally Minimal and T<=F has
  exactly one edge, G-T is hull-saturated, retains Best (F-T), and its number
  is number(G)-1. Strict global Minimality of G-T is NOT asserted.
- Best.deletion_hull_gap: for nonempty T<=F in a globally Minimal source,
  value(G-T)+1 <= number(G-T)+|E(T)|. This bounds the possible hull/raw gap
  by |E(T)|-1; it does not set that gap to zero for multi-edge deletion.

This is genuine inheritance along the optimal SINGLETON subset. It must not
be confused with heredity of global minimality, or with inheritance after
arbitrary hull-maximizing core extraction. The known K3 join I4 star example
already has raw numbers 7,6,5 but hull values 7,6,6 along two singleton
edge deletions, so extending the one-edge saturation claim by iteration is
invalid. The even-core route likewise cannot assume a cycle cofactor is
even-minimal. No general selective vertex loss, core-rigidity, or linear
bound was proved. Spec.lean remains unchanged with its original sorry.
No further proof submission was made.

## Continuation: simultaneous high-connectivity/vertex-loss reduction VERIFIED

New module Submission/HighlyConnectedVertexLoss.lean compiles successfully;
current olean installed. Log /tmp/highly-connected-vertex-loss.log, exit file 0.
Principal axiom audits contain only propext, Classical.choice, Quot.sound.
Namespace Erdos184Work.HighlyConnectedVertexLoss:

- Property k C asks only that a globally Minimal G with DeletionConnected G k
  and |V|>2*k+1 have SOME vertex v with
    number G <= value(G.induce({v}^c)) + C.
  This is an explicit, still-UNPROVED hypothesis.
- uniform_of_property proves from it the general bound
    number G <= ((2*k+1)^2+C)*|V|.
  It combines separator induction with selective vertex deletion, using the
  order potential n-k. No preservation of connectivity by extraction or
  deletion is assumed. Small orders are handled by the square bound.
- asymptotic_of_property yields the original asymptotic proposition under
  that hypothesis.
- obstruction_of_asymptotic_failure: ORIGINAL FAILURE would force, for every
  k,C, a globally Minimal graph with DeletionConnected G k, order >2*k+1,
  and hull loss >C at EVERY vertex SIMULTANEOUSLY.
- number_le_induced_hull_add_degree is the elementary all-incident-edge bound.
- high_minimum_degree_obstruction adds degree(v)>C for every vertex to that
  same conditional obstruction. These graphs are NOT constructed or shown
  to exist unconditionally. The result does not settle the conjecture.

The previous SingletonSubsetDeletion module remains verified. The main gaps
are still genuine: no fixed high-connectivity selective-loss bound, no
sufficient Best-edge hull transfer theorem, and no general even-core rigidity
or separating-cycle theorem has been proved.

A small exact EXTERNAL query of the existing three-hub recurrence checked
full K3,t for t=4,7,10,13 and transfer of one right-side vertex to one hub.
The source numbers/hulls are 6,10,14,18, and transferred raw/hull values agree
with them (including the resulting pendant edge). This is not Lean evidence
or a general theorem. Artifacts /tmp/three_hub_transfer_query.cpp and
/tmp/three-hub-transfer-query.log; 228684 orbit states. No new counterexample
or original settlement follows.

Spec.lean is unchanged and still has its original sorry. No further original
submission was made. All launched builds and diagnostics have completed.

## Continuation review: no new settlement or verified theorem

Rechecked the unchanged original statement and reviewed the high-connectivity
vertex-loss reduction, global-minimal cycle-deletion connectivity, even-core
separating-cycle reduction, Best-forest structure, and prior path/fractional
routes. No unconditional bridge was obtained. In particular, the exact
cycle-deletion number identity still does not provide inheritance of
EvenMinimal, and the path/LP routes still lack the required conversion or
rounding theorem. No new Lean proof or external diagnostic was produced in
this continuation. Spec.lean retains the original sorry. It has not been
submitted again as a purported settlement.

## Continuation: exact three-hub family and failure of ALL optimal-remainder minimality VERIFIED

Original Spec remains unchanged and UNSOLVED. Five new modules (738 lines total)
compile successfully, with current oleans and clean principal axiom audits:
propext, Classical.choice, Quot.sound only. No proof of the original conjecture
or its negation was obtained or submitted. No jobs remain.

1. Submission/ThreeHubFullStructure.lean
   Namespace Erdos184Work.ThreeHubFullStructure.
   - Full G b: the independent-side vertex b is adjacent to all three hubs.
   - no_degree_two_of_full: a globally Minimal G <= K_(3,B) with one Full
     right vertex has NO degree-two right vertex. The proof constructs a
     square through any alleged degree-two vertex and uses
     Minimal.cycle_vertex_degree.
   - nonfull_degree_le_one: every nonfull right vertex then has degree <=1.
   Log /tmp/three-hub-full-structure.log, exit0.

2. Submission/ThreeHubCompleteNumber.lean
   Namespace Erdos184Work.ThreeHubCompleteNumber.
   - number_map_le and bipartite_sum_right: injective image and right-side
     splitting upper bounds.
   - explicit K3,2 / K3,3 / K3,4 bounds, then induction by adding three leaves.
   - exact_number: for EVERY n>=2,
       number(K3,n) = n + (n+2)/3.
   - upper_type transports the sharp upper bound to any finite right type.
   Log /tmp/three-hub-complete-number.log, exit0.

3. Submission/ThreeHubGlobalMinimal.lean
   Namespace Erdos184Work.ThreeHubGlobalMinimal.
   A globally Minimal bipartite three-hub graph is either acyclic, or consists
   of its complete K3,a part together with nonfull right leaves/isolates.
   minimal_upper gives
       number G <= |B| + max 2 ((a+2)/3),
   where a is the number of full right vertices.
   proper_upper: every proper subgraph of K3,3q+1 has number <=4q+1 for q>=2.
   complete_minimal: K3,3q+1 is globally Minimal for every q>=2.
   Proof extracts a minimal hull maximizer of an arbitrary proper subgraph,
   applies the structural upper bound, and uses a<3q+1. This is not merely a
   single-edge criticality assertion.
   Log /tmp/three-hub-global-minimal.log, exit0.

4. Submission/BestEvenRemainderObstruction.lean
   Namespace Erdos184Work.BestEvenRemainderObstruction.
   Source is K3,10 on Fin3 + Fin10, number14 and globally Minimal.
   The displayed forest assigns leaves0,1 to hub0; leaves2..5 to hub1;
   leaves6..9 to hub2. It has10 edges and is Best. The even remainder has
   number4, with an explicit partition of lengths6,6,4,4. Deleting its square
   hub1-leaf0-hub2-leaf1-hub1 preserves degree8 at hub0, so the remainder is
   NOT EvenMinimal. obstruction packages source minimality, Best, and failure
   of even-remainder minimality.
   Log /tmp/best-even-remainder-obstruction.log, exit0.

5. Submission/NoBestMinimalRemainder.lean
   Namespace Erdos184Work.NoBestMinimalRemainder.
   Stronger results for the SAME globally Minimal source K3,10:
   - any_best_not_evenMinimal / no_best_even_minimal;
   - optimal_singleton_count: EVERY Optimal split has exactly10 singletons;
   - every_optimal_best;
   - any_optimal_not_evenMinimal;
   - optimal_obstruction: source is globally Minimal but there is NO Optimal
     singleton forest whose even remainder is EvenMinimal.
   Proof: every optimal even remainder has20 edges and number4. Its three
   hub degrees are even, at most8, and sum to20, so one equals8. If that
   remainder were EvenMinimal, saturation at that hub would make its
   complement acyclic. That complement has12 edges on12 vertices, impossible.
   To force10 singletons in every optimum, use the known lower bound10 and
   |E(remainder)|<=6*number(remainder), obtaining5*singles<=54.
   Log /tmp/no-best-minimal-remainder.log, exit0. Both final audits are clean.

This refutes even the EXISTENTIAL inheritance shortcut "a globally Minimal
source admits an Optimal split with an EvenMinimal remainder". It does NOT
refute even-core rigidity, selective Best-edge hull comparison, or the original
conjecture. The exact family remains linear in its vertex count.

One targeted EXTERNAL diagnostic also finished:
 /tmp/three_hub_dominated_best_query.cpp and executable;
 /tmp/three-hub-dominated-best-query.log and .exit(0).
It used the exact orbit recurrence on1,961,256 three-hub states with at most16
independent-side vertices, testing DOMINATED HUB-TO-HUB Best singleton edges.
There were56,916 tests,2,652 on globally Minimal states; maximum dominated hub
sender degree on these Minimal states was1. Without Minimality it reached17.
This query does NOT test right-side senders, and does not prove a general
bounded-degree or hull-loss rule. It is not a Lean theorem.

Spec SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
The original sorry remains. No further original proof submission was made.

## Continuation: non-cut low-singleton-degree selection VERIFIED

Submission/NonCutSingletonLeaf.lean compiles with -M8500; current olean.
Log /tmp/noncut-singleton-leaf.log. Both displayed axiom audits contain only
propext, Classical.choice, Quot.sound.

Namespace Erdos184Work.NonCutSingletonLeaf:
- exists_noncut_low_forest_degree: for any forest F<=G in a finite nontrivial
  connected graph G, there exists v such that G-v is connected and
  Nat.card (F.neighborSet v)<=1.
- exists_noncut_low_optimal_degree and exists_noncut_low_best_degree:
  specializations using Optimal.acyclic.

Proof extends F to a maximal acyclic subgraph of G, hence a spanning tree,
then selects a leaf of that tree. This proves the previously promised
selection lemma. The selected vertex need not have forest degree exactly1.
It gives NO bound on ambient degree or raw-number/deleted-hull loss.

Reviewed existing minimal-core degree, parity, rigidity, and Best-edge
transfer reductions. No unconditional loss or uniform decomposition bound
was obtained. Spec remains unchanged with the original sorry; no complete
proof or disproof of Erdos184.erdos_184 is available. No new submission of the
incomplete Spec was made.

## Continuation: actual singleton leaves in the high-connectivity class VERIFIED

Submission/HighlyConnectedSingletonLeaf.lean compiles with -M8500; current
olean. Log /tmp/highly-connected-singleton-leaf.log, exit0. Principal axiom
audits use only propext, Classical.choice, Quot.sound.

Namespace Erdos184Work.HighlyConnectedSingletonLeaf:
- forest_has_leaf: every nonempty finite forest has a vertex of degree one.
  Proof takes a nontrivial connected component and transports a tree leaf.
- optimal_ne_bot: an Optimal singleton forest of a nonempty globally Minimal
  graph is nonempty, since a globally edge-critical even graph is empty.
- connected_after_singleton: DeletionConnected G 1 and Nontrivial V imply
  G-v is Connected for every v.
- exists_noncut_optimal_leaf: under these hypotheses, every Optimal forest
  has a vertex v with F-degree EXACTLY ONE, G-v connected, and G-degree odd.
- Property C is the UNPROVED selective loss hypothesis: in every sufficiently
  large Minimal graph with DeletionConnected G 1, some Best forest has some
  actual leaf whose raw-source versus deleted-hull loss is at most C.
- asymptotic_of_property: this hypothesis implies the original proposition.
- asymptotic_of_all_leaf_bound: a universal loss bound for all Best leaves in
  that class also implies the original proposition, using forest_has_leaf.

This does not establish a uniform loss bound. It does not assert that an
actual non-cut singleton leaf exists under mere ambient connectedness; the
one-vertex-deletion connectivity hypothesis in the new theorem is essential
to the proof given. The earlier arbitrary connected selection theorem still
only asserts forest degree at most one.

Re-examined Best-edge transfer, dominated terminal configurations, and the
previous block profiles. No new general hull comparison, bounded loss, or
original-conjecture disproof resulted. No new block-profile computation was
launched and no speculative block amplification was promoted to a theorem.
A bounded literature request still failed DNS resolution.

Spec.lean remains unchanged, original sorry present. No complete settlement
is available and the incomplete file was not submitted again.

## Continuation: direct deletion accounting reviewed; no new bridge

Reviewed the repair construction based on an optimum of G-v, the exact
singleton-subset deletion identities, positive-endpoint path completion,
and Best-edge contraction. The forest in an optimum of G-v need not be the
restriction of the source Best forest. No uniform control of that change
was proved. Nor was a source upper bound deduced from an arbitrary deleted
hull maximizer: such a maximizer may omit host edges which still need covering.
No new Lean theorem or original settlement resulted in this continuation.

One exact NON-LEAN binary-circuit diagnostic was run:
 /tmp/affine_best_contraction.py
 /tmp/affine-best-contraction.log (exit0, DONE)
For affine columns (2^d | x), x=0,...,2^d-1, d=2,3,4, it enumerates subsets,
circuit/singleton optima, secondary singleton counts, and arbitrary-subset
hulls. Distinguished element x=0 is contracted, giving projective columns
1,...,2^d-1. Eligible sources were strictly minimal subsets in which that
element can be a singleton in a secondary optimum. Counts: 7,57,1381;
maximum raw-source/contracted-hull loss1. HOWEVER, ALL eligible sources in
these three tests were independent sets (CYCLIC_ELIGIBLE=0). Source hulls
were3,4,5 respectively. Thus the pass supplies NO test of the difficult cyclic
core case, and is not evidence for a general graphical transfer theorem.

Spec remains unchanged with original sorry. No complete proof or disproof
has been obtained; no incomplete submission was made. No build or diagnostic
is left running.

## Continuation: tree-hitting and two-color completion revisited, still unproved

Reviewed PrescribedEndpointPaths, TwoColorInitialPacking, EndpointDefectStep,
EndpointSupportCompletion, and the saved tree-hitting-cycle proposal.
Prescribed positive endpoint multiplicities do not control endpoint pairings.
The existing endpoint-fan rotations do not have a proved two-color preservation
property, so ColorMaximal cannot simply replace uncolored Maximal in the
absorption proof. No general two-color completion proof was obtained.

Likewise, cutting tree edges and joining the resulting paths only supplies
closed trails. Refinement into simple cycles can produce tree-free cycles;
no valid bounded charging or termination argument eliminating them was found.
No new original-conjecture bridge, Lean theorem, or external diagnostic was
produced in this continuation. Spec retains the original sorry unchanged.
No proof/disproof was submitted, and no development job remains running.

## Continuation: single enhanced certificate completeness REFUTED — Lean verified

New current oleans, both built with -M8500 and clean principal axiom audits:
 Submission/CertificateNormalization.lean
 Submission/CertificateIncompleteness.lean
Logs /tmp/certificate-normalization.log and /tmp/certificate-incompleteness.log.
All displayed final axioms are propext, Classical.choice, Quot.sound.

ParityDegreeLower.Certificate G k A B O packages the enhanced independent-odd
lower bound crossing 2*|A|*(k-1), requiring A nonempty, A disjoint O,
B independent, and all B and O vertices odd. A and B may overlap.
- Certificate.erase_overlap: if k>=|V| and x in A intersect B, moving x
  from A to O preserves the certificate. Independence gives deg(x)+|B|<=n;
  odd degree gives |B|<n. The threshold gap cannot shrink. A singleton A
  overlapping B cannot be a certificate at k>=n.
- Certificate.exists_disjoint: minimize |A| to obtain a certificate with
  A disjoint B, with B unchanged.

CertificateIncompleteness.obstruction_with_order_bound strengthens the previous
ChainRing minimal compression obstruction by retaining number(R)>=|V|=25.
- exists_minimal_without_certificate: some globally Minimal graph on the
  25-vertex ChainRing.Vertex has number>=25 but NO single enhanced certificate
  at its exact decomposition number, even with overlapping A and B.
- not_complete_on_minimal: negates completeness for all Minimal graphs on
  that type. Proof normalizes a hypothetical certificate, applies the verified
  adjacent-transfer certificate preservation, and contradicts the target hull
  bound24.

This eliminates SINGLE-certificate completeness as a general route. It does
not refute blockwise/combined certificates, a restricted higher-connectivity
characterization, Best-edge hull transfer, or Erdős184 itself. No general
uniform decomposition bound or actual original counterexample was obtained.
Spec.lean remains unchanged with its original sorry. No incomplete proof was
submitted. Subsequent rereading of the transfer, fractional rounding, dominated
leaf and two-color endpoint arguments did not establish their missing bridges.

## Continuation: path gluing and dominated-leaf deletion rechecked; no settlement

No new main bound was obtained. Exact_endpoint_partition supplies at most n
simple paths, but joining their endpoints produces closed trails, not a cycle
partition with a proved linear bound on the number of simple refinements.
Endpoint multiplicities alone do not justify preserving marker transitions or
charging each resulting simple cycle to a different original endpoint.

One-step saturation observation (a direct consequence of existing lemmas, not
newly packaged in Lean): if G is globally Minimal and C is a simple cycle,
then number(G-C)=value(G-C)=number(G)-1. The upper hull bound follows because
all subgraphs of G-C are proper subgraphs of G. This does NOT imply G-C is
Minimal. Nor does it imply an arbitrary cycle in a Best even remainder is
additive there or leaves the old Best forest optimal. Best.delete_even requires
that additivity explicitly. Minimal core extraction need not retain the old
singleton forest, dominated-edge pattern, or connectivity after deleting the
selected vertex. Consequently this observation does not support the proposed
iteration of four-cycle deletion at a dominated Best leaf.

The degree<=3 proposal for dominated Best leaves of globally Minimal graphs
remains only bounded-order evidence (old order7 diagnostic), NOT a theorem.
No uniform selective hull-transfer or vertex-loss bound was established.
No external diagnostic or Lean build was left running. Spec.lean is unchanged
with its original sorry; no complete proof or disproof is available and no
incomplete proof was submitted.

## NEW structured obstruction: non-cut Best leaves can have unbounded loss

IMPORTANT STATUS: the GRAPH construction and its general proof below are
mathematical/external, NOT yet transported to Lean. Only its arithmetic is
Lean-verified in Submission/ParallelLeafArithmetic.lean (current olean, log
/tmp/parallel-leaf-arithmetic.log; audits propext and Quot.sound).
This is an auxiliary obstruction, NOT a disproof of Erdős184.

Artifacts:
 /tmp/parallel_noncut_leaf_certificate.py
 /tmp/parallel-noncut-leaf-certificate.log (exit0)
 /tmp/parallel-noncut-leaf-certificate.json
The script recomputes exact cycle/singleton optima and subgraph hulls for all
16384 edge-subgraphs of the 14-edge seven-vertex base, and verifies explicit
large-graph partitions and single-vertex-deletion connectivity for m=2,4,...,20.
It is an exact combinatorial check, not a floating-point search.

BASE B: vertices0,...,6, hubs0,1,2 forming a triangle, independent rights3,4,5,6,
all hub/right edges EXCEPT03. Terminals a=0, b=3.
Verified externally from all subsets and all34 simple a--b paths:
 (i) number(B)=value(B)=6, BestSingles(B)=3;
 (ii) min_P number(B-P)=6;
 (iii) every proper S<B has number(S)<=5 OR an a--b path P with
       number(S-P)<=5;
 (iv) every S<=B has number(S)<=6;
 (v) value(B-a)=5.
These agree with the earlier saved block profile data.

CONSTRUCTION G_m for EVEN m>=2:
Take m copies B_i, identifying all a_i to one vertex v. Keep all other block
vertices private. Add one new vertex z, all m connector edges b_i--z, and the
single closing edge e=v--z. Thus |V|=6m+2 and |E|=15m+1.

GENERAL LOWER ARGUMENT:
Every cycle containing z uses either e and one block terminal path, or two
connector edges and one terminal path in each of two different blocks. Each
block participates in at most one such cycle (its connector is unique).
Deleting all r cycles through z leaves in each block either B or B-P, each
with number>=6 by (i),(ii). All remaining pieces not incident to z are confined
to one block, since G-z is a wedge of the blocks at v. If s is the number of
singleton pieces at z, then 2r+s=m+1 and every decomposition has at least
6m+r+s >= 13m/2+1 pieces.

EXPLICIT OPTIMUM with 4m singletons and deg_F(v)=1:
Make block0 inactive. In it take singleton edges04,15,16, and cycles
 [2,1,3], [2,0,5], [2,4,1,0,6], plus its connector3--z as a singleton.
In each other block remove path P=[0,1,3], take singleton edges23,24,15,16
and cycles [0,2,1,4], [0,5,2,6]. Close the block1 path with its connector and e.
Pair remaining active blocks; each pair of paths plus their connectors is one
simple cycle through v,z. Total: 4m singleton edges and 5m/2+1 cycles,
hence number(G_m)=13m/2+1. The 4m private right vertices are independent and
all have odd degree3, so every partition needs at least4m singletons. The
explicit singleton forest is therefore Best, and v has forest degree exactly1.

GENERAL GLOBAL-MINIMALITY ARGUMENT using (iii),(iv):
For arbitrary R<=G_m, call a block heavy if its restriction S_i has number6
AND its connector is present. Every light block plus its optional connector
costs at most6. Each heavy block has a terminal path cofactor of cost<=6,
and cost<=5 if that heavy block is proper. Let h be the heavy-block count.
If e is absent, pair heavy paths, leaving one heavy block unpaired when h is
odd. The cost is <=6m+ceil(h/2)<=13m/2.
If e is present, use all heavy paths, pairing them and using e in a cycle
when h is odd, or e as a singleton when h is even. Cost is
 <=6m+floor(h/2)+1. If h<m this is <=13m/2. If h=m but R is proper, some heavy
block is proper, and its unit path-cofactor saving again gives <=13m/2.
Thus EVERY proper R has number strictly below number(G_m): G_m is globally
Minimal. This argument is not newly Lean-verified.

DELETION HULL AND CONNECTIVITY:
G_m-v consists of m copies of B-a, each joined to z by its connector; cycles
are confined to individual copies, and connectors are bridges. By (v), its
hull is exactly m*(5+1)=6m. A spanning tree attains this value.
G_m is 2-vertex-connected: delete v and the remaining blocks connect through z;
delete z and they connect through v; a deletion internal to a block leaves
that block connected (B is 2-connected), and if its port is deleted z still
connects through another block. Removing BOTH v,z disconnects the m blocks.
Therefore at the exhibited Best leaf v, even with G_m-v connected,
 number(G_m)-value(G_m-v)=m/2+1 is unbounded.

SCOPE: this refutes the proposed bound at EVERY Best leaf even in the
2-vertex-connected/global-Minimal class, not merely the old cut-vertex wedge
version. It does NOT refute selection of SOME favorable leaf, the dominated
Best-leaf bound (v is not dominated), Best-edge hull transfer, or a hypothesis
restricted to sufficiently higher connectivity. In this construction a
low-degree leaf elsewhere remains available. It does not settle Spec.

For m=2,4,6,8 the checked counts (vertices,number,deleted hull,loss) are
 (14,14,12,2), (26,27,24,3), (38,40,36,4), (50,53,48,5).
The source counts remain linear; ParallelLeafArithmetic.source_cost_linear
explicitly records this. Do not promote the auxiliary family to an original
disproof or describe its graph statements as kernel-verified.

Spec.lean remains unchanged with original sorry. No valid original proof or
disproof has been obtained or submitted. No diagnostic/build remains active.

## VERIFIED: half-degree hull loss at a non-cut vertex

Submission/NonCutHalfDegreeLoss.lean now compiles (exit0) with audits using
only propext, Classical.choice, Quot.sound. Log:
 /tmp/noncut-half-degree-loss.log
Current olean:
 .lake/build/lib/lean/Submission/NonCutHalfDegreeLoss.olean

Namespace Erdos184Work.NonCutHalfDegreeLoss:
 even_degree_bound: if G-v is Preconnected and degree(v) even,
   number G <= value(G-v) + degree(v)/2.
 half_degree_bound: if G-v is Preconnected,
   number G <= value(G-v) + (degree(v)+1)/2.
 loss_two_of_degree_le_four: non-cut degree <=4 gives hull loss <=2.
 degree_large_of_loss: non-cut hull loss >C implies degree(v)>2*C.

Proof: existing vertex-cycle cover captures all incident edges at even degree;
its complement has support avoiding v. At odd degree delete one incident edge,
apply the even case, and restore that edge as a singleton. Compilation fixes
normalize Fintype-dependent number/value/degree expressions; no mathematical
extra assumption was needed.

This is a positive degree-dependent estimate, NOT a uniform selective bound.
It does not settle Spec.lean, which is unchanged with its original sorry.

The same module additionally verifies high_minimum_degree_obstruction:
for any k>=1,C, FAILURE of the original conjecture implies a finite globally
Minimal graph G with DeletionConnected G k, |V|>2k+1, all vertex degrees>2C,
and hull(G-v)+C<number(G) for every vertex v. The universe of the existential
vertex type matches the universe quantified in the failure hypothesis.
Final build exit0, all four printed principal axiom audits clean; no warnings.
This improves the previous >C minimum-degree consequence, but constructs no
counterexample and gives no contradiction. The uniform selective vertex loss,
Best-edge hull comparison, and even-core structural gaps are still unresolved.
Spec.lean is unchanged; no complete proof/disproof obtained or submitted.
No build or diagnostic job was left running.

## VERIFIED: quantitative reduction to connected nonseparating even cores

New module Submission/NonseparatingCoreBudget.lean imports only the existing
ConnectedCoreObstruction module. It compiles (exit0) with principal audits
containing only propext, Classical.choice, Quot.sound. Log:
 /tmp/nonseparating-core-budget.log
Current olean:
 .lake/build/lib/lean/Submission/NonseparatingCoreBudget.olean

Namespace Erdos184Work.NonseparatingCoreBudget:
- component_budget: for C>=1, an estimate number(R)+C*components(R)<=C*n
  on all nonseparating even-minimal cores propagates to ALL even G on the
  same vertex type. Extract an even-minimal core; if it has a separating
  cycle, delete it at unit number cost, which is paid by component increase.
- number_le_component_sum: subadditivity over actual connected components.
- Property C: every connected even-minimal graph with no separating cycle
  has number<=C*(n-1). This remains an explicit UNPROVED hypothesis.
- terminal_component_budget sums Property over connected components,
  using verified transport of even-minimality and nonseparation.
- asymptotic_of_property: Property C, C>=1, implies the original proposition.
- large_ratio_obstruction: FAILURE of the original implies, for EVERY B,
  existence of a connected, 4-edge-connected even-minimal graph G with no
  separating cycle, number(G)>=4, and number(G)>B*|V(G)|.
  This is stronger than the earlier mere existence of a number>=4 core.

This module supplies no terminal estimate and constructs no counterexample.
The general core-rigidity / nonseparating-core bound remains unresolved.
Regular-matroid or fractional-exactness heuristics were reconsidered but not
promoted to lemmas: existing tests and small-optimum rigidity do not imply
arbitrary-optimum rigidity or fractional rounding.
Spec.lean remains unchanged with its original sorry. No original proof or
disproof obtained or submitted. No build or diagnostic remains active.

## VERIFIED: simultaneous high-degree and nonseparating even-core reduction

Submission/HighDegreeNonseparatingBudget.lean now compiles (exit0), importing
NonseparatingCoreBudget and MinimalBridgeRestoration. Principal audits list
only propext, Classical.choice, Quot.sound. Log:
 /tmp/high-degree-nonseparating-budget.log
Current olean:
 .lake/build/lib/lean/Submission/HighDegreeNonseparatingBudget.olean
Namespace Erdos184Work.HighDegreeNonseparatingBudget:
- low_degree_descent: for even G and supported v with degree(v)<=2C, there
  exists a proper even R<=G with strictly more connected components and
  number(G)<=number(R)+C. Proof prunes every cycle incident to v from a cycle
  partition. The removed family has degree(v)/2 pieces; v becomes isolated.
- component_budget: induction with C*component-count credit simultaneously
  handles separating-cycle deletion and this low-degree pruning.
- Property C: an UNPROVED bound number(G)<=C*(n-1) only on connected,
  nonseparating even-minimal G whose supported degrees are all >2C.
- asymptotic_of_property: for C>=1 this Property implies the original.
- large_ratio_high_degree_obstruction: FAILURE of the original implies,
  for EVERY B, a connected nonempty even-minimal G, with no separating cycle,
  4-edge-connectivity, number>=4, number(G)>B*|V(G)|, and EVERY degree>4B+2.
  This combines the quantitative ratio obstruction with high minimum degree.

No terminal Property is established, and no graph satisfying this conditional
obstruction is constructed. The original remains UNSOLVED.

The support/rank charge was rechecked before this work. The verified
SpanningCoreObstruction already shows a proper cycle cofactor can stay
connected, spanning, rigid, and even-minimal; arbitrary descent cannot be
charged to a vertex or component loss. A favorable-selection or amortized
argument remains missing. No false universal charge is used above.

Submission/ProbeBudgetDegree.lean has failed #checks and is not imported;
it is only a development probe. All actual new module builds are clean.
Spec.lean is unchanged with the original sorry. No original proof/disproof
obtained or submitted, and no build/diagnostic job is left running.

## Further local-exchange audit: no settlement

Reviewed MaximumTripleThreshold, MaximumCoreFamilies, the square-extraction
route, and ExactEdgeDeletion against the newly combined high-degree,
nonseparating even-core obstruction. No local exchange preserving the MINIMUM
number on a proper even subgraph was established. The maximum-family triple
threshold cannot be substituted for such a step. Nor does EvenMinimal G
imply global edge-Minimal(G-e); the existing two-triangle obstruction still
rules out the unrestricted implication. The nonseparating/high-degree
restricted version was not proved.

No additional theorem or computational search was produced in this audit.
Latest checked result remains HighDegreeNonseparatingBudget. Spec unchanged
with original sorry; no original proof or disproof and no settlement submitted.
No development job left running.

## Literature/path-conversion continuation: original unresolved

Fresh retrieval attempts for erdosproblems.com/184 and export.arxiv.org failed
DNS resolution. A direct-address export.arxiv.org request using --resolve timed
out after20s. No current literature result was retrieved or used.

Rechecked BoundedEndpointPaths, PrescribedEndpointPaths, UniversalBound,
UniversalEvenCycles, and the two-color endpoint notes. Exact positive endpoint
multiplicities do not preserve pairings or furnish a bound on simple-cycle
refinement of joined closed trails. The two-color completion theorem remains
unproved here, and no original-conjecture bridge from it was established.
No path/trail conversion shortcut was asserted. No new Lean theorem in this
continuation. Spec unchanged with original sorry; no original proof/disproof,
no submission, and no active build or external computation remains.

## Edge-excess continuation: no unconditional core estimate

Reviewed CoreExcess, IncidenceExcess, ShortCycles, SquarePieces, and the
recorded binary/regular-matroid models. The sufficient inequality
 |E(R)| <= C*|V(R)| + 2*number(R)
for arbitrary even-minimal R is still UNPROVED. Its checked rigid-core
version cannot be applied without first proving rigidity. Short-cycle
subfamily bounds do not bound all cycle lengths or make square cofactor
minimality/accessibility automatic. No cycle-space dimension shortcut or
regular-matroid rank estimate supplying the graph inequality was obtained.
No new Lean theorem or external search in this continuation. Original Spec
unchanged with sorry; no proof/disproof obtained, no settlement submitted,
and no development job remains running.

## VERIFIED: square-family optimality-defect and discarded-graph budget

New Submission/SquareDiscardBudget.lean imports SquarePieces and
MinimalBridgeRestoration, compiles exit0, and principal audits use only
propext, Classical.choice, Quot.sound. Log /tmp/square-discard-budget.log;
current olean .lake/build/lib/lean/Submission/SquareDiscardBudget.olean.
Namespace Erdos184Work.SquareDiscardBudget:
- square_union_number_le: any edge-disjoint cycle family A has
  number(union A)<=|A| (the name is used in the square context).
- squares_le_order_add_defect: for an edge-disjoint square family A,
  |A| <=9*n +5*(|A|-number(union A)). No minimum-family hypothesis.
  This follows from the checked 5*number(H)<=|E(H)|+9*n estimate.
- square_discard_bound: if G is the edge-disjoint union of square union S,
  discarded J, and final R, and number(G)=|A|+number(R), then
  |A|<=9*n+5*number(J).
- total_discard_bound: with number(R)<=6*n, obtain
  number(G)<=15*n+5*number(J).

The endpoint conditions are explicit; this module does not construct or
formalize an entire extraction chain. No O(n) bound on number(J) is supplied.
The remaining discarded-graph term may NOT be omitted or charged to vertices
without a new theorem. Thus this quantifies the existing gap rather than
settling the original conjecture. Spec remains unchanged with original sorry;
no original proof/disproof or settlement submission. No job remains active.

## Discard-selection continuation: no missing selection theorem proved

Investigated selecting the square-deletion/core-extraction chain so that the
UNION of discarded edges is C4-free. Combined with SquareDiscardBudget and
the checked C4-free decomposition bound this would suffice, but no such
selection argument was established. exists_even_minimal_core preserves the
number and minimizes an even subgraph; it gives no restriction on cycles
in the discarded difference. Restricting each individual discard separately
would also not establish C4-freeness of their union. No extra hypothesis was
silently dropped and no theorem of this kind was added.

No new Lean result in this continuation. Spec unchanged with original sorry;
no original proof/disproof, no settlement submission, no active computation.

## Continuation audit: no settlement and no new theorem

Re-read the exact Spec and the latest parity, vertex-loss, and even-core results.
The existential minimum-parity/Best equality is refuted for hull-saturated
(non-Minimal) chain graphs; its globally Minimal restriction remains unproved.
Neither equality nor a submodularity argument was assumed.

The half-degree non-cut bound remains degree-dependent. It does not give a
uniform selective vertex-loss bound. The cycle-only fractional O(n) theorem
still lacks a justified integral-rounding step on even-minimal cores. The
maximum-family rigid-triple theorem has a fixed threshold of three; it cannot
be extended to arbitrary decomposition number by the available arguments.
No new general structural implication was established during this audit.

No new Lean theorem, proof of the original, or disproof of the original was
obtained. Spec.lean is unchanged with its original sorry. No verification
submission was made and no background job was started in this continuation.

## VERIFIED: actual square extraction and strict core descent

New Submission/SquareExtractionAccounting.lean compiles with current olean:
 .lake/build/lib/lean/Submission/SquareExtractionAccounting.olean
Log: /tmp/square-extraction-accounting.log. All three principal axiom audits
contain only propext, Classical.choice, Quot.sound. No build remains active.
Namespace Erdos184Work.SquareExtractionAccounting:

- exists_extraction: for every even G, constructs edge-disjoint even S,R <= G
  and k, with R even-minimal and square-free, |E(S)|=4*k, and
  number(G)=k+number(R). The construction recursively deletes squares and
  extracts cores. The theorem's type gives S's evenness and exact edge count;
  it does not expose a Finset square partition as an additional conclusion.
- exists_discard_budget: defines the ENTIRE discarded graph J=G\(S union R).
  It is even, J<=G, and
    number(G) <= 15*n + 5*number(J),
    |E(J)| + 4*number(G) <= |E(G)| + 24*n.
  This closes the old construction gap behind SquareDiscardBudget's abstract
  endpoint hypotheses, while keeping the discarded term explicit.
- core_descent: if G is even-minimal and number(G)>6*n, extracting a core
  inside J gives an even-minimal R<=G with number(R)<number(G), and
    number(G) <= 15*n + 5*number(R),
    |E(R)| + 4*number(G) <= |E(G)| + 24*n.

No uniform linear bound follows just by iterating this recurrence: the
factor-five number loss is not offset by a proved vertex budget. Reconsidering
the square-cofactor obstruction did not establish accessibility. Neither the
already refuted unrestricted square marginal inequality nor an unproved
extension of the rigid-triple threshold was used.

Spec.lean is unchanged with its original sorry; SHA256 remains
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.
No complete original proof/disproof obtained and no submission made.

## Continuation: dominated-neighbor local repair investigated; no settlement

No new Lean theorem in this continuation. The new candidate below is UNPROVED.
All computations here are exact external diagnostics, not kernel verification.

Correction to an initial plan: NestedBound handles NestedAlongEdges, whereas
Best-edge compression yields only NestedSingletons. The weaker terminal class
still needs its own bound; the compression comparison would not alone complete
that route using the current library.

Candidate local even repair: let E be even, with distinct u,v,a,b,c, with
u,v nonadjacent, all six edges from {u,v} to {a,b,c} present, no edges among
{a,b,c}, and N_E(v) subset N_E(u). Define
 T = E - {ua,vc} + {uv,ab,bc}.
Question: is number(T) <= number(E)+1 always? No proof was obtained.
If true, this would rule out a path a-b-c in F[N_G(v) minus {u}] when
Best G F, F.Adj u v, and v is dominated by u: replace the three singleton
edges uv,ab,bc by ua,vc. The even remainder becomes T, the singleton count
falls by one, and the asserted repair inequality would keep the total cost
optimal. This reasoning is conditional on the unproved repair inequality.
Even that local structural conclusion is not a uniform decomposition bound.

Exact external tests:
- /tmp/dominated_best_twoedge_path.cpp and executable.
  All graph DP computes (minimum pieces, least singles among optima), hull,
  and global Minimality. Then tests fixed marked singleton edges 01,23,34,
  required K_{2,3} edges from 0,1 to 2,3,4, and domination of 1 by 0.
  Simultaneous Best exposure is checked by
    c(G-marked)+3=c(G), best(G-marked)+3=best(G).
  /tmp/dominated-best-twoedge-path7.log: 2304 dominated candidates, zero Best.
  /tmp/dominated-best-twoedge-path8.log: 221184 candidates, zero Best.
- /tmp/dominated_even_repair.cpp and executable test the candidate inequality
  directly on even graphs, using exact recursive cycle-partition DP.
  /tmp/dominated-even-repair8.log: 896 configurations, zero failures.
  /tmp/dominated-even-repair9.log: 81920 configurations, zero failures.
  The six required and four forbidden edges are fixed up to relabeling.
  No arbitrary-order conclusion follows.

A supporting shortcut was ruled out: arbitrary simple smoothing can INCREASE
minimum number. Exact order-seven tables are /tmp/decomposition-tables-7.bin,
created by /tmp/local_even_repair_check.cpp, with log
/tmp/local-even-repair-check7.log. One even source has edges
  01,02,03,04,13,15,16,23,25,26,34,
number 2. Replace edges 01,02 by 12: target number 3. Vertex 1 had degree4
in the source, so even saturation of that root in a chosen optimum does not
justify a count-preserving smoothing. Merely sliding 02 to12 while retaining
01 gives number4, so a general loss-one edge-slide upper bound fails too.
These are external certificates, not newly Lean-formalized results. They do
not refute the candidate dominated repair, which has extra hypotheses.

No proof of dominated Best-leaf bounded hull loss, Best-edge hull transfer,
or the original conjecture was obtained. Spec.lean remains unchanged with
its original sorry. No jobs remain active and no proof submission was made.

## Continuation: two local-repair obstructions independently checked

The exact Python cycle-partition recursion /tmp/check_repair_examples.py
independently confirms the earlier C++ double-smoothing result and the
explicit unrestricted-repair obstruction. Log: /tmp/check-repair-examples.log.
These are external exact computations, NOT Lean proofs.

1. Dominated double smoothing is FALSE. Vertices u=0,v=1,a=2,b=3,c=4.
Source E edges:
  02,03,04,05,12,13,14,15,27,28,37,38,45,46,56.
It is even, has N(v) subset N(u), and contains the required K_(2,3),
with a,b,c independent. Source number=2. Deleting 02,03,13,14 and
adding23,34 gives number=3. This refutes the stronger smoothing proposal.
The actual repair (delete02,14; add01,23,34) has number3 on this source,
so the original candidate number(T)<=number(E)+1 survives this example.
The original C++ logs are /tmp/dominated-double-smoothing8.log (896 tests,
no failure) and /tmp/dominated-double-smoothing9.log (failure at1571).

2. Unrestricted repair is FALSE. Source E edges:
  02,03,07,08,13,14,17,18,26,35,36,45.
Source number=2, with a partition into cycles
  3-0-7-1-4-5-3 and 3-1-8-0-2-6-3.
Delete02,14 and add01,23,34. Target number=4: triangles3-2-6-3 and
3-4-5-3 are separate blocks; the remaining block is four internally
vertex-disjoint 0--1 paths (01,0-3-1,0-7-1,0-8-1), requiring two cycles.
The source LACKS04 and12, so this is not a counterexample to the K_(2,3)
or dominated repair candidate. It also refutes unrestricted endpoint-
preserving path reassembly of the kind considered in the preceding context.

Same-cycle special case (mathematical observation only): if an optimum E
partition exposes a cycle segment a-u-b-v-c, replacing it by a-b-c and
adding triangleu-b-v gives the desired increase at most one. There is no
proved general optimal-cycle exposure rule; global Minimality of G does
not provide that exposure in E=G minus its chosen Best singleton forest.

No new Lean theorem or original settlement. Spec remains unchanged/UNSOLVED.

## Continuation: core-accounting audit and five-hub guard against a false lead

No original settlement and no new Lean theorem. The square-extraction
recurrence still has number(G)<=15*n+5*number(R) with only strict decrease
of number(R); it has no proved vertex credit. The minimum-degree route for
globally Minimal graphs remains unresolved, not implied by the old density
obstructions and not refuted by the following full-graph examples.

Exact structural guard (external, not Lean): K_(5,8) is NOT globally Minimal.
/tmp/five_hub_degree_guard.py verifies an explicit partition into four
8-cycles and eight singletons. Parity on the eight right vertices forces at
least eight singletons, and cycle length<=10 gives the matching lower bound
number=12. A proper subgraph is K_(3,7) plus three pendant edges, with number
10+3=13 by the already established three-hub formula and bridge additivity.
Log: /tmp/five-hub-degree-guard.log. Thus its minimum degree5 cannot be used
as a globally Minimal example. More generally, a full host's minimum degree
must not be attributed to an extracted globally minimal subgraph.

A separate exact construction checks K_(5,8) minus the two edges from the
last right vertex to hubs0,1: it has a partition into three10-cycles and
eight singletons. Script /tmp/five_hub_near_complete.py, log
/tmp/five-hub-near-complete.log. This is only an upper-bound certificate,
not a global-minimality computation or a proof for all proper subgraphs.

No bound on minimum degree of all global cores, no square-accessibility or
discard-budget theorem, and no contradiction to the conditional high-degree
obstructions was obtained. Spec remains unchanged with its original sorry.

## VERIFIED: unrestricted local repair obstruction

Submission/UnrestrictedRepairObstruction.lean (196 lines) compiles with -M8500.
Current artifact:
 .lake/build/lib/lean/Submission/UnrestrictedRepairObstruction.olean
Log /tmp/unrestricted-repair-obstruction.log, exit file contains0.
Both printed principal audits list only propext, Classical.choice, Quot.sound.
Namespace Erdos184Work.UnrestrictedRepairObstruction:
- source_even and source_number: the previously recorded nine-vertex source
  is even with number2, certified by two six-cycles and a degree lower bound.
- target_number: repaired target has number4, using two triangle blocks of
  number1 and a four-path two-hub block of number2. One-vertex block additivity
  is applied twice; no computational minimum-partition oracle is assumed.
- target_repair identifies the target exactly as
  (source minus {02,14}) union {01,23,34}.
- obstruction packages the four required old edges02,03,13,14, absence of
  the three new edges, evenness, and strict failure of the loss-one estimate.
- missing_common_edges proves04 and12 are absent. Thus the actual K_(2,3)
  dominated repair candidate is NOT refuted.

The endpoint-path audit did not close colored completion or tree-hitting
cycle conversion. Uncolored endpoint rotations change endpoint pairings and
can change their colors; the existing maximization proof cannot simply be
reused with ColorMaximal. No original O(n) bridge was established.

Spec.lean is unchanged, with the original sorry. No original proof/disproof
has been submitted. No live Lean compilation or diagnostic remains.

## Continuation: optimal-remainder dual criterion and a three-hub family VERIFIED

Original Spec remains unchanged and UNSOLVED. Two new auxiliary modules compile
with current oleans and principal audits listing only propext, Classical.choice,
and Quot.sound. No original proof/disproof has been obtained or submitted.

1. Submission/ThreeHubOptimalRemainders.lean
   Namespace Erdos184Work.ThreeHubOptimalRemainders.
   Source(q) is K_(3,3q+1). For q>=1, EVERY Optimal singleton split F has
     |F|=3q+1, number(source\F)=q+1, |E(source\F)|=6q+2.
   Thus every Optimal split is Best. There is a hub of degree 2q+2 in the
   remainder. Half weight on its incident edges is a cycle-upper dual with
   total q+1, exactly the integral cycle number. `optimal_exact_dual` proves
   that certificate directly; no numerical LP or unproved rounding is used.
   For q>=3 every Optimal remainder is NOT EvenMinimal, NOT CycleCritical,
   and NOT CycleRigid. `family` packages these conclusions with global
   Minimality of the source and existence of a Best split.
   The nonminimality proof deletes a saturated hub: the remaining graph has
   4q edges on 3q+3 vertices and hence cannot be acyclic. Cycle-criticality
   together with exactness would force rigidity, contradicting nonminimality.
   Log /tmp/three-hub-optimal-remainders.log, exit file contains0.
   Minor warning: an unused hypothesis on remainder_edge_bound; no sorryAx.

2. Submission/OptimalRemainderDualCriterion.lean
   Namespace Erdos184Work.OptimalRemainderDualCriterion.
   HasExactOptimalRemainder G means SOME Optimal split F (not necessarily
   Best) has a cycle-upper signed dual w on G\F with total>=number(G\F).
   This exactness hypothesis is NOT proved for arbitrary global cores.
   - number_bound: this property gives number(G)<=3*(|V|-1).
     Proof: signed cycle-only dual bound gives remainder number<=2*(|V|-1),
     and Optimal.acyclic bounds singleton count by |V|-1.
   - bound_of_minimal_exactness: it suffices to assume the property on every
     globally Minimal graph; extract a minimal arbitrary-subgraph maximizer.
   - asymptotic_of_minimal_exactness: the hypothesis implies the full original
     asymptotic proposition, with uniform constant3.
   - obstruction_of_asymptotic_failure: original failure forces a globally
     Minimal graph with NO dual-exact Optimal remainder.
   Log /tmp/optimal-remainder-dual-criterion.log, exit file contains0.
   This is a CONDITIONAL sufficient criterion, not an original settlement.

New targeted EXTERNAL diagnostic (not Lean checked):
 /tmp/catalogue_best_even_export.cpp and executable
 /tmp/catalogue-best-even-export.txt/.log/.exit(0)
 /tmp/catalogue_best_even_fractional.py
 /tmp/catalogue-best-even-fractional.log/.exit(0)
On the stored1201-graph global-core catalogue,84 graphs were cyclic. Their
4176 Best even remainders ALL have number equal to the sum, over vertex blocks,
of half the maximum block degree. Thus all were certified fractionally exact
by degree bounds; zero LPs were needed. This is finite evidence ONLY, and does
not prove arbitrary-core exactness. The input is the earlier external catalogue
/tmp/catalogue-core-parity-input.txt, not a new kernel classification.
The nonminimal block K3 join I4 minus03 was also checked separately: all7 of
its Best remainders meet the same degree bound; this supplies no minimality
claim about that block. See /tmp/block-best-even-fractional.log.

Further mathematical review did not close the general exactness, rigidity,
selective vertex-loss, or discard-budget gap. Do NOT equate exactness with
EvenMinimal/CycleCritical/CycleRigid; the new infinite family separates them.
No live compilation or diagnostic remains. Spec SHA256 is still
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Continuation: maximum-singleton choice does NOT force block-degree saturation

Original Spec remains unchanged and UNSOLVED. No new Lean theorem or original
settlement was obtained in this continuation. The following are EXACT EXTERNAL
finite checks and the stated mathematical block-separation argument, NOT Lean
verification. They address auxiliary simplifications, not Erdős184 itself.

A secondary choice opposite to Best was examined: MAXIMIZE singleton count
among all minimum decompositions, equivalently minimize the cycle count.
On the stored1201-graph catalogue,84 cyclic sources had4758 such remainders,
all degree-certified exact. Their cycle counts were2 for71 sources and3 for13
sources (Best counts had been3 and4 respectively). Every source edge appeared
as a singleton in SOME maximum-singleton optimum in this small catalogue.
Neither apparent structural property holds generally, as the next construction
shows. External files:
 /tmp/catalogue_max_singleton_export.cpp and executable
 /tmp/catalogue-max-singleton-export.txt/.log
 /tmp/catalogue_max_singleton_fractional.py
 /tmp/catalogue-max-singleton-fractional.log

STRUCTURED SOURCE, vertices0..12:
Take two copies of B=K3 join I4 minus03, with maps
 [0,1,2,3,4,5,6] and [3,7,8,9,10,11,12], then add edge09.
Source has29 edges and13 vertices. The seven-vertex block facts were rechecked
independently by exact DP on all16384 edge subsets:
 - number(B)=hull(B)=6;
 - maximum singleton count in an optimum of B is4 (Best count is3);
 - minimum number(B-P), over terminal0--3 paths P, is6;
 - maximum optimal singleton count among these cofactors is5;
 - if H<=B has number6, it has a terminal path and minimum cofactor number<=6;
   equality of that path minimum with6 occurs ONLY for H=B.

These finite facts give a mathematical global-minimality proof for the source:
A decomposition either uses09 as a singleton, with cost>=1+6+6=13, or uses one
cycle through09. That cycle traverses a terminal path in each B, and all other
cycles are block-local, again giving cost>=1+6+6=13. Both bounds are attained.
For any proper subgraph, if09 is absent the bound is12. If a block has number
<=5, use09 as a singleton for bound12. Otherwise both block numbers are6 and
at least one block is proper: that block has a terminal-path cofactor of number
<=5, and the other has one of number<=6. Removing the corresponding closing
cycle gives total<=12. Thus the full source is globally Minimal.
This argument and its finite base verification are NOT formalized in Lean.

The same profiles show the maximum singleton count is
 max(1+4+4,5+5)=10.
If09 is singleton, an optimum has at most9 singleton pieces. Hence09 is NEVER
a singleton in a maximum-singleton optimum, despite global minimality. Do NOT
assume that every edge is exposable with this secondary optimum preserved.

Exact cycle-space DP of the13-vertex source independently found:
 - number13;
 - optimal singleton counts7,8,9,10, respectively with49,364,816,576 remainders;
 - all576 maximum-singleton remainders have19 edges, are biconnected on all13
   vertices, and have maximum degree4, MINIMUM cycle count3 and MAXIMUM5.
Thus ALL of these remainders are nonrigid and fail block-degree saturation:
the sum of half maximum degrees over vertex blocks is2, not3.
This refutes the proposed existence shortcut for maximum-singleton optima,
not just its universal variant (subject to the external block argument above).

Dual exactness nevertheless survives:
 - all1805 optimal remainders are exact;
 -361 were certified by block degrees;
 -1444 LP solutions had rational duals reconstructed and checked EXACTLY:
   every simple cycle has weight<=1 and total edge weight is the known integer
   minimum. So the conclusion is not merely a floating-point equality.
The HasExactOptimalRemainder hypothesis from OptimalRemainderDualCriterion
remains UNPROVED/UNREFUTED on general global cores. Maximum-singleton selection
has not supplied its missing proof.

Principal artifacts:
 /tmp/max-singleton-chain-input.txt
 /tmp/max-singleton-chain-export.txt/.log/.exit(0)
 /tmp/max_singleton_chain_rigidity.cpp and executable
 /tmp/max-singleton-chain-rigidity.txt/.log
 /tmp/max_singleton_chain_certificate.py
 /tmp/max-singleton-chain-certificate.log/.json/.exit(0)
 /tmp/max-singleton-chain-fractional-exact.log
 /tmp/all_optimal_chain_export.cpp and executable
 /tmp/all-optimal-chain-export.txt/.log
 /tmp/all_optimal_chain_fractional_exact.py
 /tmp/all-optimal-chain-fractional-exact.log/.exit(0)
The JSON has an explicit maximum-singleton forest, a3-cycle and a5-cycle
partition of its even remainder, and a nonnegative half-integral exact dual.

No live diagnostic or compilation remains. Spec SHA256 is unchanged:
509244f56c6c2b5f1249af332dadaf0f83b8abc75bab2a209334179fc909a8e5.

## Continuation: nonnegative duals on maximum-singleton remainders have UNBOUNDED gap

Original Spec remains unchanged and UNSOLVED. This entry gives a mathematical
family argument with exact EXTERNAL finite local certificates, NOT Lean proofs.
It refutes a proposed auxiliary restriction, not the original conjecture and
not HasExactOptimalRemainder (which allows a different Optimal split and signed
weights).

Let G_m be a chain of m copies of B=K3 join I4 minus03, with terminal3 of each
copy identified with terminal0 of the next, plus one closing edge between the
outer terminals. The finite block facts in the preceding entry imply:
 - |V(G_m)|=6m+1 and number(G_m)=6m+1;
 - G_m is globally Minimal, by exactly the preceding block-separation argument;
 - maximum optimal singleton count is max(4m+1,5m), hence5m for m>=2;
 - every maximum-singleton optimum for m>=2 places the closing edge in a cycle,
   and its even remainder has number m+1.
Proof of the maximum: closing-edge-singleton route has at most1+4m singletons;
closing-cycle route has at most5m. Both are attained from the block profiles.

For the closing-cycle route, each block's local remainder is the edge-disjoint
union of one terminal path P and one simple cycle C, leaving5 singleton edges.
An INDEPENDENT exhaustive enumeration of the34 terminal paths and69 cycles of
B gives exactly24 such local edge sets (the same24 types seen in the earlier
13-vertex computation). Every one of the24 is covered by THREE simple terminal
paths, with overlaps allowed. This finite fact is now explicitly checked and
its path certificates saved. Gluing the three paths through all blocks and
closing each with the closing edge gives THREE SIMPLE CYCLES covering the
entire even remainder of ANY maximum-singleton optimum of G_m.

Therefore any NONNEGATIVE cycle-upper dual on such a remainder has total<=3,
whereas its integral cycle number is m+1. For m>=3 no maximum-singleton optimum
admits a nonnegative exact dual. The additive gap is at least m-2 and the
integral/nonnegative-dual ratio is unbounded. This refutes even the existential
nonnegative-exactness restriction within maximum-singleton optima.
It does NOT refute unrestricted signed exactness or the existential criterion
on SOME Optimal remainder: the closing-edge-singleton route with Best local
B splits has positive degree certificates blockwise and is itself Optimal.

Explicit m=3 certificate (19 vertices, source43 edges):
 local remainder edges
  02,05,06,12,14,15,16,23,24.
 Local covering paths:
  0-2-3;
  0-5-1-4-2-3;
  0-6-1-2-3.
 Maps of the three blocks:
  [0,1,2,3,4,5,6],
  [3,7,8,9,10,11,12],
  [9,13,14,15,16,17,18].
 Closing edge:0--15.
 The even remainder has28 edges and143 simple cycles. An explicit4-cycle
 partition consists of the global cycle using the second displayed path and
 the local square0-2-1-6-0 in each block. An exact SIGNED dual is half a star at
 each of vertices2,8,14 and weight-2 on the closing edge. Its total is4 and
 every simple cycle was checked to have weight<=1. The3-cycle covering repeats
 some edges, so it is NOT an edge-disjoint decomposition.

Artifacts:
 /tmp/max_singleton_nonnegative_family.py
 /tmp/max-singleton-nonnegative-family.log/.exit(0)
 /tmp/max-singleton-local-three-path-covers.json
 /tmp/max-singleton-nonnegative-family-certificate.json
All finite checks use exact integer/rational comparisons. The generic source
minimality and max-singleton formulas use the described mathematical block
argument; no Lean transport has been written. No new Lean file, original
proof/disproof, or submission was produced. No live jobs remain.

## Continuation: unrestricted optimal exactness also fails in the nongraphic binary example

Original Spec remains unchanged and UNSOLVED. No new Lean theorem or original
settlement was produced. The optimal-remainder exactness criterion was reviewed;
no graph-specific existence proof follows from the existing singleton exchanges.

The exact external PG(3,2)-minus-column1 certificate was rerun. Enumeration of
ALL xor-zero remainders yields exactly seven Optimal splits, all with two
singletons. Thus the previously documented fractional gap12/5<3 concerns every
Optimal remainder, not merely every Best remainder.

There is also a short independent count argument: the source has14 elements,
number5, and all circuits have size at most5. If an optimal partition has s
singletons, then14-s<=5*(5-s), giving s<=2. The total syndrome is1, which is
not a source column, so s=0 and s=1 are impossible. Therefore s=2, leaving
precisely the seven pairs {a,a xor1}. Their exact uniform48-circuit fractional
certificates (coefficient1/20) were rechecked by the existing script
/tmp/projective_best_gap_certificate.py. These are exact external calculations,
NOT Lean proofs. This is a nongraphic binary matroid, NOT a counterexample to
Erdos184 or to the graph-specific HasExactOptimalRemainder criterion.

Consequently singleton exposure plus generic binary-circuit properties cannot
prove that criterion; graphic structure must enter essentially. No universal
graphical signed-dual existence result was established. No development process
remains active, and no incomplete original settlement was submitted.

## Continuation: small-correction exactness VERIFIED; generic edge-exposure shortcut refuted

Original Spec remains unchanged and UNSOLVED. No original settlement.

NEW LEAN RESULT: Submission/EdgeCriticalSmallCorrection.lean (current olean)
compiles with only propext, Classical.choice, Quot.sound. Log:
/tmp/edge-critical-small-correction.log, exit file0.
- delete_at_most_one_to_even: deleting at most one edge to obtain an even
  graph lowers number by exactly the number of deleted edges; no criticality.
- delete_at_most_two_to_even: the same for at most two edges if the source
  is EdgeCritical (every edge optimally exposable as a singleton).
- optimal_of_card_le_two: EVERY parity correction of size<=2 in an
  EdgeCritical graph is Optimal. No minimum-cardinality assumption is needed.
- smaller_correction_three_le: any smaller-than-Best parity correction in an
  EdgeCritical graph has size>=3. No claim about larger corrections.
The proof uses the existing single-addition-to-even equality after one
critical deletion. It supplies no uniform cycle decomposition bound.

EXTERNAL DIAGNOSTICS (exact, not Lean):
/tmp/exposure_parity_binary.cpp tested all subsets of PG3, doubled Fano,
AG4, the old rank-five extension, R10 plus six columns, a two-sum of R10,
and weight-three rank-five columns. No EdgeCritical Best/min-parity gap.
Many of these observations are explained by the new <=2 theorem; they must
not be treated as general evidence without checking the correction size.
/tmp/exposure_parity_graph.cpp tested all256 one-vertex extensions of the
old order8 parity-gap source, and26460 two-vertex extensions with each new
vertex's initial degree3 or4. The first run had15 parity gaps,1 critical
source; the second362 parity gaps,24 critical sources. No gap was critical.
Logs: /tmp/exposure-parity-graph.log/.exit(0),
/tmp/exposure-parity-graph2.log/.exit(0). These are targeted finite tests,
not a general graphical theorem or a global-minimality classification.

A GENERIC REGULAR-MATROID SHORTCUT IS FALSE. Adding binary column112 to the
old order8 gap representation gives rank7 on12 elements, number5, Best4,
minimum correction3, hull7. EVERY single deletion has number4. All three
Optimal singleton sets have size4 and partition the ground set. Thus mere
individual edge exposure does NOT imply minimum-parity optimality for
binary or even regular matroids. The source is not globally Minimal.

This has a clean independent description: the BOND system of H=K3 join I3.
H has12 edges. Its maximum cut is the9 bipartite edges, uniquely, so the
unique minimum correction is the triangle on the three hubs (size3).
That9-edge cut requires three disjoint bonds, the stars of the independent
vertices. But a cut isolating two hubs is an8-edge bond; with the four
remaining singleton edges it gives number5. There are exactly three such
optimal singleton sets, and they partition all12 elements. Maximum bond
size8 and minimum correction3 rule out cost<=4; the unique3-correction's
cofactor cost3 rules out an optimum with3 singletons.

Independent exact certificate:
/tmp/cographic_exposure_parity_certificate.py
/tmp/cographic-exposure-parity-certificate.log
Sage separately checked that the discovered binary matroid is isomorphic
in dual to the cycle matroid of H, is nongraphic, and has no Fano or dual
Fano minor. This is a cographic regular matroid, NOT a graph-cycle example.
Planarizing one crossing of H produces a simple nine-vertex planar dual;
its analogous parity gap disappears. No graphical edge-critical or global
Minimal counterexample was obtained. None of this settles Erdos184.

No Lean build or diagnostic remains active. Spec still has its original sorry.

## Continuation: maximum-singleton selection also has unavoidable bad non-cut leaves

Original Spec remains unchanged and UNSOLVED. The parallel-block family already
refuted a uniform bound at EVERY non-cut Best leaf. Its maximum-singleton optima
also have an unavoidable bad leaf. This is an external exact local certificate
plus a mathematical family argument, NOT a Lean graph-family theorem.

Let B=K3 join I4 minus03, hubs0,1,2 and terminals a=0,b=3. Its number and
hull are6, Best singleton count3, maximum optimal singleton count4. Every
terminal-path cofactor has number>=6; among those with number6 the maximum
singleton count is5. Form G_m for even m>=2 by identifying a in m copies of B
at v, adding z, the m connectors b_i--z, and the closing edge v--z. The earlier
certificate proves global Minimality and 2-vertex-connectivity, with
n=6m+2 and number=13m/2+1.

In any optimum, if r cycles and s singleton edges meet z, then 2r+s=m+1 and
pieces>=6m+r+s. Equality at number13m/2+1 forces r=m/2,s=1. If the central
singleton is v--z, all m blocks are active and contribute at most5m local
singletons; total<=5m+1. If it is a connector, one full block contributes<=4
and the m-1 active blocks each<=5; total<=5m. The first bound is attained:
use terminal path0-1-2-3 in each block, local singles02,06,13,15,24, and local
cycle0-5-2-6-1-4-0; pair terminal paths through z and leave v--z singleton.
Thus EVERY maximum-singleton optimum has v--z as its unique singleton at z.
Yet G_m-z is connected, hull(G_m-z)=6m, so loss=m/2+1 is unbounded.

This refutes universal non-cut leaf loss for maximum-singleton optima, NOT
existence of SOME favorable leaf, the higher-connectivity restriction, the
dominated Best-leaf rule, or Erdős184. Maximizing singleton count merely moves
the bad leaf from v to z. Explicit partitions and graph checks for even m<=20:
 /tmp/parallel_max_singleton_leaf_certificate.py
 /tmp/parallel-max-singleton-leaf-certificate.log
 /tmp/parallel-max-singleton-leaf-certificate.exit (0)
 /tmp/parallel-max-singleton-leaf-certificate.json (full m=4 data).

## Continuation: two-terminal bottleneck audit; no settlement

No original proof/disproof or new Lean theorem. The dominated Best-leaf route
still lacks both a general Best-edge hull transfer and a bound for the weaker
NestedSingletons terminal class. DominatedSingletonRemainder only provides an
even double-star subgraph; its size can grow with the degree.

Guard against a tempting incorrect amplification: in B=K3 join I4 minus03,
minimum ONE-terminal-path cofactor number is6, but TWO edge-disjoint terminal
paths can leave a four-piece cofactor. Explicit paths are0-1-4-2-3 and
0-2-5-1-3; leftover pieces are singles04,05,06 and triangle1-2-6-1.
Direct edge partition verification passed. Therefore identifying BOTH terminals
of many B copies does not preserve the one-active-path-per-block lower bound.
The already recorded dominated edge-amalgam partition uses these two paths
per block to obtain5m+1 pieces on5m+2 vertices (m>=2). Its proper spanning tree
has the same count, so that full amalgam is not globally Minimal. The separate
parallel family WITH connectors has a genuine one-path bottleneck, and its
previously stated obstruction is unaffected. No original settlement follows.

## VERIFIED: square accounting alone admits unbounded abstract ratios

NEW Lean module Submission/SquareBudgetArithmeticObstruction.lean compiles
with a current olean, exit0, and only propext, Classical.choice, Quot.sound.
Log: /tmp/square-budget-arithmetic-obstruction.log.
Theorem no_linear_bound_from_accounting: for every C there are positive n,
a finite descent length t, and positive integer sequences k_i,m_i such that
 k_0 > C*n, k_t=n, every m_i<=n*(n-1)/2,
 and for each i<t:
   k_(i+1)<k_i,
   k_i<=15*n+5*k_(i+1),
   m_(i+1)+4*k_i<=m_i+24*n.
Explicit data: t=C, n=10*5^t+1, k_i=n*5^(t-i), m_i=5*k_i.
In fact k_i=5*k_(i+1), m_(i+1)+4*k_i=m_i, and the initial edge cap is
attained. This demonstrates that no numerical induction using ONLY these
inequalities can establish a uniform linear bound. A new structural charge
is needed. These sequences are NOT graphs, NOT claimed realizable as graph
decomposition numbers, and NOT a disproof of Erdős184. No square-accessibility
or discarded-graph bound was proved. Spec remains unchanged with its sorry.

## VERIFIED: full mixed-dual exactness obstruction on edge-critical graphs

Submission/MixedDualCriticality.lean imports Submission.TightDual and has a
current olean. /tmp/mixed-dual-criticality.exit is 0. Its three principal
axiom audits contain only propext, Classical.choice, Quot.sound.

MixedUpperWeight G w requires w(e)<=1 for every edge and total weight<=1
on every simple cycle; weights may be signed. Verified:
- total_le_number for every graph, with no evenness hypothesis;
- edge_weight_lower: edge-criticality gives
  total(w)-number(G)+1 <= w(e) on every edge;
- cycle_gap_bound: every cycle of length L forces
  L-1 <= L*(number(G)-total(w));
- cyclic_gap: a cyclic edge-critical graph has mixed-dual gap >=2/3;
- exact_mixed_dual_iff_acyclic: on an EdgeCritical graph, some full mixed
  dual attains the integer optimum iff the graph is acyclic.

These facts concern the FULL cycle-and-single-edge dual. They do not refute
HasExactOptimalRemainder, which asks for a cycle-only dual on some optimal
EVEN remainder. They give no upper bound on the integral gap and do not
settle the original conjecture. Spec remains unchanged with its original
sorry. No original proof/disproof or submission was made; no job remains.
