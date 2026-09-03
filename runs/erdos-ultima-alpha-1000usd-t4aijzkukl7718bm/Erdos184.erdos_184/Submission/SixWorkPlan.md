# Six-color continuation plan (NOT a settlement)

The original conjecture is still UNSOLVED. In particular no arbitrary-optimum
core bound or reduction to optimum three has been found. Even finishing all
six/seven finite work below will NOT by itself settle Spec.lean.

## Current mathematical finite route

1. Complete all five local classifications (patterns0..3 allowed; pattern4
   impossible). This yields max-family size>=6 for a hypothetical nonrigid
   optimum-three minimal core.
2. The six numerical classification has five patterns, in order:
   {}, {01}, {01,23}, {01,23,45}, {01,02}.
3. All six-to-five projections and pure projected-word coverage reduce six
   layouts to 276744 known records. Quotienting by color permutations AND
   doubled-slot flips gives:
     pattern0: 242508 records, 720 automorphisms, 381 orbits, 13 max<=6 orbits
     pattern1:  33948 records,  96 automorphisms, 387 orbits,  0 max<=6 orbits
     pattern2:    288 records,  64 automorphisms,  10 orbits,  0 max<=6 orbits
     pattern3,4: no records.
   These orbit counts are exact Python data. Formal coverage is being checked.
4. Each of the 778 representatives has an explicit circuit certificate:
   a two-cycle partition for max<=6, otherwise a >6-cycle partition. The C++
   witness generator and independent Python verification finished successfully.
   These are NOT all Lean-checked yet.
5. SixOrbitKernel0..2, SixRepresentativeKernels and SixGraphFamily are generated
   but unverified. Intended consequences: six local families have optimum<=2,
   only the all-single numerical pattern survives, bad optimum-three cores
   have maximum family>=7.
6. Still needed after that: formal seven-color exclusion. External exact work
   already found no extension of any of the 13 six-layout orbit representatives
   (203125 prefix extensions tested). This is NOT yet formalized.

## Seven-color normalization idea (NOT implemented)

All pairs in a bad core will be single-contact once every six-subfamily is
all-single. For a seven-subfamily, each row then has six markers / 60 canonical
undirected orders. Naively using all 7284 labelled allowed six-tuples is costly.
Normalize the first six colors to one of the 13 six orbits by extending its S6
color permutation to seven colors, fixing color6. This is another checked row
action, analogous to PureSixActions0 but on seven rows of length6/60 choices.
Its 720*7*60 local row maps can be constructed exactly. Prove numerically that
omitting color6 commutes with this action. Then the first-six compressed rows
are a fixed representative, reducing to 13*5^6=203125 prefix extensions and a
60-choice seventh row. Other six-projection tests should rule all out.

No assumption of such normalization or exclusion is currently used as a proof.

## New generic interfaces (CHECKED)

CyclicRowActions.lean (small imports):
- Rows choices := forall i, Fin (choices i)
- Edges length := Sigma i, Fin (length i)
- Action contains a color equivalence, vertex embedding, row-image function,
  per-row edge equivalences, and explicit unordered endpoint identities.
- Action.apply uses Equiv.piCongrLeft. Action.apply_color, edgeEquiv,
  edge_color and endpoints_apply are proved.

CyclicRowKernel.lean (graph import):
- Action.flatEdge, Action.embedding and Action.map_univ transport the row
  action through ANY equivalence J equiv Sigma-row-edges. This provides
  labelled circuit-kernel embeddings without enumerating all global row tuples.

FiniteLookupCertificates.lean (small imports):
- FiniteCaseLookup.Table.Every P is a leafwise predicate P key value.
- Table.lookup_every extracts it from a successful lookup.

All printed axioms are permitted.

## Pure six row / action infrastructure

PureSixRowModel0..4 are CHECKED. They define static length/choices vectors,
all normalized row words, flattened source/target maps, mixed-radix key/unkey,
and key injectivity. Generator /tmp/generate_pure_six_row_models.py.
The key proofs need explicitly typed bounds `(q i).val < literal`; simp over
numeral Fin indices was insufficient. key_unkey uses an explicit `change` to
its arithmetic expression before omega. The flattening equivalence requires
`finSigmaFinEquiv (n := length)` explicitly.

PureSixActions{k}Base / CheckXX / assembly:
- Base0 checked; checks are RUNNING. Check00..02 used original 12-group checks;
  later ones were split into one-group subchecks to reduce memory.
- Base1/2 and their checks/assemblies are pending.
- Source generator /tmp/generate_pure_six_actions.py.
- REQUIRED postprocessing /tmp/refine_pure_six_actions.py preserves the small
  checks; do not blindly regenerate over the repaired sources.
- applyRows/actionKey definitions were moved out of the assemblies into
  PureSixActionNumbers0..2 (imports only the corresponding Base), so numerical
  orbit certificates can be checked independently of the row-action proofs.
  Numbers0 is checked. Numbers1/2 are queued as soon as their Bases finish.
  This extraction is NOT built into the original generator; preserve sources.
- Action assemblies import these Numbers modules and prove action_apply_eq.
  They have not been checked yet. Do not assume their elaboration succeeds.

## Six-to-five projections

Generators:
 /tmp/make_six_projection_generator.py -> /tmp/generate_six_projections.py
 /tmp/make_six_projection_codes_generator.py -> /tmp/generate_six_projection_codes.py
 /tmp/generate_six_raw_rows.py

All30 projection Base/Theory pairs and all30 code modules plus SixRows0..4 are
generated. Prototypes SixProjection00Base, SixProjection00, SixProjection41Base,
SixProjection41 PASSED (41 includes a seven-marker/arity5 row).
They use LargerColoredCoarsening.localBounds_large (arity<=6).
Projection-code proofs use FiveWordOrbits*.good_eq to avoid iterating every raw
five-key just to prove codes_of_good.
SixCanonicalCounts is CHECKED; it now imports FiveCanonicalCounts and
PureSixDoubleTransfer instead of the unnecessarily heavy AllowedFiveCounts.

## Orbit numerical data and lookup certificates

Data generator /tmp/six_all_word_orbits.py, finished in ~7 seconds.
Output /tmp/six-all-word-orbits.json (~22MB) contains:
 - all per-row normalized words and markers;
 - automorphisms: color/vertex permutations, inverse group index, each row's
   image index, shift, and reversal bit;
 - representatives with key, source, target, exact known maximum;
 - each surviving raw key with group action taking it TO its representative.
The action group's vertex maps are bijections on all72 slots (including unused).

Lookup generator /tmp/generate_six_orbit_lookup.py:
- PureSixOrbitLookup{k}DefsXXX: blocks of256 leaves,16 blocks per definition file.
- PureSixOrbitLookup{k}Base: table and representative keys, and packed-code
  extraction groupOfCode / representativeOfCode.
- CertificateBase imports PureSixActionNumbers{k}; Certificate j c states
  actionKey (groupOfCode c) j = representativeKey (representativeOfCode c).
- CheckXXXX verifies Table.Every Certificate on one256-leaf block.
- Assembly uses Table.lookup_every.
Counts: pattern0 948 blocks/60 def files; pattern1 133/9; pattern2 2/1.
ALL definition files and Bases are CHECKED. Pattern0 CertificateBase and
Check0000 passed (~7 seconds). Remaining certificates are queued AFTER coverage.
Generator's CertificateBase import was postprocessed to Numbers, not Actions;
preserve this change if regenerating.

## Factored pure local coverage

Generator /tmp/generate_pure_six_local_filters.py.
PureSixLocalFilter0..3 CHECKED; 4 was most recently checking.
Each omission has:
- raw row encoders, typed five-row project key, balanced allowed-key lookup;
- correctness of that lookup and forward implication from the graph projection
  code catalogue;
- Test0..5 and Compatible (all six tests).
For omission5 the color order is identity in all five numeric patterns.
Typed preimage tables lift projected five-row words to full six-row words.
`factor` recovers the five projected case plus extension indices.
`CompleteAt t e0` tests the remaining extension choices, placing Test4 BEFORE
choosing e4 for early rejection. `complete_of_factored` gives global coverage
from these finite checks. No completeness hypothesis is silently discharged.

Allowed five cases / extension-fibre sizes:
 0:156 / [4,4,4,4,4]
 1:396 / [5,5,4,4,4]
 2:24  / [5,5,5,5,4]
 3:24  / [5,5,5,5,20]
 4:80  / [6,5,5,4,4]

Generator /tmp/generate_pure_six_completeness.py creates one file per allowed
five-case, containing4..6 CompleteAt checks, then an assembly per pattern.
Order of batch:3,4,2,0,1. Prototype CompleteAt pattern3 t0/e0=0 PASSED in21s.
That prototype file was subsequently expanded to ALL five e0 checks, and will
be rebuilt by the queued batch. Do not describe the full file as checked yet.

## Graph representative certificate sources / transport (GENERATED, UNCHECKED)

/tmp/six_partition_cert.cpp (uint64_t, cutoff6) and executable
/tmp/six_orbit_certificates.py -> /tmp/six-orbit-certificates.json.
All778 witnesses generated and independently verified in36s. The helper for
five cases used uint32_t, so it was NOT reused unchanged for34-edge kernels.

/tmp/generate_six_representative_certificates.py generates certificate modules
in chunks50, source/target identities to PureSixRowModel, and
SixRepresentativeCertificates{k}.exists_two_of_upper.
List /tmp/six-representative-certificate-modules. NONE checked yet.

/tmp/generate_six_case_compatibility.py connects actual normalized rows via
SixProjectionCode to the checked pure filters and the pending coverage.
SixCaseCompatibility0..4 are GENERATED, NOT CHECKED.

/tmp/generate_six_orbit_kernels.py generates SixOrbitKernel0..2:
- numerical lookup certificate -> action_rows_eq;
- row-action kernel embedding -> transfer local maximum bound;
- representative certificate -> two-circuit partition;
- back transport to canonical rows; patterns1/2 excluded by empty good sets.
These are NOT CHECKED, including possible elaboration details with dependent
casts and source/target rewriting.

SixRepresentativeKernels.lean and SixGraphFamily.lean are also GENERATED,
NOT CHECKED. SixGraphFamily comes from /tmp/generate_six_graph_family.py,
using AllowedFiveCounts.pattern_count_le for its natural-count classification.

## Original mathematical gap

No new theorem was obtained by reconsidering rank-three obstruction reduction,
weak minimal-cofactor accessibility, one-cycle extensions of rigid cores,
LP rounding, regular matroids, vertex splitting, or circuit exchanges. Do not
infer a general bound from the finite work. Spec.lean remains unchanged.
