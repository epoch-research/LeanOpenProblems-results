# Colors chosen after the fixed sign pattern / field translate

## Original task status

Spec.lean is unchanged with its original sorry. The existential conjecture
is still neither proved nor disproved. No proof submission has been made.

## Compiled finite pipeline

The following seven files compile, with current oleans:

1. UniformColorMomentsExplore.lean
2. MatchingColorMomentsExplore.lean
3. FixedPatternColorEnergyExplore.lean
4. OrderedColorEnergyExplore.lean
5. CenteredColorSelectionExplore.lean
6. FiniteLabelRootTransferExplore.lean
7. FixedTranslateColorRootExplore.lean

FixedTranslateColorAudit.lean checks 19 principal results, all depending only
on propext, Classical.choice, and Quot.sound.

For fixed signs f_i^2=1 on i<h, the unordered pairs i<j, i+j=q form a
matching. Under independent uniform colors omega_i, for any kernel K,
mu=mean(K), nu=mean(K^2), the exact second moment is

  E [sum_edges f_i f_j K(omega_i,omega_j)]^2
   = mu^2 (sum_edges f_i f_j)^2 + (nu-mu^2) #edges.

This is genuinely AFTER the sign pattern has been fixed.

For symmetric K the full ordered fiber splits into twice the unordered
fiber plus its diagonal. The diagonal has exact squared energy

  sum_i K(omega_i,omega_i)^2.

No diagonal contribution is discarded. The ordered average-energy bound is

  8[mu^2 edgeEnergy(f)+h^2 nu]+2h mean_x K(x,x)^2.

Also edgeEnergy(f) <= [orderedEnergy(f tensor f)+h]/2.

## Centered joint selection

Let L=K-mu,

  var(K)=mean_(x,y) L(x,y)^2,
  diag(K)=mean_x L(x,x)^2.

Let J(f,K,omega) be the sum of ordered energies with weights
f_i f_j L(omega_i,omega_j) and L(omega_i,omega_j). Then

  E J <=16h^2 var(K)+4h diag(K).

A finite nonnegatively weighted kernel family has ONE coloring with the
sum of J's at most the corresponding sum of these budgets. This controls
both the signed root error AND the unsigned coarse main-term error.

## Root transfer

For a fixed admissible a in ZMod p, f_i=chi(a+i), write E0 for its ordered
unweighted sign energy. For every coloring and every fine target (t,s),

  (R_a(K,omega;t,s)-h^2 mean(K))^2
   <= 6h [mean(K)^2 E0+J(f,K,omega)].

The proof retains the deterministic unsigned target h^2 mean(K), not just
the random matrix sum. In particular, for a finite weighted family, a
coloring selected after a has all fine-target errors satisfying

  w_k error_k^2 <= 6h [w_k mean(K_k)^2 E0+B],
  B=sum_l w_l [16h^2 var(K_l)+4h diag(K_l)].

There is no factor counting fine field-plane targets.

`exists_pattern_for_later_kernels` first selects an admissible a with
E0<=8h^2 (assuming p>4h), then quantifies over every later finite symmetric
kernel family and selects its coloring. This improves the quantifier order
of the earlier matrix-selection theorem. It does NOT allow arbitrary
later color assignments; only one good assignment is asserted.

## Still unresolved

The total budget still depends on the finite kernel family. No uniformly
bounded infinite coarse profile, period-change compatibility, or all-tail
finite-prefix feasibility has been proved. The root counts alone also need
actual-set multiplicity and integer carry transfer before application to A.
A permanent fixed residue restriction would violate the already proved
necessary residue equidistribution.

## Subsequent actual-set investigation (in progress)

`DisjointPaletteAssemblyExplore.lean` now compiles. It proves exact pair
counts for A=union_i P_i x B_i when the fine palettes P_i are pairwise
disjoint. Coarse sets B_i may overlap arbitrarily. An L1 approximation of
the fine pair-count matrix by a reference matrix transfers to actual-set
counts with error <= M times the L1 error, if all coarse mixed counts are
<=M. This conditional lemma has not yet been added to the axiom audit.

Proposed concrete palette conversion (not yet formalized):
- Start with distinct nonzero/nonopposite parameter curves C_i.
- Remove their common origin, yielding pairwise-disjoint E_i.
- For each unordered label pair i<j choose a distinct nonzero point x_ij
  on one auxiliary parabola with parameter outside +/- all old parameters.
- Assign +x_ij to D_i and -x_ij to D_j. Let P_i=E_i union D_i.
- P_i are disjoint. At origin, pairCount(P_i,P_j) is 1 for i!=j and 0 for
  i=j, whereas pairCount(C_i,C_j)=1. Thus L1 error at origin is h.
- Away from origin, removing common endpoints costs total <=2h. The full
  repair support lies on two auxiliary curves, giving total mixed cost
  <=8h and self cost <=8. Hence L1 error should be <=10h+8 uniformly.
- Embedding all pairs into the auxiliary curve needs about h^2/2<p.
- Combined with the checked assembly lemma this would handle arbitrary
  coarse-color overlaps, with an extra error (10h+8) max_ij K_ij(q).

Useful existing files: PartitionCurveRepairExplore.lean (partition_curve_embedding,
pointRepair_origin, curve_point_not_mem, multiple_curve_error),
ParabolaRepairExplore.lean (curve_intersection, curve_pairCount,
parabolaSet_pairCount_le), SharedParameterSetExplore.lean (pairCount_product).
This conversion would still be finite, not a solution of the conjecture.

## Update: the proposed actual-set conversion is now complete

The five-file pipeline in ActualColorTransferProgress.md formalizes the
edge-indexed repair plan above and composes it with the fixed-translate
selection. All five files compile, and ActualColorTransferAudit.lean checks
15 declarations with only the allowed axioms. Thus arbitrary coarse-color
overlaps are no longer an unproved step of this finite transfer. The
infinite profile, changing-period/carry, and uniform-prefix issues remain.
