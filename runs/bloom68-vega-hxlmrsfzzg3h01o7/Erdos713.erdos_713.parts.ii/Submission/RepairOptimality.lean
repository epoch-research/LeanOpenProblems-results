import FormalConjecturesUtil

/-!
# Exact global optimality via minimum old-edge repair

An addition `R` is a simple graph edge-disjoint from the host `G`, and is itself
`H`-free. A feasible deletion `D` consists only of old edges of `G` and makes
`(G - D) ⊔ R` free. Deleting all old edges is feasible, so `repairNumber` is a
minimum over an explicitly nonempty finite family, not an infimum with a
fallback value. Its proof argument is just the freeness of `R`.

The maximum integer repair gain is exactly `extremalNumber n H - e(G)`.
An actual extremal graph `F` attains it with `R = F \ G` and `D = E(G) \ E(F)`;
this `D` is already a minimum repair for that `R`. We also give an exact
ordinary-copy transversal criterion and characterize global edge extremality
by the requirement that every addition has minimum repair at least its size.

Only the host vertex type needs to be finite. No edge, vertex, or non-isolation
assumption on `H` is imposed. In particular, the given `H.Free G` hypothesis,
not a claim that the empty graph is always free, supplies extremal existence.
If an edgeless `H` injects into the host, this hypothesis is impossible; if it
does not, all the results still apply. All copies are ordinary injective graph
homomorphisms (`SimpleGraph.Copy`), never induced embeddings.

These are deterministic finite optimization statements. They do not prove an
asymptotic conjecture or an assertion about extremal exponents.
-/

open SimpleGraph

namespace Erdos713RepairOptimality

universe u v

variable {V : Type u} {W : Type v}

/-- A new-edge candidate has no old edges, and is itself forbidden-copy-free. -/
def IsAddition (H : SimpleGraph W) (G R : SimpleGraph V) : Prop :=
  Disjoint G R ∧ H.Free R

/-- Delete only the specified old edges, then add the candidate graph. -/
def repairGraph (G R : SimpleGraph V) (D : Finset (Sym2 V)) : SimpleGraph V :=
  G.deleteEdges (D : Set (Sym2 V)) ⊔ R

variable {H : SimpleGraph W} {G R F : SimpleGraph V}

/-- Freeness of a larger graph certifies freeness of a disjoint candidate. -/
lemma isAddition_of_le (hdis : Disjoint G R) (hRF : R ≤ F) (hF : H.Free F) :
    IsAddition H G R :=
  ⟨hdis, fun h => hF (h.mono_right hRF)⟩

/-- The part of any free graph outside the host is an admissible addition. -/
lemma isAddition_sdiff (hF : H.Free F) : IsAddition H G (F \ G) :=
  isAddition_of_le disjoint_sdiff_self_right sdiff_le hF

/-- Deleting edges destroys every ordinary copy exactly when every such copy
uses a deleted edge. This includes copies of edgeless forbidden graphs. -/
theorem free_deleteEdges_iff_hits_copies (K : SimpleGraph V) (s : Set (Sym2 V)) :
    H.Free (K.deleteEdges s) ↔
      ∀ c : H.Copy K, ∃ e ∈ c.toSubgraph.edgeSet, e ∈ s := by
  classical
  constructor
  · intro hfree c
    by_contra! hmiss
    apply hfree
    refine ⟨⟨⟨c, ?_⟩, c.injective⟩⟩
    intro x y hxy
    refine deleteEdges_adj.mpr ⟨c.toHom.map_adj hxy, hmiss s(c x, c y) ?_⟩
    rw [Copy.toSubgraph, Subgraph.edgeSet_map, Subgraph.edgeSet_top]
    exact ⟨s(x, y), hxy, rfl⟩
  · intro hhit ⟨c⟩
    obtain ⟨e, hec, hes⟩ := hhit ((Copy.ofLE _ _ (K.deleteEdges_le s)).comp c)
    have he : e ∈ (K.deleteEdges s).edgeSet := c.toSubgraph.edgeSet_subset hec
    rw [edgeSet_deleteEdges] at he
    exact he.2 hes

@[simp]
lemma repairGraph_empty : repairGraph G R ∅ = G ⊔ R := by
  simp [repairGraph]

section Finite

variable [Fintype V]

open scoped Classical

/-- A feasible repair deletes a subset of the old edges and leaves no copy. -/
def FeasibleDeletion (H : SimpleGraph W) (G R : SimpleGraph V)
    (D : Finset (Sym2 V)) : Prop :=
  D ⊆ G.edgeFinset ∧ H.Free (repairGraph G R D)

/-- The finite family over which minimum repair is optimized. -/
noncomputable def feasibleDeletions (H : SimpleGraph W) (G R : SimpleGraph V) :
    Finset (Finset (Sym2 V)) :=
  G.edgeFinset.powerset.filter (fun D => H.Free (repairGraph G R D))

@[simp]
lemma mem_feasibleDeletions {D : Finset (Sym2 V)} :
    D ∈ feasibleDeletions H G R ↔ FeasibleDeletion H G R D := by
  simp [feasibleDeletions, FeasibleDeletion]

@[simp]
lemma repairGraph_all : repairGraph G R G.edgeFinset = R := by
  simp [repairGraph]

/-- Every free candidate admits a repair, even when the original host is not free. -/
lemma feasibleDeletion_all (hR : H.Free R) :
    FeasibleDeletion H G R G.edgeFinset := by
  exact ⟨Finset.Subset.refl _, by simpa only [repairGraph_all] using hR⟩

lemma feasibleDeletions_nonempty (hR : H.Free R) :
    (feasibleDeletions H G R).Nonempty :=
  ⟨G.edgeFinset, mem_feasibleDeletions.mpr (feasibleDeletion_all hR)⟩

/-- `τ_G(R)`: the minimum number of old edges that must be deleted to add `R`.
The minimum exists because deleting all old edges leaves the free graph `R`.
Disjointness is needed for gain accounting, not for this definition. -/
noncomputable def repairNumber (H : SimpleGraph W) (G R : SimpleGraph V)
    (hR : H.Free R) : ℕ :=
  ((feasibleDeletions H G R).image Finset.card).min'
    ((feasibleDeletions_nonempty (G := G) hR).image Finset.card)

/-- The finite minimum is attained by a feasible old-edge deletion. -/
theorem exists_minimum_deletion (hR : H.Free R) :
    ∃ D, FeasibleDeletion H G R D ∧ D.card = repairNumber H G R hR := by
  have hmem := Finset.min'_mem ((feasibleDeletions H G R).image Finset.card)
    ((feasibleDeletions_nonempty (G := G) hR).image Finset.card)
  obtain ⟨D, hD, hcard⟩ := Finset.mem_image.mp hmem
  exact ⟨D, mem_feasibleDeletions.mp hD, hcard⟩

lemma repairNumber_le_card (hR : H.Free R) {D : Finset (Sym2 V)}
    (hD : FeasibleDeletion H G R D) : repairNumber H G R hR ≤ D.card :=
  Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨D, mem_feasibleDeletions.mpr hD, rfl⟩)

lemma le_repairNumber_iff (hR : H.Free R) (k : ℕ) :
    k ≤ repairNumber H G R hR ↔
      ∀ D, FeasibleDeletion H G R D → k ≤ D.card := by
  constructor
  · intro hk D hD
    exact hk.trans (repairNumber_le_card hR hD)
  · intro h
    obtain ⟨D, hD, hcard⟩ := exists_minimum_deletion (G := G) hR
    simpa only [hcard] using h D hD

lemma repairNumber_le_old_card (hR : H.Free R) :
    repairNumber H G R hR ≤ G.edgeFinset.card :=
  repairNumber_le_card hR (feasibleDeletion_all hR)

/-- Minimum repair zero means precisely that no deletions are necessary. -/
theorem repairNumber_eq_zero_iff (hR : H.Free R) :
    repairNumber H G R hR = 0 ↔ H.Free (G ⊔ R) := by
  constructor
  · intro hzero
    obtain ⟨D, hD, hcard⟩ := exists_minimum_deletion (G := G) hR
    have hDzero : D = ∅ := Finset.card_eq_zero.mp (hcard.trans hzero)
    simpa only [hDzero, repairGraph_empty] using hD.2
  · intro hfree
    have hD : FeasibleDeletion H G R ∅ :=
      ⟨Finset.empty_subset _, by simpa only [repairGraph_empty] using hfree⟩
    exact Nat.eq_zero_of_le_zero (repairNumber_le_card hR hD)

/-- Exact finite edge set; `R` is a graph, so there is no issue with loops. -/
lemma edgeFinset_repairGraph (D : Finset (Sym2 V)) :
    (repairGraph G R D).edgeFinset = (G.edgeFinset \ D) ∪ R.edgeFinset := by
  simp [repairGraph]

/-- Exact edge accounting in additive naturals, with no truncated subtraction. -/
theorem card_repairGraph_add_card {D : Finset (Sym2 V)}
    (hdis : Disjoint G R) (hD : D ⊆ G.edgeFinset) :
    (repairGraph G R D).edgeFinset.card + D.card =
      G.edgeFinset.card + R.edgeFinset.card := by
  have hdis' : Disjoint (G.edgeFinset \ D) R.edgeFinset :=
    (disjoint_edgeFinset.mpr hdis).mono_left Finset.sdiff_subset
  rw [edgeFinset_repairGraph, Finset.card_union_of_disjoint hdis',
    Finset.card_sdiff_of_subset hD]
  have hle := Finset.card_le_card hD
  omega

/-- Every feasible repair has gain at most the global extremal deficit.
Neither freeness of the original host nor minimality of the deletion is needed. -/
theorem feasibleDeletion_bound {D : Finset (Sym2 V)} (hdis : Disjoint G R)
    (hD : FeasibleDeletion H G R D) :
    G.edgeFinset.card + R.edgeFinset.card ≤
      extremalNumber (Fintype.card V) H + D.card := by
  have hcount := card_repairGraph_add_card hdis hD.1
  have hbound := card_edgeFinset_le_extremalNumber hD.2
  omega

/-- Additive-natural form of `e(R) - τ_G(R) ≤ ex(n,H) - e(G)`. -/
theorem repairNumber_bound (hR : IsAddition H G R) :
    G.edgeFinset.card + R.edgeFinset.card ≤
      extremalNumber (Fintype.card V) H + repairNumber H G R hR.2 := by
  obtain ⟨D, hD, hcard⟩ := exists_minimum_deletion (G := G) hR.2
  simpa only [hcard] using feasibleDeletion_bound hR.1 hD

/-- Integer gain, so that a net loss is negative rather than truncated to zero. -/
noncomputable def repairGain (H : SimpleGraph W) (G R : SimpleGraph V)
    (hR : H.Free R) : ℤ :=
  (R.edgeFinset.card : ℤ) - (repairNumber H G R hR : ℤ)

theorem repairGain_le_deficit (hR : IsAddition H G R) :
    repairGain H G R hR.2 ≤
      (extremalNumber (Fintype.card V) H : ℤ) - (G.edgeFinset.card : ℤ) := by
  have hbound := repairNumber_bound hR
  unfold repairGain
  omega

/-- Deterministic density increment from any specified feasible repair. -/
theorem density_increment {D : Finset (Sym2 V)} {gain : ℕ}
    (hdis : Disjoint G R) (hD : FeasibleDeletion H G R D)
    (hgain : D.card + gain ≤ R.edgeFinset.card) :
    G.edgeFinset.card + gain ≤ extremalNumber (Fintype.card V) H := by
  have hbound := feasibleDeletion_bound hdis hD
  omega

/-- A minimum-repair certificate also gives the deterministic increment. -/
theorem density_increment_of_repairNumber {gain : ℕ} (hR : IsAddition H G R)
    (hgain : repairNumber H G R hR.2 + gain ≤ R.edgeFinset.card) :
    G.edgeFinset.card + gain ≤ extremalNumber (Fintype.card V) H := by
  have hbound := repairNumber_bound hR
  omega

/-- Symmetric difference replacement recovers the target graph exactly. -/
lemma repairGraph_sdiff :
    repairGraph G (F \ G) (G.edgeFinset \ F.edgeFinset) = F := by
  ext x y
  simp only [repairGraph, sup_adj, deleteEdges_adj, Finset.mem_coe,
    Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet, sdiff_adj]
  tauto

lemma feasibleDeletion_sdiff (hF : H.Free F) :
    FeasibleDeletion H G (F \ G) (G.edgeFinset \ F.edgeFinset) :=
  ⟨Finset.sdiff_subset, by simpa only [repairGraph_sdiff] using hF⟩

/-- For an actual extremal target `F`, deleting `G \ F` is a *minimum* repair
for the candidate `F \ G`, not just a feasible repair. -/
theorem repairNumber_sdiff_of_isExtremal (hF : F.IsExtremal H.Free) :
    repairNumber H G (F \ G) (isAddition_sdiff (G := G) hF.1).2 =
      (G.edgeFinset \ F.edgeFinset).card := by
  have hadd := isAddition_sdiff (G := G) hF.1
  have hcount := card_repairGraph_add_card hadd.1
    (show G.edgeFinset \ F.edgeFinset ⊆ G.edgeFinset from Finset.sdiff_subset)
  rw [repairGraph_sdiff, card_edgeFinset_of_isExtremal_free hF] at hcount
  have hbound := repairNumber_bound hadd
  have hmin := repairNumber_le_card hadd.2 (feasibleDeletion_sdiff hF.1)
  omega

/-- Explicit optimal witnesses can always be taken from an actual extremal
`F` on the *same* host vertex type: `R = F \ G` and `D = G \ F`. -/
theorem exists_extremal_difference_repair (hG : H.Free G) :
    ∃ F : SimpleGraph V, F.IsExtremal H.Free ∧
      ∃ hR : IsAddition H G (F \ G),
        FeasibleDeletion H G (F \ G) (G.edgeFinset \ F.edgeFinset) ∧
        repairGraph G (F \ G) (G.edgeFinset \ F.edgeFinset) = F ∧
        (G.edgeFinset \ F.edgeFinset).card = repairNumber H G (F \ G) hR.2 ∧
        G.edgeFinset.card + (F \ G).edgeFinset.card =
          extremalNumber (Fintype.card V) H + (G.edgeFinset \ F.edgeFinset).card := by
  obtain ⟨F, _, hF'⟩ := (exists_isExtremal_iff_exists H.Free).mpr ⟨G, hG⟩
  letI : DecidableRel F.Adj := fun _ _ => Classical.propDecidable _
  have hF : F.IsExtremal H.Free := by convert hF'
  refine ⟨F, hF, isAddition_sdiff hF.1, feasibleDeletion_sdiff hF.1,
    repairGraph_sdiff, (repairNumber_sdiff_of_isExtremal hF).symm, ?_⟩
  have hcount := card_repairGraph_add_card (isAddition_sdiff (G := G) hF.1).1
    (show G.edgeFinset \ F.edgeFinset ⊆ G.edgeFinset from Finset.sdiff_subset)
  rw [repairGraph_sdiff, card_edgeFinset_of_isExtremal_free hF] at hcount
  convert hcount.symm

/-- The universal gain bound is attained by a feasible *minimum* deletion. -/
theorem exists_repair_attaining_deficit (hG : H.Free G) :
    ∃ (R : SimpleGraph V) (hR : IsAddition H G R) (D : Finset (Sym2 V)),
      FeasibleDeletion H G R D ∧ D.card = repairNumber H G R hR.2 ∧
        G.edgeFinset.card + R.edgeFinset.card =
          extremalNumber (Fintype.card V) H + D.card := by
  obtain ⟨F, _, hR, hD, _, hmin, hcount⟩ := exists_extremal_difference_repair hG
  refine ⟨F \ G, hR, G.edgeFinset \ F.edgeFinset, hD, hmin, ?_⟩
  convert hcount

/-- Attainment in integers, including hosts with zero extremal deficit. -/
theorem exists_repairGain_eq_deficit (hG : H.Free G) :
    ∃ (R : SimpleGraph V) (hR : IsAddition H G R),
      repairGain H G R hR.2 =
        (extremalNumber (Fintype.card V) H : ℤ) - (G.edgeFinset.card : ℤ) := by
  obtain ⟨R, hR, D, _, hmin, hcount⟩ := exists_repair_attaining_deficit hG
  refine ⟨R, hR, ?_⟩
  unfold repairGain
  omega

/-- Exact global maximum repair gain = extremal deficit. `IsGreatest` includes
both attainment and the bound for every admissible candidate. -/
theorem isGreatest_repairGain (hG : H.Free G) :
    IsGreatest
      {z : ℤ | ∃ (R : SimpleGraph V) (hR : IsAddition H G R),
        repairGain H G R hR.2 = z}
      ((extremalNumber (Fintype.card V) H : ℤ) - (G.edgeFinset.card : ℤ)) := by
  refine ⟨exists_repairGain_eq_deficit hG, ?_⟩
  rintro z ⟨R, hR, rfl⟩
  exact repairGain_le_deficit hR

/-- A prescribed natural-number increment is available exactly when some
admissible candidate has a feasible repair with at least that net gain. -/
theorem density_increment_iff (hG : H.Free G) (gain : ℕ) :
    G.edgeFinset.card + gain ≤ extremalNumber (Fintype.card V) H ↔
      ∃ (R : SimpleGraph V) (D : Finset (Sym2 V)),
        IsAddition H G R ∧ FeasibleDeletion H G R D ∧
          D.card + gain ≤ R.edgeFinset.card := by
  constructor
  · intro hgain
    obtain ⟨R, hR, D, hD, _, hcount⟩ := exists_repair_attaining_deficit hG
    exact ⟨R, D, hR, hD, by omega⟩
  · rintro ⟨R, D, hR, hD, hgain⟩
    exact density_increment hR.1 hD hgain

/-- Global edge extremality, not mere one-edge saturation, is equivalent to
minimum repair costing at least the entire addition for every free new graph. -/
theorem isExtremal_iff_forall_le_repairNumber (hG : H.Free G) :
    G.IsExtremal H.Free ↔
      ∀ (R : SimpleGraph V) (hR : IsAddition H G R),
        R.edgeFinset.card ≤ repairNumber H G R hR.2 := by
  constructor
  · intro hmax R hR
    have hbound := repairNumber_bound hR
    have heq := card_edgeFinset_of_isExtremal_free hmax
    omega
  · intro h
    obtain ⟨R, hR, D, _, hmin, hcount⟩ := exists_repair_attaining_deficit hG
    have hcost := h R hR
    have hbound := card_edgeFinset_le_extremalNumber hG
    exact isExtremal_free_iff.mpr ⟨hG, by omega⟩

/-- Equivalent formulation quantifying over all feasible deletions. -/
theorem isExtremal_iff_forall_feasible_card (hG : H.Free G) :
    G.IsExtremal H.Free ↔
      ∀ (R : SimpleGraph V), IsAddition H G R →
        ∀ D, FeasibleDeletion H G R D → R.edgeFinset.card ≤ D.card := by
  rw [isExtremal_iff_forall_le_repairNumber hG]
  exact forall_congr' (fun R => forall_congr' (fun hR => le_repairNumber_iff hR.2 _))

/-- For disjoint additions, deleting old edges before the union is the same
as deleting them from the union. In particular, none is reintroduced by `R`. -/
lemma repairGraph_eq_deleteEdges_sup {D : Finset (Sym2 V)}
    (hdis : Disjoint G R) (hD : D ⊆ G.edgeFinset) :
    repairGraph G R D = (G ⊔ R).deleteEdges (D : Set (Sym2 V)) := by
  have hdisD : Disjoint R.edgeSet (D : Set (Sym2 V)) := by
    apply Set.disjoint_left.mpr
    intro e heR heD
    exact (Set.disjoint_left.mp (disjoint_edgeSet.mpr hdis))
      (mem_edgeFinset.mp (hD heD)) heR
  simp only [deleteEdges_sup, (deleteEdges_eq_self.mpr hdisD), repairGraph]

/-- A transversal uses only old edges and meets every ordinary copy in `G ⊔ R`.
Copies and their edge sets are not required to be induced. -/
def IsOldEdgeTransversal (H : SimpleGraph W) (G R : SimpleGraph V)
    (D : Finset (Sym2 V)) : Prop :=
  D ⊆ G.edgeFinset ∧
    ∀ c : H.Copy (G ⊔ R), ∃ e ∈ c.toSubgraph.edgeSet, e ∈ D

/-- Feasible old-edge deletions are exactly the transversals of the old-edge
parts of all ordinary forbidden copies in the union. -/
theorem feasibleDeletion_iff_isOldEdgeTransversal {D : Finset (Sym2 V)}
    (hdis : Disjoint G R) :
    FeasibleDeletion H G R D ↔ IsOldEdgeTransversal H G R D := by
  unfold FeasibleDeletion IsOldEdgeTransversal
  apply and_congr_right
  intro hD
  rw [repairGraph_eq_deleteEdges_sup hdis hD, free_deleteEdges_iff_hits_copies]
  rfl

/-- Thus `repairNumber` really is the minimum old-edge transversal size, with
an attaining transversal, even when the family of copies is empty. -/
theorem isLeast_oldEdgeTransversal_card (hR : IsAddition H G R) :
    IsLeast {k : ℕ | ∃ D, IsOldEdgeTransversal H G R D ∧ D.card = k}
      (repairNumber H G R hR.2) := by
  constructor
  · obtain ⟨D, hD, hcard⟩ := exists_minimum_deletion (G := G) hR.2
    exact ⟨D, (feasibleDeletion_iff_isOldEdgeTransversal hR.1).mp hD, hcard⟩
  · rintro k ⟨D, hD, rfl⟩
    exact repairNumber_le_card hR.2
      ((feasibleDeletion_iff_isOldEdgeTransversal hR.1).mpr hD)

/-- Lower bounds on minimum repair are precisely lower bounds on all old-edge
transversals. Together with the extremality iff, this is a minimum-transversal
characterization of global edge optimality. -/
theorem le_repairNumber_iff_transversals (hR : IsAddition H G R) (k : ℕ) :
    k ≤ repairNumber H G R hR.2 ↔
      ∀ D, IsOldEdgeTransversal H G R D → k ≤ D.card := by
  rw [le_repairNumber_iff]
  simp only [feasibleDeletion_iff_isOldEdgeTransversal hR.1]

/-- Global edge optimality expressed entirely in ordinary-copy transversals. -/
theorem isExtremal_iff_forall_transversal_card (hG : H.Free G) :
    G.IsExtremal H.Free ↔
      ∀ (R : SimpleGraph V), IsAddition H G R →
        ∀ D, IsOldEdgeTransversal H G R D → R.edgeFinset.card ≤ D.card := by
  rw [isExtremal_iff_forall_le_repairNumber hG]
  exact forall_congr' (fun R => forall_congr'
    (fun hR => le_repairNumber_iff_transversals hR _))

end Finite

end Erdos713RepairOptimality

/- Axiom audit of every named declaration in this file. -/

#print axioms Erdos713RepairOptimality.IsAddition
#print axioms Erdos713RepairOptimality.repairGraph
#print axioms Erdos713RepairOptimality.isAddition_of_le
#print axioms Erdos713RepairOptimality.isAddition_sdiff
#print axioms Erdos713RepairOptimality.free_deleteEdges_iff_hits_copies
#print axioms Erdos713RepairOptimality.repairGraph_empty
#print axioms Erdos713RepairOptimality.FeasibleDeletion
#print axioms Erdos713RepairOptimality.feasibleDeletions
#print axioms Erdos713RepairOptimality.mem_feasibleDeletions
#print axioms Erdos713RepairOptimality.repairGraph_all
#print axioms Erdos713RepairOptimality.feasibleDeletion_all
#print axioms Erdos713RepairOptimality.feasibleDeletions_nonempty
#print axioms Erdos713RepairOptimality.repairNumber
#print axioms Erdos713RepairOptimality.exists_minimum_deletion
#print axioms Erdos713RepairOptimality.repairNumber_le_card
#print axioms Erdos713RepairOptimality.le_repairNumber_iff
#print axioms Erdos713RepairOptimality.repairNumber_le_old_card
#print axioms Erdos713RepairOptimality.repairNumber_eq_zero_iff
#print axioms Erdos713RepairOptimality.edgeFinset_repairGraph
#print axioms Erdos713RepairOptimality.card_repairGraph_add_card
#print axioms Erdos713RepairOptimality.feasibleDeletion_bound
#print axioms Erdos713RepairOptimality.repairNumber_bound
#print axioms Erdos713RepairOptimality.repairGain
#print axioms Erdos713RepairOptimality.repairGain_le_deficit
#print axioms Erdos713RepairOptimality.density_increment
#print axioms Erdos713RepairOptimality.density_increment_of_repairNumber
#print axioms Erdos713RepairOptimality.repairGraph_sdiff
#print axioms Erdos713RepairOptimality.feasibleDeletion_sdiff
#print axioms Erdos713RepairOptimality.repairNumber_sdiff_of_isExtremal
#print axioms Erdos713RepairOptimality.exists_extremal_difference_repair
#print axioms Erdos713RepairOptimality.exists_repair_attaining_deficit
#print axioms Erdos713RepairOptimality.exists_repairGain_eq_deficit
#print axioms Erdos713RepairOptimality.isGreatest_repairGain
#print axioms Erdos713RepairOptimality.density_increment_iff
#print axioms Erdos713RepairOptimality.isExtremal_iff_forall_le_repairNumber
#print axioms Erdos713RepairOptimality.isExtremal_iff_forall_feasible_card
#print axioms Erdos713RepairOptimality.repairGraph_eq_deleteEdges_sup
#print axioms Erdos713RepairOptimality.IsOldEdgeTransversal
#print axioms Erdos713RepairOptimality.feasibleDeletion_iff_isOldEdgeTransversal
#print axioms Erdos713RepairOptimality.isLeast_oldEdgeTransversal_card
#print axioms Erdos713RepairOptimality.le_repairNumber_iff_transversals
#print axioms Erdos713RepairOptimality.isExtremal_iff_forall_transversal_card
