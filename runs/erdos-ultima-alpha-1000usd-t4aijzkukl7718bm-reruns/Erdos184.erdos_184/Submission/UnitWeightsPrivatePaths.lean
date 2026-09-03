import Submission.UnitCycleWeights
import Submission.PrivatePathLifting

/-!
Unit cycle weights pull back along mutually private path replacements.
Consequently a graph with unit cycle weights has no private-path model of K4.
This is a structural consequence of unit weights, not a proof that invariant
or count-critical graphs admit those weights, and not a settlement of Erdos 184.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.UnitCycleWeights
open WeightedPaths FractionalCycles FractionalDualCertificate
set_option maxHeartbeats 1000000

variable {U V : Type*} [Fintype U] [Fintype V]
variable {K : SimpleGraph U} {G : SimpleGraph V}

lemma unit_walk_weight {w : Sym2 V → ℝ}
    (hw : ∀ H : CyclePiece G, pieceWeight w H = 1)
    {v : V} (p : G.Walk v v) (hp : p.IsCycle) : walkWeight w p = 1 := by
  have hh := hw ⟨p.toSubgraph, cycle_subgraph_regular G hp⟩
  simpa only [pieceWeight, ← walk_weight_eq_edge_sum w p hp.isTrail] using hh

lemma unit_weights_of_walks (w : Sym2 V → ℝ)
    (hw : ∀ v (p : G.Walk v v), p.IsCycle → walkWeight w p = 1) :
    HasUnitWeights G := by
  refine ⟨w, fun H => ?_⟩
  obtain ⟨v⟩ := H.property.1.nonempty
  obtain ⟨p,hp,hpeq⟩ := CycleRing.cycle_piece_walk_at H.val
    H.property.1 H.property.2 v.val v.property
  have hh := hw v.val p hp
  rw [walk_weight_eq_edge_sum w p hp.isTrail, hpeq] at hh
  exact hh

omit [Fintype U] in
lemma replacement_weight_symm (M : PrivatePathLifting.Model K G)
    (w : Sym2 V → ℝ) {a b : U} (h : K.Adj a b) :
    walkWeight w (M.path h) = walkWeight w (M.path h.symm) := by
  rw [walk_weight_eq_edge_sum w _ (M.isPath h).isTrail,
    walk_weight_eq_edge_sum w _ (M.isPath h.symm).isTrail]
  have hh : (M.path h).toSubgraph.edgeSet = (M.path h.symm).toSubgraph.edgeSet := by
    ext e
    simp only [Walk.mem_edges_toSubgraph]
    exact M.symmetric_edges h e
  rw [hh]

noncomputable def replacementWeight (M : PrivatePathLifting.Model K G)
    (w : Sym2 V → ℝ) : Sym2 U → ℝ :=
  Sym2.lift ⟨fun a b => if h : K.Adj a b then walkWeight w (M.path h) else 0, by
    intro a b
    by_cases h : K.Adj a b
    · simp only [dif_pos h, dif_pos h.symm]
      exact replacement_weight_symm M w h
    · have hr : ¬ K.Adj b a := fun hh => h hh.symm
      simp only [dif_neg h, dif_neg hr]⟩

omit [Fintype U] in
lemma replacementWeight_edge (M : PrivatePathLifting.Model K G)
    (w : Sym2 V → ℝ) {a b : U} (h : K.Adj a b) :
    replacementWeight M w s(a,b) = walkWeight w (M.path h) := by
  simp only [replacementWeight, Sym2.lift_mk, dif_pos h]

omit [Fintype V] in
lemma chain_weight (w : Sym2 V → ℝ) (v : ℕ → V) (r : ℕ → ℝ)
    (n : ℕ) (p : ∀ i, i < n → G.Walk (v i) (v (i+1)))
    (hp : ∀ i hi, walkWeight w (p i hi) = r i) :
    walkWeight w (CycleRing.chain v n p) = ∑ i ∈ Finset.range n, r i := by
  induction n with
  | zero => simp [CycleRing.chain]
  | succ n ih =>
    rw [CycleRing.chain, weight_append, Finset.sum_range_succ]
    rw [ih _ (fun i hi => hp i _), hp]

omit [Fintype U] in
lemma lift_weight (M : PrivatePathLifting.Model K G) (w : Sym2 V → ℝ)
    {u : U} (c : K.Walk u u) :
    walkWeight w (M.lift c) = walkWeight (replacementWeight M w) c := by
  rw [PrivatePathLifting.Model.lift, weight_copy,
    weight_eq_sum_range (replacementWeight M w) c]
  apply chain_weight
  intro i hi
  exact (replacementWeight_edge M w (c.adj_getVert_succ hi)).symm

/-- Pullback uses actual simple lifted cycles and the sum along each private
replacement path. The ambient graph need not be even. -/
theorem pullback_private_paths (M : PrivatePathLifting.Model K G)
    (hu : HasUnitWeights G) : HasUnitWeights K := by
  obtain ⟨w,hw⟩ := hu
  apply unit_weights_of_walks (replacementWeight M w)
  intro u c hc
  rw [← lift_weight M w c]
  exact unit_walk_weight hw (M.lift c) (M.lift_isCycle c hc)

end UnitCycleWeights

namespace UnitCycleWeights.K4
open WeightedPaths
abbrev complete : SimpleGraph (Fin 4) := ⊤

def c0 : complete.Walk 0 0 :=
  .cons (by decide : complete.Adj 0 1) <|
  .cons (by decide : complete.Adj 1 2) <|
  .cons (by decide : complete.Adj 2 0) <|
  .nil
lemma c0_cycle : c0.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [c0], by decide⟩

def c1 : complete.Walk 0 0 :=
  .cons (by decide : complete.Adj 0 1) <|
  .cons (by decide : complete.Adj 1 3) <|
  .cons (by decide : complete.Adj 3 0) <|
  .nil
lemma c1_cycle : c1.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [c1], by decide⟩

def c2 : complete.Walk 0 0 :=
  .cons (by decide : complete.Adj 0 2) <|
  .cons (by decide : complete.Adj 2 3) <|
  .cons (by decide : complete.Adj 3 0) <|
  .nil
lemma c2_cycle : c2.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [c2], by decide⟩

def c3 : complete.Walk 1 1 :=
  .cons (by decide : complete.Adj 1 2) <|
  .cons (by decide : complete.Adj 2 3) <|
  .cons (by decide : complete.Adj 3 1) <|
  .nil
lemma c3_cycle : c3.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [c3], by decide⟩

def c4 : complete.Walk 0 0 :=
  .cons (by decide : complete.Adj 0 1) <|
  .cons (by decide : complete.Adj 1 2) <|
  .cons (by decide : complete.Adj 2 3) <|
  .cons (by decide : complete.Adj 3 0) <|
  .nil
lemma c4_cycle : c4.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [c4], by decide⟩

def c5 : complete.Walk 0 0 :=
  .cons (by decide : complete.Adj 0 1) <|
  .cons (by decide : complete.Adj 1 3) <|
  .cons (by decide : complete.Adj 3 2) <|
  .cons (by decide : complete.Adj 2 0) <|
  .nil
lemma c5_cycle : c5.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [c5], by decide⟩

def c6 : complete.Walk 0 0 :=
  .cons (by decide : complete.Adj 0 2) <|
  .cons (by decide : complete.Adj 2 1) <|
  .cons (by decide : complete.Adj 1 3) <|
  .cons (by decide : complete.Adj 3 0) <|
  .nil
lemma c6_cycle : c6.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [c6], by decide⟩

/-- The four triangles and three Hamilton cycles each cover every edge twice. -/
lemma no_unit_weights : ¬ HasUnitWeights complete := by
  rintro ⟨w,hw⟩
  have h0 := unit_walk_weight hw c0 c0_cycle
  have h1 := unit_walk_weight hw c1 c1_cycle
  have h2 := unit_walk_weight hw c2 c2_cycle
  have h3 := unit_walk_weight hw c3 c3_cycle
  have h4 := unit_walk_weight hw c4 c4_cycle
  have h5 := unit_walk_weight hw c5 c5_cycle
  have h6 := unit_walk_weight hw c6 c6_cycle
  simp only [c0, c1, c2, c3, c4, c5, c6, weight_cons, weight_nil, add_zero] at *
  have h20 : s((2 : Fin 4),0) = s(0,2) := Sym2.eq_swap
  have h30 : s((3 : Fin 4),0) = s(0,3) := Sym2.eq_swap
  have h31 : s((3 : Fin 4),1) = s(1,3) := Sym2.eq_swap
  have h32 : s((3 : Fin 4),2) = s(2,3) := Sym2.eq_swap
  have h21 : s((2 : Fin 4),1) = s(1,2) := Sym2.eq_swap
  simp only [h20,h30,h31,h32,h21] at h0 h1 h2 h3 h4 h5 h6
  linarith

end UnitCycleWeights.K4

namespace UnitCycleWeights
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Exclusion of every K4 subdivision expressed by six mutually private
simple replacement paths. No evenness hypothesis is needed. -/
theorem no_K4_private_model (hu : HasUnitWeights G) :
    ¬ Nonempty (PrivatePathLifting.Model K4.complete G) := by
  rintro ⟨M⟩
  exact K4.no_unit_weights (pullback_private_paths M hu)

end Erdos184.UnitCycleWeights
