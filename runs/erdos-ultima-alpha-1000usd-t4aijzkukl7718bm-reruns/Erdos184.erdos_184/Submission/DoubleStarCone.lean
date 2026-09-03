import Submission.ConeEnvelopeLoss
import Submission.FeedbackKernels

/-!
A family of count-critical cones over double-star trees. This certifies the
criticality side of the light-triangle investigation, not the spanning-tree
mass formula and not the original cycle-decomposition conjecture.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.DoubleStarCone
open ConeEnvelopeLoss CountCritical
set_option maxHeartbeats 800000

abbrev Base (r : ℕ) := Bool × Option (Fin r)

def base (r : ℕ) : SimpleGraph (Base r) where
  Adj
    | (b,none), (c,none) => b ≠ c
    | (b,none), (c,some _) => b = c
    | (b,some _), (c,none) => b = c
    | (_,some _), (_,some _) => False
  symm := by
    rintro ⟨b,x⟩ ⟨c,y⟩ h
    cases x <;> cases y <;> simp_all [eq_comm]
  loopless := by rintro ⟨b,x⟩; cases x <;> simp

lemma leaf_degree (r : ℕ) (b : Bool) (i : Fin r) :
    (base r).degree (b,some i) = 1 := by
  have hn : (base r).neighborFinset (b,some i) = {(b,none)} := by
    ext x
    rcases x with ⟨c,x⟩
    cases x <;> simp [SimpleGraph.mem_neighborFinset,base,eq_comm]
  rw [← card_neighborFinset_eq_degree,hn]
  simp

lemma center_degree (r : ℕ) (b : Bool) :
    (base r).degree (b,none) = r+1 := by
  have hn : (base r).neighborFinset (b,none) =
      insert (!b,none) (Finset.univ.image (fun i : Fin r => (b,some i))) := by
    ext x
    rcases x with ⟨c,x⟩
    cases b <;> cases c <;> cases x <;>
      simp [SimpleGraph.mem_neighborFinset,base]
  rw [← card_neighborFinset_eq_degree,hn,Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective _ (by
      intro i j h
      exact Option.some.inj (congrArg Prod.snd h))]
    simp
  · simp

lemma base_acyclic (r : ℕ) : (base r).IsAcyclic := by
  intro v p hp
  have hc := cycle_subgraph_regular (base r) hp
  have hs : p.toSubgraph.verts ⊆ ({(false,none),(true,none)} : Set (Base r)) := by
    rintro ⟨b,x⟩ hx
    cases x with
    | none => cases b <;> simp
    | some i =>
      have hd := hc.2 ⟨(b,some i),hx⟩
      rw [Subgraph.coe_degree] at hd
      have hl := p.toSubgraph.degree_le (b,some i)
      have hh := leaf_degree r b i
      simp only [Subgraph.degree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        at hd hl hh
      omega
  have hh := Set.ncard_le_ncard hs
  have hthree := cycle_edgeSet_three_le p.toSubgraph hc.1 hc.2
  rw [regular_two_edge_vertex_card p.toSubgraph hc.2] at hthree
  simp only [Set.ncard_pair (by simp : ((false,none) : Base r) ≠ (true,none))] at hh
  omega

/-- Adding an isolated apex to a forest leaves a forest. -/
lemma deleted_cone_acyclic {V : Type*} [Fintype V] (T : SimpleGraph V)
    (a : V) (ht : T.IsAcyclic) : ((fullCone T).deleteIncidenceSet none).IsAcyclic := by
  intro v p hp
  let A := (fullCone T).deleteIncidenceSet none
  let hAG : A ≤ fullCone T := (fullCone T).deleteIncidenceSet_le none
  let q := p.mapLe hAG
  have hq : q.IsCycle := hp.mapLe hAG
  have hs : ∀ x ∈ q.support, x ∈ Set.range (Option.some : V → Option V) := by
    intro x hx
    cases x with
    | some x => exact ⟨x,rfl⟩
    | none =>
      have hmem : none ∈ p.toSubgraph.verts := by
        apply p.mem_verts_toSubgraph.mpr
        simpa only [q,Walk.support_mapLe_eq_support] using hx
      have hc := cycle_subgraph_regular A hp
      have hd := hc.2 ⟨none,hmem⟩
      have hpos : 0 < p.toSubgraph.coe.degree ⟨none,hmem⟩ := by
        simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd ⊢
        omega
      obtain ⟨w,hw⟩ := (p.toSubgraph.coe.degree_pos_iff_exists_adj ⟨none,hmem⟩).mp hpos
      exact ((deleteIncidenceSet_adj.mp (p.toSubgraph.adj_sub hw)).2.1 rfl).elim
  let q' := q.induce (Set.range (Option.some : V → Option V)) hs
  have hq' : q'.IsCycle := by
    apply (Walk.map_isCycle_iff_of_injective (f := (Embedding.induce _).toHom)
      Subtype.val_injective).mp
    simpa only [q',Walk.map_induce] using hq
  exact ht _ (hq'.map (FanPaths.pullbackHom_injective T Set.univ a))

abbrev graph (r : ℕ) := fullCone (base r)

lemma graph_even {r : ℕ} (hr : Even r) : ∀ v, Even ((graph r).degree v) := by
  apply cone_even_of_odd
  · simp only [Base,Fintype.card_prod,Fintype.card_bool,Fintype.card_option,Fintype.card_fin]
    exact even_two_mul _
  · rintro ⟨b,x⟩
    cases x with
    | none =>
      rw [center_degree]
      exact hr.add_odd odd_one
    | some i => rw [leaf_degree]; exact odd_one

lemma graph_critical {r : ℕ} (hr : Even r) : IsCountCritical (r+1) (graph r) := by
  apply FeedbackKernels.critical_of_feedback (graph_even hr) none
    (deleted_cone_acyclic (base r) (false,none) (base_acyclic r)) (r+1)
  rw [degree_apex]
  simp [Base]

/-- The family has zero integral-minus-fractional gap. Its light triangle
therefore does not obstruct fractional rounding. -/
lemma graph_optimum {r : ℕ} (hr : Even r) :
    FractionalEnvelope.optimum (graph r) = (r+1 : ℝ) := by
  have hu := FractionalEnvelope.optimum_le_number (graph r) (graph_even hr)
  rw [(graph_critical hr).2.1] at hu
  have hl := FractionalEnvelope.degree_le_twice_optimum (graph r) (graph_even hr) none
  rw [degree_apex] at hl
  simp only [Base,Fintype.card_prod,Fintype.card_bool,Fintype.card_option,Fintype.card_fin,
    Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] at hl hu
  linarith

lemma graph_invariant (r : ℕ) : InvariantPartitions.HasInvariantCount (graph r) :=
  FeedbackKernels.invariant_of_feedback none
    (deleted_cone_acyclic (base r) (false,none) (base_acyclic r))

lemma graph_order (r : ℕ) : Fintype.card (Option (Base r)) = 2*r+3 := by
  simp [Base]
  omega

def triangle (r : ℕ) : (graph r).Walk none none :=
  .cons (by trivial : (graph r).Adj none (some (false,none))) <|
  .cons (show (graph r).Adj (some (false,none)) (some (true,none)) from by
    change (false : Bool) ≠ true
    decide) <|
  .cons (by trivial : (graph r).Adj (some (true,none)) none) .nil

lemma triangle_isCycle (r : ℕ) : (triangle r).IsCycle := by
  apply (Walk.cons_isCycle_iff _ _).mpr
  constructor
  · rw [Walk.isPath_def]
    change [some (false,none),some (true,none),(none : Option (Base r))].Nodup
    simp
  · simp

/-- The distinguished cycle can avoid every degree-two vertex, even though
this family is count-critical. -/
lemma triangle_degrees (r : ℕ) (v : Option (Base r))
    (hv : v ∈ (triangle r).support) : r+2 ≤ (graph r).degree v := by
  simp only [triangle,Walk.support_cons,Walk.support_nil,List.mem_cons,
    List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · rw [degree_apex]
    simp [Base]
    omega
  · rw [degree_old,center_degree]
  · rw [degree_old,center_degree]
  · rw [degree_apex]
    simp [Base]
    omega

lemma triangle_minimum_extension {r : ℕ} (hr : Even r) :
    ∃ D : Finset (graph r).Subgraph,
      (∀ C ∈ D, C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (graph r) D ∧ (triangle r).toSubgraph ∈ D ∧ D.card = r+1 := by
  have hG := graph_critical hr
  have hc := cycle_subgraph_regular (graph r) (triangle_isCycle r)
  obtain ⟨D,hcD,hdD,hmem,hb⟩ := cycle_lift (graph_even hr) (triangle r).toSubgraph hc
  rw [hG.residual_number _ hc] at hb
  have hl := number_le (graph r) D hcD hdD
  rw [hG.2.1] at hl
  exact ⟨D,hcD,hdD,hmem,by omega⟩

end Erdos184.DoubleStarCone
