import Submission.RingIndices

/-! Strong cyclic incidence patterns among edge-disjoint cycles. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleRings
open RingIndices RigidSwitching
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- There are `n+3` cycles, so the three-cycle case is the induction base. -/
structure Ring (G : SimpleGraph V) (n : ℕ) where
  vertex : Fin (n+3) → V
  injective : Function.Injective vertex
  piece : Fin (n+3) → G.Subgraph
  cycle : ∀ i, (piece i).coe.Connected ∧ (piece i).coe.IsRegularOfDegree 2
  disjoint : ∀ i j, i ≠ j → Disjoint (piece i).edgeSet (piece j).edgeSet
  incidence : ∀ i j, vertex i ∈ (piece j).verts ↔ i = j ∨ i = j+1

namespace Ring
variable {n : ℕ} (R : Ring G n)

def rotate (R : Ring G n) (o : Fin (n+3)) : Ring G n where
  vertex i := R.vertex (i+o)
  injective := fun _ _ h => add_right_cancel (R.injective h)
  piece i := R.piece (i+o)
  cycle i := R.cycle (i+o)
  disjoint i j hij := R.disjoint (i+o) (j+o) (fun h => hij (add_right_cancel h))
  incidence i j := by
    rw [R.incidence]
    have he : j+o+1 = j+1+o := by ac_rfl
    rw [he]
    simp only [add_right_cancel_iff]

lemma first_mem (i : Fin (n+3)) : R.vertex i ∈ (R.piece i).verts :=
  (R.incidence i i).mpr (Or.inl rfl)
lemma last_mem (i : Fin (n+3)) : R.vertex (i+1) ∈ (R.piece i).verts :=
  (R.incidence (i+1) i).mpr (Or.inr rfl)

lemma no_base (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (R : Ring G 0) : False := by
  apply TriangleContacts.no_subgraph_ring hrig heven (R.piece 0) (R.piece 1) (R.piece 2)
    (R.cycle 0) (R.cycle 1) (R.cycle 2)
    (R.disjoint 0 1 (by decide)) (R.disjoint 0 2 (by decide)) (R.disjoint 1 2 (by decide))
    (x := R.vertex 1) (y := R.vertex 0) (z := R.vertex 2)
  all_goals simp only [R.incidence]; decide

end Ring

/-- A two-cycle switch can retain any chosen contact on either original piece. -/
lemma switch_subgraphs (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (H K : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hdis : Disjoint H.edgeSet K.edgeSet)
    {u v x y : V} (huv : u ≠ v)
    (huH : u ∈ H.verts) (huK : u ∈ K.verts) (hvH : v ∈ H.verts) (hvK : v ∈ K.verts)
    (hx : x ∈ H.verts) (hy : y ∈ K.verts) :
    ∃ A : G.Subgraph, (A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      x ∈ A.verts ∧ y ∈ A.verts ∧ A.verts ⊆ H.verts ∪ K.verts ∧ A.edgeSet ⊆ H.edgeSet ∪ K.edgeSet := by
  obtain ⟨c,hc,hcH⟩ := LongRing.regular_cycle_walk_at H hH.1 hH.2 u huH
  obtain ⟨d,hd,hdK⟩ := LongRing.regular_cycle_walk_at K hK.1 hK.2 u huK
  have sc (w) : w ∈ c.support ↔ w ∈ H.verts := by rw [← Walk.mem_verts_toSubgraph,hcH]
  have sd (w) : w ∈ d.support ↔ w ∈ K.verts := by rw [← Walk.mem_verts_toSubgraph,hdK]
  have ec (e) : e ∈ c.edges ↔ e ∈ H.edgeSet := by rw [← Walk.mem_edges_toSubgraph,hcH]
  have ed (e) : e ∈ d.edges ↔ e ∈ K.edgeSet := by rw [← Walk.mem_edges_toSubgraph,hdK]
  have hcd : c.edges.Disjoint d.edges := List.disjoint_left.mpr
    (fun e he hf => Set.disjoint_left.mp hdis ((ec e).mp he) ((ed e).mp hf))
  have hinter (z) (hzC : z ∈ c.support) (hzD : z ∈ d.support) : z = u ∨ z = v := by
    by_contra hn
    push_neg at hn
    exact rigid_no_three_common_vertices hrig heven c d hc hd hcd huv hn.1.symm hn.2.symm
      ((sc u).mpr huH) ((sc v).mpr hvH) hzC ((sd u).mpr huK) ((sd v).mpr hvK) hzD
  obtain ⟨a,b,ha,hb,hab,hcover,hxa,hya⟩ := two_cycle_switch_through c d hc hd huv
    ((sc v).mpr hvH) ((sd v).mpr hvK) hcd hinter ((sc x).mpr hx) ((sd y).mpr hy)
  refine ⟨a.toSubgraph,cycle_coe_regular G ha,a.mem_verts_toSubgraph.mpr hxa,a.mem_verts_toSubgraph.mpr hya,?_,?_⟩
  · intro z hz
    have hz' := a.mem_verts_toSubgraph.mp hz
    obtain ⟨e,hea,hze⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil ha.not_nil).mp hz'
    rcases (hcover e).mp (Or.inl hea) with he | he
    · exact Or.inl ((sc z).mp (Walk.mem_support_of_mem_edges he hze))
    · exact Or.inr ((sd z).mp (Walk.mem_support_of_mem_edges he hze))
  · intro e he
    exact ((hcover e).mp (Or.inl (a.mem_edges_toSubgraph.mp he))).imp ((ec e).mp) ((ed e).mp)

#print axioms switch_subgraphs
#print axioms Ring.no_base
end Erdos184Work.CycleRings

namespace Erdos184Work.CycleRings
open RingIndices
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma Ring.shorten_at_zero {n : ℕ} (R : Ring G (n+1))
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    {u : V} (hu0 : u ∈ (R.piece 0).verts) (hu1 : u ∈ (R.piece 1).verts)
    (hu : u ≠ R.vertex 1) : Nonempty (Ring G n) := by
  have hv0 : R.vertex 1 ∈ (R.piece 0).verts := by simpa using R.last_mem 0
  have hv2 : R.vertex 2 ∈ (R.piece 1).verts := by simpa using R.last_mem 1
  obtain ⟨A,hA,hxA,hyA,hverts,hedges⟩ := switch_subgraphs hrig heven (R.piece 0) (R.piece 1)
    (R.cycle 0) (R.cycle 1) (R.disjoint 0 1 (by simp)) hu hu0 hu1 hv0 (R.first_mem 1)
    (R.first_mem 0) hv2
  have hdisA (i : Fin (n+3)) (hi : i ≠ 0) : Disjoint A.edgeSet (R.piece (skipOne i)).edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hf
    rcases hedges he with he | he
    · exact Set.disjoint_left.mp (R.disjoint 0 (skipOne i)
        (fun h => hi ((skipOne_eq_zero_iff i).mp h.symm))) he hf
    · exact Set.disjoint_left.mp (R.disjoint 1 (skipOne i) (skipOne_ne_one i).symm) he hf
  have hincA (i : Fin (n+3)) : R.vertex (skipOne i) ∈ A.verts ↔ i = 0 ∨ i = 1 := by
    constructor
    · intro hi
      rcases hverts hi with hi | hi
      · rcases (R.incidence (skipOne i) 0).mp hi with he | he
        · exact Or.inl ((skipOne_eq_zero_iff i).mp he)
        · exact (skipOne_ne_one i (by simpa using he)).elim
      · rcases (R.incidence (skipOne i) 1).mp hi with he | he
        · exact (skipOne_ne_one i he).elim
        · exact Or.inr ((skipOne_eq_two_iff i).mp (by simpa using he))
    · rintro (rfl | rfl)
      · simpa only [skipOne_zero] using hxA
      · simpa only [skipOne_one] using hyA
  refine ⟨{
    vertex := fun i => R.vertex (skipOne i)
    injective := fun _ _ h => skipOne_injective n (R.injective h)
    piece := fun i => if i = 0 then A else R.piece (skipOne i)
    cycle := ?_
    disjoint := ?_
    incidence := ?_
  }⟩
  · intro i
    have hA' := hA
    have hR' := R.cycle (skipOne i)
    simp only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hA' hR' ⊢
    by_cases hi : i = 0
    · have he : (if i = 0 then A else R.piece (skipOne i)) = A := if_pos hi
      exact (congrArg (fun H : G.Subgraph => H.coe.Connected ∧ ∀ v, Nat.card (H.coe.neighborSet v) = 2) he).mpr hA'
    · have he : (if i = 0 then A else R.piece (skipOne i)) = R.piece (skipOne i) := if_neg hi
      exact (congrArg (fun H : G.Subgraph => H.coe.Connected ∧ ∀ v, Nat.card (H.coe.neighborSet v) = 2) he).mpr hR' 
  · intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := hij.symm
      simpa only [if_pos rfl,if_neg hj] using hdisA j hj
    · by_cases hj : j = 0
      · subst j
        simpa only [if_pos rfl,if_neg hi] using (hdisA i hi).symm
      · simp only [if_neg hi,if_neg hj]
        exact R.disjoint (skipOne i) (skipOne j) (fun h => hij (skipOne_injective n h))
  · intro i j
    by_cases hj : j = 0
    · subst j
      simpa only [if_pos rfl,zero_add] using hincA i
    · simp only [if_neg hj,R.incidence,← skipOne_add_one j hj,(skipOne_injective n).eq_iff]

#print axioms Ring.shorten_at_zero
end Erdos184Work.CycleRings
