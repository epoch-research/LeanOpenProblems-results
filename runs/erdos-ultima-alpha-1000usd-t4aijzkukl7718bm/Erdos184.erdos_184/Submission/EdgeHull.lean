import Submission.Work

/-! The maximum decomposition number over all edge-subgraphs.
This file does not establish compression monotonicity or a linear bound. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.EdgeHull
open Critical Compression

set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V]

noncomputable def value (G : SimpleGraph V) : ℕ :=
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite _
  Finset.univ.sup (fun R : SimpleGraph V => if R ≤ G then number R else 0)

lemma number_le_value (G : SimpleGraph V) : number G ≤ value G := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite _
  have h := Finset.le_sup (f := fun R : SimpleGraph V => if R ≤ G then number R else 0)
    (Finset.mem_univ G)
  simpa only [value, if_pos le_rfl] using h

lemma le_value {G R : SimpleGraph V} (hRG : R ≤ G) : number R ≤ value G := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite _
  have h := Finset.le_sup (f := fun R : SimpleGraph V => if R ≤ G then number R else 0)
    (Finset.mem_univ R)
  simpa only [value, if_pos hRG] using h

lemma value_le_iff (G : SimpleGraph V) (k : ℕ) :
    value G ≤ k ↔ ∀ R ≤ G, number R ≤ k := by
  classical
  constructor
  · intro h R hR
    exact (le_value hR).trans h
  · intro h
    unfold value
    apply Finset.sup_le
    intro R _
    split_ifs with hR
    · exact h R hR
    · exact Nat.zero_le k

lemma monotone : Monotone (value (V := V)) := by
  intro G H hGH
  apply (value_le_iff G (value H)).mpr
  intro R hRG
  exact le_value (hRG.trans hGH)

lemma exists_maximizer (G : SimpleGraph V) :
    ∃ R : SimpleGraph V, R ≤ G ∧ number R = value G := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite _
  let S : Finset (SimpleGraph V) := Finset.univ.filter (· ≤ G)
  have hS : S.Nonempty := ⟨G, by simp [S]⟩
  obtain ⟨R,hR,hm⟩ := Finset.exists_max_image S number hS
  have hRG : R ≤ G := (Finset.mem_filter.mp hR).2
  refine ⟨R,hRG,le_antisymm (le_value hRG) ?_⟩
  apply (value_le_iff G (number R)).mpr
  intro T hT
  exact hm T (by simp [S,hT])

/-- Minimality under every proper edge-subgraph, not merely single-edge deletion. -/
def Minimal (G : SimpleGraph V) : Prop :=
  ∀ R : SimpleGraph V, R ≤ G → R ≠ G → number R < number G

lemma edge_card_lt_of_ne {G R : SimpleGraph V} (hRG : R ≤ G) (hne : R ≠ G) :
    R.edgeFinset.card < G.edgeFinset.card := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨SimpleGraph.edgeFinset_mono hRG, ?_⟩
  exact fun h => hne (SimpleGraph.edgeFinset_inj.mp h)

lemma exists_minimal_maximizer (G : SimpleGraph V) (hpos : 0 < value G) :
    ∃ R : SimpleGraph V, R ≤ G ∧ Minimal R ∧ number R = value G := by
  classical
  obtain ⟨T,hTG,hT⟩ := exists_maximizer G
  obtain ⟨R,hRT,hbad,hmin⟩ := exists_edge_minimal_above T (value G - 1) (by omega)
  have hRG := hRT.trans hTG
  have hnum : number R = value G := by
    have hle := le_value hRG
    omega
  refine ⟨R,hRG,?_,hnum⟩
  intro S hSR hne
  have hs := hmin S hSR (edge_card_lt_of_ne hSR hne)
  omega

lemma Minimal.edgeCritical {G : SimpleGraph V} (hm : Minimal G) : EdgeCritical G := by
  intro e
  have hne : G.deleteEdges {e.val} ≠ G := by
    intro h
    have he : e.val ∉ (G.deleteEdges {e.val}).edgeSet := by
      simp [SimpleGraph.edgeSet_deleteEdges]
    exact he (h.symm ▸ e.property)
  have hlo := hm _ (G.deleteEdges_le _) hne
  have hhi := number_restore_edge G e
  omega

end Erdos184Work.EdgeHull

#print axioms Erdos184Work.EdgeHull.exists_minimal_maximizer
#print axioms Erdos184Work.EdgeHull.Minimal.edgeCritical

namespace Erdos184Work.Compression
variable {V : Type*} {G H : SimpleGraph V} {u v w x y : V}

lemma transfer_self (G : SimpleGraph V) (u : V) : transfer G u u = G := by
  ext x y
  simp [transfer, SimpleGraph.fromRel_adj]

lemma transfer_adj_pair (G : SimpleGraph V) (u v : V) :
    (transfer G u v).Adj u v ↔ G.Adj u v := by
  by_cases huv : u = v
  · subst v
    simp
  · simp [transfer, SimpleGraph.fromRel_adj, huv, Ne.symm huv]

lemma transfer_adj_left (G : SimpleGraph V) (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v) :
    (transfer G u v).Adj u w ↔ G.Adj u w ∨ G.Adj v w := by
  simp only [transfer, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
    SimpleGraph.fromRel_adj]
  simp only [huv, hwu, hwv, true_and, false_and, or_false]
  tauto

lemma transfer_adj_right (G : SimpleGraph V) (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v) :
    (transfer G u v).Adj v w ↔ G.Adj v w ∧ G.Adj u w := by
  simp only [transfer, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
    SimpleGraph.fromRel_adj]
  simp only [Ne.symm huv, hwu, hwv, true_and, false_and, or_false]
  tauto

lemma transfer_adj_away (G : SimpleGraph V)
    (hxu : x ≠ u) (hxv : x ≠ v) (hyu : y ≠ u) (hyv : y ≠ v) :
    (transfer G u v).Adj x y ↔ G.Adj x y := by
  simp [transfer, SimpleGraph.fromRel_adj, hxu, hxv, hyu, hyv]

/-- Neighborhood transfer itself is monotone for graph inclusion.
This does NOT assert monotonicity of the minimum decomposition number. -/
lemma transfer_mono (hGH : G ≤ H) (u v : V) : transfer G u v ≤ transfer H u v := by
  by_cases huv : u = v
  · subst v
    simpa only [transfer_self] using hGH
  intro x y hxy
  by_cases hxy' : x = y
  · subst y
    exact (SimpleGraph.loopless _ _ hxy).elim
  by_cases hxu : x = u
  · subst x
    by_cases hyv : y = v
    · subst y
      exact (transfer_adj_pair H u v).mpr (hGH ((transfer_adj_pair G u v).mp hxy))
    · have hyu : y ≠ u := Ne.symm hxy'
      exact (transfer_adj_left H huv hyu hyv).mpr
        (((transfer_adj_left G huv hyu hyv).mp hxy).imp (fun h => hGH h) (fun h => hGH h))
  by_cases hxv : x = v
  · subst x
    by_cases hyu : y = u
    · subst y
      exact ((transfer_adj_pair H u v).mpr (hGH
        ((transfer_adj_pair G u v).mp hxy.symm))).symm
    · have hyv : y ≠ v := Ne.symm hxy'
      exact (transfer_adj_right H huv hyu hyv).mpr
        ⟨hGH ((transfer_adj_right G huv hyu hyv).mp hxy).1,
          hGH ((transfer_adj_right G huv hyu hyv).mp hxy).2⟩
  by_cases hyu : y = u
  · subst y
    exact ((transfer_adj_left H huv hxu hxv).mpr
      (((transfer_adj_left G huv hxu hxv).mp hxy.symm).imp (fun h => hGH h) (fun h => hGH h))).symm
  by_cases hyv : y = v
  · subst y
    exact ((transfer_adj_right H huv hxu hxv).mpr
      ⟨hGH ((transfer_adj_right G huv hxu hxv).mp hxy.symm).1,
        hGH ((transfer_adj_right G huv hxu hxv).mp hxy.symm).2⟩).symm
  exact (transfer_adj_away H hxu hxv hyu hyv).mpr
    (hGH ((transfer_adj_away G hxu hxv hyu hyv).mp hxy))

end Erdos184Work.Compression

#print axioms Erdos184Work.Compression.transfer_mono

namespace Erdos184Work.EdgeHull
open Critical Compression
variable {V : Type*} [Fintype V]

/-- A reduction of hull compression to globally edge-minimal graphs.
The hypothesis here is not proved: it includes adding the joining edge when
that edge is absent from the chosen minimal subgraph. -/
lemma transfer_value_le_of_minimal
    (hcore : ∀ R : SimpleGraph V, Minimal R → ∀ u v : V,
      number R ≤ value (transfer R u v ⊔ SimpleGraph.edge u v))
    (G : SimpleGraph V) (u v : V) :
    value G ≤ value (transfer G u v ⊔ SimpleGraph.edge u v) := by
  by_cases hz : value G = 0
  · rw [hz]
    exact Nat.zero_le _
  obtain ⟨R,hRG,hm,hn⟩ := exists_minimal_maximizer G (Nat.pos_of_ne_zero hz)
  rw [← hn]
  exact (hcore R hm u v).trans
    (monotone (sup_le_sup_right (transfer_mono hRG u v) _))

lemma adjacent_transfer_value_le_of_minimal
    (hcore : ∀ R : SimpleGraph V, Minimal R → ∀ u v : V,
      number R ≤ value (transfer R u v ⊔ SimpleGraph.edge u v))
    (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    value G ≤ value (transfer G u v) := by
  have h := transfer_value_le_of_minimal hcore G u v
  rwa [SimpleGraph.sup_edge_of_adj (transfer G u v) ((transfer_adj_pair G u v).mpr huv)] at h

end Erdos184Work.EdgeHull

#print axioms Erdos184Work.EdgeHull.adjacent_transfer_value_le_of_minimal
