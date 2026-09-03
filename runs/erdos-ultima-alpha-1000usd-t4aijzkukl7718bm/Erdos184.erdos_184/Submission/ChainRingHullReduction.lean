import Submission.ChainRingNormalization

/-! Reduction of the two hull bounds to their canonical active-subgraph certificates.
The finite certificate hypothesis is explicit in this module. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
open Critical EdgeHull
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 10000

def host (ring : Bool) : SimpleGraph Vertex :=
  active ring (fun _ => Finset.univ) ⊔ if ring then closing else ⊥
instance (ring : Bool) : DecidableRel (host ring).Adj := by
  cases ring
  · exact inferInstanceAs (DecidableRel ((active false (fun _ => Finset.univ)) ⊔ (⊥ : SimpleGraph Vertex)).Adj)
  · exact inferInstanceAs (DecidableRel ((active true (fun _ => Finset.univ)) ⊔ closing).Adj)
lemma host_false : host false = base := by simp [host,base]
lemma host_true : host true = target := by simp [host,target]
lemma host_left_right : ∀ ring h i j,
    (host ring).Adj (.inl h) (.inr (i,j)) ↔ h ∈ hubs ring i := by decide +kernel
lemma host_hub_adj : ∀ ring h k, (host ring).Adj (.inl h) (.inl k) →
    ring = true ∧ (h = 3 ∨ k = 3) := by decide +kernel
lemma host_right_right : ∀ ring i j k l, ¬ (host ring).Adj (.inr (i,j)) (.inr (k,l)) := by
  decide +kernel
lemma host_right_degree : ∀ ring i j, (host ring).degree (.inr (i,j)) = 3 := by decide +kernel
lemma host_leaf_degree : (host true).degree (.inl 3) = 1 := by decide +kernel

open scoped Classical in
noncomputable def selected (ring : Bool) (R : SimpleGraph Vertex) (i : Fin 3) : Finset (Fin 6) :=
  Finset.univ.filter (fun j => ∀ h ∈ hubs ring i, R.Adj (.inl h) (.inr (i,j)))

lemma selected_mem (ring : Bool) (R : SimpleGraph Vertex) (i : Fin 3) (j : Fin 6) :
    j ∈ selected ring R i ↔ ∀ h ∈ hubs ring i, R.Adj (.inl h) (.inr (i,j)) := by
  classical
  simp [selected]

lemma selected_le (ring : Bool) (R : SimpleGraph Vertex) : active ring (selected ring R) ≤ R := by
  intro x y hxy
  cases x with
  | inl h =>
    cases y with
    | inl k => exact hxy.elim
    | inr p =>
      rcases p with ⟨i,j⟩
      exact (selected_mem ring R i j).mp hxy.1 h hxy.2
  | inr p =>
    rcases p with ⟨i,j⟩
    cases y with
    | inl h => exact ((selected_mem ring R i j).mp hxy.1 h hxy.2).symm
    | inr q => exact hxy.elim

lemma degree_le_two_of_not_selected {ring : Bool} {R : SimpleGraph Vertex}
    (hR : R ≤ host ring) {i : Fin 3} {j : Fin 6} (hj : j ∉ selected ring R i) :
    R.degree (.inr (i,j)) ≤ 2 := by
  classical
  have hnot : ¬ ∀ h ∈ hubs ring i, R.Adj (.inl h) (.inr (i,j)) :=
    fun h => hj ((selected_mem ring R i j).mpr h)
  push_neg at hnot
  obtain ⟨h,hh,hnot⟩ := hnot
  have hsub : R.neighborFinset (.inr (i,j)) ⊆ (host ring).neighborFinset (.inr (i,j)) := by
    intro w hw
    exact (host ring).mem_neighborFinset _ _ |>.mpr (hR (R.mem_neighborFinset _ _ |>.mp hw))
  have hmem : Sum.inl h ∈ (host ring).neighborFinset (.inr (i,j)) :=
    (host ring).mem_neighborFinset _ _ |>.mpr ((host_left_right ring h i j).mpr hh).symm
  have hne : R.neighborFinset (.inr (i,j)) ≠ (host ring).neighborFinset (.inr (i,j)) := by
    intro heq
    rw [← heq] at hmem
    exact hnot (R.mem_neighborFinset _ _ |>.mp hmem).symm
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hne⟩)
  have hd := host_right_degree ring i j
  simp only [SimpleGraph.card_neighborFinset_eq_degree,← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hlt hd ⊢
  omega

lemma selected_remainder_bridges {ring : Bool} {R : SimpleGraph Vertex}
    (hR : R ≤ host ring) (hm : Minimal R) :
    ∀ e ∈ R.edgeSet \ (active ring (selected ring R)).edgeSet, R.IsBridge e := by
  classical
  intro e he
  rcases he with ⟨heR,heK⟩
  induction e using Sym2.ind with | h x y =>
  change R.Adj x y at heR
  change ¬ (active ring (selected ring R)).Adj x y at heK
  cases x with
  | inl h =>
    cases y with
    | inl k =>
      obtain ⟨hr,hk⟩ := host_hub_adj ring h k (hR heR)
      subst ring
      rcases hk with rfl | rfl
      · apply hm.bridge_of_degree_le_two heR
        have hd := SimpleGraph.degree_le_of_le (v := (Sum.inl 3 : Vertex)) hR
        have hl := host_leaf_degree
        simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hl ⊢
        omega
      · have hb : R.IsBridge s(Sum.inl 3,Sum.inl h) := by
          apply hm.bridge_of_degree_le_two heR.symm
          have hd := SimpleGraph.degree_le_of_le (v := (Sum.inl 3 : Vertex)) hR
          have hl := host_leaf_degree
          simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hl ⊢
          omega
        exact Sym2.eq_swap ▸ hb
    | inr p =>
      rcases p with ⟨i,j⟩
      have hh := (host_left_right ring h i j).mp (hR heR)
      have hj : j ∉ selected ring R i := fun hj => heK ⟨hj,hh⟩
      have hb := hm.bridge_of_degree_le_two heR.symm (by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
          using degree_le_two_of_not_selected hR hj)
      exact Sym2.eq_swap ▸ hb
  | inr p =>
    rcases p with ⟨i,j⟩
    cases y with
    | inl h =>
      have hh := (host_left_right ring h i j).mp (hR heR.symm)
      have hj : j ∉ selected ring R i := fun hj => heK ⟨hj,hh⟩
      exact hm.bridge_of_degree_le_two heR (by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
          using degree_le_two_of_not_selected hR hj)
    | inr q =>
      rcases q with ⟨k,l⟩
      exact (host_right_right ring i j k l (hR heR)).elim

lemma host_hull_bound (ring : Bool)
    (hc : ∀ a : Fin 3 → Fin 7, ForestBound (canonical ring a)) : value (host ring) ≤ 24 := by
  have hh := value_bound_of_forest_remainders (host ring) (by
    intro R hR hm
    exact ⟨active ring (selected ring R),selected_le ring R,selected_remainder_bridges hR hm,
      active_forestBound ring hc (selected ring R)⟩)
  simpa only [card_vertex] using hh

end Erdos184Work.ChainRing
#print axioms Erdos184Work.ChainRing.host_hull_bound
