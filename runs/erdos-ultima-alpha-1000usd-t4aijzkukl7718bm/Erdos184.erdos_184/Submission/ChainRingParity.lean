import Submission.ChainRingBlocks

/-! Parity propagation and edge counts in the three two-port blocks. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 10000

def hubVertices (i : Fin 3) : Finset Vertex := {leftPort i,middlePort i,rightPort i}
lemma hubVertices_card : ∀ i, (hubVertices i).card = 3 := by decide
lemma hubVertices_independent : ∀ i u, u ∈ hubVertices i → ∀ v, v ∈ hubVertices i →
    ¬ (block i).Adj u v := by decide +kernel
lemma hubVertices_cover : ∀ i u v, (block i).Adj u v → u ∈ hubVertices i ∨ v ∈ hubVertices i := by
  decide +kernel
lemma hub_sum (i : Fin 3) (f : Vertex → ℕ) :
    (∑ v ∈ hubVertices i, f v) = f (leftPort i) + f (middlePort i) + f (rightPort i) := by
  fin_cases i <;> simp [hubVertices,leftPort,middlePort,rightPort,add_assoc]

open scoped Classical

lemma deg_mono {U : Type*} [Fintype U] {G H : SimpleGraph U} (h : G ≤ H) (v : U) :
    deg G v ≤ deg H v := by
  have hh := SimpleGraph.degree_le_of_le (v := v) h
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh

noncomputable def closingCount (S : SimpleGraph Vertex) : ℕ := if S.Adj (.inl 0) (.inl 3) then 1 else 0
lemma closingCount_le (S : SimpleGraph Vertex) : closingCount S ≤ 1 := by unfold closingCount; split_ifs <;> omega
lemma closingCount_zero_degree (S : SimpleGraph Vertex) : deg (S ⊓ closing) (.inl 0) = closingCount S := by
  rw [inf_closing]
  unfold closingCount
  split_ifs
  · simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using closing_degree_zero
  · simp [deg]
lemma closingCount_three_degree (S : SimpleGraph Vertex) : deg (S ⊓ closing) (.inl 3) = closingCount S := by
  rw [inf_closing]
  unfold closingCount
  split_ifs
  · simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using closing_degree_three
  · simp [deg]

lemma boundary_parity {S : SimpleGraph Vertex} (hS : S ≤ source)
    (heven : ∀ v, Even (deg S v)) (i : Fin 3) :
    deg (S ⊓ block i) (leftPort i) % 2 = closingCount S ∧
      deg (S ⊓ block i) (rightPort i) % 2 = closingCount S := by
  have hb0 := block_boundary_even hS heven 0
  have hb1 := block_boundary_even hS heven 1
  have hb2 := block_boundary_even hS heven 2
  have hp0 := degree_port_split hS 0
  have hp1 := degree_port_split hS 1
  have hp2 := degree_port_split hS 2
  have hp3 := degree_port_split hS 3
  change Even (deg (S ⊓ block 0) (.inl 0) + deg (S ⊓ block 0) (.inl 1)) at hb0
  change Even (deg (S ⊓ block 1) (.inl 1) + deg (S ⊓ block 1) (.inl 2)) at hb1
  change Even (deg (S ⊓ block 2) (.inl 2) + deg (S ⊓ block 2) (.inl 3)) at hb2
  change deg S (.inl 0) = deg (S ⊓ block 0) (.inl 0) + deg (S ⊓ closing) (.inl 0) at hp0
  change deg S (.inl 1) = deg (S ⊓ block 0) (.inl 1) + deg (S ⊓ block 1) (.inl 1) at hp1
  change deg S (.inl 2) = deg (S ⊓ block 1) (.inl 2) + deg (S ⊓ block 2) (.inl 2) at hp2
  change deg S (.inl 3) = deg (S ⊓ block 2) (.inl 3) + deg (S ⊓ closing) (.inl 3) at hp3
  rw [closingCount_zero_degree] at hp0
  rw [closingCount_three_degree] at hp3
  have he0 := heven (.inl 0)
  have he1 := heven (.inl 1)
  have he2 := heven (.inl 2)
  have he3 := heven (.inl 3)
  rw [Nat.even_iff] at hb0 hb1 hb2 he0 he1 he2 he3
  have hc := closingCount_le S
  fin_cases i
  · change deg (S ⊓ block 0) (.inl 0) % 2 = closingCount S ∧ deg (S ⊓ block 0) (.inl 1) % 2 = closingCount S
    omega
  · change deg (S ⊓ block 1) (.inl 1) % 2 = closingCount S ∧ deg (S ⊓ block 1) (.inl 2) % 2 = closingCount S
    omega
  · change deg (S ⊓ block 2) (.inl 2) % 2 = closingCount S ∧ deg (S ⊓ block 2) (.inl 3) % 2 = closingCount S
    omega

lemma block_even_of_no_closing {S : SimpleGraph Vertex} (hS : S ≤ source)
    (heven : ∀ v, Even (deg S v)) (he : ¬ S.Adj (.inl 0) (.inl 3)) (i : Fin 3) :
    ∀ v, Even (deg (S ⊓ block i) v) := by
  intro v
  have hp := boundary_parity hS heven i
  simp only [closingCount,if_neg he] at hp
  by_cases hl : v = leftPort i
  · rw [hl,Nat.even_iff]; exact hp.1
  by_cases hr : v = rightPort i
  · rw [hr,Nat.even_iff]; exact hp.2
  rcases block_internal_degree hS i v hl hr with h | h
  · rw [h]; exact heven v
  · rw [h]; exact ⟨0,rfl⟩

lemma block_boundary_one {S : SimpleGraph Vertex} (hS : S ≤ source)
    (heven : ∀ v, Even (deg S v)) (hmax : ∀ v, deg S v ≤ 2)
    (he : S.Adj (.inl 0) (.inl 3)) (i : Fin 3) :
    deg (S ⊓ block i) (leftPort i) = 1 ∧ deg (S ⊓ block i) (rightPort i) = 1 := by
  have hp := boundary_parity hS heven i
  simp only [closingCount,if_pos he] at hp
  have hl := (deg_mono (inf_le_left : S ⊓ block i ≤ S) (leftPort i)).trans (hmax _)
  have hr := (deg_mono (inf_le_left : S ⊓ block i ≤ S) (rightPort i)).trans (hmax _)
  omega

lemma degree_sum_independent_cover {U : Type*} [Fintype U] (G : SimpleGraph U) (A : Finset U)
    (hi : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)
    (hc : ∀ u v, G.Adj u v → u ∈ A ∨ v ∈ A) :
    (∑ v ∈ A, deg G v) = G.edgeFinset.card := by
  have hp : (A : Set U).PairwiseDisjoint (fun v => G.incidenceFinset v) := by
    intro u hu v hv huv
    apply Finset.disjoint_left.mpr
    intro e he he'
    exact hi u hu v hv (G.adj_of_mem_incidenceSet huv
      ((G.mem_incidenceFinset u e).mp he) ((G.mem_incidenceFinset v e).mp he'))
  have he : A.biUnion (fun v => G.incidenceFinset v) = G.edgeFinset := by
    ext e
    constructor
    · intro h
      obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp h
      exact G.incidenceFinset_subset v hv
    · intro h
      have hh := SimpleGraph.mem_edgeFinset.mp h
      induction e using Sym2.ind with | h u v =>
      rcases hc u v hh with hu | hv
      · exact Finset.mem_biUnion.mpr ⟨u,hu,(G.mem_incidenceFinset _ _).mpr
          (G.mk'_mem_incidenceSet_left_iff.mpr hh)⟩
      · exact Finset.mem_biUnion.mpr ⟨v,hv,(G.mem_incidenceFinset _ _).mpr
          (G.mk'_mem_incidenceSet_right_iff.mpr hh)⟩
  have hn := congrArg Finset.card he
  rw [Finset.card_biUnion hp] at hn
  simpa only [SimpleGraph.card_incidenceFinset_eq_degree,← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using hn

lemma block_edge_card {S : SimpleGraph Vertex} {i : Fin 3} (hS : S ≤ block i) :
    S.edgeFinset.card = deg S (leftPort i) + deg S (middlePort i) + deg S (rightPort i) := by
  have h := degree_sum_independent_cover S (hubVertices i)
    (fun u hu v hv huv => hubVertices_independent i u hu v hv (hS huv))
    (fun u v huv => hubVertices_cover i u v (hS huv))
  rw [hub_sum] at h
  exact h.symm

lemma block_edge_card_le_six {S : SimpleGraph Vertex} {i : Fin 3} (hS : S ≤ block i)
    (hmax : ∀ v, deg S v ≤ 2) : S.edgeFinset.card ≤ 6 := by
  rw [block_edge_card hS]
  have h0 := hmax (leftPort i)
  have h1 := hmax (middlePort i)
  have h2 := hmax (rightPort i)
  omega

lemma closing_block_edge_card_le_four {S : SimpleGraph Vertex} (hS : S ≤ source)
    (heven : ∀ v, Even (deg S v)) (hmax : ∀ v, deg S v ≤ 2)
    (he : S.Adj (.inl 0) (.inl 3)) (i : Fin 3) : (S ⊓ block i).edgeFinset.card ≤ 4 := by
  have hb := block_boundary_one hS heven hmax he i
  have hm := (deg_mono (inf_le_left : S ⊓ block i ≤ S) (middlePort i)).trans (hmax _)
  have hc := block_edge_card (inf_le_right : S ⊓ block i ≤ block i)
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hc ⊢
  omega

end Erdos184Work.ChainRing
#print axioms Erdos184Work.ChainRing.block_even_of_no_closing
#print axioms Erdos184Work.ChainRing.closing_block_edge_card_le_four
