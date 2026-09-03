import Submission.Cycles

/-! A sharp degree-budget constraint on cycle decompositions.
This does not prove the existence of a linear-size decomposition. -/

open SimpleGraph
open scoped Classical
namespace Erdos184

lemma cycle_decomposition_incidence_sum {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph) (S : Finset V)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    2 * ∑ H ∈ D, (S.filter (fun v => v ∈ H.verts)).card = ∑ v ∈ S, G.degree v := by
  have hsum : (∑ H ∈ D, (S.filter (fun v => v ∈ H.verts)).card) =
      ∑ v ∈ S, (D.filter (fun H => v ∈ H.verts)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact cycle_decomposition_vertex_count G D hcy hd v

lemma cycle_decomposition_degree_lower {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (v : V) : G.degree v ≤ 2 * D.card := by
  rw [← cycle_decomposition_vertex_count G D hcy hd v]
  exact Nat.mul_le_mul_left _ (Finset.card_filter_le _ _)

lemma cycle_decomposition_degree_budget_rigidity {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph) (S : Finset V) (w : V)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hhit : ∀ H ∈ D, ∃ v ∈ S, v ∈ H.verts)
    (hbudget : ∑ v ∈ S, G.degree v = G.degree w) :
    2 * D.card = G.degree w ∧
      ∀ H ∈ D, w ∈ H.verts ∧ (S.filter (fun v => v ∈ H.verts)).card = 1 := by
  have hpos : ∀ H ∈ D, 1 ≤ (S.filter (fun v => v ∈ H.verts)).card := by
    intro H hH
    obtain ⟨v, hv, hvH⟩ := hhit H hH
    exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hvH⟩⟩
  have hsum := cycle_decomposition_incidence_sum G D S hcy hd
  rw [hbudget] at hsum
  have hle : D.card ≤ ∑ H ∈ D, (S.filter (fun v => v ∈ H.verts)).card := by
    calc
      D.card = ∑ _H ∈ D, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum hpos
  have hw := cycle_decomposition_degree_lower G D hcy hd w
  have hcard : 2 * D.card = G.degree w := by omega
  have hsum' : (∑ H ∈ D, (S.filter (fun v => v ∈ H.verts)).card) = D.card := by omega
  refine ⟨hcard, ?_⟩
  have hfilter : D.filter (fun H => w ∈ H.verts) = D := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    have hc := cycle_decomposition_vertex_count G D hcy hd w
    omega
  intro H hH
  refine ⟨?_, ?_⟩
  · have hHw : H ∈ D.filter (fun H => w ∈ H.verts) := hfilter.symm ▸ hH
    exact (Finset.mem_filter.mp hHw).2
  · have hrest : (D.erase H).card ≤
        ∑ K ∈ D.erase H, (S.filter (fun v => v ∈ K.verts)).card := by
      calc
        (D.erase H).card = ∑ _K ∈ D.erase H, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun K hK => hpos K (Finset.mem_of_mem_erase hK))
    have heq := Finset.add_sum_erase D
      (fun K => (S.filter (fun v => v ∈ K.verts)).card) hH
    dsimp only at heq
    have herase := Finset.card_erase_add_one hH
    have hHpos := hpos H hH
    omega

lemma cycle_decomposition_transversal_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph) (S : Finset V)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hhit : ∀ H ∈ D, ∃ v ∈ S, v ∈ H.verts) :
    2 * D.card ≤ ∑ v ∈ S, G.degree v := by
  rw [← cycle_decomposition_incidence_sum G D S hcy hd]
  apply Nat.mul_le_mul_left
  calc
    D.card = ∑ _H ∈ D, 1 := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro H hH
      obtain ⟨v, hv, hvH⟩ := hhit H hH
      exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hvH⟩⟩

lemma cycle_decomposition_transversal_degree_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph) (S : Finset V)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hhit : ∀ H ∈ D, ∃ v ∈ S, v ∈ H.verts) (w : V) :
    G.degree w ≤ ∑ v ∈ S, G.degree v :=
  (cycle_decomposition_degree_lower G D hcy hd w).trans
    (cycle_decomposition_transversal_bound G D S hcy hd hhit)

end Erdos184
