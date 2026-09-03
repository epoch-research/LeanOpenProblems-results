import Submission.FiveEvenFailure
import Submission.FourEvenDegreeFour

/-! Further necessary conditions on a counterexample. These conditions are not
asserted to be contradictory in general. -/
namespace Erdos583MinimalParityProfileDevelopment
open SimpleGraph Erdos583Work Erdos583Work.ComponentDeficit
open Erdos583UnifiedMinimalDefectDevelopment Erdos583FiveEvenFailureDevelopment
open Erdos583FourEvenDegreeFourDevelopment Erdos583FourEvenNoncliqueDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
set_option Elab.async false

lemma degree_sum_lower_of_five {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hd : ∀ v, 5 ≤ Nat.card (G.neighborSet v)) :
    5*Fintype.card V+evenCount G ≤ 2*G.edgeSet.ncard := by
  classical
  have hp (v : V) :
      5+(if Even (Nat.card (G.neighborSet v)) then 1 else 0) ≤
        Nat.card (G.neighborSet v) := by
    have hv := hd v
    split_ifs with he
    · rw [Nat.even_iff] at he
      omega
    · omega
  have hs := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) ↦ hp v)
  rw [Finset.sum_add_distrib,GlobalCritical.sum_neighbor_ncard] at hs
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hs
  rw [←Finset.card_filter,←evenCount_eq_filter] at hs
  simpa only [Nat.mul_comm] using hs

lemma odd_minimal_edge_lower (F : MinimalFailure) (ho : Odd F.order) :
    5*F.order+7 ≤ 2*F.graph.edgeSet.ncard := by
  have hd := degree_sum_lower_of_five F.graph
    (DegreeFourReduction.min_degree_five_of_odd_failure F.smaller ho F.connected F.failure)
  have he := minimal_odd_failure_seven_even F ho
  simp only [Fintype.card_fin] at hd
  omega

lemma odd_minimal_order_ge_nine (F : MinimalFailure) (ho : Odd F.order) :
    9 ≤ F.order := by
  classical
  have he := minimal_odd_failure_seven_even F ho
  have hn := Set.ncard_le_card {v | Even (Nat.card (F.graph.neighborSet v))}
  change evenCount F.graph ≤ Nat.card (Fin F.order) at hn
  rw [Nat.card_fin] at hn
  by_contra hlt
  have hn7 : F.order=7 := by
    rw [Nat.odd_iff] at ho
    omega
  have hm := odd_minimal_edge_lower F ho
  have hcard : 21 ≤ F.graph.edgeFinset.card := by
    have hc : F.graph.edgeSet.ncard=F.graph.edgeFinset.card := by
      rw [←Set.ncard_coe_finset,F.graph.coe_edgeFinset]
    rw [hc] at hm
    omega
  have htop : F.graph=(⊤ : SimpleGraph (Fin F.order)) := by
    apply edgeFinset_inj.mp
    apply Finset.eq_of_subset_of_card_le (edgeFinset_mono le_top)
    simpa only [card_edgeFinset_top_eq_card_choose_two,Fintype.card_fin,hn7,
      show Nat.choose 7 2=21 by decide] using hcard
  have hgood := complete_erdos_583 (V := Fin F.order)
  rw [←htop] at hgood
  exact F.failure hgood

lemma failure_four_even_or_six {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hf : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) :
    evenCount G=4 ∨ 6 ≤ evenCount G := by
  have hthree : ¬evenCount G ≤ 3 := by
    intro h
    apply hf
    apply EndpointSelection.gallai_of_at_most_three_even G
    rw [evenCount_eq_filter] at h
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using h
  have hfive : evenCount G ≠ 5 := by
    intro h
    exact hf (Erdos583FiveEvenBoundDevelopment.five_even_path_bound h)
  omega

lemma failure_parity_profile {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hf : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) :
    (Odd (Fintype.card V) ∧ 7 ≤ evenCount G) ∨
    (Even (Fintype.card V) ∧
      (6 ≤ evenCount G ∨
        (evenCount G=4 ∧
          (∀ a b, Even (Nat.card (G.neighborSet a)) →
            Even (Nat.card (G.neighborSet b)) → a ≠ b → G.Adj a b) ∧
          (∀ a, Even (Nat.card (G.neighborSet a)) →
            6 ≤ Nat.card (G.neighborSet a))))) := by
  rcases Nat.even_or_odd (Fintype.card V) with he|ho
  · refine Or.inr ⟨he,?_⟩
    rcases failure_four_even_or_six G hf with hfour|hsix
    · exact Or.inr ⟨hfour,four_even_failure_clique hfour hf,
        four_even_failure_even_degree_ge_six hfour hf⟩
    · exact Or.inl hsix
  · exact Or.inl ⟨ho,odd_failure_seven_even G ho hf⟩

end Erdos583MinimalParityProfileDevelopment
