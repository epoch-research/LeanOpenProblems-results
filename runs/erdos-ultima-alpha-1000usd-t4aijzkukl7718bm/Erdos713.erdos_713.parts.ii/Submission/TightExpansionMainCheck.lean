import FormalConjecturesUtil
import Submission.TightExpandingRegularization
open Filter SimpleGraph Asymptotics

namespace Erdos713

open scoped Classical in
/--
Must $\alpha$ be rational?

The same nondegeneracy condition on $G$ is used as in part (i). Rationality means that the real
number $\alpha$ lies in the image of the canonical embedding $\mathbb{Q}\to\mathbb{R}$.
-/
theorem erdos_713.parts.ii :
    ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
      ∀ α c : ℝ, α ∈ Set.Ico 1 2 → 0 < c →
        Asymptotics.IsEquivalent atTop
          (fun n : ℕ => (extremalNumber n G : ℝ))
          (fun n : ℕ => c * (n : ℝ) ^ α) →
        α ∈ Set.range ((↑) : ℚ → ℝ) := by
  intro q G hBipartite hEdges α c hα hc hAsymptotic
  by_cases hαone : α = 1
  · exact ⟨1, by simpa using hαone.symm⟩
  have hαgt : 1 < α := lt_of_le_of_ne hα.1 (Ne.symm hαone)
  have hSharpWitnesses :=
    Erdos713SharpDegree.exists_sharp_minimum_degree G hαgt hc hAsymptotic
  obtain ⟨κ, hκ, hExactExpanders⟩ :=
    Erdos713Expansion.exists_exact_expanders G hαgt hc hAsymptotic
  have hTight := Erdos713Tight.of_asymptotic hα.1 hc.ne' hAsymptotic
  obtain ⟨W, inst, H, hContained, hConnected, hDegree, hHTight, hCard, hMinimal, hCritical⟩ :=
    Erdos713Critical.exists_critical_connected_core G hαgt hTight
  have hHRate := hHTight.toHasRate
  obtain ⟨a, b, ha, hb, hRegularWitnesses⟩ :=
    Erdos713Regularization.exists_almost_regular_graphs H hαgt hHTight
  obtain ⟨d, hd, hLowerSequence⟩ := Erdos713Tight.exists_positive_lower_constant hHTight
  letI : Nonempty W := hConnected.nonempty
  have hHBipartite : H.IsBipartite := hBipartite.of_hom hContained.some.toHom
  by_cases hReduction : Erdos713Reduction.Reduces W H
  · exact Erdos713Rate.rational_of_reduces hReduction hHRate
  by_contra hIrrational
  have hProper : ∀ J : SimpleGraph W, J < H →
      (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)^α) :=
    fun _ hJ => Erdos713Critical.proper_subgraph_littleO H hCritical hJ
  have hHNoIso : ∀ v, ∃ w, H.Adj v w := by
    intro v
    apply (H.degree_pos_iff_exists_adj v).mp
    have hv : 2 ≤ H.degree v := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hDegree v
    omega
  obtain ⟨aH,bH,haH,hbH,hHTightRobustExpanders⟩ :=
    Erdos713TightExpansion.robust_scaled H hαgt hHTight hHNoIso hProper
  obtain ⟨V, instV, K, hKH, hKConnected, hKDegree, hKRate, hKCard, hKMinimal,
      β, hβ, hβα, hKProper⟩ :=
    Erdos713PowerCritical.exists_uniform_power_core H hαgt hHRate
  by_cases hKReduction : Erdos713Reduction.Reduces V K
  · exact hIrrational (Erdos713Rate.rational_of_reduces hKReduction hKRate)
  have hKNoConeSandwich : ∀ t : ℕ, 1 ≤ t →
      ¬(Erdos713C4.K22 ⊑ K ∧ K ⊑ Erdos713ConeFan.Fan t) := by
    rintro t ht ⟨hlo,hhi⟩
    exact hIrrational (Erdos713ConeFan.rational_of_sandwich ht hlo hhi hKRate)
  have hKNoTreeSuspension : ∀ (U : Type) [Fintype U] (J : SimpleGraph U)
      (χ : J.Coloring Bool), J.IsTree →
        ¬(Erdos713C4.K22 ⊑ K ∧ K ⊑ Erdos713Suspension.graph J χ) := by
    rintro U _ J χ hJ ⟨hlo,hhi⟩
    apply hIrrational
    refine ⟨3/2,?_⟩
    simpa only [Rat.cast_div,Rat.cast_ofNat] using Erdos713Rate.rate_unique
      (Erdos713Suspension.tree_sandwich_rate J χ hJ K hlo hhi) hKRate
  have hKLower : ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ,
      N ≤ n ∧ C * (n : ℝ)^(β : ℝ) < (extremalNumber n K : ℝ) :=
    Erdos713PowerCritical.exists_lower_above_smaller_power hKRate hβ hβα
  have hKBipartite : K.IsBipartite := hHBipartite.of_hom hKH.some.toHom
  obtain ⟨γ, hβγ, hγα⟩ := exists_rat_btwn hβα
  have hKNoIso : ∀ v, ∃ w, K.Adj v w := by
    intro v
    apply (K.degree_pos_iff_exists_adj v).mp
    have hv : 2 ≤ K.degree v := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hKDegree v
    omega
  obtain ⟨R, hR, hKRobustRegular⟩ :=
    Erdos713ExpandingRegularization.robust_of_rate K hKRate hβ hβγ hγα hKNoIso hKProper
  have hKLarge : 8 ≤ Fintype.card V := by
    by_contra hh
    exact hKReduction (Erdos713Structural.reduces_of_card_le_seven K hKBipartite (by omega))
  have hKSmallClassification : 9 ≤ Fintype.card V ∨
      ∃ k : Fin 32, k ∈ ({1,17,23,24,27,31} : Finset (Fin 32)) ∧
        Nonempty (K ≃g Erdos713EightCore.Graph (Erdos713EightCore.representative k)) ∧
          ((k = 1 ∧ (6 : ℝ)/5 < α ∧ α < (5 : ℝ)/4) ∨
          (k ∈ ({17,23,24,27} : Finset (Fin 32)) ∧ (3 : ℝ)/2 < α ∧ α < (8 : ℝ)/5) ∨
          (k = 31 ∧ (5 : ℝ)/3 < α ∧ α < (7 : ℝ)/4)) := by
    by_cases hNine : 9 ≤ Fintype.card V
    · exact Or.inl hNine
    · exact Or.inr (Erdos713SuspensionEight.irrational_rate_core_of_card_le_eight
        K hKBipartite (by omega) hKDegree hKRate hIrrational)
  have hLarge : 8 ≤ Fintype.card W := by
    by_contra hh
    exact hReduction (Erdos713Structural.reduces_of_card_le_seven H hHBipartite (by omega))
  have hSides : ∀ S : Set W, H.IsBipartiteWith S Sᶜ → 4 ≤ Nat.card S := by
    intro S hS
    by_contra hh
    exact hReduction (Erdos713Structural.reduces_of_small_bipartition H S hS (by omega))
  have hCoreEdges : Fintype.card W ≤ H.edgeFinset.card :=
    Erdos713Alteration.card_le_edges_of_degree_two H hDegree
  have hLower : 2 - ((Fintype.card W : ℝ) - 2) / ((H.edgeFinset.card : ℝ) - 1) ≤ α :=
    Erdos713Rate.rate_alteration_lower H (by omega) (by omega) (by omega) hHRate
  have hUpper : α ≤ 2 - 1 / (Fintype.card W : ℝ) :=
    Erdos713Rate.rate_bipartite_upper hHBipartite hHRate
  have hLowerStrict : 2 - ((Fintype.card W : ℝ) - 2) / ((H.edgeFinset.card : ℝ) - 1) < α := by
    apply lt_of_le_of_ne hLower
    intro heq
    apply hIrrational
    refine ⟨2 - ((Fintype.card W : ℚ) - 2) / ((H.edgeFinset.card : ℚ) - 1), ?_⟩
    push_cast
    exact heq
  have hUpperStrict : α < 2 - 1 / (Fintype.card W : ℝ) := by
    apply lt_of_le_of_ne hUpper
    intro heq
    apply hIrrational
    refine ⟨2 - 1 / (Fintype.card W : ℚ), ?_⟩
    push_cast
    exact heq.symm
  sorry

end Erdos713
