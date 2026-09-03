import Submission.E30Bridge

/-! Compilation and dependency checks for the conditional Erdős 30 bridges. -/

#print axioms Erdos30Research.h
#print axioms Erdos30Research.sidon_card_le_maxSidonSubsetCard
#print axioms Erdos30Research.card_le_h
#print axioms Erdos30Research.not_isBigO_rpow_of_arbitrarily_large
#print axioms Erdos30Research.not_forall_isBigO_rpow_of_polynomial_lower_bound
#print axioms Erdos30Research.not_all_power_bounds_of_polynomial_excess
#print axioms Erdos30Research.card_le_endpoint
#print axioms Erdos30Research.sqrt_excess_of_diameter_saving
#print axioms Erdos30Research.polynomial_excess_family_of_diameter_saving
#print axioms Erdos30Research.not_all_power_bounds_of_diameter_saving

#check Erdos30Research.h
#check Erdos30Research.sidon_card_le_maxSidonSubsetCard
#check Erdos30Research.card_le_h
#check Erdos30Research.not_isBigO_rpow_of_arbitrarily_large
#check Erdos30Research.not_forall_isBigO_rpow_of_polynomial_lower_bound
#check Erdos30Research.not_all_power_bounds_of_polynomial_excess
#check Erdos30Research.card_le_endpoint
#check Erdos30Research.sqrt_excess_of_diameter_saving
#check Erdos30Research.polynomial_excess_family_of_diameter_saving
#check Erdos30Research.not_all_power_bounds_of_diameter_saving

open Filter Asymptotics Erdos30Research

-- Check the requested existential, arbitrarily-large formulation directly.
example
    (H : ∃ δ > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ M : ℕ, ∃ N ≥ M, ∃ B : Finset ℕ,
        IsSidon (B : Set ℕ) ∧ B ⊆ Finset.Icc 1 N ∧
        c * (N : ℝ) ^ δ ≤ (B.card : ℝ) - Real.sqrt N) :
    ¬ (∀ ε : ℝ, 0 < ε →
      (fun N : ℕ => (h N : ℝ) - Real.sqrt N) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ ε)) := by
  apply not_all_power_bounds_of_polynomial_excess
  obtain ⟨δ, hδ, c, hc, hlarge⟩ := H
  refine ⟨δ, hδ, c, hc, fun M => ?_⟩
  obtain ⟨N, hMN, B, hB, hBN, he⟩ := hlarge M
  exact ⟨N, hMN, B, hBN, hB, he⟩

-- An exact-cardinality family is in particular a family with at least k points.
example {α c : ℝ} (hα : 0 < α) (hc : 0 < c)
    (H : ∀ K : ℕ, ∃ k ≥ K, ∃ N : ℕ, ∃ B : Finset ℕ,
      B ⊆ Finset.Icc 1 N ∧ IsSidon (B : Set ℕ) ∧ B.card = k ∧
      (N : ℝ) ≤ (k : ℝ) ^ 2 - c * (k : ℝ) ^ (1 + α)) :
    ¬ (∀ ε : ℝ, 0 < ε →
      (fun N : ℕ => (h N : ℝ) - Real.sqrt N) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ ε)) := by
  apply not_all_power_bounds_of_diameter_saving hα hc
  intro K
  obtain ⟨k, hk, N, B, hBN, hB, hcard, hsave⟩ := H K
  exact ⟨k, hk, N, B, hBN, hB, hcard.ge, hsave⟩
