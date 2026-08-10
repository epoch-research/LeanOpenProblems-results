  by_cases h1 : ∃ k, c k ≥ 538
  · rcases h1 with ⟨k, hk⟩
    have h_5657 : 5657 ∈ Set.range (fun x : Fin 19 → ℕ => Finset.sum Finset.univ (fun i => c i * x i ^ 10)) := by
      rw [h_range]
      exact Set.mem_univ 5657
    exact contradiction_of_large_element c hc_pos h_rep h_sum k (c k) 5 537 5657 rfl (by rfl) h_5657 (by omega) (by omega) (by omega) (by decide) (by decide) (by decide)
  · push_neg at h1
    by_cases h2 : ∃ k, c k ≥ 512
    · rcases h2 with ⟨k, hk⟩
      have h_N : 1024 * 57 + (c k - 1) ∈ Set.range (fun x : Fin 19 → ℕ => Finset.sum Finset.univ (fun i => c i * x i ^ 10)) := by
        rw [h_range]
        exact Set.mem_univ _
      exact contradiction_of_large_element c hc_pos h_rep h_sum k (c k) 57 (c k - 1) (1024 * 57 + (c k - 1)) rfl rfl h_N (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · push_neg at h2
      -- Now ∀ k, c k ≤ 511
      by_cases h_255 : (∑ i ∈ Finset.filter (fun j => c j ≤ 255) Finset.univ, c i) < 312
      · have h_58623 : 58623 ∈ Set.range (fun x : Fin 19 → ℕ => Finset.sum Finset.univ (fun i => c i * x i ^ 10)) := by
          rw [h_range]
          exact Set.mem_univ 58623
        exact contradiction_of_small_sum c hc_pos h_sum 57 255 58623 255 (by rfl) h_58623 (by rfl) h_255 (by decide) (by decide)
      · push_neg at h_255
        sorry

end A271099
