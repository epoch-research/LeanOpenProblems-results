import os

with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    content = f.read()

# Let's find the start of the theorem g_and_not_E
start_signature = "theorem g_and_not_E"
start_idx = content.find(start_signature)

# Let's find the end, which is right before "lemma g_iterate_85_ge_85"
end_signature = "lemma g_iterate_85_ge_85"
end_idx = content.find(end_signature)

if start_idx == -1 or end_idx == -1:
    print("Error: signatures not found!")
    exit(1)

# Generate the 14 cases
cases_code = ""
bad_numbers = {
    87: 58,
    90: 60,
    93: 62,
    96: 64,
    99: 66,
    102: 68,
    105: 70,
    108: 72,
    111: 74,
    114: 76,
    117: 78,
    120: 80,
    123: 82,
    126: 84
}

for b, next_val in bad_numbers.items():
    cases_code += f"""          · have h_g_{b} : A006368_map_inv {b} = {next_val} := rfl
            have h_eq_n1 : A006368_map_inv^[n + 2] 85 = {next_val} := by
              rw [Function.iterate_succ' A006368_map_inv (n + 1)]
              exact h_g_{b} ▸ congr_arg A006368_map_inv h_eq_{b}
            have h_E : E_prime (A006368_map_inv^[n + 2] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt {next_val} (by decide)
            have h_E_85 := preimage_E_prime_iterate (n + 2) 85 h_E
            have h_not_E_85 : ¬ E_prime (A006368_map_inv^[2] 85) := (ih 1 (by omega) (by omega)).2
            have h_g_85_E_1 : E_prime (A006368_map_inv^[1] 85) := step_of_ge (by decide) h_E_85
            have h_g_85_E_2 : E_prime (A006368_map_inv^[2] 85) := step_of_ge (by decide) h_g_85_E_1
            exact h_not_E_85 h_g_85_E_2
"""

new_proof = f"""
lemma E_prime_iff (y : ℕ) : E_prime y ↔ ∃ n, A006368_map_inv^[n] y < 85 := by
  constructor
  · intro h
    induction h with
    | lt x h1 =>
      use 0
      exact h1
    | step x h ih =>
      rcases ih with ⟨n, hn⟩
      use n + 1
      have h_eq : A006368_map_inv (A006368_map_inv^[n] x) = A006368_map_inv^[n] (A006368_map_inv x) := by
        rw [← Function.iterate_succ', ← Function.iterate_succ]
      rw [h_eq] at hn
      exact hn
  · intro h
    rcases h with ⟨n, hn⟩
    induction n generalizing y with
    | zero =>
      exact E_prime.lt y hn
    | succ n ih =>
      have hn2 : A006368_map_inv^[n] (A006368_map_inv y) < 85 := by
        have h_eq : A006368_map_inv (A006368_map_inv^[n] y) = A006368_map_inv^[n] (A006368_map_inv y) := by
          rw [← Function.iterate_succ', ← Function.iterate_succ]
        rw [h_eq] at hn
        exact hn
      exact E_prime.step y (ih (A006368_map_inv y) hn2)

lemma g_and_not_E_pos (k : ℕ) (hk : k > 0) : A006368_map_inv^[k+1] 85 ≥ 85 ∧ ¬ E_prime (A006368_map_inv^[k+1] 85) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have h_ge : A006368_map_inv^[k+1] 85 ≥ 85 := by
      by_contra h_lt
      push_neg at h_lt
      rw [Function.iterate_succ' A006368_map_inv k] at h_lt
      simp only [Function.comp_apply] at h_lt
      cases k with
      | zero => omega
      | succ n =>
        have h_ge_n : A006368_map_inv^[n+1] 85 ≥ 85 := by
          by_cases hn : n = 0
          · subst hn; decide
          · exact (ih n (by omega) (by omega)).1
        by_cases h_not : A006368_map_inv^[n+1] 85 = 87 ∨ A006368_map_inv^[n+1] 85 = 90 ∨ A006368_map_inv^[n+1] 85 = 93 ∨ A006368_map_inv^[n+1] 85 = 96 ∨ A006368_map_inv^[n+1] 85 = 99 ∨ A006368_map_inv^[n+1] 85 = 102 ∨ A006368_map_inv^[n+1] 85 = 105 ∨ A006368_map_inv^[n+1] 85 = 108 ∨ A006368_map_inv^[n+1] 85 = 111 ∨ A006368_map_inv^[n+1] 85 = 114 ∨ A006368_map_inv^[n+1] 85 = 117 ∨ A006368_map_inv^[n+1] 85 = 120 ∨ A006368_map_inv^[n+1] 85 = 123 ∨ A006368_map_inv^[n+1] 85 = 126
        · rcases h_not with h_eq_87 | h_eq_90 | h_eq_93 | h_eq_96 | h_eq_99 | h_eq_102 | h_eq_105 | h_eq_108 | h_eq_111 | h_eq_114 | h_eq_117 | h_eq_120 | h_eq_123 | h_eq_126
{cases_code}        · have h_not_conj : A006368_map_inv^[n+1] 85 ≠ 87 ∧ A006368_map_inv^[n+1] 85 ≠ 90 ∧ A006368_map_inv^[n+1] 85 ≠ 93 ∧ A006368_map_inv^[n+1] 85 ≠ 96 ∧ A006368_map_inv^[n+1] 85 ≠ 99 ∧ A006368_map_inv^[n+1] 85 ≠ 102 ∧ A006368_map_inv^[n+1] 85 ≠ 105 ∧ A006368_map_inv^[n+1] 85 ≠ 108 ∧ A006368_map_inv^[n+1] 85 ≠ 111 ∧ A006368_map_inv^[n+1] 85 ≠ 114 ∧ A006368_map_inv^[n+1] 85 ≠ 117 ∧ A006368_map_inv^[n+1] 85 ≠ 120 ∧ A006368_map_inv^[n+1] 85 ≠ 123 ∧ A006368_map_inv^[n+1] 85 ≠ 126 := by
            push_neg at h_not
            exact h_not
          have h_ge_n1 := g_ge_85 (A006368_map_inv^[n+1] 85) h_ge_n h_not_conj
          omega
    refine ⟨h_ge, ?_⟩
    intro h_E
    have h_P_ind : ∀ z, E_prime z → ¬ (∃ i < k, A006368_map_inv^[i+1] 85 = z) := by
      intro z hz
      induction hz with
      | lt x h1 =>
        intro h_S
        rcases h_S with ⟨i, hi, h_eq⟩
        have h_ge_i := (ih i hi (by omega)).1
        rw [h_eq] at h_ge_i
        omega
      | step x h ih_step =>
        intro h_S
        rcases h_S with ⟨i, hi, h_eq⟩
        by_cases h_i : i + 1 < k
        · have h_S_g : ∃ j < k, A006368_map_inv^[j+1] 85 = A006368_map_inv x := by
            use i + 1
            refine ⟨h_i, ?_⟩
            rw [Function.iterate_succ' A006368_map_inv (i+1)]
            simp only [Function.comp_apply]
            rw [h_eq]
          exact ih_step h_S_g
        · have h_eq_k : i + 1 = k := by omega
          have h_E_k1 : E_prime (A006368_map_inv^[k+1] 85) := by
            have : A006368_map_inv^[k+1] 85 = A006368_map_inv x := by
              rw [← h_eq_k]
              rw [Function.iterate_succ' A006368_map_inv (i+1)]
              simp only [Function.comp_apply]
              rw [h_eq]
            rw [this]
            exact h
          have h_E_85 := preimage_E_prime_iterate (k+1) 85 h_E_k1
          have h_E_2 : E_prime (A006368_map_inv^[2] 85) := by
            have h_E_1 := step_of_ge (by decide) h_E_85
            exact step_of_ge (by decide) h_E_1
          have h_not_E_2 : ¬ E_prime (A006368_map_inv^[2] 85) := (ih 1 (by omega) (by omega)).2
          exact h_not_E_2 h_E_2
    have h_E_85 := preimage_E_prime_iterate (k+1) 85 h_E
    have h_g_85_E : E_prime (A006368_map_inv^[1] 85) := by
      cases h_E_85 with
      | lt y hy => omega
      | step y hy => exact hy
    have h_exists : ∃ i < k, A006368_map_inv^[i+1] 85 = A006368_map_inv^[1] 85 := by
      use 0
      refine ⟨hk, rfl⟩
    exact h_P_ind (A006368_map_inv^[1] 85) h_g_85_E h_exists

theorem g_and_not_E (k : ℕ) : A006368_map_inv^[k+1] 85 ≥ 85 ∧ ¬ E_prime (A006368_map_inv^[k+1] 85) := by
  by_cases hk : k = 0
  · subst hk
    refine ⟨by decide, ?_⟩
    intro h_E
    have h_E_85 := preimage_E_prime_iterate 1 85 h_E
    rw [E_prime_iff] at h_E_85
    rcases h_E_85 with ⟨M, hM⟩
    have h_M_pos : M > 0 := by
      by_contra h_zero
      have : M = 0 := by omega
      rw [this] at hM
      simp at hM
    rcases Nat.exists_eq_succ_of_ne_zero (by omega) with ⟨d, hd⟩
    subst hd
    have h_ge_pos := (g_and_not_E_pos d (by omega)).1
    omega
  · exact g_and_not_E_pos k (by omega)
"""

new_content = content[:start_idx] + new_proof + content[end_idx:]

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write(new_content)

print("Patch complete successfully!")
