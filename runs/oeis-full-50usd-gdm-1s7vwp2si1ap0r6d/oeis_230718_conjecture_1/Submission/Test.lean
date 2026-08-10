import FormalConjectures.Util.ProblemImports

open Finset Nat

lemma helper_ineq (n N : ℕ) (hn : n ≥ 9) (hN1 : 3 ≤ N) (hN2 : N ≤ 2 * n + 3) :
    (N - 1) ^ n < n * (N - 1) ^ (n - 1) + (n.choose 2) * (N - 1) ^ (n - 2) + n * (N - 2) ^ (n - 1) + (n.choose 2) * (N - 2) ^ (n - 2) := by
  sorry





lemma no_sol_n_9 (N : ℕ) (hN1 : 14 ≤ N) (hN2 : N ≤ 26) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 9) = N ^ 9 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_10 (N : ℕ) (hN1 : 15 ≤ N) (hN2 : N ≤ 29) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 10) = N ^ 10 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_11 (N : ℕ) (hN1 : 16 ≤ N) (hN2 : N ≤ 32) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 11) = N ^ 11 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_12 (N : ℕ) (hN1 : 17 ≤ N) (hN2 : N ≤ 35) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 12) = N ^ 12 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_13 (N : ℕ) (hN1 : 18 ≤ N) (hN2 : N ≤ 38) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 13) = N ^ 13 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_14 (N : ℕ) (hN1 : 19 ≤ N) (hN2 : N ≤ 41) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 14) = N ^ 14 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_15 (N : ℕ) (hN1 : 20 ≤ N) (hN2 : N ≤ 44) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 15) = N ^ 15 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_16 (N : ℕ) (hN1 : 21 ≤ N) (hN2 : N ≤ 47) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 16) = N ^ 16 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_17 (N : ℕ) (hN1 : 22 ≤ N) (hN2 : N ≤ 50) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 17) = N ^ 17 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_18 (N : ℕ) (hN1 : 23 ≤ N) (hN2 : N ≤ 53) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 18) = N ^ 18 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_19 (N : ℕ) (hN1 : 24 ≤ N) (hN2 : N ≤ 56) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 19) = N ^ 19 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_20 (N : ℕ) (hN1 : 25 ≤ N) (hN2 : N ≤ 59) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 20) = N ^ 20 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_21 (N : ℕ) (hN1 : 26 ≤ N) (hN2 : N ≤ 62) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 21) = N ^ 21 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_22 (N : ℕ) (hN1 : 27 ≤ N) (hN2 : N ≤ 65) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 22) = N ^ 22 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_23 (N : ℕ) (hN1 : 28 ≤ N) (hN2 : N ≤ 68) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 23) = N ^ 23 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_24 (N : ℕ) (hN1 : 29 ≤ N) (hN2 : N ≤ 71) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 24) = N ^ 24 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_25 (N : ℕ) (hN1 : 30 ≤ N) (hN2 : N ≤ 74) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 25) = N ^ 25 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_26 (N : ℕ) (hN1 : 31 ≤ N) (hN2 : N ≤ 77) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 26) = N ^ 26 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_27 (N : ℕ) (hN1 : 32 ≤ N) (hN2 : N ≤ 80) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 27) = N ^ 27 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_28 (N : ℕ) (hN1 : 33 ≤ N) (hN2 : N ≤ 83) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 28) = N ^ 28 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_29 (N : ℕ) (hN1 : 34 ≤ N) (hN2 : N ≤ 86) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 29) = N ^ 29 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_30 (N : ℕ) (hN1 : 35 ≤ N) (hN2 : N ≤ 89) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 30) = N ^ 30 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_31 (N : ℕ) (hN1 : 36 ≤ N) (hN2 : N ≤ 92) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 31) = N ^ 31 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_32 (N : ℕ) (hN1 : 37 ≤ N) (hN2 : N ≤ 95) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 32) = N ^ 32 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_33 (N : ℕ) (hN1 : 38 ≤ N) (hN2 : N ≤ 98) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 33) = N ^ 33 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_34 (N : ℕ) (hN1 : 39 ≤ N) (hN2 : N ≤ 101) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 34) = N ^ 34 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide

lemma no_sol_n_35 (N : ℕ) (hN1 : 40 ≤ N) (hN2 : N ≤ 104) :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧ (Ico k N).sum (fun i => i ^ 35) = N ^ 35 := by
  intro h
  rcases h with ⟨k, hk1, hk2, h_sum⟩
  interval_cases N
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
  · interval_cases k <;> revert h_sum <;> decide
