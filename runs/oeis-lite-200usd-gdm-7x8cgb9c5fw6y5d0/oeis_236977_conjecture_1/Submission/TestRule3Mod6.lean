import FormalConjectures.Util.ProblemImports

open Nat

lemma Nat.sqrt_sq (x : ℕ) : sqrt (x ^ 2) = x := by
  have h1 : x * x ≤ x * x := le_rfl
  have h2 : x ≤ sqrt (x * x) := le_sqrt.mpr h1
  have h3 : sqrt (x * x) * sqrt (x * x) ≤ x * x := sqrt_le (x * x)
  have h4 : sqrt (x * x) ≤ x := by
    nlinarith
  have h5 : sqrt (x * x) = x := le_antisymm h4 h2
  rw [show x ^ 2 = x * x by ring]
  exact h5

theorem rule_3_mod_6 (n : ℕ) (h_mod : n % 6 = 3) (h_gt : n ≥ 9) :
    ∃ k ∈ Finset.Ico 1 ((n - 1) / 2 + 1), sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) := by
  have h_div : n % 3 = 0 := by omega
  have h_odd : (n / 3) % 2 = 1 := by omega
  let k := n / 3
  use k
  have h_gt_k : k ≥ 1 := by omega
  have h_lt_k : k < (n - 1) / 2 + 1 := by omega
  have h_mem : k ∈ Finset.Ico 1 ((n - 1) / 2 + 1) := Finset.mem_Ico.mpr ⟨h_gt_k, h_lt_k⟩
  refine ⟨h_mem, ?_⟩
  have h_sub : n - k = 2 * k := by omega
  rw [h_sub]
  have h_cop : (2 : ℕ).Coprime k := by
    rw [Nat.Coprime, Nat.gcd_comm]
    exact Nat.gcd_two_odd_of_odd h_odd
  rw [totient_mul h_cop]
  have h_tot2 : totient 2 = 1 := rfl
  rw [h_tot2]
  have h_prod : totient k * (1 * totient k) = totient k ^ 2 := by ring
  rw [h_prod, Nat.sqrt_sq]
