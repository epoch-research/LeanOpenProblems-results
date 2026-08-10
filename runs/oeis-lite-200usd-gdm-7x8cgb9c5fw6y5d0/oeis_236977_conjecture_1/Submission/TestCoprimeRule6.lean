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

theorem coprime_partition_rule (n p a b m r : ℕ) 
    (h_n : n = p * m)
    (h_p : p = a + b)
    (h_phi : totient a * totient b = r ^ 2)
    (h_coprime_a : a.Coprime m)
    (h_coprime_b : b.Coprime m)
    (h_lt : a * m < (n - 1) / 2 + 1)
    (h_gt : a * m ≥ 1) :
    ∃ k ∈ Finset.Ico 1 ((n - 1) / 2 + 1), sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) := by
  use a * m
  have h_mem : a * m ∈ Finset.Ico 1 ((n - 1) / 2 + 1) := Finset.mem_Ico.mpr ⟨h_gt, h_lt⟩
  refine ⟨h_mem, ?_⟩
  have h_sub : n - a * m = b * m := by
    rw [h_n, h_p, add_mul]
    omega
  rw [h_sub]
  rw [totient_mul h_coprime_a]
  rw [totient_mul h_coprime_b]
  have h_eq : totient a * totient m * (totient b * totient m) = (totient a * totient b) * (totient m * totient m) := by ring
  rw [h_eq, h_phi]
  have h_sq : r ^ 2 * (totient m * totient m) = (r * totient m) ^ 2 := by
    rw [mul_pow]
    ring
  rw [h_sq]
  rw [Nat.sqrt_sq]
