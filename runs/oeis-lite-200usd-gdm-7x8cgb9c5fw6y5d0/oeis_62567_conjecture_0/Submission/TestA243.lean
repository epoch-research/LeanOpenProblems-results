import FormalConjectures.Util.ProblemImports

open Nat Classical

def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)
    if h_ex : ∃ k, P k then
      have HP : DecidablePred P := by infer_instance
      let k_min : ℕ := Nat.find h_ex
      k_min * n
    else
      0

theorem a_243_ne : a 243 ≠ 10^27 - 1 := by
  dsimp [a]
  split_ifs with h0
  · -- Case h_ex : ∃ k, P k
    -- We want to show Nat.find h0 * 243 ≠ 10^27 - 1.
    -- We can show Nat.find h0 ≤ 20164609.
    have h_le : Nat.find h0 ≤ 20164609 := by
      apply Nat.find_min'
      refine ⟨by decide, ?_⟩
      unfold reverse_nat
      simp; decide
    have h_val : Nat.find h0 * 243 ≤ 4899999987 := by
      omega
    omega
  · -- Case ¬ ∃ k, P k
    -- Here the value is 0, and 0 ≠ 10^27 - 1 is easy.
    decide
