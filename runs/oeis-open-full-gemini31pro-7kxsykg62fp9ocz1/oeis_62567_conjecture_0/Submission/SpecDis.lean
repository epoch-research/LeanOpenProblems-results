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

theorem disproof_check (h : ∀ n : ℕ, 2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4)) : False := by
  have h5 := h 5 (by decide)
  -- 10^(3^3) - 1 = 10^27 - 1
  -- a(243) = 4899999987
  -- h5 says: a(243) = 10^27 - 1 <-> False
  -- So h5 means a(243) != 10^27 - 1.
  -- This is TRUE! So we CANNOT get False from h5!
  sorry
