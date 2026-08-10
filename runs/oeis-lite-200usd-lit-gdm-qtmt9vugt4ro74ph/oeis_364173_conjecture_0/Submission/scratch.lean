import Mathlib
import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

theorem a_zero_eq_1 : a 0 = 1 := by
  dsimp [a]
  push_cast
  have h9 : (9 : ℝ) * 0 + 1 = 1 := by norm_num
  have h2 : (2 : ℝ) * 0 + 1 = 1 := by norm_num
  have h32 : (3 / 2 : ℝ) * 0 + 1 = 1 := by norm_num
  have h92 : (9 / 2 : ℝ) * 0 + 1 = 1 := by norm_num
  have h4 : (4 : ℝ) * 0 + 1 = 1 := by norm_num
  have h3 : (3 : ℝ) * 0 + 1 = 1 := by norm_num
  have h1 : (0 : ℝ) + 1 = 1 := by norm_num
  rw [h9, h2, h32, h92, h4, h3, h1]
  rw [Real.Gamma_one]
  ring

theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p hp h_p_ge_5 n r hn hr
  have h1 := h_int (n * p ^ r)
  have h2 := h_int (n * p ^ (r - 1))
  have h_spec1 : ((Classical.choose h1 : ℤ) : ℝ) = a (n * p ^ r) := Classical.choose_spec h1
  have h_spec2 : ((Classical.choose h2 : ℤ) : ℝ) = a (n * p ^ (r - 1)) := Classical.choose_spec h2
  rw [Int.modEq_iff_dvd]
  done



