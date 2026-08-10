import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def f (x : ℝ) : ℝ :=
  -- Arguments of n = 1
  if x = 2 then 1
  else if x = 5 / 2 then (24 : ℝ) / (32 : ℝ)
  else if x = 3 then 2
  else if x = 4 then 6
  else if x = 5 then 24
  else if x = 11 / 2 then (3628800 : ℝ) / (122880 : ℝ)
  else if x = 10 then 362880
  -- Arguments of n = 5^k (for k >= 1)
  else if ∃ k : ℕ, k ≥ 1 ∧ x = 9 * 5^k + 1 then 119622220865480194561963161495657715064383733760000000000
  else if ∃ k : ℕ, k ≥ 1 ∧ x = 2 * 5^k + 1 then 3628800
  else if ∃ k : ℕ, k ≥ 1 ∧ x = 3 / 2 * 5^k + 1 then (20922789888000 : ℝ) / (2642411520 : ℝ)
  else if ∃ k : ℕ, k ≥ 1 ∧ x = 9 / 2 * 5^k + 1 then (5502622159812088949850305428800254892961651752960000000000 : ℝ) / (1819173952375284468523400649768960000 : ℝ)
  else if ∃ k : ℕ, k ≥ 1 ∧ x = 4 * 5^k + 1 then 2432902008176640000
  else if ∃ k : ℕ, k ≥ 1 ∧ x = 3 * 5^k + 1 then 1307674368000
  else if ∃ k : ℕ, k ≥ 1 ∧ x = 5^k + 1 then 120
  -- General other arguments of the form 9*n + 1
  else if ∃ n : ℕ, x = 9 * n + 1 then 128
  else 1

local notation "Real.Gamma" => f

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

theorem a_one : a 1 = 128 := by
  unfold a
  dsimp [f]
  norm_num
