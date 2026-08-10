import FormalConjectures.Util.ProblemImports

open Filter Asymptotics Real

def F (n L : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k => ((n-k).choose k) ^ L

noncomputable def limit_value (L : ℕ) : ℝ :=
  let fib_L : ℝ := Nat.fib L
  let lucas_L : ℝ := (lucasNumber L : ℤ)
  (fib_L * sqrt 5 + lucas_L) / 2

theorem F_zero_eq (n : ℕ) : F n 0 = n / 2 + 1 := by
  simp [F]

lemma nat_div_two_le_succ_div_two (n : ℕ) : n / 2 ≤ (n + 1) / 2 := by
  apply Nat.div_le_div_right
  omega

lemma succ_div_two_le_nat_div_two_add_one (n : ℕ) : (n + 1) / 2 ≤ n / 2 + 1 := by
  omega

lemma real_nat_div_two_le_succ_div_two (n : ℕ) : (↑(n / 2) : ℝ) ≤ (↑((n + 1) / 2) : ℝ) := by
  exact (Nat.cast_le (α := ℝ)).mpr (nat_div_two_le_succ_div_two n)

lemma real_succ_div_two_le_nat_div_two_add_one (n : ℕ) : (↑((n + 1) / 2) : ℝ) ≤ ↑(n / 2) + 1 := by
  have h := (Nat.cast_le (α := ℝ)).mpr (succ_div_two_le_nat_div_two_add_one n)
  push_cast at h
  exact h


lemma nat_div_two_spec (n : ℕ) : n ≤ 2 * (n / 2) + 2 := by
  omega

lemma real_nat_div_two_spec (n : ℕ) : (n : ℝ) ≤ 2 * (((n / 2 : ℕ) : ℝ) + 1) := by
  have h := (Nat.cast_le (α := ℝ)).mpr (nat_div_two_spec n)
  push_cast at h
  linarith

lemma inv_denom_le (n : ℕ) (hn : 0 < n) : 1 / (((n / 2 : ℕ) : ℝ) + 1) ≤ 2 / (n : ℝ) := by
  have h1 : (n : ℝ) ≤ 2 * (((n / 2 : ℕ) : ℝ) + 1) := real_nat_div_two_spec n
  have h2 : 0 < (n : ℝ) := by positivity
  have h3 : 0 < (((n / 2 : ℕ) : ℝ) + 1) := by positivity
  rw [div_le_iff₀ h3]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ h2]
  simp only [one_mul]
  linarith


lemma tendsto_inv_nat_cast : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
  simp only [one_div]
  exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop



lemma tendsto_upper_bound : Tendsto (fun n : ℕ => 1 + 2 / (n : ℝ)) atTop (nhds 1) := by
  have h_lim : Tendsto (fun n : ℕ => 2 * (1 / (n : ℝ))) atTop (nhds (2 * 0)) := by
    apply Tendsto.const_mul
    exact tendsto_inv_nat_cast
  simp only [mul_zero] at h_lim
  have h_eq : (fun n : ℕ => 1 + 2 / (n : ℝ)) = (fun n : ℕ => 1 + 2 * (1 / (n : ℝ))) := by
    ext n
    ring
  rw [h_eq]
  have h_add_lim := Tendsto.const_add 1 h_lim
  simp only [add_zero] at h_add_lim
  exact h_add_lim




lemma ratio_ge_one (n : ℕ) : (1 : ℝ) ≤ (((((n + 1) / 2 : ℕ) : ℝ) + 1) / (((n / 2 : ℕ) : ℝ) + 1)) := by
  have h_pos : 0 < (((n / 2 : ℕ) : ℝ) + 1) := by positivity
  rw [le_div_iff₀ h_pos]
  simp only [one_mul]
  have h := real_nat_div_two_le_succ_div_two n
  linarith

lemma ratio_le_upper (n : ℕ) : (((((n + 1) / 2 : ℕ) : ℝ) + 1) / (((n / 2 : ℕ) : ℝ) + 1)) ≤ 1 + 1 / (((n / 2 : ℕ) : ℝ) + 1) := by
  have h_pos : 0 < (((n / 2 : ℕ) : ℝ) + 1) := by positivity
  have h_eq : 1 + 1 / (((n / 2 : ℕ) : ℝ) + 1) = ((((n / 2 : ℕ) : ℝ) + 1) + 1) / (((n / 2 : ℕ) : ℝ) + 1) := by
    rw [add_div, div_self (ne_of_gt h_pos)]
  rw [h_eq]
  rw [div_le_div_iff_of_pos_right h_pos]
  have h := real_succ_div_two_le_nat_div_two_add_one n
  linarith

lemma ratio_le_upper_bound (n : ℕ) (hn : 0 < n) :
    (((((n + 1) / 2 : ℕ) : ℝ) + 1) / (((n / 2 : ℕ) : ℝ) + 1)) ≤ 1 + 2 / (n : ℝ) := by
  have h1 := ratio_le_upper n
  have h2 := inv_denom_le n hn
  linarith

theorem oeis_181546_conjecture_0_zero :
    Tendsto (fun n => (F (n+1) 0 : ℝ) / (F n 0 : ℝ)) atTop (nhds (limit_value 0)) := by
  simp [F_zero_eq, limit_value, lucasNumber, LucasSequence.V]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun (_ : ℕ) => (1 : ℝ)) (h := fun (n : ℕ) => 1 + 2 / (n : ℝ))
  · exact tendsto_const_nhds
  · exact tendsto_upper_bound
  · exact Eventually.of_forall ratio_ge_one
  · have h_ev : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
    refine h_ev.mono ?_
    intro n hn
    exact ratio_le_upper_bound n hn




