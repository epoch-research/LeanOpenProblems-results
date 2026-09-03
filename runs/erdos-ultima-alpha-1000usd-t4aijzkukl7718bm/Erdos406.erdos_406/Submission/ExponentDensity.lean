import Submission.Work

/-! A density-zero consequence of the already verified trailing-digit count.
This is a sparsity theorem, not a proof of finiteness in Erdős 406. -/

namespace Erdos406Density
open Filter
open scoped Topology

noncomputable def countBelow (P : ℕ → Prop) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter P).card

lemma countBelow_mono (P : ℕ → Prop) : Monotone (countBelow P) := by
  classical
  intro M N hMN
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨lt_of_lt_of_le hn.1 hMN, hn.2⟩

lemma nat_log_three_tendsto : Tendsto (Nat.log 3) atTop atTop := by
  apply tendsto_atTop.mpr
  intro r
  filter_upwards [eventually_ge_atTop (3 ^ r)] with N hN
  exact Nat.le_log_of_pow_le (by decide) hN

lemma count_ratio_bound (P : ℕ → Prop)
    (hcount : ∀ r : ℕ, countBelow P (3 ^ r) ≤ 2 ^ r) (N : ℕ) :
    (countBelow P N : ℝ) / N ≤ 2 * (2 / 3 : ℝ) ^ Nat.log 3 N := by
  by_cases hN : N = 0
  · subst N
    simp
  · let r := Nat.log 3 N
    have hupper : countBelow P N ≤ 2 ^ (r + 1) :=
      (countBelow_mono P (Nat.lt_pow_succ_log_self (by decide : 1 < 3) N).le).trans
        (hcount (r + 1))
    have hlower : (3 : ℝ) ^ r ≤ (N : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 3 hN
    have hp : (0 : ℝ) < 3 ^ r := by positivity
    calc
      (countBelow P N : ℝ) / N ≤ (2 : ℝ) ^ (r + 1) / N := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hupper
      _ ≤ (2 : ℝ) ^ (r + 1) / 3 ^ r :=
        div_le_div_of_nonneg_left (by positivity) hp hlower
      _ = 2 * (2 / 3 : ℝ) ^ r := by rw [div_pow, pow_succ]; ring

/-- A uniform geometric counting estimate implies natural density zero.
It does not imply that the set is finite. -/
theorem density_zero_of_geometric_bound (P : ℕ → Prop)
    (hcount : ∀ r : ℕ, countBelow P (3 ^ r) ≤ 2 ^ r) :
    Tendsto (fun N : ℕ => (countBelow P N : ℝ) / N) atTop (𝓝 0) := by
  have hpow : Tendsto (fun r : ℕ => (2 / 3 : ℝ) ^ r) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlimit : Tendsto (fun N : ℕ => 2 * (2 / 3 : ℝ) ^ Nat.log 3 N) atTop (𝓝 0) := by
    simpa using (hpow.comp nat_log_three_tendsto).const_mul 2
  exact squeeze_zero (fun N => by positivity) (count_ratio_bound P hcount) hlimit

/-- The exponents of good powers of four have natural density zero. -/
theorem good_four_exponents_density_zero :
    Tendsto (fun N : ℕ =>
      (countBelow (fun m => Nat.digits 3 (4 ^ m) ⊆ [0, 1]) N : ℝ) / N)
      atTop (𝓝 0) := by
  apply density_zero_of_geometric_bound
  intro r
  unfold countBelow
  convert Erdos406Work.good_four_powers_card_le r using 1
  congr 1
  exact Finset.filter_congr_decidable ..

/-- The exponents of good powers of two have natural density zero.
No eventual cutoff is asserted. -/
theorem good_two_exponents_density_zero :
    Tendsto (fun N : ℕ =>
      (countBelow (fun k => Nat.digits 3 (2 ^ k) ⊆ [0, 1]) N : ℝ) / N)
      atTop (𝓝 0) := by
  apply density_zero_of_geometric_bound
  intro r
  refine (countBelow_mono _ (by omega : 3 ^ r ≤ 2 * 3 ^ r)).trans ?_
  unfold countBelow
  convert Erdos406Work.good_two_powers_card_le r using 1
  congr 1
  exact Finset.filter_congr_decidable ..

#print axioms good_four_exponents_density_zero
#print axioms good_two_exponents_density_zero
end Erdos406Density
