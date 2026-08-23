import Mathlib

open Complex Real Finset Nat
open scoped Real

set_option maxHeartbeats 0

noncomputable section

/-- `e(α) = exp(2 π i α)`. -/
def e (α : ℝ) : ℂ := Complex.exp (2 * π * I * α)

lemma e_add (α β : ℝ) : e (α + β) = e α * e β := by
  simp [e, mul_add, add_mul, Complex.exp_add]

lemma e_zero : e 0 = 1 := by simp [e]

lemma norm_e (α : ℝ) : ‖e α‖ = 1 := by
  simp [e, Complex.norm_exp]

lemma e_int (n : ℤ) : e n = 1 := by
  simpa [e, mul_comm, mul_left_comm, mul_assoc] using Complex.exp_int_mul_two_pi_mul_I n

lemma e_add_int (α : ℝ) (n : ℤ) : e (α + n) = e α := by
  rw [e_add, e_int, mul_one]

/-- Distance to nearest integer. -/
def distZ (α : ℝ) : ℝ := |α - round α|

lemma distZ_nonneg (α : ℝ) : 0 ≤ distZ α := abs_nonneg _

lemma distZ_le_half (α : ℝ) : distZ α ≤ 1 / 2 := abs_sub_round α

lemma abs_geom_e_le_len (N : ℕ) (α : ℝ) :
    ‖∑ k ∈ range (N + 1), e (k * α)‖ ≤ (N + 1 : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  simp [norm_e]

lemma abs_sin_pi_ge_two_distZ (x : ℝ) : 2 * distZ x ≤ |Real.sin (π * x)| := by
  have hx : |x - round x| ≤ 1 / 2 := abs_sub_round x
  have hhalf : |π * (x - round x)| ≤ π / 2 := by
    calc
      |π * (x - round x)| = π * |x - round x| := by
        rw [abs_mul, abs_of_nonneg pi_pos.le]
      _ ≤ π * (1 / 2) := mul_le_mul_of_nonneg_left hx pi_pos.le
      _ = π / 2 := by ring
  have hJ := mul_abs_le_abs_sin hhalf
  have hsin : |Real.sin (π * (x - (round x : ℝ)))| = |Real.sin (π * x)| := by
    have : π * (x - (round x : ℝ)) = π * x - (round x : ℝ) * π := by ring
    rw [this, Real.sin_sub, Real.sin_int_mul_pi (round x), Real.cos_int_mul_pi (round x)]
    simp [abs_mul]
  have : 2 / π * |π * (x - round x)| ≤ |Real.sin (π * x)| := by
    rwa [hsin] at hJ
  have hsimp : 2 / π * |π * (x - round x)| = 2 * |x - round x| := by
    rw [abs_mul, abs_of_nonneg pi_pos.le]
    field_simp
  rw [hsimp] at this
  simpa [distZ] using this

lemma e_eq_one_iff (α : ℝ) : e α = 1 ↔ ∃ n : ℤ, α = n := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (Complex.exp_eq_one_iff).mp h
    have hcoeff : (2 * π * I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
    have : (2 * π * I : ℂ) * α = (2 * π * I : ℂ) * n := by
      convert hn using 1; ring
    exact ⟨n, by exact_mod_cast (mul_left_cancel₀ hcoeff this)⟩
  · rintro ⟨n, rfl⟩
    exact e_int n

lemma abs_geom_e_le_dist (N : ℕ) (α : ℝ) (hα : distZ α ≠ 0) :
    ‖∑ k ∈ range (N + 1), e (k * α)‖ ≤ 1 / (2 * distZ α) := by
  have hz : e α ≠ 1 := by
    intro h
    obtain ⟨n, hn⟩ := (e_eq_one_iff α).mp h
    have : distZ α = 0 := by
      simp [distZ, hn, round_int]
    exact hα this
  have hpow : ∀ k : ℕ, e (k * α) = e α ^ k := by
    intro k
    induction k with
    | zero => simp [e_zero]
    | succ k ih =>
      rw [pow_succ, ← ih, ← e_add]
      ring_nf
  have hsum :
      ∑ k ∈ range (N + 1), e (k * α) =
        (e ((N + 1 : ℕ) * α) - 1) / (e α - 1) := by
    simp_rw [hpow]
    exact geom_sum_eq hz (N + 1)
  rw [hsum]
  have hnum : ‖e ((N + 1 : ℕ) * α) - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖e ((N + 1 : ℕ) * α)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by simp [norm_e]
      _ = 2 := by norm_num
  have hden : ‖e α - 1‖ = 2 * |Real.sin (π * α)| := by
    have : e α = Complex.exp (I * (2 * π * α)) := by
      simp [e, mul_comm, mul_left_comm, mul_assoc]
    rw [this, Complex.norm_exp_I_mul_ofReal_sub_one]
    simp [abs_mul, abs_two]
    ring
  have : ‖(e ((N + 1 : ℕ) * α) - 1) / (e α - 1)‖ ≤ 1 / |Real.sin (π * α)| := by
    rw [norm_div, hden]
    have : 2 / (2 * |Real.sin (π * α)|) = 1 / |Real.sin (π * α)| := by field_simp
    rw [← this]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hge : 1 / |Real.sin (π * α)| ≤ 1 / (2 * distZ α) := by
    have hpos : 0 < 2 * distZ α :=
      mul_pos two_pos (lt_of_le_of_ne (distZ_nonneg α) (Ne.symm hα))
    exact one_div_le_one_div_of_le hpos (abs_sin_pi_ge_two_distZ α)
  exact this.trans hge

lemma abs_weyl_triv (N : ℕ) (α : ℝ) (k : ℕ) :
    ‖∑ n ∈ range (N + 1), e (α * n ^ k)‖ ≤ (N + 1 : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  simp [norm_e]

#check abs_geom_e_le_dist
#check abs_weyl_triv
#check e_eq_one_iff

end
