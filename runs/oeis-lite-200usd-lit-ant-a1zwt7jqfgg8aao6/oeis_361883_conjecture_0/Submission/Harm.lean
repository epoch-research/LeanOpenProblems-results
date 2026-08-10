import FormalConjectures.Util.ProblemImports

open Nat Finset

namespace Harm

variable {p : ℕ} [hp : Fact p.Prime]

/-- `PD p t x` means "p^t divides x", encoded p-adically as `‖x‖ ≤ p^(-t)`. -/
def PD (p : ℕ) [Fact p.Prime] (t : ℤ) (x : ℚ_[p]) : Prop := ‖x‖ ≤ (p : ℝ) ^ (-t)

lemma p1 : (1:ℝ) ≤ (p:ℝ) := by
  have := hp.out.two_le; exact_mod_cast le_trans (by norm_num) this

lemma pR_pos : (0:ℝ) < (p:ℝ) := by
  have := hp.out.pos; exact_mod_cast this

lemma pR_ne : (p:ℝ) ≠ 0 := ne_of_gt pR_pos

lemma zpow_nonneg' (t : ℤ) : (0:ℝ) ≤ (p:ℝ) ^ (-t) := by positivity

lemma PD_mul {s t : ℤ} {a b : ℚ_[p]} (ha : PD p s a) (hb : PD p t b) :
    PD p (s + t) (a * b) := by
  unfold PD at *
  rw [norm_mul, neg_add, zpow_add₀ pR_ne]
  exact mul_le_mul ha hb (norm_nonneg _) (zpow_nonneg' _)

lemma PD_mul_right {t : ℤ} {a b : ℚ_[p]} (ha : PD p t a) (hb : ‖b‖ ≤ 1) :
    PD p t (a * b) := by
  unfold PD at *
  rw [norm_mul]
  calc ‖a‖ * ‖b‖ ≤ (p:ℝ)^(-t) * 1 := mul_le_mul ha hb (norm_nonneg _) (zpow_nonneg' _)
    _ = (p:ℝ)^(-t) := by ring

lemma PD_mul_left {t : ℤ} {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : PD p t b) :
    PD p t (a * b) := by
  rw [mul_comm]; exact PD_mul_right hb ha

lemma PD_sum {t : ℤ} {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p])
    (h : ∀ i ∈ s, PD p t (f i)) : PD p t (∑ i ∈ s, f i) := by
  unfold PD at *
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (zpow_nonneg' _) h

lemma PD_mono {s t : ℤ} {x : ℚ_[p]} (hst : s ≤ t) (h : PD p t x) : PD p s x := by
  unfold PD at *
  refine le_trans h ?_
  exact zpow_le_zpow_right₀ (by exact_mod_cast p1) (by omega)

lemma PD_p : PD p 1 (p : ℚ_[p]) := by
  unfold PD
  rw [Padic.norm_p]
  simp

lemma norm_natCast_coprime {i : ℕ} (hi : ¬ p ∣ i) : ‖(i : ℚ_[p])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  exact (hp.out.coprime_iff_not_dvd).2 hi

lemma norm_inv_natCast_coprime {i : ℕ} (hi : ¬ p ∣ i) : ‖(i : ℚ_[p])⁻¹‖ = 1 := by
  rw [norm_inv, norm_natCast_coprime hi]; norm_num

end Harm
