import Submission.ConvolutionSquareStabilityExplore
import Submission.ResidueSeriesExplore

/-! Weighted L2 bounds for residue pushforwards of real sequences. -/
namespace Erdos66WeightedPushEnergy
open Filter Erdos66ResidueSeries Erdos66Generating
open scoped Topology Classical

lemma tsum_cauchy_schwarz {a b c : ℕ → ℝ}
    (ha : Summable a) (hb : Summable b) (hc : Summable c)
    (hb0 : ∀ n, 0 ≤ b n) (hc0 : ∀ n, 0 ≤ c n)
    (he : ∀ n, (a n)^2=b n*c n) :
    (∑' n, a n)^2 ≤ (∑' n, b n)*(∑' n, c n) := by
  apply le_of_tendsto_of_tendsto (ha.tendsto_sum_tsum_nat.pow 2)
    (hb.tendsto_sum_tsum_nat.mul hc.tendsto_sum_tsum_nat)
  exact Eventually.of_forall (fun N ↦ Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    (Finset.range N) (fun n _ ↦ hb0 n) (fun n _ ↦ hc0 n) (fun n _ ↦ he n))

lemma tsum_sq_le_sq_tsum {f : ℕ → ℝ} (hf : Summable f)
    (hf2 : Summable (fun n ↦ (f n)^2)) (hpos : ∀ n, 0 ≤ f n) :
    (∑' n, (f n)^2) ≤ (∑' n, f n)^2 := by
  apply le_of_tendsto_of_tendsto hf2.tendsto_sum_tsum_nat (hf.tendsto_sum_tsum_nat.pow 2)
  exact Eventually.of_forall (fun N ↦ Finset.sum_sq_le_sq_sum_of_nonneg
    (fun n (_ : n∈Finset.range N) ↦ hpos n))

variable (m : ℕ) [NeZero m]

lemma push_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (z : ZMod m) :
    push m (fun n ↦ r^n) z = r^z.val/(1-r^m) := by
  rw [push_eq_subsequence]
  have he (k : ℕ) : r^(k*m+z.val)=(r^m)^k*r^z.val := by
    rw [pow_add,Nat.mul_comm k m,pow_mul]
  simp_rw [he]
  rw [tsum_mul_right]
  rw [tsum_geometric_of_lt_one (pow_nonneg hr0 _) (pow_lt_one₀ hr0 hr1 (NeZero.ne m))]
  ring

lemma push_geometric_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (z : ZMod m) :
    push m (fun n ↦ r^n) z ≤ (1-r^m)⁻¹ := by
  rw [push_geometric m hr0 hr1]
  have hp : 0 < 1-r^m := sub_pos.mpr (pow_lt_one₀ hr0 hr1 (NeZero.ne m))
  simpa only [one_div] using div_le_div_of_nonneg_right
    (pow_le_one₀ hr0 hr1.le) hp.le

lemma push_sq_le_weighted {f : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : Summable (fun n ↦ f n*r^n)) (hf2 : Summable (fun n ↦ (f n)^2*r^n))
    (z : ZMod m) :
    (push m (fun n ↦ f n*r^n) z)^2 ≤
      (1-r^m)⁻¹*push m (fun n ↦ (f n)^2*r^n) z := by
  have hg := summable_geometric_of_lt_one hr0 hr1
  have hh := tsum_cauchy_schwarz (summable_residueTerm m hf z)
    (summable_residueTerm m hf2 z) (summable_residueTerm m hg z)
    (fun n ↦ by unfold residueTerm; split_ifs <;> positivity)
    (fun n ↦ by unfold residueTerm; split_ifs <;> positivity)
    (fun n ↦ by unfold residueTerm; split_ifs <;> ring)
  change (push m (fun n ↦ f n*r^n) z)^2 ≤
    push m (fun n ↦ (f n)^2*r^n) z*push m (fun n ↦ r^n) z at hh
  have hp : 0 ≤ push m (fun n ↦ (f n)^2*r^n) z :=
    tsum_nonneg (fun n ↦ by unfold residueTerm; split_ifs <;> positivity)
  exact hh.trans (by simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (push_geometric_le m hr0 hr1 z) hp)

/-- The residue-periodization overhead tends to one when r^m is small. -/
theorem sum_push_sq_le {f : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : Summable (fun n ↦ f n*r^n)) (hf2 : Summable (fun n ↦ (f n)^2*r^n)) :
    (∑ z : ZMod m, (push m (fun n ↦ f n*r^n) z)^2) ≤
      (1-r^m)⁻¹*(∑' n, (f n)^2*r^n) := by
  calc
    _ ≤ ∑ z : ZMod m, (1-r^m)⁻¹*push m (fun n ↦ (f n)^2*r^n) z :=
      Finset.sum_le_sum (fun z _ ↦ push_sq_le_weighted m hr0 hr1 hf hf2 z)
    _ = _ := by rw [← Finset.mul_sum,sum_push m hf2]

/-- Nonnegative terms in the same residue class can only increase squared
mass when they are combined. -/
theorem weighted_mass_le_sum_push_sq {f : ℕ → ℝ} {r : ℝ}
    (hr0 : 0 ≤ r) (hf0 : ∀ n, 0 ≤ f n)
    (hf : Summable (fun n ↦ f n*r^n))
    (hf2 : Summable (fun n ↦ (f n)^2*(r^2)^n)) :
    (∑' n, (f n)^2*(r^2)^n) ≤
      ∑ z : ZMod m, (push m (fun n ↦ f n*r^n) z)^2 := by
  rw [← sum_push m hf2]
  apply Finset.sum_le_sum
  intro z hz
  have he (n : ℕ) : (residueTerm m (fun n ↦ f n*r^n) z n)^2 =
      residueTerm m (fun n ↦ (f n)^2*(r^2)^n) z n := by
    unfold residueTerm
    split_ifs
    · rw [mul_pow,← pow_mul,Nat.mul_comm n 2,pow_mul]
    · simp
  have hs : Summable (fun n ↦ (residueTerm m (fun n ↦ f n*r^n) z n)^2) := by
    simp_rw [he]
    exact summable_residueTerm m hf2 z
  have hh := tsum_sq_le_sq_tsum (summable_residueTerm m hf z) hs
    (fun n ↦ by unfold residueTerm; split_ifs; exact mul_nonneg (hf0 n) (pow_nonneg hr0 _); rfl)
  simpa only [he,push] using hh

end Erdos66WeightedPushEnergy
