import Submission.SmallDivisorAverage

/-!
# Periodic means and natural quotient normalization

Elementary limit lemmas used by the complete degree-one root-mean theorem
and by the Dirichlet-convolution transfer theorem. The periodic mean is proved
using the existing complete-block identity and a bounded remainder.
-/

namespace Erdos975Support

open Filter
open scoped Topology

/-- The normalized natural quotient tends to the reciprocal of its fixed,
positive denominator. -/
theorem tendsto_natDiv_div (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ ↦ ((N / d : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 (1 / (d : ℝ))) := by
  have ht := ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_mod_div_atTop_nhds_zero_nat hd)).div_const
    (d : ℝ)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hid : (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast Nat.div_add_mod N d
  field_simp
  nlinarith [hid]

/-- Every real-valued periodic sequence has the expected normalized mean.
There is no boundedness hypothesis: the finite period supplies it. -/
theorem tendsto_sum_range_of_periodic {u : ℕ → ℝ} {d : ℕ}
    (hu : Function.Periodic u d) (hd : 0 < d) :
    Tendsto (fun N : ℕ ↦ (∑ k ∈ Finset.range N, u k) / (N : ℝ)) atTop
      (𝓝 ((∑ k ∈ Finset.range d, u k) / (d : ℝ))) := by
  let C : ℝ := ∑ k ∈ Finset.range d, |u k|
  have hbound (N : ℕ) : |∑ k ∈ Finset.range (N % d), u k| ≤ C := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.mod_lt N hd).le)
    intro k _ _
    exact abs_nonneg _
  have herr : Tendsto (fun N : ℕ ↦
      (∑ k ∈ Finset.range (N % d), u k) / (N : ℝ)) atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero
      (Filter.Eventually.of_forall fun N ↦ (abs_le.mp (hbound N)).1)
      (Filter.Eventually.of_forall fun N ↦ (abs_le.mp (hbound N)).2)
      tendsto_natCast_atTop_atTop
  have ht := ((tendsto_natDiv_div d hd).mul_const (∑ k ∈ Finset.range d, u k)).add herr
  simp only [one_div_mul_eq_div, add_zero] at ht
  apply ht.congr
  intro N
  have hformula := sum_range_div_mod_of_periodic hu N
  simp only [nsmul_eq_mul] at hformula
  rw [hformula]
  ring

/-- The density of positive integers coprime to `d` is `φ(d) / d`. -/
theorem tendsto_coprime_count_div (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ ↦
      (((Finset.Ioc 0 N).filter (fun q ↦ d.Coprime q)).card : ℝ) / (N : ℝ))
      atTop (𝓝 ((d.totient : ℝ) / (d : ℝ))) := by
  let u : ℕ → ℝ := fun k ↦ if d.Coprime (k + 1) then 1 else 0
  have hu : Function.Periodic u d := by
    intro k
    dsimp only [u]
    simp only [show k + d + 1 = (k + 1) + d by omega, Nat.coprime_add_self_right]
  have hsum (N : ℕ) :
      (∑ k ∈ Finset.range N, u k) =
        (((Finset.Ioc 0 N).filter (fun q ↦ d.Coprime q)).card : ℝ) := by
    rw [← Finset.sum_boole]
    rw [show Finset.Ioc 0 N = Finset.Ico 1 (N + 1) by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega]
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_right]
    apply Finset.sum_congr rfl
    intro k _
    simp only [u, Nat.add_comm]
  have hperiod : (∑ k ∈ Finset.range d, u k) = (d.totient : ℝ) := by
    rw [hsum, show Finset.Ioc 0 d = Finset.Ico 1 (1 + d) by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega,
      Nat.filter_coprime_Ico_eq_totient]
  have ht := tendsto_sum_range_of_periodic hu hd
  rw [hperiod] at ht
  simpa only [hsum] using ht

end Erdos975Support
