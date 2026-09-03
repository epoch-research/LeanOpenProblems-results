import Submission.PrimitiveScalingFiniteMoments

/-! A positive-density version of the abstract finite-moment countermodel.
This is not a theorem about representations by sums of powers. -/
namespace Erdos322Research.PositivePrimitiveScalingFiniteMoments

open Finset ScalingFiniteMoments PrimitiveScalingFiniteMoments Erdos322.MomentReduction
set_option Elab.async false
set_option maxHeartbeats 1000000

/-- The indicator of positive integers. -/
def positiveBaseline (n : ℕ) : ℕ := if n = 0 then 0 else 1

/-- The indicator of integers with no nontrivial kth-power factor. -/
def reducedBaseline (k n : ℕ) : ℕ := if Nat.floorRoot k n = 1 then 1 else 0

lemma floorRoot_quotient (k n b : ℕ) (hb : b^k ∣ n) :
    Nat.floorRoot k (n/b^k) = Nat.floorRoot k n / b := by
  have hbr : b ∣ Nat.floorRoot k n := Nat.pow_dvd_iff_dvd_floorRoot.mp hb
  have ht (t : ℕ) : t ∣ Nat.floorRoot k (n/b^k) ↔ t ∣ Nat.floorRoot k n / b := by
    rw [← Nat.pow_dvd_iff_dvd_floorRoot, Nat.dvd_div_iff_mul_dvd hb,
      ← mul_pow, Nat.pow_dvd_iff_dvd_floorRoot, Nat.dvd_div_iff_mul_dvd hbr]
  exact Nat.dvd_antisymm ((ht _).mp dvd_rfl) ((ht _).mpr dvd_rfl)

/-- Every positive integer has exactly one kth-power-free common-factor quotient. -/
theorem baseline_exact_scaling (k n : ℕ) (hk : 0 < k) :
    positiveBaseline n =
      ∑ b ∈ n.divisors.filter (fun b => b^k ∣ n), reducedBaseline k (n/b^k) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [positiveBaseline]
  have hr : 0 < Nat.floorRoot k n :=
    Nat.pos_of_ne_zero (Nat.floorRoot_ne_zero.mpr ⟨hk.ne', hn⟩)
  have hrpow : Nat.floorRoot k n ^ k ∣ n := Nat.floorRoot_pow_dvd
  have hrs : Nat.floorRoot k n ∈ n.divisors.filter (fun b => b^k ∣ n) := by
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨(dvd_pow_self _ hk.ne').trans hrpow, hn⟩, hrpow⟩
  have hval : reducedBaseline k (n/Nat.floorRoot k n^k)=1 := by
    simp [reducedBaseline, floorRoot_quotient k n _ hrpow, Nat.div_self hr]
  symm
  calc
    _ = reducedBaseline k (n/Nat.floorRoot k n^k) := by
      apply Finset.sum_eq_single (Nat.floorRoot k n)
      · intro b hb hbr
        have hbpow := (mem_filter.mp hb).2
        have hbd : b ∣ Nat.floorRoot k n := Nat.pow_dvd_iff_dvd_floorRoot.mp hbpow
        have hne : Nat.floorRoot k n / b ≠ 1 := by
          intro he
          have hd := Nat.div_mul_cancel hbd
          rw [he, one_mul] at hd
          exact hbr hd
        simp [reducedBaseline, floorRoot_quotient k n b hbpow, hne]
      · exact fun h => (h hrs).elim
    _ = positiveBaseline n := by simp [hval, positiveBaseline, hn]

/-- A positive baseline plus the sparse full spikes. -/
def positiveFull (k D n : ℕ) : ℕ := positiveBaseline n + fullSpike k D n

/-- The corresponding nonnegative primitive count. -/
def positivePrimitive (k D n : ℕ) : ℕ := reducedBaseline k n + primitiveSpike D n

theorem exact_scaling (k D n : ℕ) (hk : 0 < k) :
    positiveFull k D n =
      ∑ b ∈ n.divisors.filter (fun b => b^k ∣ n), positivePrimitive k D (n/b^k) := by
  simp only [positiveFull, positivePrimitive, Finset.sum_add_distrib, fullSpike]
  rw [baseline_exact_scaling k n hk]

theorem full_pos (k D n : ℕ) (hn : 0 < n) : 1 ≤ positiveFull k D n := by
  simp only [positiveFull, positiveBaseline, if_neg hn.ne']
  omega

theorem primitive_le_full (k D n : ℕ) :
    positivePrimitive k D n ≤ positiveFull k D n := by
  have hs := primitiveSpike_le_fullSpike k D n
  have hb : reducedBaseline k n ≤ positiveBaseline n := by
    by_cases hn : n = 0
    · subst n; simp [positiveBaseline, reducedBaseline]
    · simp only [positiveBaseline, if_neg hn]
      unfold reducedBaseline
      split_ifs <;> omega
  exact Nat.add_le_add hb hs

theorem power_scaling_monotone (k D n s : ℕ) (hk : 0 < k) (hs : 0 < s) :
    positiveFull k D n ≤ positiveFull k D (n*s^k) := by
  have hb : positiveBaseline n ≤ positiveBaseline (n*s^k) := by
    by_cases hn : n = 0
    · simp [hn]
    · simp [positiveBaseline, hn, hs.ne']
  exact Nat.add_le_add hb (monotone_under_power_scaling k D n s hk hs)

/-- Every prescribed low moment is bounded above and below by positive
constant multiples of the length of summation. -/
theorem two_sided_low_moments (k D Q : ℕ) (hk : 0 < k)
    (hD : ¬ k ∣ D) (hQD : Q+2 ≤ D) :
    ∃ C > (0 : ℝ), ∀ q ≤ Q, ∀ N : ℕ,
      (N : ℝ) ≤ countMoment (positiveFull k D) q N ∧
      countMoment (positiveFull k D) q N ≤ C*(N : ℝ) := by
  have hC := momentConstant_pos
  refine ⟨2^Q*(1+momentConstant), by positivity, ?_⟩
  intro q hq N
  have hp (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (1 : ℝ) ≤ (positiveFull k D n : ℝ)^q := by
    exact one_le_pow₀ (by exact_mod_cast full_pos k D n (Finset.mem_Icc.mp hn).1)
  have ht (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (positiveFull k D n : ℝ)^q ≤ 2^Q*(1+(fullSpike k D n : ℝ)^q) := by
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    simp only [positiveFull, positiveBaseline, if_neg hn0, Nat.cast_add, Nat.cast_one]
    have he := add_pow_le (by norm_num : (0 : ℝ) ≤ 1)
      (Nat.cast_nonneg (α := ℝ) (fullSpike k D n)) q
    simp only [one_pow] at he
    exact he.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : q-1 ≤ Q))
      (by positivity))
  constructor
  · calc
      (N : ℝ) = ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by simp [Nat.card_Icc]
      _ ≤ countMoment (positiveFull k D) q N := Finset.sum_le_sum hp
  · calc
      countMoment (positiveFull k D) q N ≤
          ∑ n ∈ Finset.Icc 1 N, 2^Q*(1+(fullSpike k D n : ℝ)^q) := Finset.sum_le_sum ht
      _ = 2^Q*((N : ℝ)+countMoment (fullSpike k D) q N) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        simp [countMoment, Nat.card_Icc]
      _ ≤ 2^Q*((N : ℝ)+momentConstant*(N : ℝ)) := by
        gcongr
        exact low_moments_linear k D q N hk hD (by omega)
      _ = 2^Q*(1+momentConstant)*(N : ℝ) := by ring

theorem primitive_peaks (k D : ℕ) (hD : 0 < D) :
    ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < (positivePrimitive k D n : ℝ)}.Infinite := by
  obtain ⟨c,hc,hi⟩ := primitive_polynomial_peaks D hD
  refine ⟨c,hc,hi.mono ?_⟩
  intro n hn
  change (n : ℝ)^c < (primitiveSpike D n : ℝ) at hn
  have hb : (primitiveSpike D n : ℝ) ≤ positivePrimitive k D n := by
    exact_mod_cast (Nat.le_add_left (primitiveSpike D n) (reducedBaseline k n))
  exact hn.trans_le hb

theorem full_peaks (k D : ℕ) (hD : 0 < D) :
    ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < (positiveFull k D n : ℝ)}.Infinite := by
  obtain ⟨c,hc,hi⟩ := primitive_peaks k D hD
  refine ⟨c,hc,hi.mono ?_⟩
  intro n hn
  change (n : ℝ)^c < (positivePrimitive k D n : ℝ) at hn
  have hb : (positivePrimitive k D n : ℝ) ≤ positiveFull k D n := by
    exact_mod_cast primitive_le_full k D n
  exact hn.trans_le hb

/-- Exact primitive scaling, positivity at every positive index, and any
finite collection of two-sided linear moment estimates still permit power peaks.
The functions here are abstract; they are not representation counts. -/
theorem positive_exact_scaling_and_finite_moments_do_not_suffice
    (k Q : ℕ) (hk : 2 ≤ k) :
    ∃ f g : ℕ → ℕ,
      (∀ n, f n=∑ b ∈ n.divisors.filter (fun b => b^k ∣ n), g (n/b^k)) ∧
      (∀ n s, 0 < s → f n ≤ f (n*s^k)) ∧
      (∀ n, g n ≤ f n) ∧
      (∀ n, 0 < n → 1 ≤ f n) ∧
      (∃ C > (0 : ℝ), ∀ q ≤ Q, ∀ N : ℕ,
        (N : ℝ) ≤ countMoment f q N ∧ countMoment f q N ≤ C*(N : ℝ)) ∧
      (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < (g n : ℝ)}.Infinite) ∧
      (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < (f n : ℝ)}.Infinite) := by
  let D := k*(Q+2)+1
  have hD : ¬ k ∣ D := by
    intro h
    have hm := Nat.mod_eq_zero_of_dvd h
    dsimp [D] at hm
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : 1 < k)] at hm
    omega
  have hDQ : Q+2 ≤ D := by dsimp [D]; nlinarith
  have hDpos : 0 < D := by omega
  exact ⟨positiveFull k D, positivePrimitive k D,
    fun n => exact_scaling k D n (by omega),
    fun n s hs => power_scaling_monotone k D n s (by omega) hs,
    primitive_le_full k D, full_pos k D,
    two_sided_low_moments k D Q (by omega) hD hDQ,
    primitive_peaks k D hDpos, full_peaks k D hDpos⟩

end Erdos322Research.PositivePrimitiveScalingFiniteMoments
