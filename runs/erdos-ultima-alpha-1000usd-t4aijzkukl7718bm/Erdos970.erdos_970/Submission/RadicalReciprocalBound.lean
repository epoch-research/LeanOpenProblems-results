import Submission.RadicalHarmonicWindow

/-! A uniform additive harmonic bound for finite families whose radicals lie
below a fixed cutoff. -/
namespace Erdos970.FiniteSelberg
open Finset Real
set_option maxHeartbeats 1000000

lemma primeRadical_div_dvd (n : ℕ) :
    primeRadical (n / primeRadical n) ∣ primeRadical n := by
  by_cases hn : n = 0
  · simp [hn, primeRadical]
  apply prod_dvd_prod_of_subset
  exact Nat.primeFactors_mono (Nat.div_dvd_of_dvd (primeRadical_dvd n)) hn

lemma radicalQuotient_pos (n : ℕ) (hn : 0 < n) : 0 < n / primeRadical n :=
  Nat.div_pos (Nat.le_of_dvd hn (primeRadical_dvd n)) (primeRadical_pos n)

lemma radicalHalfWeight_finite_bound (P s : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ b ∈ s, b ∈ Nat.factoredNumbers P) :
    (∑ b ∈ s, radicalHalfWeight b) ≤ exp (4 * radicalTailSeries) := by
  let e (b : s) : Nat.factoredNumbers P := ⟨b.val, hs b.val b.property⟩
  have hi : Function.Injective e := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x : Nat.factoredNumbers P => x.val) hab)
  have hh := Summable.tsum_le_tsum_of_inj
    (f := fun b : s => radicalHalfWeight b.val)
    (g := fun b : Nat.factoredNumbers P => radicalHalfWeight b.val) e hi
    (fun _ _ => radicalHalfWeight_nonneg _)
    (fun _ => le_rfl) (Summable.of_finite : Summable (fun b : s => radicalHalfWeight b.val))
    (radicalHalfWeight_factored_hasSum P hP).summable
  rw [tsum_fintype, sum_coe_sort] at hh
  exact hh.trans (radicalHalfWeight_factored_bound P hP)

lemma radical_fiber_window_bound (s : Finset ℕ) (R b : ℕ) (hb : 0 < b)
    (hs : ∀ n ∈ s, 0 < n ∧ R < n ∧ primeRadical n ≤ R ∧ n / primeRadical n = b) :
    (∑ n ∈ s, 1 / (n : ℝ)) ≤ 2 * radicalHalfWeight b := by
  have hnprod (n : ℕ) (hn : n ∈ s) : n = primeRadical n * b := by
    rw [← (hs n hn).2.2.2]
    exact (Nat.mul_div_cancel' (primeRadical_dvd n)).symm
  have hinj : Set.InjOn primeRadical (↑s : Set ℕ) := by
    intro n hn m hm he
    rw [hnprod n hn, hnprod m hm, he]
  have hwindow := reciprocal_multiples_window (s.image primeRadical) R (primeRadical b) b
    (primeRadical_pos b) hb (fun d hd => by
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hd
      refine ⟨primeRadical_pos n, (hs n hn).2.2.1, ?_, ?_⟩
      · rw [← hnprod n hn]
        exact (hs n hn).2.1
      · rw [← (hs n hn).2.2.2]
        exact primeRadical_div_dvd n)
  have he : (∑ n ∈ s, 1 / (n : ℝ)) =
      (1 / (b : ℝ)) * ∑ d ∈ s.image primeRadical, 1 / (d : ℝ) := by
    rw [sum_image hinj, mul_sum]
    apply sum_congr rfl
    intro n hn
    nth_rw 1 [hnprod n hn]
    rw [Nat.cast_mul]
    ring
  rw [he]
  calc
    _ ≤ (1 / (b : ℝ)) * ((1 + log b) / primeRadical b) :=
      mul_le_mul_of_nonneg_left hwindow (by positivity)
    _ ≤ (1 / (b : ℝ)) * ((2 * sqrt b) / primeRadical b) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right (log_add_one_le_twice_sqrt b hb) (Nat.cast_nonneg _)
    _ = 2 * radicalHalfWeight b := by
      have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
      have hs0 : sqrt (b : ℝ) ≠ 0 := (sqrt_pos.mpr (by exact_mod_cast hb)).ne'
      have hq0 : (primeRadical b : ℝ) ≠ 0 := by exact_mod_cast (primeRadical_pos b).ne'
      unfold radicalHalfWeight
      field_simp
      nlinarith [sq_sqrt (Nat.cast_nonneg b)]

/-- Numbers with radical at most R have only an absolutely bounded extra
  reciprocal mass beyond the ordinary harmonic sum through R. -/
theorem radical_reciprocal_finite_bound (P s : Finset ℕ) (R : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ n ∈ s, n ∈ Nat.factoredNumbers P ∧ primeRadical n ≤ R) :
    (∑ n ∈ s, 1 / (n : ℝ)) ≤ (harmonic R : ℝ) + 2 * exp (4 * radicalTailSeries) := by
  let U := s.filter (fun n => n ≤ R)
  let T := s.filter (fun n => ¬n ≤ R)
  let f := fun n => n / primeRadical n
  let B := T.image f
  have hsplit := sum_filter_add_sum_filter_not s (fun n => n ≤ R) (fun n => 1 / (n : ℝ))
  have hU : (∑ n ∈ U, 1 / (n : ℝ)) ≤ (harmonic R : ℝ) := by
    have hsub : U ⊆ Icc 1 R := by
      intro n hn
      obtain ⟨hns, hnR⟩ := mem_filter.mp hn
      have hn0 := Nat.ne_zero_of_mem_factoredNumbers (hs n hns).1
      exact mem_Icc.mpr ⟨by omega, hnR⟩
    have hh := sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ => 1 / (n : ℝ)) hsub
      (fun _ _ _ => by positivity)
    rw [harmonic_eq_sum_Icc]
    push_cast
    simpa only [one_div] using hh
  have hB (b : ℕ) (hb : b ∈ B) : b ∈ Nat.factoredNumbers P := by
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hb
    exact Nat.mem_factoredNumbers_of_dvd (hs n (mem_filter.mp hn).1).1
      (Nat.div_dvd_of_dvd (primeRadical_dvd n))
  have hT : (∑ n ∈ T, 1 / (n : ℝ)) ≤ 2 * exp (4 * radicalTailSeries) := by
    calc
      _ = ∑ b ∈ B, ∑ n ∈ T.filter (fun n => f n = b), 1 / (n : ℝ) :=
        (sum_fiberwise_of_maps_to (fun n hn => mem_image.mpr ⟨n, hn, rfl⟩) _).symm
      _ ≤ ∑ b ∈ B, 2 * radicalHalfWeight b := by
        apply sum_le_sum
        intro b hb
        apply radical_fiber_window_bound _ R b
          (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_factoredNumbers (hB b hb)))
        intro n hn
        obtain ⟨hnT, hnb⟩ := mem_filter.mp hn
        obtain ⟨hns, hnR⟩ := mem_filter.mp hnT
        exact ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_factoredNumbers (hs n hns).1),
          by omega, (hs n hns).2, hnb⟩
      _ = 2 * ∑ b ∈ B, radicalHalfWeight b := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (radicalHalfWeight_finite_bound P B hP hB) (by norm_num)
  change (∑ n ∈ U, 1 / (n : ℝ)) + (∑ n ∈ T, 1 / (n : ℝ)) = _ at hsplit
  linarith

#print axioms radical_reciprocal_finite_bound
end Erdos970.FiniteSelberg
