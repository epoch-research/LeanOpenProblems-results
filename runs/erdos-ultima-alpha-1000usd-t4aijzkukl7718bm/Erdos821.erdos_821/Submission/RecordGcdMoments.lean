import Submission.CoprimeRecordFibers
import Submission.LogarithmicOverlap

/-!
# Uniform gcd moments at normalized record fibers

The record condition gives a uniform moment bound whenever 1 < 2s-t.
In particular, above s=1/2 the average logarithmic gcd-totient is uniformly
bounded. Together with the overlap identity this forces a quadratic lower
bound on the logarithmic weight of any pool containing the fiber's input
primes. These are structural estimates, not an exponent amplification.
-/

open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.CoprimeRecords
open LogarithmicOverlap
set_option maxHeartbeats 2500000

noncomputable def gcdTotientMoment (K n : ℕ) (t : ℝ) : ℝ :=
  ∑ ab ∈ (avoidingFiber K n) ×ˢ (avoidingFiber K n),
    (totient (Nat.gcd ab.1 ab.2) : ℝ)^t

lemma gcd_weight_sum_le_core_squares (F : Finset ℕ) (hF : ∀ a ∈ F, 0 < a)
    (w : ℕ → ℝ) (hw : ∀ d, 0 ≤ w d) :
    (∑ ab ∈ F ×ˢ F, w (Nat.gcd ab.1 ab.2)) ≤
      ∑ d ∈ Icc 1 (F.sup id), ((F.filter (fun a => d ∣ a)).card : ℝ)^2*w d := by
  have hmap (ab : ℕ × ℕ) (hab : ab ∈ F ×ˢ F) :
      Nat.gcd ab.1 ab.2 ∈ Icc 1 (F.sup id) := by
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    exact mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left _ (hF ab.1 ha),
      (Nat.gcd_le_left _ (hF ab.1 ha)).trans (le_sup (f := id) ha)⟩
  rw [← sum_fiberwise_of_maps_to hmap]
  apply sum_le_sum
  intro d hd
  have hsub : (F ×ˢ F).filter (fun ab => Nat.gcd ab.1 ab.2=d) ⊆
      (F.filter (fun a => d ∣ a)) ×ˢ (F.filter (fun b => d ∣ b)) := by
    intro ab hab
    obtain ⟨hab, he⟩ := mem_filter.mp hab
    exact mem_product.mpr
      ⟨mem_filter.mpr ⟨(mem_product.mp hab).1, he ▸ Nat.gcd_dvd_left _ _⟩,
        mem_filter.mpr ⟨(mem_product.mp hab).2, he ▸ Nat.gcd_dvd_right _ _⟩⟩
  have hcard : (((F ×ˢ F).filter (fun ab => Nat.gcd ab.1 ab.2=d)).card : ℝ) ≤
      ((F.filter (fun a => d ∣ a)).card : ℝ)^2 := by
    exact_mod_cast (by simpa only [card_product, pow_two] using card_le_card hsub)
  calc
    _ = ∑ _ab ∈ (F ×ˢ F).filter (fun ab => Nat.gcd ab.1 ab.2=d), w d := by
      apply sum_congr rfl
      intro ab hab
      rw [(mem_filter.mp hab).2]
    _ = (((F ×ˢ F).filter (fun ab => Nat.gcd ab.1 ab.2=d)).card : ℝ)*w d := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (hw d)

/-- The constant depends only on the two real exponents, not K or n. -/
noncomputable def recordGcdConstant (s t : ℝ) : ℝ :=
  ∑' d : ℕ, (totient d : ℝ)^(-(2*s-t))

lemma recordGcdConstant_nonneg (s t : ℝ) : 0 ≤ recordGcdConstant s t :=
  tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Uniform power-moment bound from the exact common-core frequencies. -/
theorem record_gcd_totient_moment_le (K n : ℕ) (hn : 0 < n) (s t : ℝ)
    (hst : 1 < 2*s-t)
    (hrec : ∀ j : ℕ, j ≤ n → (gAvoiding K j : ℝ)/(j : ℝ)^s ≤
      (gAvoiding K n : ℝ)/(n : ℝ)^s) :
    gcdTotientMoment K n t ≤ (gAvoiding K n : ℝ)^2*recordGcdConstant s t := by
  have hbase := gcd_weight_sum_le_core_squares (avoidingFiber K n)
    (fun a ha => Nat.pos_of_ne_zero (mem_avoidingFiber.mp ha).1.ne_zero)
    (fun d => (totient d : ℝ)^t) (fun d => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hsummable := summable_totient_neg_rpow (2*s-t) hst
  calc
    gcdTotientMoment K n t ≤
        ∑ d ∈ Icc 1 ((avoidingFiber K n).sup id),
          (((avoidingFiber K n).filter (fun a => d ∣ a)).card : ℝ)^2*(totient d : ℝ)^t := hbase
    _ ≤ ∑ d ∈ Icc 1 ((avoidingFiber K n).sup id),
        (gAvoiding K n : ℝ)^2*(totient d : ℝ)^(-(2*s-t)) := by
      apply sum_le_sum
      intro d hd
      have hd0 : 0 < d := (mem_Icc.mp hd).1
      have hφ : (0 : ℝ) < totient d := by exact_mod_cast Nat.totient_pos.mpr hd0
      calc
        _ ≤ ((gAvoiding K n : ℝ)^2*(totient d : ℝ)^(-(2*s)))*(totient d : ℝ)^t :=
          mul_le_mul_of_nonneg_right (normalized_record_core_square_bound K n d hn hd0 s hrec)
            (Real.rpow_nonneg hφ.le _)
        _ = _ := by
          rw [mul_assoc, ← Real.rpow_add hφ]
          congr 2
          ring
    _ = (gAvoiding K n : ℝ)^2*
        ∑ d ∈ Icc 1 ((avoidingFiber K n).sup id), (totient d : ℝ)^(-(2*s-t)) :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hsummable.sum_le_tsum _ (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (sq_nonneg _)

/-- Markov's inequality, retaining a uniform constant instead of a divisor
count loss. This is an upper bound for large overlaps, not a lower supply. -/
theorem record_large_overlap_power_bound (K n : ℕ) (hn : 0 < n) (s t η : ℝ)
    (ht : 0 ≤ t) (hst : 1 < 2*s-t)
    (hrec : ∀ j : ℕ, j ≤ n → (gAvoiding K j : ℝ)/(j : ℝ)^s ≤
      (gAvoiding K n : ℝ)/(n : ℝ)^s) :
    (n : ℝ)^(η*t)*((largePairs (avoidingFiber K n) n η).card : ℝ) ≤
      (gAvoiding K n : ℝ)^2*recordGcdConstant s t := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply le_trans _ (record_gcd_totient_moment_le K n hn s t hst hrec)
  calc
    _ = ∑ _ab ∈ largePairs (avoidingFiber K n) n η, (n : ℝ)^(η*t) := by simp [mul_comm]
    _ ≤ ∑ ab ∈ largePairs (avoidingFiber K n) n η, (totient (Nat.gcd ab.1 ab.2) : ℝ)^t := by
      apply sum_le_sum
      intro ab hab
      rw [Real.rpow_mul hnR.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hnR.le _) (mem_filter.mp hab).2 ht
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun ab _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma log_overlap_le_power_moment (K n : ℕ) (t : ℝ) (ht : 0 < t) :
    overlap (avoidingFiber K n) ≤ gcdTotientMoment K n t/t := by
  rw [gcdTotientMoment, sum_div]
  have he : overlap (avoidingFiber K n) =
      ∑ ab ∈ (avoidingFiber K n) ×ˢ (avoidingFiber K n),
        Real.log (totient (Nat.gcd ab.1 ab.2) : ℝ) := by simp only [overlap, sum_product]
  rw [he]
  exact sum_le_sum (fun ab _ => Real.log_le_rpow_div (Nat.cast_nonneg _) ht)

/-- Above one half, every normalized record has bounded average logarithmic
common-core size, uniformly over the excluded prime set and output. -/
theorem exists_uniform_record_log_overlap_bound (s : ℝ) (hs : 1/2 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ K n : ℕ, 0 < n →
      (∀ j : ℕ, j ≤ n → (gAvoiding K j : ℝ)/(j : ℝ)^s ≤
        (gAvoiding K n : ℝ)/(n : ℝ)^s) →
      overlap (avoidingFiber K n) ≤ C*(gAvoiding K n : ℝ)^2 := by
  let t := (2*s-1)/2
  have ht : 0 < t := by dsimp [t]; linarith
  have hst : 1 < 2*s-t := by dsimp [t]; linarith
  let C := recordGcdConstant s t/t+1
  have hC : 0 < C := by dsimp [C]; positivity [recordGcdConstant_nonneg s t]
  refine ⟨C, hC, ?_⟩
  intro K n hn hrec
  calc
    _ ≤ gcdTotientMoment K n t/t := log_overlap_le_power_moment K n t ht
    _ ≤ ((gAvoiding K n : ℝ)^2*recordGcdConstant s t)/t :=
      div_le_div_of_nonneg_right (record_gcd_totient_moment_le K n hn s t hst hrec) ht.le
    _ ≤ C*(gAvoiding K n : ℝ)^2 := by
      dsimp [C]
      rw [add_mul, one_mul]
      have he : (gAvoiding K n : ℝ)^2*recordGcdConstant s t/t =
          (recordGcdConstant s t/t)*(gAvoiding K n : ℝ)^2 := by ring
      rw [he]
      exact le_add_of_nonneg_right (sq_nonneg _)

/-- Any pool containing a positive full record fiber has at least quadratic
logarithmic weight. This is a necessary support-size bound, not a construction. -/
theorem exists_quadratic_record_pool_bound (s : ℝ) (hs : 1/2 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ K n : ℕ, 0 < n → 0 < gAvoiding K n →
      (∀ j : ℕ, j ≤ n → (gAvoiding K j : ℝ)/(j : ℝ)^s ≤
        (gAvoiding K n : ℝ)/(n : ℝ)^s) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ a ∈ avoidingFiber K n, a.primeFactors ⊆ P) →
        (Real.log (n : ℝ))^2 ≤ C*poolWeight P := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_record_log_overlap_bound s hs
  refine ⟨C, hC, ?_⟩
  intro K n hn hg hrec P hP hcut
  have hG : (0 : ℝ) < gAvoiding K n := by exact_mod_cast hg
  have h1 := fiber_log_square_le_pool_mul_overlap (avoidingFiber K n) P n hP
    (fun a ha => ⟨(mem_avoidingFiber.mp ha).1, (mem_avoidingFiber.mp ha).2.2, hcut a ha⟩)
  rw [avoidingFiber_card] at h1
  have h2 := mul_le_mul_of_nonneg_left (hbound K n hn hrec) (poolWeight_nonneg P)
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hG)).mp
  nlinarith only [h1.trans h2]

end Erdos821.CoprimeRecords
