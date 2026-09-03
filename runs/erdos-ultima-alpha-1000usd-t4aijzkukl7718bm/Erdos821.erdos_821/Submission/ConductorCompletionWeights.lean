import Submission.CompositeCharacterErrors

/-!
# Completion weights for conductors of smooth product moduli

Divisors of the squarefree product moduli can be grouped by their number of
block-prime factors. This file supplies finite identities and nonnegative
upper bounds; it does not assert the missing prime-distribution estimate.
-/

open Nat Finset
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

set_option maxHeartbeats 2000000

lemma mem_primeProductModuli_iff {r m d : ℕ} :
    d ∈ primeProductModuli r m ↔ Squarefree d ∧
      d.primeFactors ⊆ geometricBlockPrimes m ∧ d.primeFactors.card = r := by
  constructor
  · intro hd
    exact ⟨(primeProductModuli_properties hd).2.1,
      fun _ hp => prime_product_prime_factor_mem hd hp,
      (primeProductModuli_properties hd).2.2.1⟩
  · rintro ⟨hsq, hsub, hcard⟩
    exact mem_image.mpr ⟨d.primeFactors, mem_powersetCard.mpr ⟨hsub, hcard⟩,
      Nat.prod_primeFactors_of_squarefree hsq⟩

lemma primeProductModuli_mul {s u m c e : ℕ}
    (hc : c ∈ primeProductModuli s m) (he : e ∈ primeProductModuli u m)
    (hcop : c.Coprime e) : c * e ∈ primeProductModuli (s + u) m := by
  obtain ⟨hcq, hcsub, hcc⟩ := mem_primeProductModuli_iff.mp hc
  obtain ⟨heq, hesub, hec⟩ := mem_primeProductModuli_iff.mp he
  apply mem_primeProductModuli_iff.mpr
  rw [hcop.primeFactors_mul]
  exact ⟨Nat.squarefree_mul_iff.mpr ⟨hcop, hcq, heq⟩,
    union_subset hcsub hesub,
    by rw [card_union_of_disjoint hcop.disjoint_primeFactors, hcc, hec]⟩

lemma primeProductModuli_divisor {r m d c : ℕ}
    (hd : d ∈ primeProductModuli r m) (hcd : c ∣ d) :
    c ∈ primeProductModuli c.primeFactors.card m := by
  obtain ⟨hsq, hsub, hcard⟩ := mem_primeProductModuli_iff.mp hd
  exact mem_primeProductModuli_iff.mpr ⟨hsq.squarefree_of_dvd hcd,
    (Nat.primeFactors_mono hcd hsq.ne_zero).trans hsub, rfl⟩

lemma primeProductModuli_complement {r s m d c : ℕ}
    (hd : d ∈ primeProductModuli r m) (hc : c ∈ primeProductModuli s m)
    (hcd : c ∣ d) : s ≤ r ∧ c.Coprime (d / c) ∧
      d / c ∈ primeProductModuli (r - s) m := by
  have hdq := (primeProductModuli_properties hd).2.1
  have hcop : c.Coprime (d / c) := Nat.coprime_of_squarefree_mul (by
    rw [Nat.mul_div_cancel' hcd]; exact hdq)
  have he := primeProductModuli_divisor hd (Nat.div_dvd_of_dvd hcd)
  have hcCard := (primeProductModuli_properties hc).2.2.1
  have hdCard := (primeProductModuli_properties hd).2.2.1
  have hcard : s + (d / c).primeFactors.card = r := by
    rw [← Nat.mul_div_cancel' hcd, hcop.primeFactors_mul,
      card_union_of_disjoint hcop.disjoint_primeFactors, hcCard] at hdCard
    exact hdCard
  refine ⟨by omega, hcop, ?_⟩
  simpa only [show (d / c).primeFactors.card = r - s by omega] using he

noncomputable def primeProductReciprocalMass (r m : ℕ) : ℝ :=
  ∑ d ∈ primeProductModuli r m, (d.totient : ℝ)⁻¹

lemma primeProductReciprocalMass_nonneg (r m : ℕ) :
    0 ≤ primeProductReciprocalMass r m :=
  sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

/-- The reciprocal completion weight is exactly the reciprocal mass of
coprime complementary products, times the conductor's own reciprocal weight. -/
theorem prime_product_conductor_completion_eq {r s m c : ℕ}
    (hsr : s ≤ r) (hc : c ∈ primeProductModuli s m) :
    (∑ d ∈ (primeProductModuli r m).filter (fun d => c ∣ d), (d.totient : ℝ)⁻¹) =
      (c.totient : ℝ)⁻¹ *
        ∑ e ∈ (primeProductModuli (r - s) m).filter (fun e => c.Coprime e),
          (e.totient : ℝ)⁻¹ := by
  rw [mul_sum]
  apply sum_bij (fun d _ => d / c)
  · intro d hd
    obtain ⟨hd, hcd⟩ := mem_filter.mp hd
    have h := primeProductModuli_complement hd hc hcd
    exact mem_filter.mpr ⟨h.2.2, h.2.1⟩
  · intro d hd e he h
    have hcd := (mem_filter.mp hd).2
    have hce := (mem_filter.mp he).2
    calc
      d = c * (d / c) := (Nat.mul_div_cancel' hcd).symm
      _ = c * (e / c) := congrArg (c * ·) h
      _ = e := Nat.mul_div_cancel' hce
  · intro e he
    obtain ⟨he, hcop⟩ := mem_filter.mp he
    have hd : c * e ∈ primeProductModuli r m := by
      simpa only [Nat.add_sub_of_le hsr] using primeProductModuli_mul hc he hcop
    have hc0 := (primeProductModuli_properties hc).1
    exact ⟨c * e, mem_filter.mpr ⟨hd, dvd_mul_right _ _⟩,
      Nat.mul_div_cancel_left e hc0⟩
  · intro d hd
    have hcd := (mem_filter.mp hd).2
    have hcop := (primeProductModuli_complement (mem_filter.mp hd).1 hc hcd).2.1
    have hφ := Nat.totient_mul hcop
    rw [Nat.mul_div_cancel' hcd] at hφ
    rw [hφ, Nat.cast_mul, mul_inv]

/-- Dropping the coprimality restriction gives a nonnegative completion bound. -/
theorem prime_product_conductor_completion_le {r s m c : ℕ}
    (hsr : s ≤ r) (hc : c ∈ primeProductModuli s m) :
    (∑ d ∈ (primeProductModuli r m).filter (fun d => c ∣ d), (d.totient : ℝ)⁻¹) ≤
      (c.totient : ℝ)⁻¹ * primeProductReciprocalMass (r - s) m := by
  rw [prime_product_conductor_completion_eq hsr hc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun e _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

lemma primeProductModuli_pairwiseDisjoint (m : ℕ) :
    Pairwise (fun r s => Disjoint (primeProductModuli r m) (primeProductModuli s m)) := by
  intro r s hrs
  apply disjoint_left.mpr
  intro d hdr hds
  exact hrs ((primeProductModuli_properties hdr).2.2.1.symm.trans
    (primeProductModuli_properties hds).2.2.1)

lemma prime_product_divisor_sum_grouped {r m d : ℕ}
    (hd : d ∈ primeProductModuli r m) (F : ℕ → ℝ) :
    (∑ c ∈ d.divisors.erase 1, F c) =
      ∑ s ∈ Icc 1 r, ∑ c ∈ (primeProductModuli s m).filter (fun c => c ∣ d), F c := by
  have hU : (Icc 1 r).biUnion (fun s =>
      (primeProductModuli s m).filter (fun c => c ∣ d)) = d.divisors.erase 1 := by
    ext c
    constructor
    · intro hc
      obtain ⟨s, hs, hcs⟩ := mem_biUnion.mp hc
      obtain ⟨hc, hcd⟩ := mem_filter.mp hcs
      have hcard := (primeProductModuli_properties hc).2.2.1
      have hc1 : c ≠ 1 := by
        intro heq
        simp only [heq, Nat.primeFactors_one, card_empty] at hcard
        have := (mem_Icc.mp hs).1
        omega
      exact mem_erase.mpr ⟨hc1,
        Nat.mem_divisors.mpr ⟨hcd, (primeProductModuli_properties hd).1.ne'⟩⟩
    · intro hc
      obtain ⟨hc1, hcd, hd0⟩ := mem_erase.mp hc |>.imp_right Nat.mem_divisors.mp
      have hc0 : 0 < c := Nat.pos_of_mem_divisors (mem_erase.mp hc).2
      have hcP := primeProductModuli_divisor hd hcd
      have hcgt : 1 ≤ c.primeFactors.card := by
        exact card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))
      have hcr : c.primeFactors.card ≤ r :=
        (primeProductModuli_complement hd hcP hcd).1
      exact mem_biUnion.mpr ⟨c.primeFactors.card, mem_Icc.mpr ⟨hcgt, hcr⟩,
        mem_filter.mpr ⟨hcP, hcd⟩⟩
  have hdis : (↑(Icc 1 r) : Set ℕ).PairwiseDisjoint
      (fun s => (primeProductModuli s m).filter (fun c => c ∣ d)) := by
    intro s hs u hu hsu
    exact (primeProductModuli_pairwiseDisjoint m hsu).mono
      (filter_subset _ _) (filter_subset _ _)
  rw [← sum_biUnion hdis, hU]

/-- Exact Fubini regrouping of the weighted divisor sum by conductor size. -/
theorem prime_product_weighted_divisor_sum_grouped (r m : ℕ) (F : ℕ → ℝ) :
    (∑ d ∈ primeProductModuli r m, (∑ c ∈ d.divisors.erase 1, F c) / (d.totient : ℝ)) =
      ∑ s ∈ Icc 1 r, ∑ c ∈ primeProductModuli s m,
        F c * (∑ d ∈ (primeProductModuli r m).filter (fun d => c ∣ d), (d.totient : ℝ)⁻¹) := by
  calc
    _ = ∑ d ∈ primeProductModuli r m, ∑ s ∈ Icc 1 r,
        ∑ c ∈ primeProductModuli s m, if c ∣ d then F c / (d.totient : ℝ) else 0 := by
      apply sum_congr rfl
      intro d hd
      rw [prime_product_divisor_sum_grouped hd F, sum_div]
      apply sum_congr rfl
      intro s hs
      rw [sum_div, sum_filter]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro s hs
      rw [sum_comm]
      apply sum_congr rfl
      intro c hc
      rw [sum_filter, mul_sum]
      apply sum_congr rfl
      intro d hd
      by_cases hcd : c ∣ d <;> simp only [hcd, if_true, if_false, mul_zero, div_eq_mul_inv]

/-- Nonnegative conductor sums are controlled by a convolution of their
primitive means with reciprocal completion masses. -/
theorem prime_product_weighted_divisor_sum_le (r m : ℕ) (F : ℕ → ℝ)
    (hF : ∀ c, 0 ≤ F c) :
    (∑ d ∈ primeProductModuli r m, (∑ c ∈ d.divisors.erase 1, F c) / (d.totient : ℝ)) ≤
      ∑ s ∈ Icc 1 r, primeProductReciprocalMass (r - s) m *
        ∑ c ∈ primeProductModuli s m, F c / (c.totient : ℝ) := by
  rw [prime_product_weighted_divisor_sum_grouped]
  apply sum_le_sum
  intro s hs
  rw [mul_sum]
  apply sum_le_sum
  intro c hc
  calc
    _ ≤ F c * ((c.totient : ℝ)⁻¹ * primeProductReciprocalMass (r - s) m) :=
      mul_le_mul_of_nonneg_left
        (prime_product_conductor_completion_le (mem_Icc.mp hs).2 hc) (hF c)
    _ = _ := by rw [div_eq_mul_inv]; ring

noncomputable def primitiveProductMangoldtMean (s m N : ℕ) : ℝ :=
  ∑ c ∈ primeProductModuli s m,
    (∑ ψ ∈ primitiveCharacters c, ‖twistedArithmeticSum ψ ArithmeticFunction.vonMangoldt N‖) /
      (c.totient : ℝ)

lemma primitiveProductMangoldtMean_nonneg (s m N : ℕ) :
    0 ≤ primitiveProductMangoldtMean s m N := by
  exact sum_nonneg (fun c _ => div_nonneg (sum_nonneg (fun ψ _ => norm_nonneg _)) (Nat.cast_nonneg _))

theorem prime_product_conductor_majorant_le (r m N : ℕ) :
    (∑ d ∈ primeProductModuli r m,
      primitiveConductorMangoldtMajorant d N / (d.totient : ℝ)) ≤
      ∑ s ∈ Icc 1 r, primeProductReciprocalMass (r - s) m * primitiveProductMangoldtMean s m N := by
  exact prime_product_weighted_divisor_sum_le r m
    (fun c => ∑ ψ ∈ primitiveCharacters c, ‖twistedArithmeticSum ψ ArithmeticFunction.vonMangoldt N‖)
    (fun c => sum_nonneg (fun ψ _ => norm_nonneg _))

lemma geometric_block_prime_count_upper (m : ℕ) (hm : 1 ≤ m) :
    (m + 1) * (geometricBlockPrimes m).card ≤ 2 ^ 64 * progressionScaleN m := by
  have hL : (0 : ℝ) < progressionScaleN m := by unfold progressionScaleN; positivity
  have hlogL : 32 * (m : ℝ) ≤ Real.log (progressionScaleN m) := by
    simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul]
    nlinarith [Real.log_two_gt_d9, Nat.cast_nonneg (α := ℝ) m]
  have htheta : 32 * (m : ℝ) * ((geometricBlockPrimes m).card : ℝ) ≤
      Chebyshev.theta (progressionScaleN (m + 1)) := by
    calc
      _ = ∑ _p ∈ geometricBlockPrimes m, 32 * (m : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ p ∈ geometricBlockPrimes m, Real.log p := by
        apply sum_le_sum
        intro p hp
        exact hlogL.trans (Real.log_le_log hL (by
          exact_mod_cast (mem_geometricBlockPrimes.mp hp).2.1.le))
      _ ≤ _ := by
        rw [Sieve.theta_nat_eq_sum_primesBelow]
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun p _ _ => Real.log_natCast_nonneg p)
  have hthetaUp := Chebyshev.theta_le_log4_mul_x
    (Nat.cast_nonneg (α := ℝ) (progressionScaleN (m + 1)))
  have hlog4 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hQ : progressionScaleN (m + 1) = 2 ^ 64 * progressionScaleN m := by
    unfold progressionScaleN
    rw [← pow_add]
    congr 1
    omega
  have hthetaUp' : Chebyshev.theta (progressionScaleN (m + 1)) ≤
      3 * ((2 : ℝ) ^ 64 * progressionScaleN m) := by
    calc
      _ ≤ 3 * (progressionScaleN (m + 1) : ℝ) :=
        hthetaUp.trans (mul_le_mul_of_nonneg_right hlog4 (Nat.cast_nonneg _))
      _ = _ := by rw [hQ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hC : 0 ≤ ((geometricBlockPrimes m).card : ℝ) := Nat.cast_nonneg _
  have hmul := mul_nonneg (show (0 : ℝ) ≤ 32 * m - 3 * ((m : ℝ) + 1) by linarith) hC
  have hres : ((m : ℝ) + 1) * ((geometricBlockPrimes m).card : ℝ) ≤
      (2 : ℝ) ^ 64 * progressionScaleN m := by linarith
  exact_mod_cast hres

lemma primeProductReciprocalMass_le_binomial (r m : ℕ) :
    primeProductReciprocalMass r m ≤
      (((geometricBlockPrimes m).card.choose r : ℕ) : ℝ) / (progressionScaleN m : ℝ) ^ r := by
  have hL : (0 : ℝ) < (progressionScaleN m : ℝ) ^ r := by unfold progressionScaleN; positivity
  calc
    _ ≤ ∑ _d ∈ primeProductModuli r m, ((progressionScaleN m : ℝ) ^ r)⁻¹ := by
      apply sum_le_sum
      intro d hd
      have hφ : (progressionScaleN m : ℝ) ^ r ≤ (d.totient : ℝ) := by
        exact_mod_cast primeProductModuli_totient_lower hd
      simpa only [one_div] using one_div_le_one_div_of_le hL hφ
    _ = _ := by rw [sum_const, nsmul_eq_mul, primeProductModuli_card]; rfl

lemma factorial_mul_primeProductReciprocalMass_le (r m : ℕ) :
    (r.factorial : ℝ) * primeProductReciprocalMass r m ≤
      (((geometricBlockPrimes m).card : ℝ) / progressionScaleN m) ^ r := by
  have hchoose : (r.factorial : ℝ) * (((geometricBlockPrimes m).card.choose r : ℕ) : ℝ) ≤
      ((geometricBlockPrimes m).card : ℝ) ^ r := by
    have h := Nat.descFactorial_le_pow (geometricBlockPrimes m).card r
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    exact_mod_cast h
  calc
    _ ≤ (r.factorial : ℝ) *
        ((((geometricBlockPrimes m).card.choose r : ℕ) : ℝ) / (progressionScaleN m : ℝ) ^ r) :=
      mul_le_mul_of_nonneg_left (primeProductReciprocalMass_le_binomial r m) (Nat.cast_nonneg _)
    _ ≤ ((geometricBlockPrimes m).card : ℝ) ^ r / (progressionScaleN m : ℝ) ^ r := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hchoose (pow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := (div_pow _ _ _).symm

/-- Complementary-product weights lose only one inverse logarithmic factor
per complementary prime, with the expected factorial saving. -/
theorem primeProductReciprocalMass_upper (r m : ℕ) (hm : 1 ≤ m) :
    primeProductReciprocalMass r m ≤
      ((2 : ℝ) ^ 64 / ((m : ℝ) + 1)) ^ r / r.factorial := by
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hL : (0 : ℝ) < progressionScaleN m := by unfold progressionScaleN; positivity
  have hcount : ((geometricBlockPrimes m).card : ℝ) / progressionScaleN m ≤
      (2 : ℝ) ^ 64 / ((m : ℝ) + 1) := by
    apply (div_le_div_iff₀ hL (by positivity)).mpr
    have h := geometric_block_prime_count_upper m hm
    have hR : ((m : ℝ) + 1) * ((geometricBlockPrimes m).card : ℝ) ≤
        (2 : ℝ) ^ 64 * progressionScaleN m := by exact_mod_cast h
    nlinarith only [hR]
  apply (le_div_iff₀ hfac).mpr
  rw [mul_comm]
  exact (factorial_mul_primeProductReciprocalMass_le r m).trans
    (pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hL.le) hcount r)

end Erdos821
