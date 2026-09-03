import Submission.Explore

/-! Fixed-width near-ties between consecutive largest prime factors.

These estimates are auxiliary; they do not establish Erdős 371.
-/

namespace Erdos371

/-- Close maximal prime factors of consecutive integers have bounded product. -/
theorem close_maxPrimeFac_product_le (n B : ℕ) (hn : 3 ≤ n)
    (h₁ : Nat.maxPrimeFac n ≤ Nat.maxPrimeFac (n + 1) + B)
    (h₂ : Nat.maxPrimeFac (n + 1) ≤ Nat.maxPrimeFac n + B) :
    Nat.maxPrimeFac n * Nat.maxPrimeFac (n + 1) ≤ (B + 1) * (n + 1) := by
  let p := Nat.maxPrimeFac n
  let q := Nat.maxPrimeFac (n + 1)
  let a := primeCofactor n
  let b := primeCofactor (n + 1)
  have ha : p * a = n := maxPrimeFac_mul_primeCofactor n
  have hb : q * b = n + 1 := maxPrimeFac_mul_primeCofactor (n + 1)
  have hab : b ≠ a := consecutive_primeCofactor_ne n hn
  have hp : p ≤ n := Nat.maxPrimeFac_le
  change p ≤ q + B at h₁
  change q ≤ p + B at h₂
  rcases lt_or_gt_of_ne hab with hba | hab
  · have hmul := Nat.mul_le_mul_left p (Nat.succ_le_iff.mpr hba)
    have hmul' := Nat.mul_le_mul_right b h₂
    have hq : p ≤ B * b := by nlinarith
    have := Nat.mul_le_mul_right q hq
    nlinarith
  · have hmul := Nat.mul_le_mul_left q (Nat.succ_le_iff.mpr hab)
    have hmul' := Nat.mul_le_mul_right a h₁
    have hq : q ≤ B * a + 1 := by nlinarith
    have := Nat.mul_le_mul_left p hq
    nlinarith

/-- In particular, a fixed additive difference forces both factors into a square-root range. -/
theorem close_maxPrimeFac_sq_le (n B : ℕ) (hn : 3 ≤ n)
    (h₁ : Nat.maxPrimeFac n ≤ Nat.maxPrimeFac (n + 1) + B)
    (h₂ : Nat.maxPrimeFac (n + 1) ≤ Nat.maxPrimeFac n + B) :
    Nat.maxPrimeFac n ^ 2 ≤ (2 * B + 1) * (n + 1) := by
  have hprod := close_maxPrimeFac_product_le n B hn h₁ h₂
  have hmul := Nat.mul_le_mul_left (Nat.maxPrimeFac n) h₁
  have hp : Nat.maxPrimeFac n ≤ n + 1 := Nat.maxPrimeFac_le.trans (by omega)
  have := Nat.mul_le_mul_left B hp
  nlinarith

/-- A pair of coprime divisor conditions occupies at most one point in each modulus block. -/
theorem consecutive_divisibility_count_le (N p q : ℕ) (hpq : p.Coprime q) :
    ((Finset.range N).filter fun n => p ∣ n ∧ q ∣ n + 1).card ≤ N / (p * q) + 1 := by
  let s := (Finset.range N).filter fun n => p ∣ n ∧ q ∣ n + 1
  have hle : s.card ≤ (Finset.range (N / (p * q) + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n / (p * q))
    · intro n hn
      have hnN : n < N := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnN.le))
    · intro a ha b hb heq
      simp only [s, Finset.mem_coe, Finset.mem_filter] at ha hb
      obtain ⟨_, hpa, hqa⟩ := ha
      obtain ⟨_, hpb, hqb⟩ := hb
      have hmodp : Nat.ModEq p a b := hpa.modEq_zero_nat.trans hpb.zero_modEq_nat
      have hmodq : Nat.ModEq q a b :=
        (hqa.modEq_zero_nat.trans hqb.zero_modEq_nat).add_right_cancel' 1
      have hmod := (Nat.modEq_and_modEq_iff_modEq_mul hpq).mp ⟨hmodp, hmodq⟩
      have haa := Nat.mod_add_div a (p * q)
      have hbb := Nat.mod_add_div b (p * q)
      change a % (p * q) = b % (p * q) at hmod
      change a / (p * q) = b / (p * q) at heq
      rw [hmod, heq] at haa
      omega
  simpa only [Finset.card_range] using hle


/-- The same counting bound holds without assuming coprimality: an actual
solution to the two divisibility conditions already forces it. -/
theorem consecutive_divisibility_count_le' (N p q : ℕ) :
    ((Finset.range N).filter fun n => p ∣ n ∧ q ∣ n + 1).card ≤ N / (p * q) + 1 := by
  by_cases h : p.Coprime q
  · exact consecutive_divisibility_count_le N p q h
  · have he : ((Finset.range N).filter fun n => p ∣ n ∧ q ∣ n + 1) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨_, hp, hq⟩ := Finset.mem_filter.mp hn
      exact h (Nat.Coprime.of_dvd hp hq (by simp))
    simp only [he, Finset.card_empty]
    exact Nat.zero_le _

def closeFactorEvent (B n : ℕ) : Prop :=
  Nat.maxPrimeFac n ≤ Nat.maxPrimeFac (n + 1) + B ∧
  Nat.maxPrimeFac (n + 1) ≤ Nat.maxPrimeFac n + B

instance (B n : ℕ) : Decidable (closeFactorEvent B n) := inferInstanceAs (Decidable (_ ∧ _))

def largeCloseFactors (N B R : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun n => 3 ≤ n ∧ R < Nat.maxPrimeFac n ∧
    R < Nat.maxPrimeFac (n + 1) ∧ closeFactorEvent B n

def divisorPairEvent (N p d : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun n =>
    (p ∣ n ∧ p + d ∣ n + 1) ∨ (p + d ∣ n ∧ p ∣ n + 1)

theorem divisorPairEvent_card_le (N p d : ℕ) (hp : 0 < p) :
    ((divisorPairEvent N p d).card : ℝ) ≤ 2 * ((N : ℝ) / (p : ℝ)^2 + 1) := by
  have hc : (divisorPairEvent N p d).card ≤
      ((Finset.range N).filter fun n => p ∣ n ∧ p + d ∣ n + 1).card +
      ((Finset.range N).filter fun n => p + d ∣ n ∧ p ∣ n + 1).card := by
    rw [divisorPairEvent, Finset.filter_or]
    exact Finset.card_union_le _ _
  have hb := hc.trans (Nat.add_le_add
    (consecutive_divisibility_count_le' N p (p + d))
    (consecutive_divisibility_count_le' N (p + d) p))
  rw [Nat.mul_comm (p + d) p] at hb
  have hb' : ((divisorPairEvent N p d).card : ℝ) ≤
      2 * ((N / (p * (p + d)) : ℕ) : ℝ) + 2 := by
    have hbNat : (divisorPairEvent N p d).card ≤ 2 * (N / (p * (p + d))) + 2 := by omega
    exact_mod_cast hbNat
  have hdiv : ((N / (p * (p + d)) : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ)^2 := by
    calc
      _ ≤ (N : ℝ) / ((p * (p + d) : ℕ) : ℝ) := Nat.cast_div_le
      _ ≤ _ := by
        push_cast
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) p) (Nat.cast_nonneg (α := ℝ) d)]
  linarith

theorem largeCloseFactors_subset (N B R : ℕ) :
    largeCloseFactors N B R ⊆
      (Finset.Ioo R (((B + 1) * N).sqrt + 1)).biUnion fun p =>
        (Finset.range (B + 1)).biUnion fun d => divisorPairEvent N p d := by
  intro n hn
  obtain ⟨hnN, hn3, hnp, hnq, h₁, h₂⟩ := Finset.mem_filter.mp hn
  have hnN' := Finset.mem_range.mp hnN
  have hprod := close_maxPrimeFac_product_le n B hn3 h₁ h₂
  have hprod' : Nat.maxPrimeFac n * Nat.maxPrimeFac (n + 1) ≤ (B + 1) * N :=
    hprod.trans (Nat.mul_le_mul_left _ (by omega))
  rcases le_total (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) with h | h
  · apply Finset.mem_biUnion.mpr
    refine ⟨Nat.maxPrimeFac n, ?_, ?_⟩
    · apply Finset.mem_Ioo.mpr
      refine ⟨hnp, Nat.lt_succ_of_le (Nat.le_sqrt.mpr ?_)⟩
      exact (Nat.mul_le_mul_left _ h).trans hprod'
    · apply Finset.mem_biUnion.mpr
      refine ⟨Nat.maxPrimeFac (n + 1) - Nat.maxPrimeFac n,
        Finset.mem_range.mpr (by omega), ?_⟩
      simp only [divisorPairEvent, Finset.mem_filter]
      rw [Nat.add_sub_of_le h]
      exact ⟨hnN, Or.inl ⟨Nat.maxPrimeFac_dvd, Nat.maxPrimeFac_dvd⟩⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨Nat.maxPrimeFac (n + 1), ?_, ?_⟩
    · apply Finset.mem_Ioo.mpr
      refine ⟨hnq, Nat.lt_succ_of_le (Nat.le_sqrt.mpr ?_)⟩
      exact (Nat.mul_le_mul_right _ h).trans hprod'
    · apply Finset.mem_biUnion.mpr
      refine ⟨Nat.maxPrimeFac n - Nat.maxPrimeFac (n + 1),
        Finset.mem_range.mpr (by omega), ?_⟩
      simp only [divisorPairEvent, Finset.mem_filter]
      rw [Nat.add_sub_of_le h]
      exact ⟨hnN, Or.inr ⟨Nat.maxPrimeFac_dvd, Nat.maxPrimeFac_dvd⟩⟩

theorem largeCloseFactors_card_le (N B R : ℕ) :
    ((largeCloseFactors N B R).card : ℝ) ≤
      2 * (B + 1 : ℝ) * ((N : ℝ) * (2 / (R + 1 : ℝ)) + ((B + 1) * N).sqrt + 1) := by
  let L := ((B + 1) * N).sqrt
  let s := Finset.Ioo R (L + 1)
  have hc : (largeCloseFactors N B R).card ≤
      ∑ p ∈ s, ∑ d ∈ Finset.range (B + 1), (divisorPairEvent N p d).card := by
    apply (Finset.card_le_card (largeCloseFactors_subset N B R)).trans
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum fun p _ => Finset.card_biUnion_le
  have hc' : ((largeCloseFactors N B R).card : ℝ) ≤
      ∑ p ∈ s, ∑ d ∈ Finset.range (B + 1), ((divisorPairEvent N p d).card : ℝ) := by
    exact_mod_cast hc
  have hs : ∑ p ∈ s, ((p : ℝ)^2)⁻¹ ≤ 2 / (R + 1 : ℝ) :=
    sum_Ioo_inv_sq_le R (L + 1)
  have hsc : (s.card : ℝ) ≤ L + 1 := by
    have hsub : s ⊆ Finset.range (L + 1) := fun p hp =>
      Finset.mem_range.mpr (Finset.mem_Ioo.mp hp).2
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
  calc
    _ ≤ ∑ p ∈ s, ∑ d ∈ Finset.range (B + 1),
        2 * ((N : ℝ) / (p : ℝ)^2 + 1) := hc'.trans (Finset.sum_le_sum fun p hp =>
      Finset.sum_le_sum fun d _ => divisorPairEvent_card_le N p d
        (lt_of_le_of_lt (Nat.zero_le R) (Finset.mem_Ioo.mp hp).1))
    _ = 2 * (B + 1 : ℝ) * ((N : ℝ) * (∑ p ∈ s, ((p : ℝ)^2)⁻¹) + s.card) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one, div_eq_mul_inv]
      rw [← Finset.mul_sum]
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        nsmul_eq_mul]
      ring
    _ ≤ _ := by
      dsimp only [L] at hsc ⊢
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hn := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) N)
      linarith


theorem closeFactorEvent_card_le (N B R : ℕ) :
    (((Finset.range N).filter (closeFactorEvent B)).card : ℝ) ≤
      3 + (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ R + B).card : ℝ) +
      2 * (B + 1 : ℝ) * ((N : ℝ) * (2 / (R + 1 : ℝ)) + ((B + 1) * N).sqrt + 1) := by
  have hsub : (Finset.range N).filter (closeFactorEvent B) ⊆
      (Finset.range 3 ∪ ((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ R + B)) ∪
        largeCloseFactors N B R := by
    intro n hn
    obtain ⟨hnN, h₁, h₂⟩ := Finset.mem_filter.mp hn
    by_cases h3 : n < 3
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_range.mpr h3))
    by_cases hR : Nat.maxPrimeFac n ≤ R + B
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnN, hR⟩))
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hnN, by omega, by omega, by omega, h₁, h₂⟩
  have hc := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hc' : (((Finset.range N).filter (closeFactorEvent B)).card : ℝ) ≤
      3 + (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ R + B).card : ℝ) +
        ((largeCloseFactors N B R).card : ℝ) := by
    simpa only [Finset.card_range, Nat.cast_add, Nat.cast_ofNat] using
      (Nat.cast_le (α := ℝ)).mpr hc
  exact hc'.trans (add_le_add le_rfl (largeCloseFactors_card_le N B R))

open Filter in
theorem sqrt_mul_add_one_div_tendsto_zero (C : ℕ) :
    Tendsto (fun N : ℕ => (((C * N).sqrt : ℝ) + 1) / N) atTop (nhds 0) := by
  have hsqrt (N : ℕ) : ((C * N).sqrt : ℝ) ≤ Real.sqrt C * Real.sqrt N := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg C), ← Nat.cast_mul]
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' (C * N)
  have hb (N : ℕ) : (((C * N).sqrt : ℝ) + 1) / N ≤
      Real.sqrt C * (Real.sqrt N)⁻¹ + 1 / N := by
    calc
      _ ≤ (Real.sqrt C * Real.sqrt N + 1) / N := by gcongr; exact hsqrt N
      _ = _ := by rw [add_div, mul_div_assoc, Real.sqrt_div_self]
  have ht : Tendsto (fun N : ℕ => Real.sqrt C * (Real.sqrt N)⁻¹ + 1 / N)
      atTop (nhds 0) := by
    have hi : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa using (hi.const_mul (Real.sqrt C)).add tendsto_one_div_atTop_nhds_zero_nat
  exact squeeze_zero (fun N => by positivity) hb ht

open Filter in
/-- The two consecutive largest prime factors escape every fixed additive
neighborhood of each other, outside a set of natural density zero. -/
theorem closeFactorEvent_hasDensity_zero (B : ℕ) :
    {n : ℕ | closeFactorEvent B n}.HasDensity 0 := by
  rw [density_iff_count]
  let f (N : ℕ) : ℝ := (((Finset.range N).filter (closeFactorEvent B)).card : ℝ) / N
  let e (R N : ℕ) : ℝ := 3 / N +
    (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ R + B).card : ℝ) / N +
    (2 * (B + 1 : ℝ)) * ((((B + 1) * N).sqrt : ℝ) + 1) / N
  have he (R : ℕ) : Tendsto (e R) atTop (nhds 0) := by
    have h₁ := tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)
    have h₂ := (density_iff_count _ 0).mp (bounded_maxPrimeFac_hasDensity_zero (R + B))
    have h₃ := (sqrt_mul_add_one_div_tendsto_zero (B + 1)).const_mul (2 * (B + 1 : ℝ))
    simpa only [e, mul_div_assoc, add_zero, mul_zero, zero_add] using (h₁.add h₂).add h₃
  have hbound (R N : ℕ) (hN : 0 < N) : f N ≤ e R N + 4 * (B + 1 : ℝ) / (R + 1 : ℝ) := by
    have hb := div_le_div_of_nonneg_right (closeFactorEvent_card_le N B R)
      (Nat.cast_nonneg (α := ℝ) N)
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    convert hb using 1
    dsimp only [e]
    field_simp
    <;> ring
  have hRlim : Tendsto (fun R : ℕ => 4 * (B + 1 : ℝ) / (R + 1 : ℝ)) atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (4 * (B + 1 : ℝ))).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R, hR⟩ := (hRlim.eventually (gt_mem_nhds (half_pos hε))).exists
  filter_upwards [(he R).eventually (gt_mem_nhds (half_pos hε)), eventually_gt_atTop 0] with N heN hN
  change dist (f N) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ f N by dsimp [f]; positivity)]
  have hb := hbound R N hN
  linarith


/-- An equivalent distance formulation of the fixed-width near-tie estimate. -/
theorem bounded_prime_factor_distance_hasDensity_zero (B : ℕ) :
    {n : ℕ | Nat.dist (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) ≤ B}.HasDensity 0 := by
  have hset : {n : ℕ | Nat.dist (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) ≤ B} =
      {n : ℕ | closeFactorEvent B n} := by
    ext n
    simp only [Set.mem_setOf_eq, closeFactorEvent, Nat.dist]
    omega
  rw [hset]
  exact closeFactorEvent_hasDensity_zero B

/-- Even arbitrary bounded, nonconstant additive perturbations leave the
possible comparison density unchanged. -/
theorem bounded_additive_perturbation_density_iff (B : ℕ) (a b : ℕ → ℕ)
    (ha : ∀ n, a n ≤ B) (hb : ∀ n, b n ≤ B) (d : ℝ) :
    {n : ℕ | Nat.maxPrimeFac n + a n < Nat.maxPrimeFac (n + 1) + b n}.HasDensity d ↔
      {n : ℕ | Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)}.HasDensity d := by
  apply density_iff_of_exception _ _ (closeFactorEvent B)
  · intro n hn
    dsimp only [closeFactorEvent] at hn
    have h₁ := ha n
    have h₂ := hb n
    omega
  · exact closeFactorEvent_hasDensity_zero B

#print axioms close_maxPrimeFac_product_le
#print axioms largeCloseFactors_card_le
#print axioms closeFactorEvent_hasDensity_zero
#print axioms bounded_additive_perturbation_density_iff

end Erdos371
