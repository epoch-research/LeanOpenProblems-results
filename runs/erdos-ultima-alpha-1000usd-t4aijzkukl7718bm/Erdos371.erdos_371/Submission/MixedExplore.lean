import Submission.TailExplore

/-! Removal of the one-sided terms in the large-divisor remainder. -/

namespace Erdos371

lemma divisors_card_le_two_sqrt_add_two (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card ≤ 2 * n.sqrt + 2 := by
  let s := Finset.range (n.sqrt + 1)
  have hsub : n.divisors ⊆ s ∪ s.image (fun d => n / d) := by
    intro d hd
    have hdn := (Nat.mem_divisors.mp hd).1
    have he : n = d * (n / d) := (Nat.mul_div_cancel' hdn).symm
    rcases Nat.le_sqrt_of_eq_mul he with h | h
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨n / d, Finset.mem_range.mpr (by omega), Nat.div_div_self hdn hn⟩
  have hc := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _))
  simp only [s, Finset.card_range] at hc
  omega

noncomputable def signedMobius (d : ℕ) : ℝ :=
  if 1 < d then (ArithmeticFunction.moebius d : ℝ) else 0

lemma signedMobius_norm_le_one (d : ℕ) : ‖signedMobius d‖ ≤ 1 := by
  unfold signedMobius
  split_ifs
  · rw [Real.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  · simp

noncomputable def mobiusTail (D n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, if D < d then signedMobius d else 0

lemma mobiusTail_norm_le (D n : ℕ) : ‖mobiusTail D n‖ ≤ n.divisors.card := by
  unfold mobiusTail
  calc
    _ ≤ ∑ d ∈ n.divisors, ‖if D < d then signedMobius d else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · exact signedMobius_norm_le_one d
      · simp
    _ = _ := by simp

lemma mobiusTail_one (D : ℕ) : mobiusTail D 1 = 0 := by
  simp [mobiusTail, signedMobius]

noncomputable def mixedOrientedDivisorTerm (d n : ℕ) : ℝ :=
  if d ∣ n ∨ d ∣ n + 1 then 0 else orientedDivisorTerm d n

lemma orientedDivisorTerm_decompose (d n : ℕ) :
    orientedDivisorTerm d n = mixedOrientedDivisorTerm d n + signedMobius d *
      ((if d ∣ n + 1 then (1 : ℝ) else 0) - (if d ∣ n then (1 : ℝ) else 0)) := by
  classical
  by_cases hd : 1 < d
  · have hp := Nat.minFac_prime (n := d) (by omega)
    by_cases h₁ : d ∣ n
    · have h₂ : ¬d ∣ n + 1 := by
        intro h
        have : d ∣ 1 := (Nat.dvd_add_iff_right h₁).mpr h
        have := Nat.dvd_one.mp this
        omega
      have hmin : ¬d.minFac ∣ n + 1 := by
        intro h
        exact hp.not_dvd_one ((Nat.dvd_add_iff_right ((Nat.minFac_dvd d).trans h₁)).mpr h)
      simp [mixedOrientedDivisorTerm, signedMobius, orientedDivisorTerm,
        dvd_mul_of_dvd_left h₁ (n + 1), leastFactorTerm_eq_moebius, hd, h₁, h₂, hmin]
    · by_cases h₂ : d ∣ n + 1
      · have hmin : d.minFac ∣ n + 1 := (Nat.minFac_dvd d).trans h₂
        simp [mixedOrientedDivisorTerm, signedMobius, orientedDivisorTerm,
          dvd_mul_of_dvd_right h₂ n, leastFactorTerm_eq_moebius, hd, h₁, h₂, hmin]
      · simp [mixedOrientedDivisorTerm, h₁, h₂]
  · simp [mixedOrientedDivisorTerm, signedMobius, hd,
      orientedDivisorTerm_eq_zero_of_le_one d n (by omega)]

lemma sum_divisors_restrict (m M : ℕ) (hm : m ≠ 0) (hM : M ≠ 0) (hd : m ∣ M)
    (f : ℕ → ℝ) :
    (∑ d ∈ M.divisors, if d ∣ m then f d else 0) = ∑ d ∈ m.divisors, f d := by
  classical
  have hs : M.divisors.filter (fun d => d ∣ m) = m.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hdm⟩
      exact ⟨hdm, hm⟩
    · rintro ⟨hdm, _⟩
      exact ⟨⟨hdm.trans hd, hM⟩, hdm⟩
  rw [← Finset.sum_filter, hs]

noncomputable def mixedDivisorTail (D n : ℕ) : ℝ :=
  ∑ d ∈ (n * (n + 1)).divisors with D < d, mixedOrientedDivisorTerm d n

lemma largeDivisorTail_decompose (D n : ℕ) (hn : 0 < n) :
    largeDivisorTail D n = mixedDivisorTail D n + mobiusTail D (n + 1) - mobiusTail D n := by
  classical
  have hm : n * (n + 1) ≠ 0 := Nat.mul_ne_zero hn.ne' (by omega)
  have hterm (d : ℕ) : (if D < d then orientedDivisorTerm d n else 0) =
      (if D < d then mixedOrientedDivisorTerm d n else 0) +
      (if d ∣ n + 1 then (if D < d then signedMobius d else 0) else 0) -
      (if d ∣ n then (if D < d then signedMobius d else 0) else 0) := by
    rw [orientedDivisorTerm_decompose]
    by_cases hD : D < d <;> by_cases h₁ : d ∣ n <;> by_cases h₂ : d ∣ n + 1 <;>
      simp [hD, h₁, h₂] <;> ring
  unfold largeDivisorTail mixedDivisorTail
  rw [Finset.sum_filter, Finset.sum_filter]
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_divisors_restrict (n + 1) (n * (n + 1)) (by omega) hm (Nat.dvd_mul_left _ _),
    sum_divisors_restrict n (n * (n + 1)) hn.ne' hm (Nat.dvd_mul_right _ _)]
  rfl

lemma one_sided_tail_prefix (D N : ℕ) :
    (∑ n ∈ Finset.range N, (largeDivisorTail D (n + 1) - mixedDivisorTail D (n + 1))) =
      mobiusTail D (N + 1) := by
  have he (n : ℕ) : largeDivisorTail D (n + 1) - mixedDivisorTail D (n + 1) =
      mobiusTail D (n + 1 + 1) - mobiusTail D (n + 1) := by
    rw [largeDivisorTail_decompose D (n + 1) (by omega)]
    ring
  simp_rw [he]
  have h := Finset.sum_range_sub (fun n => mobiusTail D (n + 1)) N
  simpa only [zero_add, mobiusTail_one, sub_zero] using h

lemma one_sided_tail_prefix_bound (D N : ℕ) :
    ‖∑ n ∈ Finset.range N, (largeDivisorTail D (n + 1) - mixedDivisorTail D (n + 1))‖ ≤
      2 * (N.sqrt : ℝ) + 4 := by
  rw [one_sided_tail_prefix]
  apply (mobiusTail_norm_le D (N + 1)).trans
  have hc := divisors_card_le_two_sqrt_add_two (N + 1) (by omega)
  have hs := Nat.sqrt_succ_le_succ_sqrt N
  change (N + 1).sqrt ≤ N.sqrt + 1 at hs
  exact_mod_cast (show (N + 1).divisors.card ≤ 2 * N.sqrt + 4 by omega)

open Filter in
lemma one_sided_tail_average_tendsto_zero (D : ℕ → ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, largeDivisorTail (D N) (n + 1)) / N -
      (∑ n ∈ Finset.range N, mixedDivisorTail (D N) (n + 1)) / N) atTop (nhds 0) := by
  have hsqrt (N : ℕ) : (N.sqrt : ℝ) ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' N
  have hb (N : ℕ) :
      ‖(∑ n ∈ Finset.range N, largeDivisorTail (D N) (n + 1)) / N -
        (∑ n ∈ Finset.range N, mixedDivisorTail (D N) (n + 1)) / N‖ ≤
      2 * (Real.sqrt N)⁻¹ + 4 / N := by
    rw [← sub_div, ← Finset.sum_sub_distrib, norm_div, Real.norm_natCast]
    calc
      _ ≤ (2 * (N.sqrt : ℝ) + 4) / N := div_le_div_of_nonneg_right
        (one_sided_tail_prefix_bound (D N) N) (Nat.cast_nonneg N)
      _ ≤ (2 * Real.sqrt N + 4) / N := by gcongr; exact hsqrt N
      _ = _ := by rw [add_div, mul_div_assoc, Real.sqrt_div_self]
  have hi : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm hb
  simpa using (hi.const_mul 2).add (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ))

open Filter in
/-- After removing all one-sided terms, only the genuinely mixed composite
large-divisor sum remains to be estimated. -/
theorem density_iff_mixed_divisor_tail :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
        mixedDivisorTail N.sqrt.sqrt (n + 1)) / N) atTop (nhds 0) := by
  rw [density_iff_large_divisor_tail]
  have he := one_sided_tail_average_tendsto_zero (fun N => N.sqrt.sqrt)
  constructor
  · intro h
    have ht := h.sub he
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    ring
  · intro h
    simpa only [sub_add_cancel, add_zero] using he.add h

#print axioms divisors_card_le_two_sqrt_add_two
#print axioms largeDivisorTail_decompose
#print axioms one_sided_tail_average_tendsto_zero
#print axioms density_iff_mixed_divisor_tail

end Erdos371
