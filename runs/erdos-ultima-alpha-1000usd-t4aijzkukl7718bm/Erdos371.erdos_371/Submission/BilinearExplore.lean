import Submission.GrowingRoughTail

/-! Bilinear form of the remaining rough mixed-divisor sum.
The finite identities here do not assert cancellation of that sum. -/

namespace Erdos371

lemma minFac_mul_of_one_lt (a b : ℕ) (ha : 1 < a) (hb : 1 < b) :
    (a * b).minFac = min a.minFac b.minFac := by
  have hab : a * b ≠ 1 := by nlinarith
  have hp := Nat.minFac_prime hab
  have ha' := Nat.minFac_prime (show a ≠ 1 by omega)
  have hb' := Nat.minFac_prime (show b ≠ 1 by omega)
  apply le_antisymm
  · exact le_min
      (Nat.minFac_le_of_dvd ha'.two_le (dvd_mul_of_dvd_left (Nat.minFac_dvd a) b))
      (Nat.minFac_le_of_dvd hb'.two_le (dvd_mul_of_dvd_right (Nat.minFac_dvd b) a))
  · rcases hp.dvd_mul.mp (Nat.minFac_dvd (a * b)) with h | h
    · exact (min_le_left _ _).trans (Nat.minFac_le_of_dvd hp.two_le h)
    · exact (min_le_right _ _).trans (Nat.minFac_le_of_dvd hp.two_le h)

lemma coprime_minFac_ne (a b : ℕ) (ha : 1 < a) (hab : a.Coprime b) :
    a.minFac ≠ b.minFac := by
  intro h
  have hp := Nat.minFac_prime (show a ≠ 1 by omega)
  apply hp.not_dvd_one
  rw [← hab.gcd_eq_one]
  exact Nat.dvd_gcd (Nat.minFac_dvd a) (h ▸ Nat.minFac_dvd b)

noncomputable def bilinearSign (a b : ℕ) : ℝ :=
  if a.minFac < b.minFac then -1 else if b.minFac < a.minFac then 1 else 0

lemma bilinearSign_swap (a b : ℕ) : bilinearSign b a = -bilinearSign a b := by
  unfold bilinearSign
  rcases lt_trichotomy a.minFac b.minFac with h | h | h
  · simp [h, h.not_gt]
  · simp [h]
  · simp [h, h.not_gt]

noncomputable def roughBilinearWeight (B D a b : ℕ) : ℝ :=
  if 1 < a ∧ 1 < b ∧ D < a * b ∧ B < a.minFac ∧ B < b.minFac then
    (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) * bilinearSign a b
  else 0

lemma roughBilinearWeight_swap (B D a b : ℕ) :
    roughBilinearWeight B D b a = -roughBilinearWeight B D a b := by
  unfold roughBilinearWeight
  rw [Nat.mul_comm b a, bilinearSign_swap]
  by_cases h : 1 < a ∧ 1 < b ∧ D < a * b ∧ B < a.minFac ∧ B < b.minFac
  · have h' : 1 < b ∧ 1 < a ∧ D < a * b ∧ B < b.minFac ∧ B < a.minFac := by tauto
    simp only [if_pos h, if_pos h']
    ring
  · have h' : ¬ (1 < b ∧ 1 < a ∧ D < a * b ∧ B < b.minFac ∧ B < a.minFac) := by tauto
    simp only [if_neg h, if_neg h', neg_zero]

lemma divisor_pair_coprime (n a b : ℕ) (ha : a ∣ n) (hb : b ∣ n + 1) : a.Coprime b :=
  Nat.Coprime.of_dvd ha hb (by simp)

lemma minFac_product_dvd_next_iff (n a b : ℕ) (ha : a ∣ n) (hb : b ∣ n + 1)
    (ha1 : 1 < a) (hb1 : 1 < b) :
    (a * b).minFac ∣ n + 1 ↔ b.minFac < a.minFac := by
  rw [minFac_mul_of_one_lt a b ha1 hb1]
  have hne := coprime_minFac_ne a b ha1 (divisor_pair_coprime n a b ha hb)
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le]
    have hn : ¬ a.minFac ∣ n + 1 := by
      intro h'
      exact (Nat.minFac_prime (show a ≠ 1 by omega)).not_dvd_one
        ((Nat.dvd_add_iff_right ((Nat.minFac_dvd a).trans ha)).mpr h')
    simp [hn, h.not_gt]
  · rw [min_eq_right h.le]
    simp [h, (Nat.minFac_dvd b).trans hb]

lemma roughBilinearWeight_eq (B D n a b : ℕ) (hn : 0 < n)
    (ha : a ∣ n) (hb : b ∣ n + 1) :
    roughBilinearWeight B D a b =
      if D < a * b ∧ B < (a * b).minFac then mixedOrientedDivisorTerm (a * b) n else 0 := by
  have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hn
  have hb0 : 0 < b := Nat.pos_of_dvd_of_pos hb (by omega)
  by_cases ha1 : 1 < a
  · by_cases hb1 : 1 < b
    · have hc := divisor_pair_coprime n a b ha hb
      have hne := coprime_minFac_ne a b ha1 hc
      have hmin := minFac_mul_of_one_lt a b ha1 hb1
      have hpcolor := minFac_product_dvd_next_iff n a b ha hb ha1 hb1
      have hnot : ¬ (a * b ∣ n ∨ a * b ∣ n + 1) := by
        rintro (h | h)
        · have hbn : b ∣ n := (Nat.dvd_mul_left b a).trans h
          have := Nat.dvd_one.mp ((Nat.dvd_add_iff_right hbn).mpr hb)
          omega
        · have han : a ∣ n + 1 := (Nat.dvd_mul_right a b).trans h
          have := Nat.dvd_one.mp ((Nat.dvd_add_iff_right ha).mpr han)
          omega
      have hprod : 1 < a * b := by nlinarith
      have hμ := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc
      rw [roughBilinearWeight, mixedOrientedDivisorTerm, if_neg hnot,
        orientedDivisorTerm, if_pos (Nat.mul_dvd_mul ha hb), leastFactorTerm_eq_moebius,
        if_pos hprod, hμ]
      push_cast
      have hcol : (if (a * b).minFac ∣ n + 1 then (1 : ℝ) else -1) = bilinearSign a b := by
        simp only [hpcolor]
        unfold bilinearSign
        rcases lt_or_gt_of_ne hne with h | h <;> simp [h, h.not_gt]
      rw [hcol]
      simp only [hmin, lt_min_iff]
      by_cases hD : D < a * b <;> by_cases hBa : B < a.minFac <;> by_cases hBb : B < b.minFac <;>
        simp [ha1, hb1, hD, hBa, hBb]
    · have hb' : b = 1 := by omega
      subst b
      simp [roughBilinearWeight, mixedOrientedDivisorTerm, ha]
  · have ha' : a = 1 := by omega
    subst a
    simp [roughBilinearWeight, mixedOrientedDivisorTerm, hb]

lemma sum_divisors_consecutive_product (n : ℕ) (hn : 0 < n) (f : ℕ → ℝ) :
    (∑ d ∈ (n * (n + 1)).divisors, f d) =
      ∑ a ∈ n.divisors, ∑ b ∈ (n + 1).divisors, f (a * b) := by
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_bij (fun ab _ => ab.1 * ab.2)
  · intro ab hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul (Nat.mem_divisors.mp ha).1
      (Nat.mem_divisors.mp hb).1, by positivity⟩
  · intro ab hab cd hcd he
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc, hd⟩ := Finset.mem_product.mp hcd
    have h₁ := (Nat.mem_divisors.mp ha).1
    have h₂ := (Nat.mem_divisors.mp hb).1
    have h₃ := (Nat.mem_divisors.mp hc).1
    have h₄ := (Nat.mem_divisors.mp hd).1
    have hac : ab.1 = cd.1 := by
      apply Nat.dvd_antisymm
      · apply (divisor_pair_coprime n ab.1 cd.2 h₁ h₄).dvd_of_dvd_mul_right
        rw [← he]
        exact Nat.dvd_mul_right _ _
      · apply (divisor_pair_coprime n cd.1 ab.2 h₃ h₂).dvd_of_dvd_mul_right
        rw [he]
        exact Nat.dvd_mul_right _ _
    have hbd : ab.2 = cd.2 := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_dvd_of_pos h₁ hn)
      simpa only [hac] using he
    exact Prod.ext hac hbd
  · intro d hd
    have hd' := (Nat.mem_divisors.mp hd).1
    refine ⟨(n.gcd d, (n + 1).gcd d), ?_, root_gcd_product d n hd'⟩
    exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, by omega⟩,
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, by omega⟩⟩
  · intro ab hab
    rfl

lemma roughMixedDivisorTail_bilinear (B D n : ℕ) (hn : 0 < n) :
    roughMixedDivisorTail B D n =
      ∑ a ∈ n.divisors, ∑ b ∈ (n + 1).divisors, roughBilinearWeight B D a b := by
  rw [roughMixedDivisorTail, Finset.sum_filter, sum_divisors_consecutive_product n hn]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact (roughBilinearWeight_eq B D n a b hn (Nat.mem_divisors.mp ha).1
    (Nat.mem_divisors.mp hb).1).symm


lemma sum_divisors_eq_range (m L : ℕ) (hm : 0 < m) (hL : m < L) (f : ℕ → ℝ) :
    (∑ d ∈ m.divisors, f d) = ∑ d ∈ Finset.range L, if d ∣ m then f d else 0 := by
  have hs : (Finset.range L).filter (fun d => d ∣ m) = m.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
    constructor
    · exact fun h => ⟨h.2, hm.ne'⟩
    · exact fun h => ⟨(Nat.le_of_dvd hm h.1).trans_lt hL, h.1⟩
  rw [← Finset.sum_filter, hs]

lemma roughMixedDivisorTail_bilinear_range (B D n L : ℕ) (hn : 0 < n) (hL : n + 1 < L) :
    roughMixedDivisorTail B D n = ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
      if a ∣ n ∧ b ∣ n + 1 then roughBilinearWeight B D a b else 0 := by
  rw [roughMixedDivisorTail_bilinear B D n hn, sum_divisors_eq_range n L hn (by omega)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sum_divisors_eq_range (n + 1) L (by omega) hL]
  by_cases h : a ∣ n <;> simp [h]

def bilinearCount (N a b : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => a ∣ n + 1 ∧ b ∣ n + 2).card

lemma roughMixedDivisorTail_prefix_bilinear (B D N : ℕ) :
    (∑ n ∈ Finset.range N, roughMixedDivisorTail B D (n + 1)) =
      ∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
        roughBilinearWeight B D a b * (bilinearCount N a b : ℝ) := by
  calc
    _ = ∑ n ∈ Finset.range N, ∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
        if a ∣ n + 1 ∧ b ∣ n + 2 then roughBilinearWeight B D a b else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnN := Finset.mem_range.mp hn
      exact roughMixedDivisorTail_bilinear_range B D (n + 1) (N + 2) (by omega) (by omega)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [← Finset.sum_filter]
      simp [bilinearCount, mul_comm]

lemma roughMixedDivisorTail_prefix_antisymmetric (B D N : ℕ) :
    2 * (∑ n ∈ Finset.range N, roughMixedDivisorTail B D (n + 1)) =
      ∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
        roughBilinearWeight B D a b * ((bilinearCount N a b : ℝ) - bilinearCount N b a) := by
  rw [roughMixedDivisorTail_prefix_bilinear]
  have he :
      (∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
        roughBilinearWeight B D a b * (bilinearCount N b a : ℝ)) =
      -(∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
        roughBilinearWeight B D a b * (bilinearCount N a b : ℝ)) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [roughBilinearWeight_swap B D a b, neg_mul]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [he]
  ring

open Filter in
/-- This bilinear limit is another exact form of the unproved cancellation. -/
theorem density_iff_bilinear_discrepancy :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ =>
        (∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
          roughBilinearWeight (roughCutoff N) (nearLinearCutoff N) a b *
            ((bilinearCount N a b : ℝ) - bilinearCount N b a)) / (2 * N)) atTop (nhds 0) := by
  rw [density_iff_growing_rough_mixed_tail]
  have he (N : ℕ) :
      (∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
        roughBilinearWeight (roughCutoff N) (nearLinearCutoff N) a b *
          ((bilinearCount N a b : ℝ) - bilinearCount N b a)) / (2 * N) =
      (∑ n ∈ Finset.range N,
        roughMixedDivisorTail (roughCutoff N) (nearLinearCutoff N) (n + 1)) / N := by
    rw [← roughMixedDivisorTail_prefix_antisymmetric]
    ring
  simp_rw [he]

noncomputable def pairIndicatorDifference (a b n : ℕ) : ℝ :=
  (if a ∣ n ∧ b ∣ n + 1 then 1 else 0) - (if b ∣ n ∧ a ∣ n + 1 then 1 else 0)

lemma pairIndicatorDifference_periodic (a b : ℕ) :
    Function.Periodic (pairIndicatorDifference a b) (a * b) := by
  intro n
  have ha : Nat.ModEq a (n + a * b) n := by simp [Nat.ModEq, Nat.add_mod]
  have hb : Nat.ModEq b (n + a * b) n := by simp [Nat.ModEq, Nat.add_mod]
  simp only [pairIndicatorDifference, ha.dvd_iff (dvd_refl a), hb.dvd_iff (dvd_refl b),
    (ha.add_right 1).dvd_iff (dvd_refl a), (hb.add_right 1).dvd_iff (dvd_refl b)]

lemma reflected_divisibility (d n m : ℕ) (h : d ∣ n + m + 1) :
    (d ∣ m ↔ d ∣ n + 1) ∧ (d ∣ m + 1 ↔ d ∣ n) := by
  have h' : d ∣ (n + 1) + m := by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have h'' : d ∣ n + (m + 1) := by simpa only [Nat.add_assoc] using h
  constructor
  · exact ⟨fun hm => (Nat.dvd_add_iff_left hm).mpr h',
      fun hn => (Nat.dvd_add_iff_right hn).mpr h'⟩
  · exact ⟨fun hm => (Nat.dvd_add_iff_left hm).mpr h'',
      fun hn => (Nat.dvd_add_iff_right hn).mpr h''⟩

lemma pairIndicatorDifference_reflection (a b n : ℕ) (hn : n < a * b) :
    pairIndicatorDifference a b (a * b - 1 - n) = -pairIndicatorDifference a b n := by
  have he : n + (a * b - 1 - n) + 1 = a * b := by omega
  have ha := reflected_divisibility a n (a * b - 1 - n) (by rw [he]; exact Nat.dvd_mul_right a b)
  have hb := reflected_divisibility b n (a * b - 1 - n) (by rw [he]; exact Nat.dvd_mul_left b a)
  simp only [pairIndicatorDifference, ha.1, ha.2, hb.1, hb.2, and_comm]
  ring

lemma pairIndicatorDifference_mean_zero (a b : ℕ) :
    ∑ n ∈ Finset.range (a * b), pairIndicatorDifference a b n = 0 := by
  have he := Finset.sum_range_reflect (pairIndicatorDifference a b) (a * b)
  have hf : ∑ n ∈ Finset.range (a * b), pairIndicatorDifference a b (a * b - 1 - n) =
      -(∑ n ∈ Finset.range (a * b), pairIndicatorDifference a b n) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun n hn =>
      pairIndicatorDifference_reflection a b n (Finset.mem_range.mp hn)
  linarith

lemma pairIndicatorDifference_shifted_mean_zero (a b : ℕ) :
    ∑ n ∈ Finset.range (a * b), pairIndicatorDifference a b (n + 1) = 0 := by
  have he := Finset.sum_range_succ' (pairIndicatorDifference a b) (a * b)
  rw [Finset.sum_range_succ] at he
  have hp : pairIndicatorDifference a b (a * b) = pairIndicatorDifference a b 0 := by
    simpa only [zero_add] using pairIndicatorDifference_periodic a b 0
  linarith [pairIndicatorDifference_mean_zero a b]

lemma bilinearCount_le_one (N a b : ℕ) (hab : a.Coprime b) (hN : N ≤ a * b) :
    bilinearCount N a b ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro r hr s hs
  obtain ⟨hrN, har, hbr⟩ := Finset.mem_filter.mp hr
  obtain ⟨hsN, has, hbs⟩ := Finset.mem_filter.mp hs
  have ha : Nat.ModEq a r s :=
    (har.modEq_zero_nat.trans has.zero_modEq_nat).add_right_cancel' 1
  have hb : Nat.ModEq b r s :=
    (hbr.modEq_zero_nat.trans hbs.zero_modEq_nat).add_right_cancel' 2
  exact ((Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨ha, hb⟩).eq_of_lt_of_lt
    ((Finset.mem_range.mp hrN).trans_le hN) ((Finset.mem_range.mp hsN).trans_le hN)

lemma bilinearCount_eq_zero_of_not_coprime (N a b : ℕ) (hab : ¬a.Coprime b) :
    bilinearCount N a b = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨_, ha, hb⟩ := Finset.mem_filter.mp hn
  exact hab (divisor_pair_coprime (n + 1) a b ha hb)

lemma bilinearCount_difference_eq_sum (N a b : ℕ) :
    (bilinearCount N a b : ℝ) - bilinearCount N b a =
      ∑ n ∈ Finset.range N, pairIndicatorDifference a b (n + 1) := by
  simp [pairIndicatorDifference, bilinearCount, Finset.sum_sub_distrib, Nat.add_assoc]

/-- The two orientations differ by at most one point, regardless of the size
of the interval. This is a bound on each pair, not on the weighted bilinear sum. -/
theorem bilinearCount_discrepancy_le_one (N a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ‖(bilinearCount N a b : ℝ) - bilinearCount N b a‖ ≤ 1 := by
  by_cases hab : a.Coprime b
  · have hp : Function.Periodic (fun n => pairIndicatorDifference a b (n + 1)) (a * b) := by
      intro n
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        pairIndicatorDifference_periodic a b (n + 1)
    rw [bilinearCount_difference_eq_sum, periodic_sum_zero_eq_remainder _ (a * b) hp
      (pairIndicatorDifference_shifted_mean_zero a b), ← bilinearCount_difference_eq_sum]
    have hmod : N % (a * b) ≤ a * b := (Nat.mod_lt N (by positivity)).le
    have h₁ : (bilinearCount (N % (a * b)) a b : ℝ) ≤ 1 := by
      exact_mod_cast bilinearCount_le_one (N % (a * b)) a b hab hmod
    have h₂ : (bilinearCount (N % (a * b)) b a : ℝ) ≤ 1 := by
      exact_mod_cast bilinearCount_le_one (N % (a * b)) b a hab.symm (by simpa [Nat.mul_comm] using hmod)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (bilinearCount (N % (a * b)) a b),
      Nat.cast_nonneg (α := ℝ) (bilinearCount (N % (a * b)) b a)]
  · have hba : ¬b.Coprime a := fun h => hab h.symm
    rw [bilinearCount_eq_zero_of_not_coprime N a b hab,
      bilinearCount_eq_zero_of_not_coprime N b a hba]
    norm_num

#print axioms roughMixedDivisorTail_prefix_antisymmetric
#print axioms density_iff_bilinear_discrepancy
#print axioms bilinearCount_discrepancy_le_one
end Erdos371
