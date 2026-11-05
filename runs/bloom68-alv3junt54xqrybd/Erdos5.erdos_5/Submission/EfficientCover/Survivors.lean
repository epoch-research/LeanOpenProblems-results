import Submission.EfficientCover.Counting

/-! The initial medium-prime sieve and its elementary cardinality estimate. -/

open Filter
open scoped BigOperators Topology

namespace Erdos5EfficientCover

/-- Primes above the fixed small cutoff and below the reserve boundary. -/
def mediumPrimes (P y T : ℕ) : Finset ℕ := primesUpTo (y / T) \ primesUpTo P

@[simp] theorem mem_mediumPrimes {p P y T : ℕ} :
    p ∈ mediumPrimes P y T ↔ p.Prime ∧ P < p ∧ p ≤ y / T := by
  simp only [mediumPrimes, Finset.mem_sdiff, mem_primesUpTo]
  constructor
  · rintro ⟨⟨hpp, hpd⟩, hn⟩
    exact ⟨hpp, lt_of_not_ge (fun h => hn ⟨hpp, h⟩), hpd⟩
  · rintro ⟨hpp, hPp, hpd⟩
    exact ⟨⟨hpp, hpd⟩, fun h => (not_le_of_gt hPp) h.2⟩

/-- The interval points left when every medium prime is assigned class zero. -/
noncomputable def mediumSurvivors (c y P T : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (c * y)).filter (fun n => ∀ p ∈ mediumPrimes P y T, ¬ p ∣ n)

@[simp] theorem mem_mediumSurvivors {n c y P T : ℕ} :
    n ∈ mediumSurvivors c y P T ↔
      (1 ≤ n ∧ n ≤ c * y) ∧ ∀ p ∈ mediumPrimes P y T, ¬ p ∣ n := by
  classical
  simp [mediumSurvivors]

/-- A non-smooth survivor has a prime factor in the large range, and a bounded cofactor. -/
theorem survivor_smooth_or_large_factor (c y P T n : ℕ) (hT : 0 < T)
    (hn : n ∈ mediumSurvivors c y P T) :
    n ∈ Nat.smoothNumbersUpTo (c * y) (P + 1) ∨
      ∃ a p : ℕ, 1 ≤ a ∧ a ≤ c * T ∧ p ∈ primesUpTo (c * y) ∧ n = a * p := by
  have hn' := mem_mediumSurvivors.mp hn
  have hnpos : 0 < n := by omega
  by_cases hs : n ∈ Nat.smoothNumbers (P + 1)
  · exact Or.inl (Nat.mem_smoothNumbersUpTo.mpr ⟨hn'.1.2, hs⟩)
  · rw [Nat.mem_smoothNumbers'] at hs
    push_neg at hs
    obtain ⟨p, hprime, hpdvd, hpP⟩ := hs
    have hpgt : P < p := by omega
    have hpbig : y / T < p := by
      by_contra h
      exact hn'.2 p (mem_mediumPrimes.mpr ⟨hprime, hpgt, le_of_not_gt h⟩) hpdvd
    have hpbound : p ≤ c * y := (Nat.le_of_dvd hnpos hpdvd).trans hn'.1.2
    obtain ⟨a, ha⟩ := hpdvd
    have heq : n = a * p := by simpa only [Nat.mul_comm] using ha
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, zero_mul] at heq
      omega
    have hyp : y < p * T := (Nat.div_lt_iff_lt_mul hT).mp hpbig
    have hamul : a * p ≤ (c * T) * p := by
      calc
        a * p = n := heq.symm
        _ ≤ c * y := hn'.1.2
        _ ≤ c * (p * T) := Nat.mul_le_mul_left c hyp.le
        _ = (c * T) * p := by ring
    have habound : a ≤ c * T := Nat.le_of_mul_le_mul_right hamul hprime.pos
    exact Or.inr ⟨a, p, Nat.one_le_iff_ne_zero.mpr ha0, habound,
      mem_primesUpTo.mpr ⟨hprime, hpbound⟩, heq⟩

/-- All products of a bounded cofactor with a prime at most `c*y`. -/
def largeMultiples (c y T : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 (c * T)).product (primesUpTo (c * y))).image (fun ap => ap.1 * ap.2)

theorem largeMultiples_card_le (c y T : ℕ) :
    (largeMultiples c y T).card ≤ (c * T) * Nat.primeCounting (c * y) := by
  unfold largeMultiples
  calc
    (((Finset.Icc 1 (c * T)).product (primesUpTo (c * y))).image
        (fun ap => ap.1 * ap.2)).card ≤
      ((Finset.Icc 1 (c * T)).product (primesUpTo (c * y))).card := Finset.card_image_le
    _ = (c * T) * Nat.primeCounting (c * y) := by
      simp [Finset.card_product, Nat.card_Icc]

/-- The full natural-number bound on the first sieve's survivors. -/
theorem mediumSurvivors_card_le (c y P T : ℕ) (hT : 0 < T) :
    (mediumSurvivors c y P T).card ≤
      2 ^ (Nat.primesBelow (P + 1)).card * Nat.sqrt (c * y) +
        (c * T) * Nat.primeCounting (c * y) := by
  have hsub : mediumSurvivors c y P T ⊆
      Nat.smoothNumbersUpTo (c * y) (P + 1) ∪ largeMultiples c y T := by
    intro n hn
    rcases survivor_smooth_or_large_factor c y P T n hT hn with hs | ⟨a, p, ha1, haN, hp, heq⟩
    · exact Finset.mem_union_left _ hs
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(a, p),
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨ha1, haN⟩, hp⟩, heq.symm⟩
  calc
    (mediumSurvivors c y P T).card ≤
        (Nat.smoothNumbersUpTo (c * y) (P + 1) ∪ largeMultiples c y T).card :=
      Finset.card_le_card hsub
    _ ≤ (Nat.smoothNumbersUpTo (c * y) (P + 1)).card + (largeMultiples c y T).card :=
      Finset.card_union_le _ _
    _ ≤ 2 ^ (Nat.primesBelow (P + 1)).card * Nat.sqrt (c * y) +
        (c * T) * Nat.primeCounting (c * y) :=
      Nat.add_le_add (Nat.smoothNumbersUpTo_card_le (c * y) (P + 1)) (largeMultiples_card_le c y T)

/-- A survivor-count constant independent of the later choice of `P`. -/
noncomputable def survivorConst (c T : ℕ) : ℝ := 1 + (c * T : ℕ) * upperConst * (c : ℝ)

theorem survivorConst_pos (c T : ℕ) : 0 < survivorConst c T := by
  unfold survivorConst
  have h : 0 ≤ (c * T : ℕ) * upperConst * (c : ℝ) := by positivity [upperConst_pos]
  linarith

/-- For fixed `c,T,P`, the medium-prime survivors have size at most `C_c*y/log y`. -/
theorem eventually_mediumSurvivors_le (c T P : ℕ) (hc : 1 ≤ c) (hT : 0 < T) :
    ∀ᶠ y : ℕ in atTop,
      ((mediumSurvivors c y P T).card : ℝ) ≤ survivorConst c T * y / Real.log (y : ℝ) := by
  filter_upwards [eventually_sqrt_term_le c (2 ^ (Nat.primesBelow (P + 1)).card) hc,
    eventually_primeCounting_mul_upper c hc] with y hsqrt hprimes
  have hcard : ((mediumSurvivors c y P T).card : ℝ) ≤
      (2 ^ (Nat.primesBelow (P + 1)).card : ℕ) * (Nat.sqrt (c * y) : ℝ) +
        (c * T : ℕ) * (Nat.primeCounting (c * y) : ℝ) := by
    exact_mod_cast mediumSurvivors_card_le c y P T hT
  calc
    ((mediumSurvivors c y P T).card : ℝ) ≤
        (2 ^ (Nat.primesBelow (P + 1)).card : ℕ) * (Nat.sqrt (c * y) : ℝ) +
          (c * T : ℕ) * (Nat.primeCounting (c * y) : ℝ) := hcard
    _ ≤ (y : ℝ) / Real.log (y : ℝ) +
        (c * T : ℕ) * (upperConst * c * y / Real.log (y : ℝ)) :=
      add_le_add hsqrt (mul_le_mul_of_nonneg_left hprimes (Nat.cast_nonneg _))
    _ = survivorConst c T * y / Real.log (y : ℝ) := by unfold survivorConst; ring

end Erdos5EfficientCover

#print axioms Erdos5EfficientCover.survivor_smooth_or_large_factor
#print axioms Erdos5EfficientCover.mediumSurvivors_card_le
#print axioms Erdos5EfficientCover.eventually_mediumSurvivors_le
