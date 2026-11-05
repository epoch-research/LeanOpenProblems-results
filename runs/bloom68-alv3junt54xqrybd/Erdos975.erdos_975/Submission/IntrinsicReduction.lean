import Submission.ConjectureReduction

/-!
# An intrinsic, monotone version of the remaining balanced-divisor mean

Using each input as its own divisor cutoff removes exactly the root-count
summatory function from the common-cutoff small-divisor sum. This is an exact
finite identity, not an equidistribution assumption. The resulting central
summatory function is monotone. Its normalized convergence is still required;
this module does not assert the original conjecture.
-/

namespace Erdos975Support

open Filter Polynomial
open scoped Topology

/-- Small divisors with cutoff equal to the input, rather than the endpoint. -/
noncomputable def intrinsicSmallAlong (g : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Iic N, (smallDivisorCount (g n) n : ℝ)

/-- The nonnegative intrinsic central summatory function. -/
noncomputable def intrinsicBalancedAlong (g : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Iic N, (balancedDivisorCount (g n) n : ℝ)

/-- The overlap at the intrinsic cutoff. -/
noncomputable def intrinsicOverlapAlong (g : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Iic N, (overlapDivisorCount (g n) n : ℝ)

lemma intrinsicBalancedAlong_nonneg (g : ℕ → ℕ) (N : ℕ) :
    0 ≤ intrinsicBalancedAlong g N :=
  Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

lemma intrinsicBalancedAlong_monotone (g : ℕ → ℕ) :
    Monotone (intrinsicBalancedAlong g) := by
  intro M N hMN
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Iic_subset_Iic.mpr hMN
  · intro n _ _
    exact Nat.cast_nonneg _

lemma intrinsic_along_pairing (g : ℕ → ℕ) (N : ℕ) :
    divisorAlong g N + intrinsicOverlapAlong g N =
      2 * intrinsicSmallAlong g N + intrinsicBalancedAlong g N := by
  unfold divisorAlong intrinsicOverlapAlong intrinsicSmallAlong intrinsicBalancedAlong
  rw [← Finset.sum_add_distrib]
  calc
    (∑ n ∈ Finset.Iic N,
      ((ArithmeticFunction.sigma 0 (g n) : ℝ) +
        (overlapDivisorCount (g n) n : ℝ))) =
      ∑ n ∈ Finset.Iic N,
        (2 * (smallDivisorCount (g n) n : ℝ) +
          (balancedDivisorCount (g n) n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n _
      exact_mod_cast sigma_zero_pairing_with_overlap (g n) n
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The input-cutoff correction is exactly the number of first residue roots.
No residue-invariance hypothesis is needed for this finite identity. -/
theorem smallAlong_eq_intrinsic_add_rootCountSummatory {g : ℕ → ℕ}
    (hg : ∀ n : ℕ, 0 < g n) (N : ℕ) :
    smallAlong g N = intrinsicSmallAlong g N + rootCountSummatory g N := by
  classical
  have hexpand (n K : ℕ) :
      (smallDivisorCount (g n) K : ℝ) =
        ∑ q ∈ Finset.Ioc 0 K, if q ∣ g n then (1 : ℝ) else 0 := by
    rw [smallDivisorCount_eq_root_filter (hg n), Finset.sum_boole]
  have hsmall (n : ℕ) (hn : n ≤ N) :
      (smallDivisorCount (g n) n : ℝ) =
        ∑ q ∈ Finset.Ioc 0 N, if q ≤ n ∧ q ∣ g n then (1 : ℝ) else 0 := by
    rw [hexpand]
    calc
      (∑ q ∈ Finset.Ioc 0 n, if q ∣ g n then (1 : ℝ) else 0) =
          ∑ q ∈ Finset.Ioc 0 n, if q ≤ n ∧ q ∣ g n then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        simp only [(Finset.mem_Ioc.mp hq).2, true_and]
      _ = _ := by
        apply Finset.sum_subset
        · intro q hq
          obtain ⟨hq0, hqn⟩ := Finset.mem_Ioc.mp hq
          exact Finset.mem_Ioc.mpr ⟨hq0, hqn.trans hn⟩
        · intro q hq hnot
          have hqn : ¬q ≤ n := by
            intro hqn
            exact hnot (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hq).1, hqn⟩)
          simp only [hqn, false_and, ↓reduceIte]
  have hroots (q : ℕ) (hq : q ≤ N) :
      (rootCount g q : ℝ) =
        ∑ n ∈ Finset.Iic N, if n < q ∧ q ∣ g n then (1 : ℝ) else 0 := by
    unfold rootCount
    rw [← Finset.sum_boole]
    calc
      (∑ n ∈ Finset.range q, if q ∣ g n then (1 : ℝ) else 0) =
          ∑ n ∈ Finset.range q, if n < q ∧ q ∣ g n then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [Finset.mem_range.mp hn, true_and]
      _ = _ := by
        apply Finset.sum_subset
        · intro n hn
          exact Finset.mem_Iic.mpr ((Finset.mem_range.mp hn).le.trans hq)
        · intro n _ hn
          have hnq : ¬n < q := by simpa only [Finset.mem_range] using hn
          simp only [hnq, false_and, ↓reduceIte]
  unfold smallAlong intrinsicSmallAlong rootCountSummatory
  rw [show (∑ n ∈ Finset.Iic N, (smallDivisorCount (g n) N : ℝ)) =
      ∑ n ∈ Finset.Iic N, ∑ q ∈ Finset.Ioc 0 N,
        if q ∣ g n then (1 : ℝ) else 0 from
      Finset.sum_congr rfl fun n _ ↦ hexpand n N]
  rw [show (∑ n ∈ Finset.Iic N, (smallDivisorCount (g n) n : ℝ)) =
      ∑ n ∈ Finset.Iic N, ∑ q ∈ Finset.Ioc 0 N,
        if q ≤ n ∧ q ∣ g n then (1 : ℝ) else 0 from
      Finset.sum_congr rfl fun n hn ↦ hsmall n (Finset.mem_Iic.mp hn)]
  rw [show (∑ q ∈ Finset.Ioc 0 N, (rootCount g q : ℝ)) =
      ∑ q ∈ Finset.Ioc 0 N, ∑ n ∈ Finset.Iic N,
        if n < q ∧ q ∣ g n then (1 : ℝ) else 0 from
      Finset.sum_congr rfl fun q hq ↦ hroots q (Finset.mem_Ioc.mp hq).2]
  conv_rhs =>
    rhs
    rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hd : q ∣ g n
  · by_cases hqn : q ≤ n
    · simp [hd, hqn, Nat.not_lt.mpr hqn]
    · simp [hd, hqn, Nat.lt_of_not_ge hqn]
  · simp [hd]

lemma intrinsicOverlapAlong_nonneg (g : ℕ → ℕ) (N : ℕ) :
    0 ≤ intrinsicOverlapAlong g N :=
  Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

lemma intrinsicOverlapAlong_le_overlapAlong (g : ℕ → ℕ) (N : ℕ) :
    intrinsicOverlapAlong g N ≤ overlapAlong g N := by
  apply Finset.sum_le_sum
  intro n hn
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro a ha
  obtain ⟨ha, han, hcomp⟩ := Finset.mem_filter.mp ha
  have hnN : n ≤ N := Finset.mem_Iic.mp hn
  exact Finset.mem_filter.mpr ⟨ha, han.trans hnN, hcomp.trans hnN⟩

/-- Exact comparison of the two central counts. -/
theorem intrinsicBalancedAlong_eq_common {g : ℕ → ℕ}
    (hg : ∀ n : ℕ, 0 < g n) (N : ℕ) :
    intrinsicBalancedAlong g N = balancedAlong g N +
      2 * rootCountSummatory g N + intrinsicOverlapAlong g N - overlapAlong g N := by
  have h1 := along_pairing g N
  have h2 := intrinsic_along_pairing g N
  have h3 := smallAlong_eq_intrinsic_add_rootCountSummatory hg N
  linarith

/-- The difference between the monotone central sum and the common-cutoff
central sum has the lower-order linear mean `2 * κ`. -/
theorem intrinsicBalancedAlong_sub_common_div_nat_limit {g : ℕ → ℕ} {κ : ℝ}
    (hg : ∀ n : ℕ, 0 < g n)
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ)) atTop (𝓝 κ))
    (ho : Tendsto (fun N : ℕ ↦ overlapAlong g N / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦
      (intrinsicBalancedAlong g N - balancedAlong g N) / (N : ℝ))
      atTop (𝓝 (2 * κ)) := by
  have hio : Tendsto (fun N : ℕ ↦ intrinsicOverlapAlong g N / (N : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N ↦
      div_nonneg (intrinsicOverlapAlong_nonneg g N) (Nat.cast_nonneg N))
      (Eventually.of_forall fun N ↦
        div_le_div_of_nonneg_right (intrinsicOverlapAlong_le_overlapAlong g N)
          (Nat.cast_nonneg N)) ho
  have ht := ((hP.const_mul 2).add hio).sub ho
  simp only [add_zero, sub_zero] at ht
  apply ht.congr
  intro N
  rw [intrinsicBalancedAlong_eq_common hg N]
  ring

/-- Intrinsic and common central sums have the same logarithmically
normalized limits. This does not assert that either limit exists. -/
theorem intrinsicBalancedAlong_limit_iff {g : ℕ → ℕ} {κ L : ℝ}
    (hg : ∀ n : ℕ, 0 < g n)
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ)) atTop (𝓝 κ))
    (ho : Tendsto (fun N : ℕ ↦ overlapAlong g N / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ intrinsicBalancedAlong g N /
      ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 L) ↔
    Tendsto (fun N : ℕ ↦ balancedAlong g N /
      ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 L) := by
  have hd : Tendsto (fun N : ℕ ↦
      (intrinsicBalancedAlong g N - balancedAlong g N) /
        ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 0) := by
    simpa only [div_div] using
      (intrinsicBalancedAlong_sub_common_div_nat_limit hg hP ho).div_atTop
        tendsto_log_nat_atTop
  constructor
  · intro hi
    have ht := hi.sub hd
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    ring
  · intro hc
    have ht := hc.add hd
    simp only [add_zero] at ht
    apply ht.congr
    intro N
    ring

/-- For a high-degree admissible polynomial, the original asymptotic exists
exactly when the monotone intrinsic central sum has a finite normalized mean. -/
theorem high_degree_divisor_average_iff_intrinsic_limit
    (f : ℤ[X]) (hf : Irreducible f) (hdeg : 3 ≤ f.natDegree)
    (hpos : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    (∃ c > (0 : ℝ), Tendsto
      (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x)) atTop (𝓝 c)) ↔
    ∃ L : ℝ, Tendsto
      (fun N : ℕ ↦ intrinsicBalancedAlong (polynomialAbsValue f) N /
        ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 L) := by
  rw [high_degree_divisor_average_iff_balanced_limit f hf hdeg hpos]
  obtain ⟨κ, _, hP⟩ := exists_pos_rootMean_of_irreducible f hf (by omega)
  have hg := polynomialAbsValue_pos f hf (by omega)
  have ho := tendsto_polynomial_overlapAlong_div_nat f hdeg
  exact exists_congr fun L ↦ (intrinsicBalancedAlong_limit_iff hg hP ho).symm

/-- The intrinsic small-divisor average has the same unconditional mean as
its common-cutoff counterpart. -/
theorem tendsto_intrinsicSmallAlong_of_linear_rootCount {g : ℕ → ℕ} {κ : ℝ}
    (hg : ∀ n : ℕ, 0 < g n)
    (hmod : ∀ q : ℕ, 0 < q → ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q))
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ)) atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ ↦ intrinsicSmallAlong g N /
      ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 κ) := by
  have hs := tendsto_smallAlong_of_linear_rootCount hg hmod hP
  have hp : Tendsto (fun N : ℕ ↦ rootCountSummatory g N /
      ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 0) := by
    simpa only [div_div] using hP.div_atTop tendsto_log_nat_atTop
  have ht := hs.sub hp
  simp only [sub_zero] at ht
  apply ht.congr
  intro N
  rw [smallAlong_eq_intrinsic_add_rootCountSummatory hg N]
  ring

/-- Exact universal reformulation using the nonnegative monotone central
summatory function. Neither side is asserted unconditionally. -/
theorem universal_divisor_average_iff_high_degree_intrinsic_limits :
    (∀ f : ℤ[X], f.natDegree ≠ 0 → Irreducible f →
      (∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) →
      ∃ c > (0 : ℝ), Tendsto
        (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x)) atTop (𝓝 c)) ↔
    (∀ f : ℤ[X], 3 ≤ f.natDegree → Irreducible f →
      (∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) →
      ∃ L : ℝ, Tendsto
        (fun N : ℕ ↦ intrinsicBalancedAlong (polynomialAbsValue f) N /
          ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 L)) := by
  constructor
  · intro h f hdeg hf hpos
    exact (high_degree_divisor_average_iff_intrinsic_limit f hf hdeg hpos).mp
      (h f (by omega) hf hpos)
  · intro h f hdeg hf hpos
    by_cases hsmall : f.natDegree ≤ 2
    · exact erdos_975_of_natDegree_le_two f hdeg hf hpos hsmall
    · have hlarge : 3 ≤ f.natDegree := by omega
      exact (high_degree_divisor_average_iff_intrinsic_limit f hf hlarge hpos).mpr
        (h f hlarge hf hpos)

/-- A strictly positive leading lower bound holds unconditionally in every
irreducible high-degree case, even though leading convergence is unresolved. -/
theorem high_degree_eventual_positive_divisor_lower_bound
    (f : ℤ[X]) (hf : Irreducible f) (hdeg : 3 ≤ f.natDegree) :
    ∃ κ > (0 : ℝ),
      Tendsto (fun N : ℕ ↦ rootCountSummatory (polynomialAbsValue f) N / (N : ℝ))
        atTop (𝓝 κ) ∧
      ∀ᶠ N : ℕ in atTop, κ < divisorAlong (polynomialAbsValue f) N /
        ((N : ℝ) * Real.log (N : ℝ)) := by
  obtain ⟨κ, hκ, hP⟩ := exists_pos_rootMean_of_irreducible f hf (by omega)
  refine ⟨κ, hκ, hP, ?_⟩
  have hs := tendsto_smallAlong_of_linear_rootCount
    (polynomialAbsValue_pos f hf (by omega)) (polynomialAbsValue_mod_dvd f) hP
  have ho := tendsto_polynomial_overlapAlong_div_mul_log f hdeg
  have ht := (hs.const_mul 2).sub ho
  simp only [sub_zero] at ht
  have hb := ht.eventually_const_lt (show κ < 2 * κ by linarith)
  filter_upwards [hb, eventually_ge_atTop 2] with N hbN hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hcentral : 0 ≤ balancedAlong (polynomialAbsValue f) N /
      ((N : ℝ) * Real.log (N : ℝ)) :=
    div_nonneg (balancedAlong_nonneg _ _)
      (mul_nonneg (Nat.cast_nonneg N) (Real.log_pos hN1).le)
  rw [normalized_along_pairing]
  linarith

/-- The positive lower bound also holds for the exact real-cutoff floor sum.
It is only a lower bound, not convergence to a constant. -/
theorem high_degree_original_eventual_positive_lower_bound
    (f : ℤ[X]) (hf : Irreducible f) (hdeg : 3 ≤ f.natDegree)
    (hpos : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    ∃ c > (0 : ℝ), ∀ᶠ x : ℝ in atTop,
      c < flooredPolynomialSum f x / (x * Real.log x) := by
  obtain ⟨κ, hκ, _, hn⟩ := high_degree_eventual_positive_divisor_lower_bound f hf hdeg
  have hr := tendsto_floor_mul_log_div.eventually_const_lt
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have he := (floor_abs_difference_vanishes f hpos).eventually_const_lt
    (show -(κ / 4) < (0 : ℝ) by linarith)
  refine ⟨κ / 4, by positivity, ?_⟩
  filter_upwards [tendsto_nat_floor_atTop.eventually hn, hr, he,
    tendsto_nat_floor_atTop.eventually (eventually_ge_atTop 2)] with x hn hr he hx
  let a := divisorAlong (polynomialAbsValue f) (Nat.floor x) /
    ((Nat.floor x : ℝ) * Real.log (Nat.floor x : ℝ))
  let r := ((Nat.floor x : ℝ) * Real.log (Nat.floor x : ℝ)) / (x * Real.log x)
  have hN1 : (1 : ℝ) < (Nat.floor x : ℝ) := by
    exact_mod_cast (show 1 < Nat.floor x by omega)
  have hNz : (Nat.floor x : ℝ) * Real.log (Nat.floor x : ℝ) ≠ 0 :=
    mul_ne_zero (ne_of_gt (zero_lt_one.trans hN1)) (ne_of_gt (Real.log_pos hN1))
  have hEq : a * r = absPolynomialSum f x / (x * Real.log x) := by
    dsimp [a, r, absPolynomialSum]
    exact div_mul_div_cancel₀ hNz
  have hlow : κ / 2 < a * r := by
    calc
      κ / 2 = κ * (1 / 2 : ℝ) := by ring
      _ < κ * r := mul_lt_mul_of_pos_left hr hκ
      _ < a * r := mul_lt_mul_of_pos_right hn (lt_trans (by norm_num) hr)
  rw [hEq] at hlow
  have hsum : flooredPolynomialSum f x / (x * Real.log x) =
      absPolynomialSum f x / (x * Real.log x) +
        (flooredPolynomialSum f x - absPolynomialSum f x) / (x * Real.log x) := by
    ring
  linarith

/-- The strictly positive leading lower bound is established for every
polynomial in the original conjecture, without asserting a leading limit. -/
theorem universal_original_eventual_positive_lower_bound :
    ∀ f : ℤ[X], f.natDegree ≠ 0 → Irreducible f →
      (∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) →
      ∃ c > (0 : ℝ), ∀ᶠ x : ℝ in atTop,
        c < flooredPolynomialSum f x / (x * Real.log x) := by
  intro f hnonconstant hf hpos
  by_cases hsmall : f.natDegree ≤ 2
  · obtain ⟨c, hc, ht⟩ := erdos_975_of_natDegree_le_two f hnonconstant hf hpos hsmall
    exact ⟨c / 2, by positivity,
      ht.eventually_const_lt (show c / 2 < c by linarith)⟩
  · exact high_degree_original_eventual_positive_lower_bound f hf (by omega) hpos

/-- Positivity of any finite leading limit follows from the proved lower
bound. The only remaining issue is finite convergence itself. -/
theorem original_positive_limit_iff_finite_limit
    (f : ℤ[X]) (hdeg : f.natDegree ≠ 0) (hf : Irreducible f)
    (hpos : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    (∃ c > (0 : ℝ), Tendsto
      (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x)) atTop (𝓝 c)) ↔
    ∃ c : ℝ, Tendsto
      (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x)) atTop (𝓝 c) := by
  constructor
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    obtain ⟨a, ha, hea⟩ := universal_original_eventual_positive_lower_bound f hdeg hf hpos
    have hac : a ≤ c := ge_of_tendsto hc (hea.mono fun _ hx ↦ hx.le)
    exact ⟨c, ha.trans_le hac, hc⟩

/-- The exact negation reduces to one genuine high-degree polynomial whose
intrinsic central mean has no finite limit. This equivalence does not assert
existence of such a polynomial. -/
theorem not_universal_divisor_average_iff_intrinsic_counterexample :
    (¬ (∀ f : ℤ[X], f.natDegree ≠ 0 → Irreducible f →
      (∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) →
      ∃ c > (0 : ℝ), Tendsto
        (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x)) atTop (𝓝 c))) ↔
    ∃ f : ℤ[X], 3 ≤ f.natDegree ∧ Irreducible f ∧
      (∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) ∧
      ∀ L : ℝ, ¬ Tendsto
        (fun N : ℕ ↦ intrinsicBalancedAlong (polynomialAbsValue f) N /
          ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 L) := by
  classical
  simpa only [not_forall, not_exists, exists_prop] using
    (not_congr universal_divisor_average_iff_high_degree_intrinsic_limits)

end Erdos975Support
