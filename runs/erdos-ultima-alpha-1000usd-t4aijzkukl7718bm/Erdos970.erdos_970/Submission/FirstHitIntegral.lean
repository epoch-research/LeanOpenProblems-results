import Submission.NormalizerPrefix

/-! A rationally certified integral for a first-hit normalizer profile.
This file supplies no unconditional bound for Jacobsthal's function. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def firstHitProfile (u : ℝ) : ℝ := 2 * u - 1 - u * log u
noncomputable def firstHitReciprocal (u : ℝ) : ℝ := 1 / firstHitProfile u

lemma firstHitProfile_concave : ConcaveOn ℝ (Set.Icc 1 3) firstHitProfile := by
  refine ⟨convex_Icc 1 3, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := convexOn_mul_log.2 (show 0 ≤ x by linarith [hx.1])
    (show 0 ≤ y by linarith [hy.1]) ha hb hab
  simp only [smul_eq_mul, firstHitProfile] at hh ⊢
  nlinarith only [hh, hab]

lemma firstHitProfile_pos (u : ℝ) (hu : u ∈ Set.Icc 1 3) : 0 < firstHitProfile u := by
  have hu0 : 0 < u := by linarith [hu.1]
  by_cases hu2 : u ≤ 2
  · have hlu : log u < 1 := (log_le_log hu0 hu2).trans_lt (by linarith [log_two_lt_d9])
    have hh := mul_lt_mul_of_pos_left hlu hu0
    unfold firstHitProfile
    nlinarith [hu.1]
  · have hl3 : log (3 : ℝ) < 3 / 2 := by
      have hh := log_le_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 2 ^ 2)
      rw [log_pow] at hh
      norm_num only [Nat.cast_ofNat] at hh
      linarith [log_two_lt_d9]
    have hlu := (log_le_log hu0 hu.2).trans_lt hl3
    have hh := mul_lt_mul_of_pos_left hlu hu0
    unfold firstHitProfile
    nlinarith

lemma firstHitReciprocal_convex : ConvexOn ℝ (Set.Icc 1 3) firstHitReciprocal := by
  have hi : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => 1 / x) := by
    simpa only [zpow_neg_one, one_div] using
      (strictConvexOn_zpow (m := (-1 : ℤ)) (by norm_num) (by norm_num)).convexOn
  refine ⟨convex_Icc 1 3, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 := firstHitProfile_pos x hx
  have hy0 := firstHitProfile_pos y hy
  have hq : 0 < a * firstHitProfile x + b * firstHitProfile y := by
    exact (convex_Ioi (0 : ℝ)) hx0 hy0 ha hb hab
  have hh := firstHitProfile_concave.2 hx hy ha hb hab
  have hh' := one_div_le_one_div_of_le hq hh
  exact hh'.trans (hi.2 hx0 hy0 ha hb hab)

lemma firstHitReciprocal_continuous : ContinuousOn firstHitReciprocal (Set.Icc 1 3) := by
  apply ContinuousOn.div continuousOn_const
  · unfold firstHitProfile
    apply ContinuousOn.sub (by fun_prop)
    exact continuousOn_id.mul (continuousOn_log.mono (fun u hu => by
      change u ≠ 0
      linarith [hu.1]))
  · intro u hu
    exact (firstHitProfile_pos u hu).ne'

/-- The trapezoidal upper bound, proved by integrating the defining chord
inequality for convexity. -/
lemma convex_integral_le_chord {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hc : ContinuousOn f (Set.Icc a b)) :
    (∫ x in a..b, f x) ≤ (b - a) / 2 * (f a + f b) := by
  let L : ℝ → ℝ := fun x => (b - x) / (b - a) * f a + (x - a) / (b - a) * f b
  have hd : 0 < b - a := sub_pos.mpr hab
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) : f x ≤ L x := by
    have h1 : 0 ≤ (b - x) / (b - a) := div_nonneg (sub_nonneg.mpr hx.2) hd.le
    have h2 : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hx.1) hd.le
    have hs : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by field_simp; ring
    have he : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by field_simp; ring
    have hh := hf.2 (show a ∈ Set.Icc a b from ⟨le_rfl, hab.le⟩)
      (show b ∈ Set.Icc a b from ⟨hab.le, le_rfl⟩) h1 h2 hs
    simpa only [smul_eq_mul, he] using hh
  have hfi : IntervalIntegrable f MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab.le]
  have hLi : IntervalIntegrable L MeasureTheory.volume a b :=
    (show Continuous L by dsimp [L]; fun_prop).intervalIntegrable _ _
  have hh := intervalIntegral.integral_mono_on hab.le hfi hLi hbound
  have hL : (∫ x in a..b, L x) = (b - a) / 2 * (f a + f b) := by
    have he : L = fun x => (b * f a - a * f b) / (b - a) +
        ((f b - f a) / (b - a)) * x := by
      funext x
      dsimp [L]
      ring
    rw [he, intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    simp only [smul_eq_mul]
    field_simp
    ring
  rwa [hL] at hh

private lemma firstHitReciprocal_upper_of_log (u c L : ℝ)
    (hu : u ∈ Set.Icc 1 3) (hc : 0 ≤ c) (hl : log u ≤ L)
    (hb : 1 ≤ c * (2 * u - 1 - u * L)) : firstHitReciprocal u ≤ c := by
  unfold firstHitReciprocal
  apply (div_le_iff₀ (firstHitProfile_pos u hu)).mpr
  have hh := mul_le_mul_of_nonneg_left hl
    (mul_nonneg hc (show 0 ≤ u by linarith [hu.1]))
  unfold firstHitProfile
  nlinarith only [hh, hb]

private lemma firstHitReciprocal_grid_0 : firstHitReciprocal (1 : ℝ) ≤ 1 := by
  norm_num [firstHitReciprocal, firstHitProfile]

private lemma firstHitReciprocal_grid_1 : firstHitReciprocal ((11 / 10) : ℝ) ≤ (913111 / 1000000) := by
  have hh := sum_range_sub_log_div_le (x := ((1 / 21) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((11 / 10) : ℝ) ≤ (95311 / 1000000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_2 : firstHitReciprocal ((6 / 5) : ℝ) ≤ (846587 / 1000000) := by
  have hh := sum_range_sub_log_div_le (x := ((1 / 11) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((6 / 5) : ℝ) ≤ (91161 / 500000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_3 : firstHitReciprocal ((13 / 10) : ℝ) ≤ (794329 / 1000000) := by
  have hh := sum_range_sub_log_div_le (x := ((3 / 23) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((13 / 10) : ℝ) ≤ (52473 / 200000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_4 : firstHitReciprocal ((7 / 5) : ℝ) ≤ (752481 / 1000000) := by
  have hh := sum_range_sub_log_div_le (x := ((1 / 6) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((7 / 5) : ℝ) ≤ (336473 / 1000000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_5 : firstHitReciprocal ((3 / 2) : ℝ) ≤ (359247 / 500000) := by
  have hh := sum_range_sub_log_div_le (x := ((1 / 5) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((3 / 2) : ℝ) ≤ (202733 / 500000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_6 : firstHitReciprocal ((8 / 5) : ℝ) ≤ (690611 / 1000000) := by
  have hh := sum_range_sub_log_div_le (x := ((3 / 13) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((8 / 5) : ℝ) ≤ (117501 / 250000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_7 : firstHitReciprocal ((17 / 10) : ℝ) ≤ (166897 / 250000) := by
  have hh := sum_range_sub_log_div_le (x := ((7 / 27) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((17 / 10) : ℝ) ≤ (530629 / 1000000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_8 : firstHitReciprocal ((9 / 5) : ℝ) ≤ (162129 / 250000) := by
  have hh := sum_range_sub_log_div_le (x := ((2 / 7) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((9 / 5) : ℝ) ≤ (587787 / 1000000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_9 : firstHitReciprocal ((19 / 10) : ℝ) ≤ (632721 / 1000000) := by
  have hh := sum_range_sub_log_div_le (x := ((9 / 29) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((19 / 10) : ℝ) ≤ (320927 / 500000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_10 : firstHitReciprocal (2 : ℝ) ≤ (619693 / 1000000) := by
  have hh := sum_range_sub_log_div_le (x := ((1 / 3) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log (2 : ℝ) ≤ (173287 / 250000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_11 : firstHitReciprocal ((21 / 10) : ℝ) ≤ (7613 / 12500) := by
  have hh := sum_range_sub_log_div_le (x := ((11 / 31) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((21 / 10) : ℝ) ≤ (370969 / 500000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_12 : firstHitReciprocal ((11 / 5) : ℝ) ≤ (30023 / 50000) := by
  have hh := sum_range_sub_log_div_le (x := ((3 / 8) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((11 / 5) : ℝ) ≤ (394229 / 500000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_13 : firstHitReciprocal ((23 / 10) : ℝ) ≤ (148429 / 250000) := by
  have hh := sum_range_sub_log_div_le (x := ((13 / 33) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((23 / 10) : ℝ) ≤ (83291 / 100000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_14 : firstHitReciprocal ((12 / 5) : ℝ) ≤ (294313 / 500000) := by
  have hh := sum_range_sub_log_div_le (x := ((7 / 17) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((12 / 5) : ℝ) ≤ (875469 / 1000000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_15 : firstHitReciprocal ((5 / 2) : ℝ) ≤ (117009 / 200000) := by
  have hh := sum_range_sub_log_div_le (x := ((3 / 7) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((5 / 2) : ℝ) ≤ (916291 / 1000000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_16 : firstHitReciprocal ((13 / 5) : ℝ) ≤ (36429 / 62500) := by
  have hh := sum_range_sub_log_div_le (x := ((4 / 9) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((13 / 5) : ℝ) ≤ (119439 / 125000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_17 : firstHitReciprocal ((27 / 10) : ℝ) ≤ (290999 / 500000) := by
  have hh := sum_range_sub_log_div_le (x := ((17 / 37) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((27 / 10) : ℝ) ≤ (248313 / 250000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_18 : firstHitReciprocal ((14 / 5) : ℝ) ≤ (58239 / 100000) := by
  have hh := sum_range_sub_log_div_le (x := ((9 / 19) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((14 / 5) : ℝ) ≤ (51481 / 50000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_19 : firstHitReciprocal ((29 / 10) : ℝ) ≤ (583997 / 1000000) := by
  have hh := sum_range_sub_log_div_le (x := ((19 / 39) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log ((29 / 10) : ℝ) ≤ (1064711 / 1000000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

private lemma firstHitReciprocal_grid_20 : firstHitReciprocal (3 : ℝ) ≤ (1467 / 2500) := by
  have hh := sum_range_sub_log_div_le (x := ((1 / 2) : ℝ)) (by norm_num) 12
  norm_num [sum_range_succ] at hh
  have hl : log (3 : ℝ) ≤ (1098613 / 1000000) := by
    linarith only [(abs_le.mp hh).2]
  exact firstHitReciprocal_upper_of_log _ _ _ (by norm_num) (by norm_num) hl (by norm_num)

noncomputable def firstHitGridUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => 1
  | 1 => (913111 / 1000000)
  | 2 => (846587 / 1000000)
  | 3 => (794329 / 1000000)
  | 4 => (752481 / 1000000)
  | 5 => (359247 / 500000)
  | 6 => (690611 / 1000000)
  | 7 => (166897 / 250000)
  | 8 => (162129 / 250000)
  | 9 => (632721 / 1000000)
  | 10 => (619693 / 1000000)
  | 11 => (7613 / 12500)
  | 12 => (30023 / 50000)
  | 13 => (148429 / 250000)
  | 14 => (294313 / 500000)
  | 15 => (117009 / 200000)
  | 16 => (36429 / 62500)
  | 17 => (290999 / 500000)
  | 18 => (58239 / 100000)
  | 19 => (583997 / 1000000)
  | 20 => (1467 / 2500)
  | _ => 0

lemma firstHitReciprocal_grid_bound (j : ℕ) (hj : j < 21) :
    firstHitReciprocal (1 + (j : ℝ) / 10) ≤ firstHitGridUpper j := by
  interval_cases j
  · convert firstHitReciprocal_grid_0 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_1 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_2 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_3 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_4 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_5 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_6 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_7 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_8 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_9 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_10 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_11 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_12 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_13 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_14 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_15 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_16 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_17 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_18 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_19 using 1 <;> norm_num [firstHitGridUpper]
  · convert firstHitReciprocal_grid_20 using 1 <;> norm_num [firstHitGridUpper]

/-- Twenty rational trapezoids, with endpoint logarithms certified by the
convergent log series and its explicit remainder. -/
theorem firstHitReciprocal_integral_le :
    (∫ u in (1 : ℝ)..3, firstHitReciprocal u) ≤ 67 / 50 := by
  let a : ℕ → ℝ := fun j => 1 + (j : ℝ) / 10
  have hlt (j : ℕ) : a j < a (j + 1) := by dsimp [a]; push_cast; linarith
  have hsub (j : ℕ) (hj : j < 20) : Set.Icc (a j) (a (j + 1)) ⊆ Set.Icc (1 : ℝ) 3 := by
    intro u hu
    have hjr : (j : ℝ) < 20 := by exact_mod_cast hj
    have hju : (j : ℝ) ≤ 19 := by exact_mod_cast (show j ≤ 19 by omega)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    dsimp [a] at hu
    push_cast at hu
    constructor <;> linarith [hu.1, hu.2]
  have hint (j : ℕ) (hj : j < 20) :
      IntervalIntegrable firstHitReciprocal MeasureTheory.volume (a j) (a (j + 1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (hlt j).le]
    exact firstHitReciprocal_continuous.mono (hsub j hj)
  calc
    _ = ∑ j ∈ range 20, ∫ u in a j..a (j + 1), firstHitReciprocal u := by
      symm
      convert intervalIntegral.sum_integral_adjacent_intervals hint using 1 <;> norm_num [a]
    _ ≤ ∑ j ∈ range 20, (firstHitGridUpper j + firstHitGridUpper (j + 1)) / 20 := by
      apply sum_le_sum
      intro j hj
      have hj20 := mem_range.mp hj
      have hh := convex_integral_le_chord (hlt j)
        (firstHitReciprocal_convex.subset (hsub j hj20) (convex_Icc _ _))
        (firstHitReciprocal_continuous.mono (hsub j hj20))
      have he : (a (j + 1) - a j) / 2 = 1 / 20 := by dsimp [a]; push_cast; ring
      rw [he] at hh
      apply hh.trans
      have h0 := firstHitReciprocal_grid_bound j (by omega)
      have h1 := firstHitReciprocal_grid_bound (j + 1) (by omega)
      change firstHitReciprocal (a j) ≤ _ at h0
      change firstHitReciprocal (a (j + 1)) ≤ _ at h1
      linarith
    _ ≤ 67 / 50 := by norm_num [sum_range_succ, firstHitGridUpper]

lemma log_ten_sevenths_le : log (10 / 7 : ℝ) ≤ 9 / 25 := by
  have hh := sum_range_sub_log_div_le (x := (3 / 17 : ℝ)) (by norm_num) 3
  norm_num [sum_range_succ] at hh
  linarith only [(abs_le.mp hh).2]

/-- A sufficient analytic budget for the prospective exponent 12/5
first-hit construction. This is only an integral certificate. -/
theorem firstHit_integral_budget :
    log (10 / 7 : ℝ) + (∫ u in (1 : ℝ)..3, firstHitReciprocal u) ≤ 17 / 10 := by
  linarith [log_ten_sevenths_le, firstHitReciprocal_integral_le]

lemma firstHit_analytic_margin_pos : (0 : ℝ) < 70 / 19 - 2 * (17 / 10) - 2 / 9 := by
  norm_num

#print axioms firstHitReciprocal_integral_le
#print axioms firstHit_integral_budget
end Erdos970.FiniteSelberg
