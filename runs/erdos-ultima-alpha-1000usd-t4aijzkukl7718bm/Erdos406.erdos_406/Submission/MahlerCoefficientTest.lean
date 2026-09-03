import FormalConjecturesUtil

/-! An exact diagnostic for a possible Mahler-measure approach to Erdős 406.
No theorem in this file settles the original missing-digit conjecture. -/
namespace Erdos406Mahler
open Polynomial
noncomputable section

lemma mahler_comp_neg_X (P : ℂ[X]) : (P.comp (-X)).mahlerMeasure = P.mahlerMeasure := by
  refine Submonoid.closure_induction ?_ ?_ ?_ (IsAlgClosed.splits P)
  · rintro Q (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · simp
    · have he : (X + C a : ℂ[X]).comp (-X) = C (-1) * (X - C a) := by
        simp; ring
      rw [he, mahlerMeasure_mul, mahlerMeasure_const,
        mahlerMeasure_X_sub_C, mahlerMeasure_X_add_C]
      simp
  · simp
  · intro Q R _ _ hQ hR
    simp only [mul_comp, mahlerMeasure_mul, hQ, hR]

lemma mahler_X_sq_add_C (a : ℂ) : (X ^ 2 + C a : ℂ[X]).mahlerMeasure = max 1 ‖a‖ := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-a) (by decide : 0 < 2)
  have hp : (X ^ 2 + C a : ℂ[X]) = (X - C z) * (X + C z) := by
    have hc : C (z ^ 2) = C (-a) := congrArg C hz
    simp only [map_pow, map_neg] at hc
    calc
      _ = X ^ 2 - (C z) ^ 2 := by rw [hc]; ring
      _ = _ := by ring
  have hn : ‖z‖ ^ 2 = ‖a‖ := by
    have hh := congrArg norm hz
    simpa using hh
  rw [hp, mahlerMeasure_mul, mahlerMeasure_X_sub_C, mahlerMeasure_X_add_C]
  by_cases h : ‖z‖ ≤ 1
  · have ha : ‖a‖ ≤ 1 := by nlinarith [norm_nonneg z]
    rw [max_eq_left h, max_eq_left ha]
    norm_num
  · have hz1 : 1 ≤ ‖z‖ := le_of_not_ge h
    have ha : 1 ≤ ‖a‖ := by nlinarith
    rw [max_eq_right hz1, max_eq_right ha]
    nlinarith

lemma mahler_comp_X_sq (P : ℂ[X]) : (P.comp (X ^ 2)).mahlerMeasure = P.mahlerMeasure := by
  refine Submonoid.closure_induction ?_ ?_ ?_ (IsAlgClosed.splits P)
  · rintro Q (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · simp
    · simp only [add_comp, X_comp, C_comp, mahler_X_sq_add_C, mahlerMeasure_X_add_C]
  · simp
  · intro Q R _ _ hQ hR
    simp only [mul_comp, mahlerMeasure_mul, hQ, hR]

/-- A root-squaring identity provides an exact Mahler-measure certificate. -/
lemma mahler_of_graeffe_identity (P Q : ℂ[X])
    (he : Q.comp (X ^ 2) = P * P.comp (-X)) :
    Q.mahlerMeasure = P.mahlerMeasure ^ 2 := by
  rw [← mahler_comp_X_sq Q, he, mahlerMeasure_mul, mahler_comp_neg_X, pow_two]

lemma mahler_le_abs_coeff_sum (P : ℤ[X]) (M : ℕ) (hM : P.natDegree < M) :
    (P.map (Int.castRingHom ℂ)).mahlerMeasure ≤
      ∑ i ∈ Finset.range M, |(P.coeff i : ℝ)| := by
  have hh := (P.map (Int.castRingHom ℂ)).mahlerMeasure_le_sum_norm_coeff
  rw [Polynomial.sum_def] at hh
  calc
    _ ≤ ∑ i ∈ (P.map (Int.castRingHom ℂ)).support,
        ‖(P.map (Int.castRingHom ℂ)).coeff i‖ := hh
    _ ≤ ∑ i ∈ Finset.range M, ‖(P.map (Int.castRingHom ℂ)).coeff i‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        apply Finset.mem_range.mpr
        have hi' := le_natDegree_of_mem_supp i hi
        have hd : (P.map (Int.castRingHom ℂ)).natDegree ≤ P.natDegree := natDegree_map_le
        omega
      · intro i _ _
        positivity
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Complex.norm_intCast]

def q15 : ℤ[X] :=
  1 + X ^ 2 + X ^ 6 + X ^ 8 + 2 * X ^ 10 + X ^ 11 + X ^ 12 + X ^ 13 + X ^ 15

def g1 : ℤ[X] :=
  1 + 2 * X + X ^ 2 + 2 * X ^ 3 + 4 * X ^ 4 + 6 * X ^ 5 + 7 * X ^ 6 + 4 * X ^ 7 + 5 * X ^ 8 + 6 * X ^ 9 + 6 * X ^ 10 + 3 * X ^ 11 - X ^ 12 - 3 * X ^ 13 - 2 * X ^ 14 - X ^ 15

def g2 : ℤ[X] :=
  1 - 2 * X + X ^ 2 - 6 * X ^ 3 + 2 * X ^ 5 + 15 * X ^ 6 + 24 * X ^ 7 + 29 * X ^ 8 + 10 * X ^ 9 - 2 * X ^ 10 + 3 * X ^ 11 + 7 * X ^ 12 + X ^ 13 - 2 * X ^ 14 - X ^ 15

def g3 : ℤ[X] :=
  1 - 2 * X - 23 * X ^ 2 + 2 * X ^ 3 + 208 * X ^ 4 + 378 * X ^ 5 + 271 * X ^ 6 + 304 * X ^ 7 + 293 * X ^ 8 - 166 * X ^ 9 + 246 * X ^ 10 - 125 * X ^ 11 + 71 * X ^ 12 - 23 * X ^ 13 + 6 * X ^ 14 - X ^ 15

set_option maxHeartbeats 2000000 in
lemma graeffe_identity_1 : g1.comp (X ^ 2) = q15 * q15.comp (-X) := by
  norm_num [g1, q15, add_comp, sub_comp, mul_comp, pow_comp]
  ring

set_option maxHeartbeats 2000000 in
lemma graeffe_identity_2 : g2.comp (X ^ 2) = g1 * g1.comp (-X) := by
  norm_num [g2, g1, add_comp, sub_comp, mul_comp, pow_comp]
  ring

set_option maxHeartbeats 2000000 in
lemma graeffe_identity_3 : g3.comp (X ^ 2) = g2 * g2.comp (-X) := by
  norm_num [g3, g2, add_comp, sub_comp, mul_comp, pow_comp]
  ring

lemma mahler_int_graeffe (P Q : ℤ[X])
    (he : Q.comp (X ^ 2) = P * P.comp (-X)) :
    (Q.map (Int.castRingHom ℂ)).mahlerMeasure =
      (P.map (Int.castRingHom ℂ)).mahlerMeasure ^ 2 := by
  apply mahler_of_graeffe_identity
  have hh := congrArg (Polynomial.map (Int.castRingHom ℂ)) he
  simpa only [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_mul, Polynomial.map_neg] using hh

lemma q15_eval_three : q15.eval 3 = (2 : ℤ) ^ 24 := by norm_num [q15]
lemma q15_eval_one : q15.eval 1 = 10 := by norm_num [q15]
lemma q15_coeff_ten : q15.coeff 10 = 2 := by norm_num [q15, coeff_X_pow, coeff_one]
lemma q15_degree : q15.natDegree = 15 := by unfold q15; compute_degree!

lemma g3_mahler_bound : (g3.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2120 := by
  have hdeg : g3.natDegree < 16 := by unfold g3; compute_degree!
  have hb := mahler_le_abs_coeff_sum g3 16 hdeg
  have he : (∑ i ∈ Finset.range 16, |(g3.coeff i : ℝ)|) = 2120 := by
    norm_num [Finset.sum_range_succ, g3, coeff_X_pow, coeff_one, coeff_X]
  rwa [he] at hb

lemma q15_mahler_eighth_power :
    (q15.map (Int.castRingHom ℂ)).mahlerMeasure ^ 8 ≤ 2120 := by
  have h1 := mahler_int_graeffe q15 g1 graeffe_identity_1
  have h2 := mahler_int_graeffe g1 g2 graeffe_identity_2
  have h3 := mahler_int_graeffe g2 g3 graeffe_identity_3
  have hb := g3_mahler_bound
  rw [h3, h2, h1] at hb
  convert hb using 1
  ring

lemma q15_mahler_square_lt_eval_one :
    (q15.map (Int.castRingHom ℂ)).mahlerMeasure ^ 2 < ((q15.eval 1 : ℤ) : ℝ) := by
  have hb := q15_mahler_eighth_power
  rw [q15_eval_one]
  norm_num only [Int.cast_ofNat]
  by_contra hn
  have hlarge : (10 : ℝ) ^ 4 ≤ ((q15.map (Int.castRingHom ℂ)).mahlerMeasure ^ 2) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) (le_of_not_gt hn) 4
  norm_num at hlarge
  rw [← pow_mul] at hlarge
  norm_num at hlarge
  linarith

lemma q15_coeff_bounds (i : ℕ) : 0 ≤ q15.coeff i ∧ q15.coeff i ≤ 2 := by
  by_cases hi : i ≤ 15
  · interval_cases i <;> norm_num [q15, coeff_one, coeff_X_pow]
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [q15_degree]; omega)]
    norm_num

lemma q15_coeff_square_sum : (∑ i ∈ Finset.range 16, (q15.coeff i) ^ 2) = 12 := by
  norm_num [Finset.sum_range_succ, q15, coeff_one, coeff_X_pow]

lemma q15_not_binary : ¬ ∀ i, q15.coeff i = 0 ∨ q15.coeff i = 1 := by
  intro h
  have hh := h 10
  rw [q15_coeff_ten] at hh
  omega

/-- The numerical factor gap does not follow merely from nonnegative bounded
coefficients, a pure-power value, and the Mahler/digit-sum inequality. The
coefficient2 is precisely why this is NOT an Erdős406 counterexample. -/
theorem mahler_factor_surrogate_false :
    ¬ ∀ P : ℤ[X], P.Monic → P.coeff 0 = 1 →
      (∀ i, 0 ≤ P.coeff i ∧ P.coeff i ≤ 2) →
      (∃ e : ℕ, P.eval 3 = (2 : ℤ) ^ e) →
      (P.map (Int.castRingHom ℂ)).mahlerMeasure ^ 2 ≤ ((P.eval 1 : ℤ) : ℝ) →
      (P.eval 3) ^ 2 ≤ 2 * (8 : ℤ) ^ P.natDegree := by
  intro h
  have hm : q15.Monic := by unfold q15; monicity <;> norm_num
  have h0 : q15.coeff 0 = 1 := by norm_num [q15, coeff_one, coeff_X_pow]
  have hh := h q15 hm h0 q15_coeff_bounds ⟨24, q15_eval_three⟩
    q15_mahler_square_lt_eval_one.le
  rw [q15_eval_three, q15_degree] at hh
  norm_num at hh

#print axioms mahler_comp_neg_X
#print axioms mahler_comp_X_sq
#print axioms q15_mahler_eighth_power
#print axioms q15_mahler_square_lt_eval_one
#print axioms q15_not_binary
#print axioms mahler_factor_surrogate_false

end
end Erdos406Mahler
