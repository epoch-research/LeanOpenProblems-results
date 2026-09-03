import Submission.NewmanFactorCount

/-! Small-degree factor restrictions. These do not classify arbitrary
irreducible factors and do not settle Erdős 406. -/
namespace Erdos406SmallFactors
open Polynomial Erdos406Cyclotomic Erdos406FactorParity Erdos406FactorCount

lemma ofDigits_half_interval (w : List ℕ) (hw : w ⊆ [0, 1]) (x : ℝ)
    (hx : -(1 / 2 : ℝ) ≤ x) (hx0 : x ≤ 0) :
    -(2 / 3 : ℝ) ≤ Nat.ofDigits x w ∧ Nat.ofDigits x w ≤ 4 / 3 := by
  induction w with
  | nil => norm_num [Nat.ofDigits]
  | cons d w ih =>
    have hd := hw (List.mem_cons_self ..)
    have hh := ih (fun a ha => hw (List.mem_cons_of_mem d ha))
    have hlo := mul_le_mul_of_nonpos_left hh.2 hx0
    have hhi := mul_le_mul_of_nonpos_left hh.1 hx0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp only [Nat.ofDigits, Nat.cast_zero, Nat.cast_one]
    · constructor <;> nlinarith
    · constructor <;> nlinarith

lemma digitPoly_pos_half_interval (w : List ℕ) (hw : w ⊆ [0, 1]) (x : ℝ)
    (hx : -(1 / 2 : ℝ) ≤ x) (hx0 : x ≤ 0) :
    0 < ((digitPoly (1 :: w)).map (Int.castRingHom ℝ)).eval x := by
  rw [eval_map_digitPoly]
  simp only [Nat.ofDigits, Nat.cast_one]
  have hh := (ofDigits_half_interval w hw x hx hx0).2
  have hlo := mul_le_mul_of_nonpos_left hh hx0
  nlinarith

/-- A factor of a Newman polynomial with constant term one is positive at
minus one half. This uses the whole parent polynomial, not the factor's
coefficient signs. -/
lemma monic_factor_neg_half_positive (w : List ℕ) (hw : w ⊆ [0, 1])
    (Q : ℤ[X]) (hQ : Q.Monic) (hd : Q ∣ digitPoly (1 :: w)) :
    0 < (Q.map (Int.castRingHom ℝ)).eval (-(1 / 2)) := by
  let F := Q.map (Int.castRingHom ℝ)
  have hF0 : F.eval 0 = 1 := by
    have hh := monic_factor_constant_one w Q hQ hd
    simp [F, ← coeff_zero_eq_eval_zero, hh]
  by_contra hh
  have hn : F.eval (-(1 / 2)) ≤ 0 := le_of_not_gt hh
  obtain ⟨x, hx, he⟩ := intermediate_value_Icc (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    F.continuous.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (F.eval (-(1 / 2))) (F.eval 0) from ⟨hn, by rw [hF0]; norm_num⟩)
  change F.eval x = 0 at he
  have hv := eval_dvd (x := x) (map_dvd (Int.castRingHom ℝ) hd)
  change F.eval x ∣ _ at hv
  rw [he, zero_dvd_iff] at hv
  have hp := digitPoly_pos_half_interval w hw x hx.1 hx.2
  rw [hv] at hp
  exact lt_irrefl _ hp

lemma candidate_factor_neg_half_positive (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) :
    0 < (Q.map (Int.castRingHom ℝ)).eval (-(1 / 2)) := by
  have he := good_two_power_digits_head k hg
  rw [he] at hd hg
  exact monic_factor_neg_half_positive _ (fun d hd => hg (List.mem_cons_of_mem _ hd)) Q hQ hd

/-- The only possible normalized quadratic factor is (X+1)^2. -/
theorem quadratic_factor_coefficient (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (b : ℤ)
    (hd : (X ^ 2 + C b * X + 1 : ℤ[X]) ∣ digitPoly (Nat.digits 3 (2 ^ k))) : b = 2 := by
  let Q : ℤ[X] := X ^ 2 + C b * X + 1
  have hQ : Q.Monic := by dsimp [Q]; monicity <;> norm_num
  have hdeg : 0 < Q.natDegree := by
    have he : Q.natDegree = 2 := by dsimp [Q]; compute_degree!
    omega
  have hlow := (candidate_factor_eval_one_even k hg Q hQ hd hdeg).2
  have hhi := candidate_factor_neg_half_positive k hg Q hQ hd
  have hb0 : 0 ≤ b := by norm_num [Q] at hlow; omega
  have hb2 : b ≤ 2 := by
    norm_num [Q] at hhi
    have hbR : (b : ℝ) < 5 / 2 := by linarith
    have : b < 3 := by exact_mod_cast (by linarith : (b : ℝ) < 3)
    omega
  obtain ⟨t, ht, _, he⟩ := candidate_factor_four_exponent_positive k hg Q hQ hd hdeg
  have h4 : (4 : ℤ) ∣ Q.eval 3 := by rw [he]; exact dvd_pow_self 4 (ne_of_gt ht)
  norm_num [Q] at h4
  interval_cases b <;> norm_num at *

theorem quadratic_factor_shape (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hdeg : Q.natDegree = 2) :
    Q = (X + 1) ^ 2 := by
  have hc := (candidate_monic_factor k hg Q hQ hd).1
  have h2 : Q.coeff 2 = 1 := by rw [← hdeg, coeff_natDegree, hQ.leadingCoeff]
  have he := Q.as_sum_range_C_mul_X_pow
  rw [hdeg] at he
  norm_num [Finset.sum_range_succ, hc, h2] at he
  change Q = 1 + C (Q.coeff 1) * X + X ^ 2 at he
  have hshape : Q = X ^ 2 + C (Q.coeff 1) * X + 1 := he.trans (by ring)
  have hd' := hd
  rw [hshape] at hd'
  have hb := quadratic_factor_coefficient k hg _ hd'
  rw [hshape, hb]
  norm_num
  ring

lemma candidate_factor_real_root_bound (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (x : ℝ)
    (hx : (Q.map (Int.castRingHom ℝ)).eval x = 0) : |x| < 2 := by
  have he := eval₂_at_apply Complex.ofRealHom x (p := Q.map (Int.castRingHom ℝ))
  rw [eval₂_map] at he
  have hcomp : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := by
    ext z
    simp
  rw [hcomp, hx, map_zero] at he
  have hr : (Q.map (Int.castRingHom ℂ)).IsRoot (x : ℂ) := by
    simpa only [IsRoot, eval_map] using he
  have hm := (mem_roots (hQ.map _).ne_zero).mpr hr
  simpa using candidate_factor_root_bound k hg Q hQ hd (x : ℂ) hm

lemma candidate_factor_odd_degree_neg_two (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hodd : Odd Q.natDegree) :
    Q.eval (-2) < 0 := by
  let F : ℝ[X] := (Q.map (Int.castRingHom ℝ)).comp (-X)
  have hlead : F.leadingCoeff = -1 := by
    dsimp [F]
    rw [leadingCoeff_comp (by simp), (hQ.map _).leadingCoeff]
    simp only [leadingCoeff_neg, leadingCoeff_X, hQ.natDegree_map, one_mul]
    exact hodd.neg_one_pow
  have hdeg : 0 < F.degree := by
    apply natDegree_pos_iff_degree_pos.mp
    dsimp [F]
    rw [natDegree_comp, hQ.natDegree_map]
    simpa using hodd.pos
  have ht := F.tendsto_atBot_of_leadingCoeff_nonpos hdeg (by rw [hlead]; norm_num)
  obtain ⟨y, hy, hFy⟩ := ((Filter.eventually_ge_atTop (2 : ℝ)).and
    (ht.eventually_lt_atBot 0)).exists
  have hF2 : F.eval 2 < 0 := by
    by_contra hh
    have h2 : 0 ≤ F.eval 2 := le_of_not_gt hh
    obtain ⟨z, hz, he⟩ := intermediate_value_Icc' hy F.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (F.eval y) (F.eval 2) from ⟨hFy.le, h2⟩)
    change F.eval z = 0 at he
    have hzero : (Q.map (Int.castRingHom ℝ)).eval (-z) = 0 := by
      simpa [F] using he
    have hb := candidate_factor_real_root_bound k hg Q hQ hd (-z) hzero
    rw [abs_neg, abs_of_nonneg (by linarith [hz.1])] at hb
    linarith [hz.1]
  have he := eval_map_int Q (-2)
  norm_num only [Int.cast_neg, Int.cast_ofNat] at he
  have hb : (Q.map (Int.castRingHom ℝ)).eval (-2) < 0 := by simpa [F] using hF2
  rw [he] at hb
  exact_mod_cast hb

/-- The only possible normalized cubic factor is (X+1)^3. -/
theorem cubic_factor_coefficients (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (a b : ℤ)
    (hd : (X ^ 3 + C a * X ^ 2 + C b * X + 1 : ℤ[X]) ∣
      digitPoly (Nat.digits 3 (2 ^ k))) : a = 3 ∧ b = 3 := by
  let Q : ℤ[X] := X ^ 3 + C a * X ^ 2 + C b * X + 1
  have hQ : Q.Monic := by dsimp [Q]; monicity <;> norm_num
  have hdeg : Q.natDegree = 3 := by dsimp [Q]; compute_degree!
  have hposdeg : 0 < Q.natDegree := by omega
  have hodd : Odd Q.natDegree := by rw [hdeg]; decide
  have h1 := (candidate_factor_eval_one_even k hg Q hQ hd hposdeg).2
  have hh := candidate_factor_neg_half_positive k hg Q hQ hd
  have h2 := candidate_factor_odd_degree_neg_two k hg Q hQ hd hodd
  have hab : 0 ≤ a + b := by norm_num [Q] at h1; omega
  have hab' : 2 * a - b ≤ 3 := by norm_num [Q] at h2; omega
  have hba : 2 * b - a ≤ 3 := by
    norm_num [Q] at hh
    have hr : (2 * b - a : ℝ) < 7 / 2 := by linarith
    have hn : 2 * b - a < 4 := by exact_mod_cast (by linarith : (2 * b - a : ℝ) < 4)
    omega
  have ha : -1 ≤ a ∧ a ≤ 3 := by omega
  have hb : -1 ≤ b ∧ b ≤ 3 := by omega
  obtain ⟨t, htpos, _, he⟩ := candidate_factor_four_exponent_positive k hg Q hQ hd hposdeg
  norm_num [Q] at he
  have htlo : 2 < t := by
    by_contra hn
    have htle : t ≤ 2 := by omega
    have hpow : (4 : ℤ) ^ t ≤ 4 ^ 2 := by gcongr; norm_num
    norm_num at hpow
    omega
  have hthi : t < 4 := by
    by_contra hn
    have htle : 4 ≤ t := by omega
    have hpow : (4 : ℤ) ^ 4 ≤ 4 ^ t := by gcongr; norm_num
    norm_num at hpow
    omega
  have ht3 : t = 3 := by omega
  rw [ht3] at he
  norm_num at he
  omega

theorem cubic_factor_shape (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hdeg : Q.natDegree = 3) :
    Q = (X + 1) ^ 3 := by
  have hc := (candidate_monic_factor k hg Q hQ hd).1
  have h3 : Q.coeff 3 = 1 := by rw [← hdeg, coeff_natDegree, hQ.leadingCoeff]
  have he := Q.as_sum_range_C_mul_X_pow
  rw [hdeg] at he
  norm_num [Finset.sum_range_succ, hc, h3] at he
  change Q = 1 + C (Q.coeff 1) * X + C (Q.coeff 2) * X ^ 2 + X ^ 3 at he
  have hshape : Q = X ^ 3 + C (Q.coeff 2) * X ^ 2 + C (Q.coeff 1) * X + 1 :=
    he.trans (by ring)
  have hd' := hd
  rw [hshape] at hd'
  obtain ⟨ha, hb⟩ := cubic_factor_coefficients k hg _ _ hd'
  rw [hshape, ha, hb]
  norm_num
  ring

/-- All monic factors of degree at most three are powers of X+1. Higher
irreducible degrees, starting with the known quartic, are not addressed. -/
theorem factor_degree_le_three_shape (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hdeg : Q.natDegree ≤ 3) :
    Q = (X + 1) ^ Q.natDegree := by
  have hc := (candidate_monic_factor k hg Q hQ hd).1
  rcases (by omega : Q.natDegree = 0 ∨ Q.natDegree = 1 ∨ Q.natDegree = 2 ∨ Q.natDegree = 3) with
    hz | h1 | h2 | h3
  · rw [hz, pow_zero]
    rw [eq_C_of_natDegree_eq_zero hz, hc, C_1]
  · have hlead : Q.coeff 1 = 1 := by rw [← h1, coeff_natDegree, hQ.leadingCoeff]
    have he := Q.as_sum_range_C_mul_X_pow
    rw [h1] at he
    norm_num [Finset.sum_range_succ, hc, hlead] at he
    rw [h1, pow_one]
    exact he.trans (by ring)
  · rw [h2]
    exact quadratic_factor_shape k hg Q hQ hd h2
  · rw [h3]
    exact cubic_factor_shape k hg Q hQ hd h3

/-- Any irreducible monic factor other than X+1 has degree at least four. -/
theorem irreducible_factor_alternative (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hI : Irreducible Q) :
    Q = X + 1 ∨ 4 ≤ Q.natDegree := by
  by_cases hdeg : Q.natDegree ≤ 3
  · have hs := factor_degree_le_three_shape k hg Q hQ hd hdeg
    have hn : Q.natDegree = 1 := by
      by_contra hh
      have hi := hI
      rw [hs] at hi
      exact not_irreducible_pow hh hi
    left
    simpa only [hn, pow_one] using hs
  · right
    omega

#print axioms monic_factor_neg_half_positive
#print axioms quadratic_factor_coefficient
#print axioms quadratic_factor_shape
#print axioms candidate_factor_odd_degree_neg_two
#print axioms cubic_factor_coefficients
#print axioms cubic_factor_shape
#print axioms factor_degree_le_three_shape
#print axioms irreducible_factor_alternative
end Erdos406SmallFactors
