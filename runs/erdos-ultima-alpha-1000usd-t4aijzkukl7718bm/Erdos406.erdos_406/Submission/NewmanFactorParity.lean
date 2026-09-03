import Submission.CyclotomicObstruction

/-! Positivity and parity restrictions on monic factors of digit polynomials.
These restrictions do not provide a degree bound or settle Erdős 406. -/
namespace Erdos406FactorParity
open Polynomial Filter Erdos406Cyclotomic

/-- A monic real factor of a polynomial positive on the nonnegative ray is
itself positive there. -/
lemma monic_factor_positive {P Q : ℝ[X]} (hQ : Q.Monic) (hd : Q ∣ P)
    (hP : ∀ x : ℝ, 0 ≤ x → 0 < P.eval x) (x : ℝ) (hx : 0 ≤ x) :
    0 < Q.eval x := by
  have hno : ∀ z : ℝ, 0 ≤ z → Q.eval z ≠ 0 := by
    intro z hz hzero
    obtain ⟨R, he⟩ := hd
    have hp := hP z hz
    rw [he, eval_mul, hzero, zero_mul] at hp
    exact lt_irrefl _ hp
  by_cases hdeg : 0 < Q.degree
  · have ht := Q.tendsto_atTop_of_leadingCoeff_nonneg hdeg
      (by rw [hQ.leadingCoeff]; norm_num)
    obtain ⟨y, hxy, hy⟩ :=
      ((eventually_ge_atTop x).and (ht.eventually_gt_atTop 0)).exists
    by_contra hnot
    have hneg : Q.eval x ≤ 0 := le_of_not_gt hnot
    obtain ⟨z, hz, hroot⟩ := intermediate_value_Icc hxy Q.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (Q.eval x) (Q.eval y) from ⟨hneg, hy.le⟩)
    exact hno z (hx.trans hz.1) hroot
  · have hc := eq_C_of_degree_le_zero (le_of_not_gt hdeg)
    have hcoeff : Q.coeff 0 = 1 := by
      have hh := hQ.leadingCoeff
      rw [hc, leadingCoeff_C] at hh
      exact hh
    rw [hc, eval_C, hcoeff]
    norm_num

lemma eval_map_int (P : ℤ[X]) (a : ℤ) :
    (P.map (Int.castRingHom ℝ)).eval (a : ℝ) = ((P.eval a : ℤ) : ℝ) := by
  rw [eval_map]
  exact eval₂_at_apply (Int.castRingHom ℝ) a

lemma eval_map_digitPoly (w : List ℕ) (x : ℝ) :
    ((digitPoly w).map (Int.castRingHom ℝ)).eval x = Nat.ofDigits x w := by
  induction w with
  | nil => simp [digitPoly, Nat.ofDigits]
  | cons d w ih =>
    simpa [digitPoly, Nat.ofDigits] using congrArg (fun y : ℝ => d + x * y) ih

lemma real_ofDigits_nonneg (w : List ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ Nat.ofDigits x w := by
  induction w with
  | nil => simp [Nat.ofDigits]
  | cons d w ih => simp only [Nat.ofDigits]; positivity

lemma factor_positive_on_ray (w : List ℕ) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (1 :: w)) (x : ℝ) (hx : 0 ≤ x) :
    0 < (Q.map (Int.castRingHom ℝ)).eval x := by
  apply monic_factor_positive (hQ.map _) (map_dvd _ hd) _ x hx
  intro y hy
  rw [eval_map_digitPoly]
  simp only [Nat.ofDigits, Nat.cast_one]
  have hh := real_ofDigits_nonneg w y hy
  positivity

/-- Monic integer factors have constant coefficient one, not minus one. -/
theorem monic_factor_constant_one (w : List ℕ) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (1 :: w)) : Q.coeff 0 = 1 := by
  have hp := factor_positive_on_ray w Q hQ hd 0 (by norm_num)
  have hc : 0 < Q.eval 0 := by
    have hh := eval_map_int Q 0
    norm_num only [Int.cast_zero] at hh
    rw [hh] at hp
    exact_mod_cast hp
  have hv := eval_dvd (x := (0 : ℤ)) hd
  have hv' : Q.eval 0 ∣ 1 := by simpa [eval_digitPoly, Nat.ofDigits] using hv
  rw [coeff_zero_eq_eval_zero]
  exact Int.eq_one_of_dvd_one hc.le hv'

/-- Every monic integer factor of a digit polynomial whose value at three
is a power of two has value a power of FOUR. This says nothing about a
uniform bound on its degree. -/
theorem monic_factor_eval_four_power (w : List ℕ) (Q : ℤ[X]) (k : ℕ)
    (hQ : Q.Monic) (hd : Q ∣ digitPoly (1 :: w))
    (hval : (digitPoly (1 :: w)).eval 3 = (2 : ℤ) ^ k) :
    ∃ t : ℕ, 2 * t ≤ k ∧ Q.eval 3 = (4 : ℤ) ^ t := by
  have hp := factor_positive_on_ray w Q hQ hd 3 (by norm_num)
  have hpos : 0 < Q.eval 3 := by
    have hh := eval_map_int Q 3
    norm_num only [Int.cast_ofNat] at hh
    rw [hh] at hp
    exact_mod_cast hp
  have hv := eval_dvd (x := (3 : ℤ)) hd
  rw [hval] at hv
  have hvN : (Q.eval 3).natAbs ∣ 2 ^ k := by
    simpa using Int.natAbs_dvd_natAbs.mpr hv
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hvN
  have he : Q.eval 3 = (2 : ℤ) ^ j := by
    have hh := Int.natAbs_of_nonneg hpos.le
    rw [hj] at hh
    exact_mod_cast hh.symm
  have hc : Q.eval 0 = 1 := by
    simpa only [coeff_zero_eq_eval_zero] using monic_factor_constant_one w Q hQ hd
  have hdiff := sub_dvd_eval_sub (3 : ℤ) 0 Q
  rw [sub_zero, he, hc] at hdiff
  rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
  · refine ⟨t, by omega, ?_⟩
    rw [he, ht, ← two_mul, pow_mul]
    norm_num
  · have hp3 : (2 ^ j : ℤ) % 3 = 1 := by omega
    have hb : Int.ModEq 3 (2 : ℤ) (-1) := by decide
    have hm := hb.pow j
    change (2 ^ j : ℤ) % 3 = ((-1 : ℤ) ^ j) % 3 at hm
    have hneg : (-1 : ℤ) ^ j = -1 := by rw [ht, pow_add, pow_mul]; norm_num
    rw [hneg] at hm
    norm_num only [show (-1 : ℤ) % 3 = 2 from rfl] at hm
    omega

lemma good_two_power_digits_head (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) :
    Nat.digits 3 (2 ^ k) = 1 :: Nat.digits 3 (2 ^ k / 3) := by
  have hp : 0 < 2 ^ k := by positivity
  have he := Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hp
  have hm : 2 ^ k % 3 ∈ Nat.digits 3 (2 ^ k) := by rw [he]; simp
  have hb := hg hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  have hd : 2 ^ k % 3 = 1 := by
    rcases hb with hz | ho
    · have hh := Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero hz)
      norm_num at hh
    · exact ho
  simpa only [hd] using he

/-- Factor restrictions applied to the exact candidates in Erdős 406. -/
theorem candidate_monic_factor (k : ℕ) (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1])
    (Q : ℤ[X]) (hQ : Q.Monic) (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) :
    Q.coeff 0 = 1 ∧ ∃ t : ℕ, 2 * t ≤ k ∧ Q.eval 3 = (4 : ℤ) ^ t := by
  have hh := good_two_power_digits_head k hg
  rw [hh] at hd
  refine ⟨monic_factor_constant_one _ Q hQ hd, ?_⟩
  apply monic_factor_eval_four_power _ Q k hQ hd
  have hv := digitPoly_eval_three (2 ^ k)
  rw [hh] at hv
  exact_mod_cast hv

#print axioms monic_factor_positive
#print axioms monic_factor_constant_one
#print axioms monic_factor_eval_four_power
#print axioms candidate_monic_factor
end Erdos406FactorParity
