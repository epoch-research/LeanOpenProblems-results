import Submission.PositivePerturbationData
import Submission.PolynomialEndGapRoots
import Submission.MonicEvaluationIrreducibility
import Submission.NewmanEventualFactorBound

/-! Irreducible bounded-coefficient polynomials with pure-power evaluation at
three and arbitrarily thin root annuli. These are NOT asserted to divide
Newman polynomials, and are NOT counterexamples to Erdős 406. -/
namespace Erdos406Perturbation
open Polynomial Erdos406Cyclotomic Erdos406FactorParity
  Erdos406EvaluationIrreducible Erdos406EndGapRoots Erdos406EventualFactorBound

lemma digitPoly_coeff_getD (w : List ℕ) (i : ℕ) :
    (digitPoly w).coeff i = (w.getD i 0 : ℤ) := by
  induction w generalizing i with
  | nil => simp [digitPoly, Nat.ofDigits]
  | cons a w ih =>
    cases i with
    | zero => simp [digitPoly, Nat.ofDigits]
    | succ i =>
      simpa [digitPoly, Nat.ofDigits, coeff_X_mul] using ih i

lemma ternary_digitPoly_coeff (r i : ℕ) :
    (digitPoly (Nat.digits 3 r)).coeff i = (r / 3 ^ i % 3 : ℕ) := by
  rw [digitPoly_coeff_getD, Nat.getD_digits _ _ (by decide)]

lemma ternary_digitPoly_coeff_bounds (r i : ℕ) :
    0 ≤ (digitPoly (Nat.digits 3 r)).coeff i ∧
      (digitPoly (Nat.digits 3 r)).coeff i ≤ 2 := by
  rw [ternary_digitPoly_coeff]
  have hh := Nat.mod_lt (r / 3 ^ i) (by decide : 0 < 3)
  constructor <;> omega

lemma ternary_digitPoly_low_zero (r G : ℕ) (hdiv : 3 ^ G ∣ r)
    (i : ℕ) (hi : i < G) : (digitPoly (Nat.digits 3 r)).coeff i = 0 := by
  rw [ternary_digitPoly_coeff]
  have hpow : 3 ^ (i + 1) ∣ r := (pow_dvd_pow 3 (by omega)).trans hdiv
  have hpow' : 3 ^ i ∣ r := (pow_dvd_pow 3 hi.le).trans hdiv
  have hh : 3 ∣ r / 3 ^ i := (Nat.dvd_div_iff_mul_dvd hpow').mpr (by
    simpa only [pow_succ] using hpow)
  simp [Nat.mod_eq_zero_of_dvd hh]

lemma ternary_digitPoly_degree_bound (r K : ℕ) (hK : 0 < K) (hr : r < 3 ^ K) :
    (digitPoly (Nat.digits 3 r)).natDegree < K := by
  have hh : (digitPoly (Nat.digits 3 r)).natDegree ≤ K - 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have hKi : K ≤ i := by omega
    have hri : r < 3 ^ i := hr.trans_le (Nat.pow_le_pow_right (by decide) hKi)
    rw [ternary_digitPoly_coeff, Nat.div_eq_of_lt hri]
    norm_num
  omega

lemma square_difference_coeff_bound (R : ℤ[X])
    (hR : ∀ i, 0 ≤ R.coeff i ∧ R.coeff i ≤ 2) (i : ℕ) :
    |(((X - 1) ^ 2 * R : ℤ[X]).coeff i)| ≤ 4 := by
  have hs (j : ℕ) : 0 ≤ (X ^ j * R).coeff i ∧ (X ^ j * R).coeff i ≤ 2 := by
    rw [coeff_X_pow_mul']
    split_ifs <;> simp_all
  have h2 := hs 2
  have h1 := hs 1
  have h0 := hR i
  have he : (X - 1) ^ 2 * R = X ^ 2 * R - C 2 * (X ^ 1 * R) + R := by norm_num; ring
  rw [he, coeff_add, coeff_sub, coeff_C_mul]
  exact abs_le.mpr (by constructor <;> omega)

lemma square_difference_low_zero (R : ℤ[X]) (G : ℕ)
    (hR : ∀ i, i < G → R.coeff i = 0) (i : ℕ) (hi : i < G) :
    (((X - 1) ^ 2 * R : ℤ[X]).coeff i) = 0 := by
  have hs (j : ℕ) : (X ^ j * R).coeff i = 0 := by
    rw [coeff_X_pow_mul']
    split_ifs with hj
    · exact hR _ (by omega)
    · rfl
  have he : (X - 1) ^ 2 * R = X ^ 2 * R - C 2 * (X ^ 1 * R) + R := by norm_num; ring
  rw [he, coeff_add, coeff_sub, coeff_C_mul, hs 2, hs 1, hR i hi]
  ring

/-- Turn the arithmetic data into a polynomial with controlled coefficients
and long zero blocks. -/
lemma perturbation_polynomial (G D m t : ℕ) (hG : 0 < G) (hD : 3 * G + 3 ≤ D)
    (he : 4 ^ m = 1 + 3 ^ D + 4 * (3 ^ G * t))
    (hsmall : 3 ^ G * t < 3 ^ (D - (2 * G + 1))) :
    ∃ Q : ℤ[X], Q.IsMonicOfDegree D ∧ Q.coeff 0 = 1 ∧ Q.eval 1 = 2 ∧
      Q.eval 3 = (2 : ℤ) ^ (2 * m) ∧
      (∀ x : ℝ, 0 ≤ x → 0 < (Q.map (Int.castRingHom ℝ)).eval x) ∧
      (∀ i, |Q.coeff i| ≤ 10) ∧
      (∀ i, 0 < i → i < G → Q.coeff i = 0) ∧
      (∀ i, D - G < i → i < D → Q.coeff i = 0) := by
  let R := digitPoly (Nat.digits 3 (3 ^ G * t))
  let T : ℤ[X] := (X - 1) ^ 2 * R
  let Q : ℤ[X] := 1 + X ^ D + T
  have hRdeg : R.natDegree < D - (2 * G + 1) :=
    ternary_digitPoly_degree_bound _ _ (by omega) hsmall
  have hRlow : ∀ i, i < G → R.coeff i = 0 :=
    ternary_digitPoly_low_zero _ G (dvd_mul_right _ _)
  have hRcoeff : ∀ i, 0 ≤ R.coeff i ∧ R.coeff i ≤ 2 :=
    ternary_digitPoly_coeff_bounds _
  have hTdeg : T.natDegree ≤ D - 2 * G := by
    have h1 : ((X - 1 : ℤ[X]) ^ 2).natDegree ≤ 2 := by
      have hh := natDegree_pow_le (p := (X - 1 : ℤ[X])) (n := 2)
      have heq : (X - 1 : ℤ[X]).natDegree = 1 := by
        simpa using (natDegree_X_sub_C (1 : ℤ))
      rw [heq] at hh
      omega
    have hh := natDegree_mul_le (p := (X - 1 : ℤ[X]) ^ 2) (q := R)
    change T.natDegree ≤ _ at hh
    omega
  have hTlow : ∀ i, i < G → T.coeff i = 0 := square_difference_low_zero R G hRlow
  have hTcoeff : ∀ i, |T.coeff i| ≤ 4 := square_difference_coeff_bound R hRcoeff
  have hQD : Q.IsMonicOfDegree D := by
    have hh : (1 + T).natDegree < D := by
      have hb := natDegree_add_le (1 : ℤ[X]) T
      rw [natDegree_one] at hb
      omega
    have hh' := (isMonicOfDegree_X_pow ℤ D).add_right hh
    have heq : Q = X ^ D + (1 + T) := by dsimp [Q]; ring
    rw [heq]
    exact hh'
  have hQ0 : Q.coeff 0 = 1 := by
    dsimp [Q]
    rw [coeff_add, coeff_add, hTlow 0 hG]
    simp [coeff_X_pow, show 0 ≠ D by omega]
  have hQ1 : Q.eval 1 = 2 := by simp [Q, T]
  have hQ3 : Q.eval 3 = (2 : ℤ) ^ (2 * m) := by
    have hh : (4 : ℤ) ^ m = 1 + 3 ^ D + 4 * (3 ^ G * t) := by exact_mod_cast he
    dsimp [Q, T, R]
    rw [eval_add, eval_add, eval_one, eval_pow, eval_X, eval_mul, eval_pow,
      eval_sub, eval_X, eval_one, digitPoly_eval_three]
    push_cast
    rw [pow_mul]
    norm_num at hh ⊢
    exact hh.symm
  refine ⟨Q, hQD, hQ0, hQ1, hQ3, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hRpos : 0 ≤ (R.map (Int.castRingHom ℝ)).eval x := by
      rw [eval_map_digitPoly]
      exact real_ofDigits_nonneg _ x hx
    have hpow : 0 ≤ x ^ D := pow_nonneg hx _
    have hmul : 0 ≤ (x - 1) ^ 2 * (R.map (Int.castRingHom ℝ)).eval x :=
      mul_nonneg (sq_nonneg _) hRpos
    dsimp [Q, T]
    simp only [Polynomial.map_add, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_mul, Polynomial.map_sub, eval_add, eval_one, eval_pow, eval_X,
      eval_mul, eval_sub]
    linarith
  · intro i
    have h1 : |(1 : ℤ[X]).coeff i| ≤ 1 := by simp only [coeff_one]; split_ifs <;> norm_num
    have hX : |(X ^ D : ℤ[X]).coeff i| ≤ 1 := by simp only [coeff_X_pow]; split_ifs <;> norm_num
    dsimp [Q]
    rw [coeff_add, coeff_add]
    have hh1 := abs_add_le ((1 : ℤ[X]).coeff i) ((X ^ D : ℤ[X]).coeff i)
    have hh2 := abs_add_le ((1 : ℤ[X]).coeff i + (X ^ D : ℤ[X]).coeff i) (T.coeff i)
    have ht := hTcoeff i
    omega
  · intro i hi hiG
    dsimp [Q]
    rw [coeff_add, coeff_add, hTlow i hiG]
    simp [coeff_one, coeff_X_pow, show i ≠ 0 by omega, show i ≠ D by omega]
  · intro i hi hiD
    have ht : T.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    dsimp [Q]
    rw [coeff_add, coeff_add, ht]
    simp [coeff_one, coeff_X_pow, show i ≠ 0 by omega, show i ≠ D by omega]

/-- For any fixed allowance and any radius above one, there are arbitrarily
large irreducible positive polynomials violating the proposed root-only gap.
No Newman-divisibility conclusion is asserted. -/
theorem arbitrarily_large_root_only_exceptions (ρ : ℝ) (hρ : 1 < ρ) (hρ2 : ρ < 2)
    (B c : ℕ) :
    ∃ Q : ℤ[X], Q.Monic ∧ Irreducible Q ∧ B < Q.natDegree ∧
      Q.coeff 0 = 1 ∧ Q.eval 1 = 2 ∧
      (∃ e : ℕ, Q.eval 3 = (2 : ℤ) ^ e) ∧
      (∀ x : ℝ, 0 ≤ x → 0 < (Q.map (Int.castRingHom ℝ)).eval x) ∧
      (∀ i, |Q.coeff i| ≤ 10) ∧
      (∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, ρ⁻¹ < ‖z‖ ∧ ‖z‖ < ρ) ∧
      (2 : ℤ) ^ c * 8 ^ Q.natDegree < (Q.eval 3) ^ 2 := by
  obtain ⟨g, hg⟩ := pow_unbounded_of_one_lt (11 / (ρ - 1)) hρ
  have hgap : 11 < (ρ - 1) * ρ ^ g := by
    have hh := (div_lt_iff₀ (by linarith : 0 < ρ - 1)).mp hg
    nlinarith only [hh]
  obtain ⟨N, hN⟩ := exponential_dominates_polynomial c
  obtain ⟨m, D, t, hm, hD, hodd, he, hsmall⟩ := positive_perturbation_data (g + 1) (N + B)
  obtain ⟨Q, hQD, hQ0, hQ1, hQ3, hQpos, hQcoeff, hQlow, hQhigh⟩ :=
    perturbation_polynomial (g + 1) D m t (by omega) (by omega) he hsmall
  have hroot : ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots,
      ρ⁻¹ < ‖z‖ ∧ ‖z‖ < ρ := by
    intro z hz
    exact root_annulus_of_end_gaps Q D (g + 1) ρ hQD hQ0 (by omega) (by omega)
      hQcoeff hQlow hQhigh hρ (by simpa using hgap) z
      ((mem_roots (hQD.monic.map _).ne_zero).mp hz)
  have hI := irreducible_of_eval_one_two Q hQD.monic (2 * m) hQ3 hQ1 hQpos
    (fun z hz => (hroot z hz).2.trans hρ2)
  refine ⟨Q, hQD.monic, hI, ?_, hQ0, hQ1, ⟨2 * m, hQ3⟩, hQpos, hQcoeff, hroot, ?_⟩
  · rw [hQD.natDegree_eq]
    omega
  · have hb : 2 ^ c * 8 ^ D < 9 ^ D := by
      calc
        2 ^ c * 8 ^ D ≤ (D + 1) ^ c * 8 ^ D :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
        _ = 8 ^ D * (D + 1) ^ c := Nat.mul_comm _ _
        _ < 9 ^ D := hN D (by omega)
    have hsize : 3 ^ D ≤ 4 ^ m := by omega
    have hval : 9 ^ D ≤ (4 ^ m) ^ 2 := by
      calc
        _ = (3 ^ D) ^ 2 := by rw [← pow_mul, Nat.mul_comm D 2, pow_mul]; norm_num
        _ ≤ _ := Nat.pow_le_pow_left hsize _
    have hh : 2 ^ c * 8 ^ D < (2 ^ (2 * m)) ^ 2 := by
      have heq : 2 ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
      rw [heq]
      exact hb.trans_le hval
    rw [hQD.natDegree_eq, hQ3]
    exact_mod_cast hh

#print axioms perturbation_polynomial
#print axioms arbitrarily_large_root_only_exceptions
end Erdos406Perturbation
