import Submission.PositivePerturbationPolynomials

/-! Taylor-coefficient bounds alone do not give the missing factor gap.
The polynomials constructed here are not claimed to have coefficients 0/1,
and are not counterexamples to Erdős 406. -/
namespace Erdos406Taylor
open Polynomial Finset Erdos406Perturbation Erdos406Cyclotomic
  Erdos406EventualFactorBound Erdos406FactorParity Erdos406EndGapRoots
  Erdos406EvaluationIrreducible

lemma taylor_one_coeff_sum (P : ℤ[X]) (M : ℕ) (hM : P.natDegree < M) (j : ℕ) :
    (taylor 1 P).coeff j = ∑ i ∈ range M, P.coeff i * (i.choose j : ℤ) := by
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow' hM]
  simp only [map_sum, taylor_mul, taylor_C, taylor_X_pow, C_1, finset_sum_coeff,
    coeff_C_mul, coeff_X_add_one_pow]

lemma hockey_stick (M j : ℕ) :
    (∑ i ∈ range M, i.choose j) = M.choose (j + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih, Nat.choose_succ_succ]
    simp only [Nat.succ_eq_add_one]
    omega

lemma taylor_one_coeff_bounds (P : ℤ[X]) (M H : ℕ) (hM : P.natDegree < M)
    (hP : ∀ i, 0 ≤ P.coeff i ∧ P.coeff i ≤ H) (j : ℕ) :
    0 ≤ (taylor 1 P).coeff j ∧
      (taylor 1 P).coeff j ≤ H * (M.choose (j + 1) : ℤ) := by
  rw [taylor_one_coeff_sum P M hM]
  constructor
  · exact sum_nonneg (fun i _ => mul_nonneg (hP i).1 (by positivity))
  · calc
      _ ≤ ∑ i ∈ range M, (H : ℤ) * (i.choose j : ℤ) := by
        apply sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hP i).2 (by positivity)
      _ = _ := by rw [← mul_sum, ← Nat.cast_sum, hockey_stick]

lemma newman_taylor_bounds (P : ℤ[X]) (D : ℕ) (hP : P.IsMonicOfDegree D)
    (hc : ∀ i, 0 ≤ P.coeff i ∧ P.coeff i ≤ 1) (j : ℕ) :
    (D.choose j : ℤ) ≤ (taylor 1 P).coeff j ∧
      (taylor 1 P).coeff j ≤ ((D + 1).choose (j + 1) : ℤ) := by
  have hM : P.natDegree < D + 1 := by rw [hP.natDegree_eq]; omega
  constructor
  · rw [taylor_one_coeff_sum P (D + 1) hM]
    have hh := single_le_sum (f := fun i => P.coeff i * (i.choose j : ℤ))
      (fun i (_ : i ∈ range (D + 1)) => mul_nonneg (hc i).1 (by positivity))
      (show D ∈ range (D + 1) by simp)
    have hlead : P.coeff D = 1 := by
      rw [← hP.natDegree_eq, coeff_natDegree, hP.monic.leadingCoeff]
    simpa [hlead] using hh
  · simpa using (taylor_one_coeff_bounds P (D + 1) 1 hM hc j).2

lemma triple_pascal_bound (d j : ℕ) :
    3 * d.choose (j + 1) ≤ (d + 3).choose (j + 3) := by
  have h1 := Nat.choose_succ_succ (d + 2) (j + 2)
  have h2 := Nat.choose_succ_succ (d + 1) (j + 1)
  have h3 := Nat.choose_succ_succ (d + 1) (j + 2)
  have h4 := Nat.choose_succ_succ d j
  have h5 := Nat.choose_succ_succ d (j + 1)
  have h6 := Nat.choose_succ_succ d (j + 2)
  simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] at *
  omega

lemma perturbation_taylor_bounds (R : ℤ[X]) (D : ℕ) (hD : 4 ≤ D)
    (hRdeg : R.natDegree < D - 3)
    (hR : ∀ i, 0 ≤ R.coeff i ∧ R.coeff i ≤ 2) (j : ℕ) :
    (D.choose j : ℤ) ≤ (taylor 1 (1 + X ^ D + (X - 1) ^ 2 * R)).coeff j ∧
      (taylor 1 (1 + X ^ D + (X - 1) ^ 2 * R)).coeff j ≤
        ((D + 1).choose (j + 1) : ℤ) := by
  have he : taylor 1 (1 + X ^ D + (X - 1) ^ 2 * R) =
      1 + (X + 1) ^ D + X ^ 2 * taylor 1 R := by simp
  rw [he, coeff_add, coeff_add, coeff_X_add_one_pow]
  rcases j with _ | j
  · simp only [coeff_one_zero, coeff_X_pow_mul', Nat.choose_zero_right,
      Nat.cast_one, show ¬2 ≤ 0 by omega, ite_false, add_zero]
    norm_num
    omega
  rcases j with _ | j
  · simp only [coeff_one, show (1 : ℕ) ≠ 0 by omega, ite_false,
      coeff_X_pow_mul', show ¬2 ≤ 1 by omega, ite_false, zero_add, add_zero]
    constructor
    · rfl
    · exact_mod_cast Nat.choose_le_succ D 1 |>.trans (by
        simpa using Nat.choose_le_succ_of_lt_half_left (n := D + 1) (r := 1) (by omega))
  · have hj : j + 1 + 1 - 2 = j := by omega
    simp only [coeff_one, show j + 1 + 1 ≠ 0 by omega, ite_false, zero_add,
      coeff_X_pow_mul', show 2 ≤ j + 1 + 1 by omega, ite_true, hj]
    have hb := taylor_one_coeff_bounds R (D - 3) 2 hRdeg hR j
    norm_num only [Nat.cast_ofNat] at hb
    have hp := triple_pascal_bound (D - 3) j
    have heD : D - 3 + 3 = D := by omega
    rw [heD] at hp
    have hpZ : 3 * ((D - 3).choose (j + 1) : ℤ) ≤ (D.choose (j + 3) : ℤ) :=
      by exact_mod_cast hp
    have hpas := Nat.choose_succ_succ D (j + 2)
    have hpasZ : ((D + 1).choose (j + 3) : ℤ) =
        (D.choose (j + 2) : ℤ) + (D.choose (j + 3) : ℤ) := by exact_mod_cast hpas
    constructor
    · linarith [hb.1]
    · have hz : 0 ≤ ((D - 3).choose (j + 1) : ℤ) := by positivity
      simpa only [Nat.add_assoc, Nat.reduceAdd] using
        (show (D.choose (j + 2) : ℤ) + (taylor 1 R).coeff j ≤
          ((D + 1).choose (j + 3) : ℤ) by linarith [hb.2])

noncomputable def binaryPrefix (P : ℤ[X]) (s : ℕ) : ℤ :=
  ∑ j ∈ range s, (taylor 1 P).coeff j * 2 ^ j

lemma eval_three_binaryPrefix (P : ℤ[X]) (s : ℕ) :
    P.eval 3 = binaryPrefix P s +
      ∑ j ∈ range (P.natDegree + 1), (taylor 1 P).coeff (s + j) * 2 ^ (s + j) := by
  have hd : (taylor 1 P).natDegree < s + (P.natDegree + 1) := by
    rw [natDegree_taylor]
    omega
  have he : P.eval 3 = (taylor 1 P).eval 2 := by rw [taylor_eval]; norm_num
  rw [he, eval_eq_sum_range' hd, sum_range_add]
  rfl

lemma binaryPrefix_dvd_of_eval_power (P : ℤ[X]) (e : ℕ)
    (he : P.eval 3 = (2 : ℤ) ^ e) (s : ℕ) (hs : s ≤ e) :
    (2 : ℤ) ^ s ∣ binaryPrefix P s := by
  have htail : (2 : ℤ) ^ s ∣
      ∑ j ∈ range (P.natDegree + 1), (taylor 1 P).coeff (s + j) * 2 ^ (s + j) := by
    apply dvd_sum
    intro j _
    exact dvd_mul_of_dvd_right (pow_dvd_pow 2 (by omega : s ≤ s + j)) _
  have htotal : (2 : ℤ) ^ s ∣ P.eval 3 := by rw [he]; exact pow_dvd_pow 2 hs
  have hd := dvd_sub htotal htail
  rw [eval_three_binaryPrefix P s, add_sub_cancel_right] at hd
  exact hd

lemma binary_carry_system (P : ℤ[X]) (e : ℕ)
    (he : P.eval 3 = (2 : ℤ) ^ e)
    (hA : ∀ j, 0 ≤ (taylor 1 P).coeff j) :
    ∃ C : ℕ → ℤ, C 0 = 0 ∧
      (∀ j, j ≤ e → 0 ≤ C j ∧ binaryPrefix P j = 2 ^ j * C j) ∧
      (∀ j, j < e → 2 * C (j + 1) = C j + (taylor 1 P).coeff j) := by
  let C : ℕ → ℤ := fun j => binaryPrefix P j / 2 ^ j
  have hC (j : ℕ) (hj : j ≤ e) : binaryPrefix P j = 2 ^ j * C j := by
    exact (Int.mul_ediv_cancel' (binaryPrefix_dvd_of_eval_power P e he j hj)).symm
  refine ⟨C, ?_, ?_, ?_⟩
  · simp [C, binaryPrefix]
  · intro j hj
    refine ⟨?_, hC j hj⟩
    apply Int.ediv_nonneg
    · exact sum_nonneg (fun i _ => mul_nonneg (hA i) (by positivity))
    · positivity
  · intro j hj
    have hh : binaryPrefix P (j + 1) =
        binaryPrefix P j + (taylor 1 P).coeff j * 2 ^ j := by
      exact sum_range_succ _ _
    rw [hC (j + 1) (by omega), hC j (by omega), pow_succ] at hh
    apply mul_left_cancel₀ (show (2 : ℤ) ^ j ≠ 0 by positivity)
    nlinarith only [hh]

lemma binary_carry_terminal (P : ℤ[X]) (e : ℕ) (hD : P.natDegree < e)
    (he : P.eval 3 = (2 : ℤ) ^ e) : binaryPrefix P e / 2 ^ e = 1 := by
  have hA : (taylor 1 P).natDegree < e := by simpa using hD
  have hh : binaryPrefix P e = P.eval 3 := by
    rw [← show (taylor 1 P).eval 2 = P.eval 3 by rw [taylor_eval]; norm_num]
    exact (eval_eq_sum_range' hA 2).symm
  rw [hh, he]
  exact Int.ediv_self (by positivity)

lemma eq_zero_of_nonneg_eval_one_zero (P : ℤ[X])
    (hc : ∀ i, 0 ≤ P.coeff i) (he : P.eval 1 = 0) : P = 0 := by
  have hs : (∑ i ∈ range (P.natDegree + 1), P.coeff i) = 0 := by
    have hh := taylor_one_coeff_sum P (P.natDegree + 1) (by omega) 0
    simpa [he] using hh.symm
  have hzero := (sum_eq_zero_iff_of_nonneg (fun i _ => hc i)).mp hs
  ext i
  rw [coeff_zero]
  by_cases hi : i < P.natDegree + 1
  · exact hzero i (mem_range.mpr hi)
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

lemma nonneg_eval_one_two_shape (P : ℤ[X]) (D : ℕ) (hD : 0 < D)
    (hP : P.IsMonicOfDegree D) (hP0 : P.coeff 0 = 1) (hP1 : P.eval 1 = 2)
    (hc : ∀ i, 0 ≤ P.coeff i) : P = 1 + X ^ D := by
  have hlead : P.coeff D = 1 := by
    rw [← hP.natDegree_eq, coeff_natDegree, hP.monic.leadingCoeff]
  have hz : P - 1 - X ^ D = 0 := by
    apply eq_zero_of_nonneg_eval_one_zero
    · intro i
      rw [coeff_sub, coeff_sub]
      by_cases hi0 : i = 0
      · subst i
        simp [hP0, coeff_X_pow, ne_of_lt hD]
      by_cases hiD : i = D
      · subst i
        simp [hlead, coeff_one, ne_of_gt hD]
      · simpa [coeff_one, coeff_X_pow, hi0, hiD] using hc i
    · simp [hP1]
  linear_combination hz

/-- These pure-power-valued polynomials with value two at one must actually
have a negative coefficient once their degree exceeds one. -/
lemma negative_coeff_of_eval_one_two (P : ℤ[X]) (hP : P.Monic)
    (hD : 1 < P.natDegree) (hP0 : P.coeff 0 = 1) (hP1 : P.eval 1 = 2)
    (e : ℕ) (hP3 : P.eval 3 = (2 : ℤ) ^ e) : ∃ i, P.coeff i < 0 := by
  by_contra hn
  push_neg at hn
  have he := nonneg_eval_one_two_shape P P.natDegree (by omega)
    ⟨rfl, hP⟩ hP0 hP1 hn
  rw [he] at hP3
  simp only [eval_add, eval_one, eval_pow, eval_X] at hP3
  have hh : 3 ^ P.natDegree + 1 = 2 ^ e := by
    exact_mod_cast (show (3 : ℤ) ^ P.natDegree + 1 = 2 ^ e by linarith)
  have hD1 := Erdos406Structure.three_pow_add_one_dvd_two_pow
    (a := P.natDegree) (k := e) (by omega) (by rw [hh])
  omega

lemma perturbation_polynomial_with_taylor (G D m t : ℕ) (hG : 0 < G) (hD : 3 * G + 3 ≤ D)
    (he : 4 ^ m = 1 + 3 ^ D + 4 * (3 ^ G * t))
    (hsmall : 3 ^ G * t < 3 ^ (D - (2 * G + 1))) :
    ∃ Q : ℤ[X], Q.IsMonicOfDegree D ∧ Q.coeff 0 = 1 ∧ Q.eval 1 = 2 ∧
      Q.eval 3 = (2 : ℤ) ^ (2 * m) ∧
      (∀ x : ℝ, 0 ≤ x → 0 < (Q.map (Int.castRingHom ℝ)).eval x) ∧
      (∀ i, |Q.coeff i| ≤ 10) ∧
      (∀ i, 0 < i → i < G → Q.coeff i = 0) ∧
      (∀ i, D - G < i → i < D → Q.coeff i = 0) ∧
      (∀ j, (D.choose j : ℤ) ≤ (taylor 1 Q).coeff j ∧
        (taylor 1 Q).coeff j ≤ ((D + 1).choose (j + 1) : ℤ)) := by
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
  refine ⟨Q, hQD, hQ0, hQ1, hQ3, ?_, ?_, ?_, ?_, ?_⟩
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

  · intro j
    exact perturbation_taylor_bounds R D (by omega) (by omega) hRcoeff j

theorem arbitrarily_large_taylor_bound_exceptions (ρ : ℝ) (hρ : 1 < ρ) (hρ2 : ρ < 2)
    (B c : ℕ) :
    ∃ Q : ℤ[X], Q.Monic ∧ Irreducible Q ∧ B < Q.natDegree ∧
      Q.coeff 0 = 1 ∧ Q.eval 1 = 2 ∧
      (∃ e : ℕ, Q.eval 3 = (2 : ℤ) ^ e) ∧
      (∃ i, Q.coeff i < 0) ∧
      (∀ x : ℝ, 0 ≤ x → 0 < (Q.map (Int.castRingHom ℝ)).eval x) ∧
      (∀ i, |Q.coeff i| ≤ 10) ∧
      (∀ j, (Q.natDegree.choose j : ℤ) ≤ (taylor 1 Q).coeff j ∧
        (taylor 1 Q).coeff j ≤ ((Q.natDegree + 1).choose (j + 1) : ℤ)) ∧
      (∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, ρ⁻¹ < ‖z‖ ∧ ‖z‖ < ρ) ∧
      (2 : ℤ) ^ c * 8 ^ Q.natDegree < (Q.eval 3) ^ 2 := by
  obtain ⟨g, hg⟩ := pow_unbounded_of_one_lt (11 / (ρ - 1)) hρ
  have hgap : 11 < (ρ - 1) * ρ ^ g := by
    have hh := (div_lt_iff₀ (by linarith : 0 < ρ - 1)).mp hg
    nlinarith only [hh]
  obtain ⟨N, hN⟩ := exponential_dominates_polynomial c
  obtain ⟨m, D, t, hm, hD, hodd, he, hsmall⟩ := positive_perturbation_data (g + 1) (N + B)
  obtain ⟨Q, hQD, hQ0, hQ1, hQ3, hQpos, hQcoeff, hQlow, hQhigh, hQtaylor⟩ :=
    perturbation_polynomial_with_taylor (g + 1) D m t (by omega) (by omega) he hsmall
  have hroot : ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots,
      ρ⁻¹ < ‖z‖ ∧ ‖z‖ < ρ := by
    intro z hz
    exact root_annulus_of_end_gaps Q D (g + 1) ρ hQD hQ0 (by omega) (by omega)
      hQcoeff hQlow hQhigh hρ (by simpa using hgap) z
      ((mem_roots (hQD.monic.map _).ne_zero).mp hz)
  have hI := irreducible_of_eval_one_two Q hQD.monic (2 * m) hQ3 hQ1 hQpos
    (fun z hz => (hroot z hz).2.trans hρ2)
  refine ⟨Q, hQD.monic, hI, ?_, hQ0, hQ1, ⟨2 * m, hQ3⟩,
    negative_coeff_of_eval_one_two Q hQD.monic (by rw [hQD.natDegree_eq]; omega)
      hQ0 hQ1 (2 * m) hQ3, hQpos, hQcoeff,
    by simpa only [hQD.natDegree_eq] using hQtaylor, hroot, ?_⟩
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

#print axioms binary_carry_system
#print axioms binary_carry_terminal
#print axioms binaryPrefix_dvd_of_eval_power
#print axioms newman_taylor_bounds
#print axioms negative_coeff_of_eval_one_two
#print axioms arbitrarily_large_taylor_bound_exceptions
end Erdos406Taylor
