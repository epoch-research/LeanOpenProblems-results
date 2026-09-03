import Submission.PolynomialSquareApproximation

/-! A fixed monic nonsquare polynomial of positive even degree takes square
values at only finitely many natural inputs. The cutoff depends on the
polynomial; this is not a uniform theorem for Erdős406. -/
namespace Erdos406Runge
open Polynomial Filter
open scoped Topology nonZeroDivisors

lemma integer_square_gap (u v : ℤ) (hne : u^2 ≠ v^2) :
    |v| ≤ |u^2-v^2| := by
  have hu := abs_nonneg u
  have hv := abs_nonneg v
  have hneq : |u| ≠ |v| := by
    intro he
    have hh := congrArg (fun x : ℤ => x^2) he
    exact hne (by simpa only [sq_abs] using hh)
  rcases lt_or_gt_of_ne hneq with h | h
  · have hm := mul_nonneg (by omega : 0 ≤ |v|-|u|-1) (by omega : 0 ≤ |v|+|u|)
    have hb := le_abs_self (u^2-v^2)
    have hb' := neg_le_abs (u^2-v^2)
    nlinarith only [hm, hu, hb', sq_abs u, sq_abs v]
  · have hm := mul_nonneg (by omega : 0 ≤ |u|-|v|-1) (by omega : 0 ≤ |u|+|v|)
    have hb := le_abs_self (u^2-v^2)
    nlinarith only [hm, hu, hb, sq_abs u, sq_abs v]

lemma eventually_abs_eval_lt (P Q : ℤ[X]) (hdeg : P.natDegree < Q.natDegree) :
    ∀ᶠ n : ℕ in atTop, |P.eval (n : ℤ)| < |Q.eval (n : ℤ)| := by
  let F := P.map (Int.castRingHom ℚ)
  let G := Q.map (Int.castRingHom ℚ)
  have hd : F.degree < G.degree := by
    dsimp only [F, G]
    rw [degree_map_eq_of_injective Int.cast_injective,
      degree_map_eq_of_injective Int.cast_injective]
    exact degree_lt_degree hdeg
  have hG : G ≠ 0 := by intro h; simp [h] at hd
  have ht := (F.div_tendsto_zero_of_degree_lt G hd).abs
  have hb : ∀ᶠ x : ℚ in atTop, |F.eval x / G.eval x| < 1 :=
    ht.eventually_lt_const (by norm_num)
  have hr := G.eventually_no_roots hG
  have hh : ∀ᶠ x : ℚ in atTop, |F.eval x| < |G.eval x| := by
    filter_upwards [hb, hr] with x hx hne
    rw [abs_div, div_lt_one (abs_pos.mpr hne)] at hx
    exact hx
  have hn := (tendsto_natCast_atTop_atTop (R := ℚ)).eventually hh
  filter_upwards [hn] with n h
  have he (T : ℤ[X]) : (T.map (Int.castRingHom ℚ)).eval (n : ℚ) =
      ((T.eval (n : ℤ) : ℤ) : ℚ) := by
    rw [eval_map]
    simpa using eval₂_at_apply (p := T) (Int.castRingHom ℚ) (n : ℤ)
  dsimp only [F, G] at h
  rw [he P, he Q] at h
  exact_mod_cast h

lemma finite_square_values_of_certificate (P R T : ℤ[X]) (q : ℤ)
    (hT : T = C (q^2) * P - R^2) (hTne : T ≠ 0)
    (hdeg : T.natDegree < R.natDegree) :
    {n : ℕ | IsSquare (P.eval (n : ℤ))}.Finite := by
  have hfinite : {n : ℕ | T.eval (n : ℤ) = 0}.Finite := by
    have hh := (finite_setOf_isRoot hTne).preimage
      (fun a ha b hb h => (Nat.cast_injective (R := ℤ)) h)
    simpa only [Set.preimage_setOf_eq, IsRoot] using hh
  have hn : ∀ᶠ n : ℕ in atTop, T.eval (n : ℤ) ≠ 0 :=
    atTop_le_cofinite hfinite.compl_mem_cofinite
  have hlt := eventually_abs_eval_lt T R hdeg
  have hno : ∀ᶠ n : ℕ in atTop, ¬ IsSquare (P.eval (n : ℤ)) := by
    filter_upwards [hn, hlt] with n hn hlt
    rintro ⟨u, hu⟩
    have he : T.eval (n : ℤ) = (q*u)^2 - (R.eval (n : ℤ))^2 := by
      rw [hT, eval_sub, eval_mul, eval_C, eval_pow, hu]
      ring
    have hs : (q*u)^2 ≠ (R.eval (n : ℤ))^2 := by
      intro hh
      rw [he, hh, sub_self] at hn
      exact hn rfl
    have hb := integer_square_gap (q*u) (R.eval (n : ℤ)) hs
    rw [← he] at hb
    exact (not_le_of_gt hlt) hb
  obtain ⟨N, hN⟩ := eventually_atTop.mp hno
  apply (Set.finite_Iio N).subset
  intro n hn
  change n < N
  by_contra hh
  exact hN n (by omega) hn

lemma clear_polynomial_denominators (Q : ℚ[X]) :
    ∃ q : ℤ, q ≠ 0 ∧ ∃ R : ℤ[X],
      R.map (Int.castRingHom ℚ) = C (q : ℚ) * Q := by
  obtain ⟨q, hq⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) Q
  refine ⟨q.val, (mem_nonZeroDivisors_iff_ne_zero.mp q.property),
    IsLocalization.integerNormalization (nonZeroDivisors ℤ) Q, ?_⟩
  simpa only [Algebra.smul_def, Polynomial.algebraMap_apply] using hq

lemma monic_rational_square_lifts (P : ℤ[X]) (hP : P.Monic)
    (Q : ℚ[X]) (hQ : Q.Monic) (he : P.map (Int.castRingHom ℚ) = Q^2) :
    IsSquare P := by
  have hd : Q ∣ P.map (algebraMap ℤ ℚ) := by
    change Q ∣ P.map (Int.castRingHom ℚ)
    rw [he]
    exact dvd_pow_self Q (by decide)
  obtain ⟨R, hR⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hP hd
  rw [hQ.leadingCoeff, C_1, mul_one] at hR
  change R.map (Int.castRingHom ℚ) = Q at hR
  have hP2 : P = R^2 := by
    apply map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [Polynomial.map_pow, hR, he]
  exact ⟨R, by simpa only [pow_two] using hP2⟩

/-- The elementary Runge argument for monic even-degree polynomials.
The finite set, and hence its bound, depends on the entire polynomial. -/
theorem finite_square_values (P : ℤ[X]) (hP : P.Monic) (d : ℕ)
    (hd : 0 < d) (hdeg : P.natDegree = 2*d) (hns : ¬ IsSquare P) :
    {n : ℕ | IsSquare (P.eval (n : ℤ))}.Finite := by
  let F := P.map (Int.castRingHom ℚ)
  have hF : F.IsMonicOfDegree (2*d) :=
    ⟨(hP.natDegree_map _).trans hdeg, hP.map _⟩
  obtain ⟨Q, hQ, herror⟩ := square_approximation F d hd hF
  obtain ⟨q, hq, R, hR⟩ := clear_polynomial_denominators Q
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  let T : ℤ[X] := C (q^2) * P - R^2
  have hmapT : T.map (Int.castRingHom ℚ) = C ((q : ℚ)^2) * (F - Q^2) := by
    dsimp only [T, F]
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, hR]
    change C (((q^2 : ℤ) : ℚ)) * P.map (Int.castRingHom ℚ) - (C (q : ℚ) * Q)^2 =
      C ((q : ℚ)^2) * (P.map (Int.castRingHom ℚ) - Q^2)
    simp only [Int.cast_pow, map_pow]
    ring
  have hRD : R.natDegree = d := by
    have hh := congrArg natDegree hR
    rw [natDegree_map_eq_of_injective Int.cast_injective, natDegree_C_mul hqQ,
      hQ.natDegree_eq] at hh
    exact hh
  have hTD : T.natDegree = (F-Q^2).natDegree := by
    have hh := congrArg natDegree hmapT
    rw [natDegree_map_eq_of_injective Int.cast_injective,
      natDegree_C_mul (pow_ne_zero 2 hqQ)] at hh
    exact hh
  have hTne : T ≠ 0 := by
    intro hz
    have he : C ((q : ℚ)^2) * (F-Q^2) = 0 := by rw [← hmapT, hz]; simp
    have hn : C ((q : ℚ)^2) ≠ (0 : ℚ[X]) := by simp [hq]
    have hzero := (mul_eq_zero.mp he).resolve_left hn
    exact hns (monic_rational_square_lifts P hP Q hQ.monic (sub_eq_zero.mp hzero))
  exact finite_square_values_of_certificate P R T q rfl hTne (by
    rw [hTD, hRD]
    exact herror)

/-- The corresponding finiteness theorem over all integer inputs. -/
theorem finite_integer_square_values (P : ℤ[X]) (hP : P.Monic) (d : ℕ)
    (hd : 0 < d) (hdeg : P.natDegree = 2*d) (hns : ¬ IsSquare P) :
    {n : ℤ | IsSquare (P.eval n)}.Finite := by
  let F := P.comp (-X)
  have hFm : F.Monic := by
    change (P.comp (-X)).leadingCoeff = 1
    rw [comp_neg_X_leadingCoeff_eq, hP.leadingCoeff, hdeg, pow_mul]
    norm_num
  have hFD : F.natDegree = 2*d := by simp [F, natDegree_comp, hdeg]
  have hFns : ¬ IsSquare F := by
    rintro ⟨Q, he⟩
    have hh := congrArg (fun R : ℤ[X] => R.comp (-X)) he
    change (P.comp (-X)).comp (-X) = (Q*Q).comp (-X) at hh
    rw [comp_neg_X_comp_neg_X, mul_comp] at hh
    exact hns ⟨Q.comp (-X), hh⟩
  have hpos := finite_square_values P hP d hd hdeg hns
  have hneg := finite_square_values F hFm d hd hFD hFns
  apply ((hpos.image (fun n : ℕ => (n : ℤ))).union
    (hneg.image (fun n : ℕ => -(n : ℤ)))).subset
  intro n hn
  cases n with
  | ofNat n => exact Or.inl ⟨n, hn, rfl⟩
  | negSucc n =>
    right
    refine ⟨n+1, ?_, rfl⟩
    change IsSquare ((P.comp (-X)).eval ((n+1 : ℕ) : ℤ))
    rw [eval_comp, eval_neg, eval_X]
    exact hn

#print axioms finite_integer_square_values
#print axioms finite_square_values
#print axioms finite_square_values_of_certificate
end Erdos406Runge
