import Submission.PolynomialLocalSquareApproximation
import Submission.PolynomialSquareValues

/-! Finiteness of square values of a fixed normalized nonsquare polynomial
at powers of three. Unlike the approximation-at-infinity argument, this
local argument has no parity restriction on the degree. The cutoff is
not uniform as the polynomial varies. -/
namespace Erdos406LocalRunge
open Polynomial Filter Erdos406Runge

lemma monic_rational_isSquare_lifts (P : ℤ[X]) (hm : P.Monic)
    (hs : IsSquare (P.map (Int.castRingHom ℚ))) : IsSquare P := by
  obtain ⟨Q, hQ⟩ := hs
  have he : P.map (Int.castRingHom ℚ) = Q^2 := by simpa [pow_two] using hQ
  have hl : Q.leadingCoeff^2 = 1 := by
    have hh := congrArg leadingCoeff he
    simpa only [(hm.map (Int.castRingHom ℚ)).leadingCoeff, leadingCoeff_pow] using hh.symm
  rcases sq_eq_one_iff.mp hl with h | h
  · exact monic_rational_square_lifts P hm Q h he
  · apply monic_rational_square_lifts P hm (-Q)
    · change (-Q).leadingCoeff = 1
      rw [leadingCoeff_neg, h]
      norm_num
    · simpa using he

lemma monic_scaled_square_lifts (P R : ℤ[X]) (hm : P.Monic)
    (q : ℤ) (hq : q ≠ 0) (he : C (q^2) * P = R^2) : IsSquare P := by
  apply monic_rational_isSquare_lifts P hm
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hh := congrArg (fun F : ℤ[X] => F.map (Int.castRingHom ℚ)) he
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow] at hh
  change C ((q : ℚ)^2) * P.map (Int.castRingHom ℚ) =
    (R.map (Int.castRingHom ℚ))^2 at hh
  refine ⟨C ((q : ℚ)⁻¹) * R.map (Int.castRingHom ℚ), ?_⟩
  rw [← pow_two]
  symm
  calc
    _ = C ((q : ℚ)⁻¹)^2 * (R.map (Int.castRingHom ℚ))^2 := by ring
    _ = C ((q : ℚ)⁻¹)^2 * (C ((q : ℚ)^2) * P.map (Int.castRingHom ℚ)) := by rw [hh]
    _ = P.map (Int.castRingHom ℚ) := by
      rw [← map_pow, ← mul_assoc, ← C_mul, ← mul_pow, inv_mul_cancel₀ hqQ]
      simp

lemma three_power_square_congruence (u v : ℤ) (N : ℕ)
    (hv : ¬ (3 : ℤ) ∣ v) (hd : (3 : ℤ)^N ∣ u^2-v^2) :
    (3 : ℤ)^N ∣ u-v ∨ (3 : ℤ)^N ∣ u+v := by
  have hp : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)
  have hd' : (3 : ℤ)^N ∣ (u-v)*(u+v) := by convert hd using 1; ring
  by_cases h : (3 : ℤ) ∣ u-v
  · have hn : ¬ (3 : ℤ) ∣ u+v := by
      intro hh
      have h2 : (3 : ℤ) ∣ 2*v := by
        convert dvd_sub hh h using 1; ring
      exact hv ((hp.dvd_mul.mp h2).resolve_left (by decide))
    exact Or.inl (hp.pow_dvd_of_dvd_mul_right N hn hd')
  · exact Or.inr (hp.pow_dvd_of_dvd_mul_left N h hd')

lemma ternary_eval_not_dvd_three (R : ℤ[X]) (s L : ℕ)
    (h0 : R.coeff 0 = (2 : ℤ)^s) (hL : 0 < L) :
    ¬ (3 : ℤ) ∣ R.eval ((3 : ℤ)^L) := by
  have hh := sub_dvd_eval_sub ((3 : ℤ)^L) 0 R
  simp only [sub_zero, ← coeff_zero_eq_eval_zero, h0] at hh
  have h3 : (3 : ℤ) ∣ (3 : ℤ)^L := dvd_pow_self _ (by omega)
  intro hd
  have ht : (3 : ℤ) ∣ (2 : ℤ)^s := by
    convert dvd_sub hd (h3.trans hh) using 1; ring
  have hp : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)
  exact (by decide : ¬ (3 : ℤ) ∣ 2) (hp.dvd_of_dvd_pow ht)

lemma integer_abs_le_square (z : ℤ) : |z| ≤ z^2 := by
  by_cases hz : z = 0
  · simp [hz]
  have hpos := abs_pos.mpr hz
  have hm := mul_nonneg (by omega : 0 ≤ |z|) (by omega : 0 ≤ |z|-1)
  nlinarith only [hm, sq_abs z]

lemma integer_eq_zero_of_dvd_small (d z : ℤ) (hd : d ∣ z) (hb : |z| < |d|) : z = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hb
  exact_mod_cast hb

/-- A local certificate forces square values to be polynomial roots, once
its prime-power argument is large enough. -/
theorem finite_ternary_square_values_of_certificate (P R : ℤ[X]) (s n : ℕ)
    (hP : P.natDegree ≤ n) (hR : R.natDegree ≤ n)
    (h0 : R.coeff 0 = (2 : ℤ)^s)
    (hd : X^(n+1) ∣ C ((2 : ℤ)^(2*s)) * P - R^2)
    (hne : C ((2 : ℤ)^(2*s)) * P - R^2 ≠ 0) :
    {L : ℕ | IsSquare (P.eval ((3 : ℤ)^L))}.Finite := by
  let q : ℤ := 2^s
  let T : ℤ[X] := C (q^2) * P - R^2
  have hq : (2 : ℤ)^(2*s) = q^2 := by dsimp [q]; rw [Nat.mul_comm 2 s, pow_mul]
  have hTne : T ≠ 0 := by simpa only [T, hq] using hne
  have hdivT : X^(n+1) ∣ T := by simpa only [T, hq] using hd
  have hfinite : {x : ℕ | T.eval (x : ℤ) = 0}.Finite := by
    have hh := (finite_setOf_isRoot hTne).preimage
      (fun a ha b hb h => (Nat.cast_injective (R := ℤ)) h)
    simpa only [Set.preimage_setOf_eq, IsRoot] using hh
  have hn : ∀ᶠ x : ℕ in atTop, T.eval (x : ℤ) ≠ 0 :=
    atTop_le_cofinite hfinite.compl_mem_cofinite
  have hbP := eventually_abs_eval_lt (C (2*q^2) * P) (X^(n+1)) (by
    rw [natDegree_X_pow]
    exact lt_of_le_of_lt (natDegree_C_mul_le _ _) (by omega))
  have hbR := eventually_abs_eval_lt (C (2 : ℤ) * R) (X^(n+1)) (by
    rw [natDegree_X_pow]
    exact lt_of_le_of_lt (natDegree_C_mul_le _ _) (by omega))
  have hevent : ∀ᶠ x : ℕ in atTop,
      T.eval (x : ℤ) ≠ 0 ∧
      |2*q^2*P.eval (x : ℤ)| < (x : ℤ)^(n+1) ∧
      |2*R.eval (x : ℤ)| < (x : ℤ)^(n+1) := by
    filter_upwards [hn, hbP, hbR] with x hn hp hr
    simp only [eval_mul, eval_C, eval_pow, eval_X,
      abs_of_nonneg (pow_nonneg (Int.natCast_nonneg x) _)] at hp hr
    exact ⟨hn, hp, hr⟩
  have hpow := (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (3 : ℕ))).eventually hevent
  have hno : ∀ᶠ L : ℕ in atTop, ¬ IsSquare (P.eval ((3 : ℤ)^L)) := by
    filter_upwards [hpow, eventually_gt_atTop 0] with L he hL
    simp only [Nat.cast_pow, Nat.cast_ofNat] at he
    obtain ⟨hn, hbP, hbR⟩ := he
    rintro ⟨y, hy⟩
    have hy' : P.eval ((3 : ℤ)^L) = y^2 := by simpa only [pow_two] using hy
    let u : ℤ := q*y
    let v : ℤ := R.eval ((3 : ℤ)^L)
    let M : ℤ := ((3 : ℤ)^L)^(n+1)
    have hM : 0 < M := by dsimp [M]; positivity
    have hTe : T.eval ((3 : ℤ)^L) = u^2-v^2 := by
      dsimp [T, u, v]
      rw [eval_sub, eval_mul, eval_C, eval_pow, hy']
      ring
    have hdu : M ∣ u^2-v^2 := by
      have hh := eval_dvd (x := (3 : ℤ)^L) hdivT
      simpa only [eval_pow, eval_X, hTe] using hh
    have hsum : |u|+|v| < M := by
      have hPu : |2*q^2*P.eval ((3 : ℤ)^L)| = 2*u^2 := by
        rw [hy']
        have he : 2*q^2*y^2 = 2*u^2 := by dsimp [u]; ring
        rw [he, abs_of_nonneg (by positivity)]
      have hRv : |2*R.eval ((3 : ℤ)^L)| = 2*|v| := by simp [v, abs_mul]
      rw [hPu] at hbP
      rw [hRv] at hbR
      have hh := integer_abs_le_square u
      change 2*u^2 < M at hbP
      change 2*|v| < M at hbR
      omega
    have hv : ¬ (3 : ℤ) ∣ v := ternary_eval_not_dvd_three R s L h0 hL
    have hh := three_power_square_congruence u v (L*(n+1)) hv (by
      simpa only [pow_mul] using hdu)
    have hsmall (z : ℤ) (hz : M ∣ z) (hb : |z| ≤ |u|+|v|) : z = 0 := by
      apply integer_eq_zero_of_dvd_small M z hz
      rw [abs_of_pos hM]
      exact hb.trans_lt hsum
    have heq : u^2-v^2 = 0 := by
      rcases hh with hh | hh
      · have hz := hsmall (u-v) (by simpa only [pow_mul] using hh) (abs_sub _ _)
        rw [sub_eq_zero.mp hz, sub_self]
      · have hz := hsmall (u+v) (by simpa only [pow_mul] using hh) (abs_add_le _ _)
        have hu : u = -v := by omega
        simp [hu]
    exact hn (hTe.trans heq)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hno
  apply (Set.finite_Iio N).subset
  intro L hL
  change L < N
  by_contra hh
  exact hN L (by omega) hL

/-- No parity restriction on the fixed polynomial's degree is needed. -/
theorem finite_ternary_square_values (P : ℤ[X]) (hm : P.Monic)
    (h0 : P.coeff 0 = 1) (hns : ¬ IsSquare P) :
    {L : ℕ | IsSquare (P.eval ((3 : ℤ)^L))}.Finite := by
  obtain ⟨s, R, hR, hR0, hdiv⟩ := local_square_approximation P h0 P.natDegree
  apply finite_ternary_square_values_of_certificate P R s P.natDegree le_rfl hR hR0 hdiv
  intro hz
  apply hns
  apply monic_scaled_square_lifts P R hm ((2 : ℤ)^s) (by positivity)
  have he := sub_eq_zero.mp hz
  simpa only [← pow_mul, Nat.mul_comm s 2] using he

#print axioms finite_ternary_square_values
end Erdos406LocalRunge
