import Submission.PolynomialRadiusCertificates

/-! Degree-independent root bounds from bounded coefficients and long zero
blocks at both ends. These do not assert Newman divisibility. -/
namespace Erdos406EndGapRoots
open Polynomial

lemma eval_norm_geom_bound (P : ℤ[X]) (H : ℝ) (_hH : 0 ≤ H)
    (hcoeff : ∀ i, |(P.coeff i : ℝ)| ≤ H) (z : ℂ) (hz : 1 < ‖z‖) :
    ‖(P.map (Int.castRingHom ℂ)).eval z‖ * (‖z‖ - 1) ≤
      H * (‖z‖ ^ (P.natDegree + 1) - 1) := by
  have hb : ‖(P.map (Int.castRingHom ℂ)).eval z‖ ≤
      H * ∑ i ∈ Finset.range (P.natDegree + 1), ‖z‖ ^ i := by
    rw [eval_map, eval₂_eq_sum_range]
    calc
      _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖((P.coeff i : ℤ) : ℂ) * z ^ i‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), H * ‖z‖ ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [norm_mul, norm_pow, Complex.norm_intCast]
        exact mul_le_mul_of_nonneg_right (hcoeff i) (by positivity)
      _ = _ := (Finset.mul_sum ..).symm
  have hh := mul_le_mul_of_nonneg_right hb (by linarith : 0 ≤ ‖z‖ - 1)
  rwa [mul_assoc, geom_sum_mul] at hh

lemma root_norm_lt_of_leading_gap (Q P : ℤ[X]) (D g : ℕ) (ρ H : ℝ)
    (hQ : Q = X ^ D + P) (hdegree : P.natDegree + g < D)
    (hcoeff : ∀ i, |(P.coeff i : ℝ)| ≤ H) (hH : 0 ≤ H)
    (hρ : 1 < ρ) (hgap : H < (ρ - 1) * ρ ^ g)
    (z : ℂ) (hz : (Q.map (Int.castRingHom ℂ)).eval z = 0) : ‖z‖ < ρ := by
  by_contra hh
  have hr : ρ ≤ ‖z‖ := le_of_not_gt hh
  have hr1 : 1 < ‖z‖ := hρ.trans_le hr
  have hnorm : ‖(P.map (Int.castRingHom ℂ)).eval z‖ = ‖z‖ ^ D := by
    rw [hQ, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      eval_add, eval_pow, eval_X] at hz
    have he : (P.map (Int.castRingHom ℂ)).eval z = -(z ^ D) := by
      exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hz)
    rw [he, norm_neg, norm_pow]
  have hb := eval_norm_geom_bound P H hH hcoeff z hr1
  rw [hnorm] at hb
  have hp : ‖z‖ ^ (P.natDegree + 1 + g) ≤ ‖z‖ ^ D :=
    pow_le_pow_right₀ hr1.le (by omega)
  have hpg : ρ ^ g ≤ ‖z‖ ^ g := pow_le_pow_left₀ (by linarith) hr g
  have hcoef : H < (‖z‖ - 1) * ‖z‖ ^ g := by
    exact hgap.trans_le (mul_le_mul (by linarith) hpg (by positivity) (by linarith))
  have hmul := mul_lt_mul_of_pos_left hcoef (pow_pos (by linarith : 0 < ‖z‖)
    (P.natDegree + 1))
  have hp' := mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ ‖z‖ - 1)
  rw [pow_add] at hp'
  nlinarith

/-- Removing the leading term leaves the prescribed high-end zero block. -/
lemma remainder_degree_bound (Q : ℤ[X]) (D G : ℕ)
    (hQ : Q.IsMonicOfDegree D) (_hG : G ≤ D)
    (hhigh : ∀ i, D - G < i → i < D → Q.coeff i = 0) :
    (Q - X ^ D).natDegree ≤ D - G := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_sub]
  by_cases hiD : i = D
  · subst i
    simp [coeff_X_pow, ← hQ.natDegree_eq, hQ.monic.coeff_natDegree]
  · have hx : (X ^ D : ℤ[X]).coeff i = 0 := by simp [coeff_X_pow, hiD]
    rw [hx, sub_zero]
    rcases lt_or_gt_of_ne hiD with hlt | hgt
    · exact hhigh i hi hlt
    · exact coeff_eq_zero_of_natDegree_lt (by rw [hQ.natDegree_eq]; exact hgt)

lemma reverse_isMonicOfDegree (Q : ℤ[X]) (D : ℕ)
    (hQ : Q.IsMonicOfDegree D) (hzero : Q.coeff 0 = 1) :
    Q.reverse.IsMonicOfDegree D := by
  have hc : Q.reverse.coeff D = 1 := by
    rw [coeff_reverse, hQ.natDegree_eq, revAt_le le_rfl, Nat.sub_self, hzero]
  have hd : Q.reverse.natDegree = D := by
    apply le_antisymm
    · exact Q.reverse_natDegree_le.trans hQ.natDegree_eq.le
    · exact le_natDegree_of_ne_zero (by rw [hc]; norm_num)
  refine ⟨hd, ?_⟩
  change Q.reverse.leadingCoeff = 1
  rwa [leadingCoeff, hd]

/-- Long zero blocks at both ends force all roots into an arbitrarily thin
annulus. The coefficient bound here is deliberately coarse. -/
theorem root_annulus_of_end_gaps (Q : ℤ[X]) (D G : ℕ) (ρ : ℝ)
    (hQ : Q.IsMonicOfDegree D) (hzero : Q.coeff 0 = 1)
    (hGpos : 0 < G) (hGD : G ≤ D)
    (hcoeff : ∀ i, |Q.coeff i| ≤ 10)
    (hlow : ∀ i, 0 < i → i < G → Q.coeff i = 0)
    (hhigh : ∀ i, D - G < i → i < D → Q.coeff i = 0)
    (hρ : 1 < ρ) (hgap : 11 < (ρ - 1) * ρ ^ (G - 1))
    (z : ℂ) (hz : (Q.map (Int.castRingHom ℂ)).eval z = 0) :
    ρ⁻¹ < ‖z‖ ∧ ‖z‖ < ρ := by
  have upper (P : ℤ[X]) (hP : P.IsMonicOfDegree D)
      (hb : ∀ i, |P.coeff i| ≤ 10)
      (hh : ∀ i, D - G < i → i < D → P.coeff i = 0)
      (w : ℂ) (hw : (P.map (Int.castRingHom ℂ)).eval w = 0) : ‖w‖ < ρ := by
    apply root_norm_lt_of_leading_gap P (P - X ^ D) D (G - 1) ρ 11
      (by ring) _ _ (by norm_num) hρ hgap w hw
    · have hd := remainder_degree_bound P D G hP hGD hh
      omega
    · intro i
      rw [coeff_sub]
      have hb' : |(P.coeff i : ℝ)| ≤ 10 := by exact_mod_cast hb i
      have hx : |(((X ^ D : ℤ[X]).coeff i : ℤ) : ℝ)| ≤ 1 := by
        simp only [coeff_X_pow]
        split_ifs <;> norm_num
      push_cast
      exact (abs_sub _ _).trans (by linarith)
  have hu := upper Q hQ hcoeff hhigh z hz
  have hz0 : z ≠ 0 := by
    intro he
    rw [he, ← coeff_zero_eq_eval_zero, coeff_map, hzero] at hz
    norm_num at hz
  have hrQ := reverse_isMonicOfDegree Q D hQ hzero
  have hrcoeff : ∀ i, |Q.reverse.coeff i| ≤ 10 := by
    intro i
    rw [coeff_reverse]
    exact hcoeff _
  have hrhigh : ∀ i, D - G < i → i < D → Q.reverse.coeff i = 0 := by
    intro i hi hiD
    rw [coeff_reverse, hQ.natDegree_eq, revAt_le hiD.le]
    exact hlow _ (by omega) (by omega)
  have hrroot : (Q.reverse.map (Int.castRingHom ℂ)).eval z⁻¹ = 0 := by
    letI : Invertible z := invertibleOfNonzero hz0
    rw [eval_map]
    have hh := (eval₂_reverse_eq_zero_iff (Int.castRingHom ℂ) z Q).mpr (by
      rwa [eval_map] at hz)
    simpa only [invOf_eq_inv] using hh
  have hl := upper Q.reverse hrQ hrcoeff hrhigh z⁻¹ hrroot
  rw [norm_inv] at hl
  exact ⟨(inv_lt_comm₀ (by linarith : 0 < ρ) (norm_pos_iff.mpr hz0)).mpr hl, hu⟩

#print axioms root_annulus_of_end_gaps
end Erdos406EndGapRoots
