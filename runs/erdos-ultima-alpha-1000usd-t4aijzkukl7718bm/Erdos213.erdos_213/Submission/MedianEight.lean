import FormalConjecturesUtil

/-!
# Erdős Problem 213

*Reference:* [erdosproblems.com/213](https://www.erdosproblems.com/213)
-/

open EuclideanGeometry

namespace Erdos213

/--
The predicate (on $n$) that there exist $n$ points in $\mathbb{R}^2$,
no three on a line and no four on a circle,
such that all pairwise distances are integers.
-/
def Erdos213For (n : ℕ) : Prop := ∃ S : Set ℝ², S.Finite ∧ S.ncard = n ∧
    NonTrilinear S ∧
    (∀ Q : Set ℝ², Q ⊆ S ∧ Q.ncard = 4 → ¬ EuclideanGeometry.Cospherical Q) ∧
    (S.Pairwise fun p₁ p₂ => dist p₁ p₂ ∈ Set.range Int.cast)

lemma Erdos213For.mono {m n : ℕ} (h : Erdos213For n) (hmn : m ≤ n) :
    Erdos213For m := by
  rcases h with ⟨S, hfin, hcard, htri, hcirc, hdist⟩
  obtain ⟨T, hTS, hTcard⟩ := Set.exists_subset_card_eq (hcard ▸ hmn)
  exact ⟨T, hfin.subset hTS, hTcard, htri.mono hTS,
    fun Q hQ => hcirc Q ⟨hQ.1.trans hTS, hQ.2⟩, hdist.mono hTS⟩

private lemma collinear_det_zero {a b c : ℝ²} (h : Collinear ℝ {a, b, c}) :
    (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (by simp : a ∈ ({a,b,c} : Set ℝ²))).mp h
  obtain ⟨r, hr⟩ := hv b (by simp)
  obtain ⟨s, hs⟩ := hv c (by simp)
  subst b c
  simp
  ring

private lemma p4_dist_sq (a b : ℝ²) :
    dist a b ^ 2 = (a 0 - b 0)^2 + (a 1 - b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]

/-- A finite set of rational real numbers admits a positive common denominator. -/
lemma finite_common_denominator {T : Set ℝ} (hT : T.Finite)
    (hQ : T ⊆ Set.range ((↑) : ℚ → ℝ)) :
    ∃ D : ℕ, 0 < D ∧ ∀ x ∈ T, (D : ℝ) * x ∈ Set.range ((↑) : ℤ → ℝ) := by
  induction T, hT using Set.Finite.induction_on with
  | empty => exact ⟨1, by omega, by simp⟩
  | @insert x T hx hT ih =>
    obtain ⟨D, hD, hd⟩ := ih (fun y hy => hQ (Set.mem_insert_of_mem _ hy))
    obtain ⟨q, rfl⟩ := hQ (Set.mem_insert x T)
    refine ⟨q.den * D, Nat.mul_pos q.den_pos hD, ?_⟩
    intro y hy
    rcases hy with rfl | hy
    · refine ⟨(D : ℤ) * q.num, ?_⟩
      have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
      rw [Rat.cast_def]
      push_cast
      field_simp
    · obtain ⟨z, hz⟩ := hd y hy
      refine ⟨(q.den : ℤ) * z, ?_⟩
      push_cast
      rw [hz]
      ring

private lemma collinear_scale_image {T : Set ℝ²} (h : Collinear ℝ T) (c : ℝ) :
    Collinear ℝ ((fun x : ℝ² => c • x) '' T) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
  obtain ⟨o, v, h⟩ := h
  refine ⟨c • o, c • v, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, rfl⟩ := h x hx
  refine ⟨r, ?_⟩
  simp [smul_add, smul_smul, mul_comm]

private lemma cospherical_scale_image {T : Set ℝ²} (h : Cospherical T) (c : ℝ) :
    Cospherical ((fun x : ℝ² => c • x) '' T) := by
  obtain ⟨o, r, h⟩ := h
  refine ⟨c • o, ‖c‖ * r, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [dist_smul₀, h x hx]

lemma general_position_scale {T : Set ℝ²} (h : InGeneralPosition T) {c : ℝ}
    (hc : c ≠ 0) : InGeneralPosition ((fun x : ℝ² => c • x) '' T) := by
  have hi : Function.Injective (fun x : ℝ² => c⁻¹ • x) := by
    intro x y hxy
    simpa [hc] using congrArg (fun z : ℝ² => c • z) hxy
  constructor
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hxy hyz hxz hcol
    have hback := collinear_scale_image hcol c⁻¹
    simp only [Set.image_insert_eq, Set.image_singleton, inv_smul_smul₀ hc] at hback
    exact h.1 hx hy hz (fun he => hxy (he ▸ rfl))
      (fun he => hyz (he ▸ rfl)) (fun he => hxz (he ▸ rfl)) hback
  · intro Q hQ hcard hcos
    apply h.2 ((fun x : ℝ² => c⁻¹ • x) '' Q) ?_ ?_
      (cospherical_scale_image hcos c⁻¹)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hQ hx
      simpa [hc] using hy
    · rwa [Set.ncard_image_of_injective _ hi]

/-- For a fixed finite cardinality, rational and integer distances give equivalent
existence problems: a common dilation clears all denominators. -/
lemma erdos213For_iff_rational (n : ℕ) : Erdos213For n ↔
    ∃ S : Set ℝ², S.Finite ∧ S.ncard = n ∧ InGeneralPosition S ∧
      S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℚ → ℝ)) := by
  constructor
  · rintro ⟨S, hfin, hn, htri, hcircle, hdist⟩
    refine ⟨S, hfin, hn, ⟨htri, fun Q hQ h4 => hcircle Q ⟨hQ, h4⟩⟩, ?_⟩
    intro x hx y hy hxy
    obtain ⟨z, hz⟩ := hdist hx hy hxy
    exact ⟨(z : ℚ), by simpa using hz⟩
  · rintro ⟨S, hfin, hn, hgen, hdist⟩
    let T : Set ℝ := (fun p : ℝ² × ℝ² => dist p.1 p.2) '' (S ×ˢ S)
    have hTf : T.Finite := (hfin.prod hfin).image _
    have hTr : T ⊆ Set.range ((↑) : ℚ → ℝ) := by
      rintro _ ⟨⟨x,y⟩, ⟨hx,hy⟩, rfl⟩
      by_cases hxy : x = y
      · subst y
        exact ⟨0, by simp⟩
      · exact hdist hx hy hxy
    obtain ⟨D, hD, hmul⟩ := finite_common_denominator hTf hTr
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hD0 := ne_of_gt hDr
    have hinj : Function.Injective (fun x : ℝ² => (D : ℝ) • x) := by
      intro x y hxy
      simpa [hD0] using congrArg (fun z : ℝ² => (D : ℝ)⁻¹ • z) hxy
    have hg := general_position_scale hgen hD0
    refine ⟨(fun x : ℝ² => (D : ℝ) • x) '' S, hfin.image _, ?_, hg.1, ?_, ?_⟩
    · rwa [Set.ncard_image_of_injective _ hinj]
    · intro Q hQ
      exact hg.2 Q hQ.1 hQ.2
    · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ _
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hDr]
      exact hmul _ ⟨(x,y), ⟨hx,hy⟩, rfl⟩




end Erdos213


/-! Checked rational-root and determinant-factor certificates for the median family.
This file gives no rational point on the extra-square curve and does not settle Erdős 213. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 10000
set_option linter.unusedSimpArgs false

namespace Erdos213.MedianGeometry
open Polynomial

private lemma monic_no_root_of_mod (P : ℤ[X]) (hP : P.Monic) (p : ℕ)
    (hm : ∀ x : ZMod p, P.eval₂ (Int.castRingHom _) x ≠ 0) (r : ℚ) :
    Polynomial.aeval r P ≠ 0 := by
  intro hr
  obtain ⟨z,hz,_⟩ := exists_integer_of_is_root_of_monic hP hr
  have hZ : P.eval z = 0 := by
    apply IsFractionRing.injective ℤ ℚ
    simpa [hz, Polynomial.aeval_def, Polynomial.eval₂_at_apply] using hr
  apply hm (z : ZMod p)
  change P.eval₂ (Int.castRingHom _) ((Int.castRingHom (ZMod p)) z) = 0
  rw [Polynomial.eval₂_at_apply, hZ, map_zero]

private def factor0 (r : ℚ) : ℚ := 3*r^4 + 10*r^2 - 9
private lemma factor0_ne (r : ℚ) : factor0 r ≠ 0 := by
  let P : ℤ[X] := X^4 + 30*X^2 - 243
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (3*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor0] at hz
  linear_combination 27*hz

private def factor1 (r : ℚ) : ℚ := r^4 + 2*r^2 - 24*r + 9
private lemma factor1_ne (r : ℚ) : factor1 r ≠ 0 := by
  let P : ℤ[X] := X^4 + 2*X^2 - 24*X + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor1] at hz
  linear_combination 1*hz

private def factor2 (r : ℚ) : ℚ := r^5 - 3*r^4 - 22*r^3 - 30*r^2 + 9*r - 27
private lemma factor2_ne (r : ℚ) : factor2 r ≠ 0 := by
  let P : ℤ[X] := X^5 - 3*X^4 - 22*X^3 - 30*X^2 + 9*X - 27
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor2] at hz
  linear_combination 1*hz

private def factor3 (r : ℚ) : ℚ := r^2 - 12*r + 9
private lemma factor3_ne (r : ℚ) : factor3 r ≠ 0 := by
  let P : ℤ[X] := X^2 - 12*X + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor3] at hz
  linear_combination 1*hz

private def factor4 (r : ℚ) : ℚ := r^2 - 3
private lemma factor4_ne (r : ℚ) : factor4 r ≠ 0 := by
  let P : ℤ[X] := X^2 - 3
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor4] at hz
  linear_combination 1*hz

private def factor5 (r : ℚ) : ℚ := r^2 + 4*r + 1
private lemma factor5_ne (r : ℚ) : factor5 r ≠ 0 := by
  let P : ℤ[X] := X^2 + 4*X + 1
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor5] at hz
  linear_combination 1*hz

private def factor6 (r : ℚ) : ℚ := r^4 + 2*r^3 + 10*r^2 - 6*r + 9
private lemma factor6_ne (r : ℚ) : factor6 r ≠ 0 := by
  let P : ℤ[X] := X^4 + 2*X^3 + 10*X^2 - 6*X + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor6] at hz
  linear_combination 1*hz

private def factor7 (r : ℚ) : ℚ := r^5 - r^4 - 6*r^3 - 26*r^2 + 9*r - 9
private lemma factor7_ne (r : ℚ) : factor7 r ≠ 0 := by
  let P : ℤ[X] := X^5 - X^4 - 6*X^3 - 26*X^2 + 9*X - 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor7] at hz
  linear_combination 1*hz

private def factor8 (r : ℚ) : ℚ := r^2 + 3
private lemma factor8_ne (r : ℚ) : factor8 r ≠ 0 := by
  let P : ℤ[X] := X^2 + 3
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor8] at hz
  linear_combination 1*hz

private def factor9 (r : ℚ) : ℚ := r^4 - 4*r^3 + 10*r^2 + 12*r + 9
private lemma factor9_ne (r : ℚ) : factor9 r ≠ 0 := by
  let P : ℤ[X] := X^4 - 4*X^3 + 10*X^2 + 12*X + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor9] at hz
  linear_combination 1*hz

private def factor10 (r : ℚ) : ℚ := r^4 + 4*r^3 + 10*r^2 - 12*r + 9
private lemma factor10_ne (r : ℚ) : factor10 r ≠ 0 := by
  let P : ℤ[X] := X^4 + 4*X^3 + 10*X^2 - 12*X + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor10] at hz
  linear_combination 1*hz

private def factor11 (r : ℚ) : ℚ := r^5 - 3*r^4 + 26*r^3 + 18*r^2 + 9*r - 27
private lemma factor11_ne (r : ℚ) : factor11 r ≠ 0 := by
  let P : ℤ[X] := X^5 - 3*X^4 + 26*X^3 + 18*X^2 + 9*X - 27
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor11] at hz
  linear_combination 1*hz

private def factor12 (r : ℚ) : ℚ := r^2 - 8*r - 3
private lemma factor12_ne (r : ℚ) : factor12 r ≠ 0 := by
  let P : ℤ[X] := X^2 - 8*X - 3
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor12] at hz
  linear_combination 1*hz

private def factor13 (r : ℚ) : ℚ := r^3 + r^2 + 5*r - 3
private lemma factor13_ne (r : ℚ) : factor13 r ≠ 0 := by
  let P : ℤ[X] := X^3 + X^2 + 5*X - 3
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor13] at hz
  linear_combination 1*hz

private def factor14 (r : ℚ) : ℚ := r^3 + 5*r^2 - 3*r + 9
private lemma factor14_ne (r : ℚ) : factor14 r ≠ 0 := by
  let P : ℤ[X] := X^3 + 5*X^2 - 3*X + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor14] at hz
  linear_combination 1*hz

private def factor15 (r : ℚ) : ℚ := r^5 - 9*r^4 - 10*r^3 - 30*r^2 - 27*r + 27
private lemma factor15_ne (r : ℚ) : factor15 r ≠ 0 := by
  let P : ℤ[X] := X^5 - 9*X^4 - 10*X^3 - 30*X^2 - 27*X + 27
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor15] at hz
  linear_combination 1*hz

private def factor16 (r : ℚ) : ℚ := r^5 + 9*r^4 - 10*r^3 + 30*r^2 - 27*r - 27
private lemma factor16_ne (r : ℚ) : factor16 r ≠ 0 := by
  let P : ℤ[X] := X^5 + 9*X^4 - 10*X^3 + 30*X^2 - 27*X - 27
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor16] at hz
  linear_combination 1*hz

private def factor17 (r : ℚ) : ℚ := r^4 - 8*r^3 + 10*r^2 - 24*r + 9
private lemma factor17_ne (r : ℚ) : factor17 r ≠ 0 := by
  let P : ℤ[X] := X^4 - 8*X^3 + 10*X^2 - 24*X + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor17] at hz
  linear_combination 1*hz

private def factor18 (r : ℚ) : ℚ := r^4 + 8*r^3 + 10*r^2 + 24*r + 9
private lemma factor18_ne (r : ℚ) : factor18 r ≠ 0 := by
  let P : ℤ[X] := X^4 + 8*X^3 + 10*X^2 + 24*X + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor18] at hz
  linear_combination 1*hz

private def factor19 (r : ℚ) : ℚ := r^4 + 26*r^2 + 9
private lemma factor19_ne (r : ℚ) : factor19 r ≠ 0 := by
  let P : ℤ[X] := X^4 + 26*X^2 + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor19] at hz
  linear_combination 1*hz

private def factor20 (r : ℚ) : ℚ := r^4 - 10*r^2 - 27
private lemma factor20_ne (r : ℚ) : factor20 r ≠ 0 := by
  let P : ℤ[X] := X^4 - 10*X^2 - 27
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor20] at hz
  linear_combination 1*hz

private def factor21 (r : ℚ) : ℚ := r^4 + 2*r^2 + 24*r + 9
private lemma factor21_ne (r : ℚ) : factor21 r ≠ 0 := by
  let P : ℤ[X] := X^4 + 2*X^2 + 24*X + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor21] at hz
  linear_combination 1*hz

private def factor22 (r : ℚ) : ℚ := r^5 + 3*r^4 - 22*r^3 + 30*r^2 + 9*r + 27
private lemma factor22_ne (r : ℚ) : factor22 r ≠ 0 := by
  let P : ℤ[X] := X^5 + 3*X^4 - 22*X^3 + 30*X^2 + 9*X + 27
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor22] at hz
  linear_combination 1*hz

private def factor23 (r : ℚ) : ℚ := r^2 - 4*r + 1
private lemma factor23_ne (r : ℚ) : factor23 r ≠ 0 := by
  let P : ℤ[X] := X^2 - 4*X + 1
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor23] at hz
  linear_combination 1*hz

private def factor24 (r : ℚ) : ℚ := r^2 + 12*r + 9
private lemma factor24_ne (r : ℚ) : factor24 r ≠ 0 := by
  let P : ℤ[X] := X^2 + 12*X + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor24] at hz
  linear_combination 1*hz

private def factor25 (r : ℚ) : ℚ := r^4 - 2*r^3 + 10*r^2 + 6*r + 9
private lemma factor25_ne (r : ℚ) : factor25 r ≠ 0 := by
  let P : ℤ[X] := X^4 - 2*X^3 + 10*X^2 + 6*X + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor25] at hz
  linear_combination 1*hz

private def factor26 (r : ℚ) : ℚ := r^5 + r^4 - 6*r^3 + 26*r^2 + 9*r + 9
private lemma factor26_ne (r : ℚ) : factor26 r ≠ 0 := by
  let P : ℤ[X] := X^5 + X^4 - 6*X^3 + 26*X^2 + 9*X + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor26] at hz
  linear_combination 1*hz

private def factor27 (r : ℚ) : ℚ := r^5 + 3*r^4 + 26*r^3 - 18*r^2 + 9*r + 27
private lemma factor27_ne (r : ℚ) : factor27 r ≠ 0 := by
  let P : ℤ[X] := X^5 + 3*X^4 + 26*X^3 - 18*X^2 + 9*X + 27
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor27] at hz
  linear_combination 1*hz

private def factor28 (r : ℚ) : ℚ := r^2 + 8*r - 3
private lemma factor28_ne (r : ℚ) : factor28 r ≠ 0 := by
  let P : ℤ[X] := X^2 + 8*X - 3
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor28] at hz
  linear_combination 1*hz

private def factor29 (r : ℚ) : ℚ := r^3 - 5*r^2 - 3*r - 9
private lemma factor29_ne (r : ℚ) : factor29 r ≠ 0 := by
  let P : ℤ[X] := X^3 - 5*X^2 - 3*X - 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor29] at hz
  linear_combination 1*hz

private def factor30 (r : ℚ) : ℚ := r^3 - r^2 + 5*r + 3
private lemma factor30_ne (r : ℚ) : factor30 r ≠ 0 := by
  let P : ℤ[X] := X^3 - X^2 + 5*X + 3
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor30] at hz
  linear_combination 1*hz

private def factor31 (r : ℚ) : ℚ := r^4 - 8*r^3 + 2*r^2 + 9
private lemma factor31_ne (r : ℚ) : factor31 r ≠ 0 := by
  let P : ℤ[X] := X^4 - 8*X^3 + 2*X^2 + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor31] at hz
  linear_combination 1*hz

private def factor32 (r : ℚ) : ℚ := r^5 - r^4 + 10*r^3 + 22*r^2 + 9*r - 9
private lemma factor32_ne (r : ℚ) : factor32 r ≠ 0 := by
  let P : ℤ[X] := X^5 - X^4 + 10*X^3 + 22*X^2 + 9*X - 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor32] at hz
  linear_combination 1*hz

private def factor33 (r : ℚ) : ℚ := r^4 + 8*r^3 + 2*r^2 + 9
private lemma factor33_ne (r : ℚ) : factor33 r ≠ 0 := by
  let P : ℤ[X] := X^4 + 8*X^3 + 2*X^2 + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor33] at hz
  linear_combination 1*hz

private def factor34 (r : ℚ) : ℚ := r^5 + r^4 + 10*r^3 - 22*r^2 + 9*r + 9
private lemma factor34_ne (r : ℚ) : factor34 r ≠ 0 := by
  let P : ℤ[X] := X^5 + X^4 + 10*X^3 - 22*X^2 + 9*X + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor34] at hz
  linear_combination 1*hz

private def factor35 (r : ℚ) : ℚ := r^5 - 3*r^4 - 10*r^3 - 10*r^2 - 27*r + 9
private lemma factor35_ne (r : ℚ) : factor35 r ≠ 0 := by
  let P : ℤ[X] := X^5 - 3*X^4 - 10*X^3 - 10*X^2 - 27*X + 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor35] at hz
  linear_combination 1*hz

private def factor36 (r : ℚ) : ℚ := r^5 + 3*r^4 - 10*r^3 + 10*r^2 - 27*r - 9
private lemma factor36_ne (r : ℚ) : factor36 r ≠ 0 := by
  let P : ℤ[X] := X^5 + 3*X^4 - 10*X^3 + 10*X^2 - 27*X - 9
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor36] at hz
  linear_combination 1*hz

private def factor37 (r : ℚ) : ℚ := r^8 + 9*r^7 + r^6 + 3*r^5 - 35*r^4 - 117*r^3 - 261*r^2 + 81*r - 162
private lemma factor37_ne (r : ℚ) : factor37 r ≠ 0 := by
  let P : ℤ[X] := X^8 + 9*X^7 + X^6 + 3*X^5 - 35*X^4 - 117*X^3 - 261*X^2 + 81*X - 162
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor37] at hz
  linear_combination 1*hz

private def factor38 (r : ℚ) : ℚ := r^9 - 9*r^8 + 16*r^7 + 24*r^6 + 490*r^5 + 126*r^4 + 1512*r^3 - 432*r^2 - 243*r + 243
private lemma factor38_ne (r : ℚ) : factor38 r ≠ 0 := by
  let P : ℤ[X] := X^9 - 9*X^8 + 16*X^7 + 24*X^6 + 490*X^5 + 126*X^4 + 1512*X^3 - 432*X^2 - 243*X + 243
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor38] at hz
  linear_combination 1*hz

private def factor39 (r : ℚ) : ℚ := r^8 - 9*r^7 + r^6 - 3*r^5 - 35*r^4 + 117*r^3 - 261*r^2 - 81*r - 162
private lemma factor39_ne (r : ℚ) : factor39 r ≠ 0 := by
  let P : ℤ[X] := X^8 - 9*X^7 + X^6 - 3*X^5 - 35*X^4 + 117*X^3 - 261*X^2 - 81*X - 162
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor39] at hz
  linear_combination 1*hz

private def factor40 (r : ℚ) : ℚ := r^9 + 9*r^8 + 16*r^7 - 24*r^6 + 490*r^5 - 126*r^4 + 1512*r^3 + 432*r^2 - 243*r - 243
private lemma factor40_ne (r : ℚ) : factor40 r ≠ 0 := by
  let P : ℤ[X] := X^9 + 9*X^8 + 16*X^7 - 24*X^6 + 490*X^5 - 126*X^4 + 1512*X^3 + 432*X^2 - 243*X - 243
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor40] at hz
  linear_combination 1*hz

private def factor41 (r : ℚ) : ℚ := r^4 - 34*r^2 + 45
private lemma factor41_ne (r : ℚ) : factor41 r ≠ 0 := by
  let P : ℤ[X] := X^4 - 34*X^2 + 45
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor41] at hz
  linear_combination 1*hz

private def factor42 (r : ℚ) : ℚ := r^6 + 5*r^4 + 63*r^2 + 27
private lemma factor42_ne (r : ℚ) : factor42 r ≠ 0 := by
  let P : ℤ[X] := X^6 + 5*X^4 + 63*X^2 + 27
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor42] at hz
  linear_combination 1*hz

private def factor43 (r : ℚ) : ℚ := r^9 - 13*r^8 - 12*r^7 - 20*r^6 + 182*r^5 + 114*r^4 + 1044*r^3 + 108*r^2 + 81*r + 243
private lemma factor43_ne (r : ℚ) : factor43 r ≠ 0 := by
  let P : ℤ[X] := X^9 - 13*X^8 - 12*X^7 - 20*X^6 + 182*X^5 + 114*X^4 + 1044*X^3 + 108*X^2 + 81*X + 243
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor43] at hz
  linear_combination 1*hz

private def factor44 (r : ℚ) : ℚ := r^9 + 13*r^8 - 12*r^7 + 20*r^6 + 182*r^5 - 114*r^4 + 1044*r^3 - 108*r^2 + 81*r - 243
private lemma factor44_ne (r : ℚ) : factor44 r ≠ 0 := by
  let P : ℤ[X] := X^9 + 13*X^8 - 12*X^7 + 20*X^6 + 182*X^5 - 114*X^4 + 1044*X^3 - 108*X^2 + 81*X - 243
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor44] at hz
  linear_combination 1*hz

private def factor45 (r : ℚ) : ℚ := 5*r^8 - 10*r^6 + 428*r^4 + 234*r^2 - 81
private lemma factor45_ne (r : ℚ) : factor45 r ≠ 0 := by
  let P : ℤ[X] := X^8 - 50*X^6 + 53500*X^4 + 731250*X^2 - 6328125
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (5*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor45] at hz
  linear_combination 78125*hz

private def factor46 (r : ℚ) : ℚ := r^10 - 53*r^8 - 446*r^6 - 3762*r^4 - 1539*r^2 - 729
private lemma factor46_ne (r : ℚ) : factor46 r ≠ 0 := by
  let P : ℤ[X] := X^10 - 53*X^8 - 446*X^6 - 3762*X^4 - 1539*X^2 - 729
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor46] at hz
  linear_combination 1*hz

private def factor47 (r : ℚ) : ℚ := 2*r^8 + 3*r^7 + 29*r^6 - 39*r^5 + 35*r^4 + 9*r^3 - 9*r^2 + 243*r - 81
private lemma factor47_ne (r : ℚ) : factor47 r ≠ 0 := by
  let P : ℤ[X] := X^8 + 3*X^7 + 58*X^6 - 156*X^5 + 280*X^4 + 144*X^3 - 288*X^2 + 15552*X - 10368
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (2*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor47] at hz
  linear_combination 128*hz

private def factor48 (r : ℚ) : ℚ := r^9 + 3*r^8 - 16*r^7 - 168*r^6 + 42*r^5 - 490*r^4 + 72*r^3 - 144*r^2 - 243*r - 81
private lemma factor48_ne (r : ℚ) : factor48 r ≠ 0 := by
  let P : ℤ[X] := X^9 + 3*X^8 - 16*X^7 - 168*X^6 + 42*X^5 - 490*X^4 + 72*X^3 - 144*X^2 - 243*X - 81
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor48] at hz
  linear_combination 1*hz

private def factor49 (r : ℚ) : ℚ := r^8 - 26*r^6 - 428*r^4 + 90*r^2 - 405
private lemma factor49_ne (r : ℚ) : factor49 r ≠ 0 := by
  let P : ℤ[X] := X^8 - 26*X^6 - 428*X^4 + 90*X^2 - 405
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor49] at hz
  linear_combination 1*hz

private def factor50 (r : ℚ) : ℚ := r^10 + 19*r^8 + 418*r^6 + 446*r^4 + 477*r^2 - 81
private lemma factor50_ne (r : ℚ) : factor50 r ≠ 0 := by
  let P : ℤ[X] := X^10 + 19*X^8 + 418*X^6 + 446*X^4 + 477*X^2 - 81
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor50] at hz
  linear_combination 1*hz

private def factor51 (r : ℚ) : ℚ := 2*r^8 - 3*r^7 + 29*r^6 + 39*r^5 + 35*r^4 - 9*r^3 - 9*r^2 - 243*r - 81
private lemma factor51_ne (r : ℚ) : factor51 r ≠ 0 := by
  let P : ℤ[X] := X^8 - 3*X^7 + 58*X^6 + 156*X^5 + 280*X^4 - 144*X^3 - 288*X^2 - 15552*X - 10368
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (2*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor51] at hz
  linear_combination 128*hz

private def factor52 (r : ℚ) : ℚ := r^9 - 3*r^8 - 16*r^7 + 168*r^6 + 42*r^5 + 490*r^4 + 72*r^3 + 144*r^2 - 243*r + 81
private lemma factor52_ne (r : ℚ) : factor52 r ≠ 0 := by
  let P : ℤ[X] := X^9 - 3*X^8 - 16*X^7 + 168*X^6 + 42*X^5 + 490*X^4 + 72*X^3 + 144*X^2 - 243*X + 81
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor52] at hz
  linear_combination 1*hz

private def factor53 (r : ℚ) : ℚ := 5*r^4 - 34*r^2 + 9
private lemma factor53_ne (r : ℚ) : factor53 r ≠ 0 := by
  let P : ℤ[X] := X^4 - 170*X^2 + 1125
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (5*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor53] at hz
  linear_combination 125*hz

private def factor54 (r : ℚ) : ℚ := r^6 + 21*r^4 + 15*r^2 + 27
private lemma factor54_ne (r : ℚ) : factor54 r ≠ 0 := by
  let P : ℤ[X] := X^6 + 21*X^4 + 15*X^2 + 27
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 5 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor54] at hz
  linear_combination 1*hz

private def factor55 (r : ℚ) : ℚ := r^9 - r^8 + 4*r^7 - 116*r^6 + 38*r^5 - 182*r^4 - 60*r^3 + 108*r^2 - 351*r - 81
private lemma factor55_ne (r : ℚ) : factor55 r ≠ 0 := by
  let P : ℤ[X] := X^9 - X^8 + 4*X^7 - 116*X^6 + 38*X^5 - 182*X^4 - 60*X^3 + 108*X^2 - 351*X - 81
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor55] at hz
  linear_combination 1*hz

private def factor56 (r : ℚ) : ℚ := r^9 + r^8 + 4*r^7 + 116*r^6 + 38*r^5 + 182*r^4 - 60*r^3 - 108*r^2 - 351*r + 81
private lemma factor56_ne (r : ℚ) : factor56 r ≠ 0 := by
  let P : ℤ[X] := X^9 + X^8 + 4*X^7 + 116*X^6 + 38*X^5 + 182*X^4 - 60*X^3 - 108*X^2 - 351*X + 81
  have hP : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 7, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_add, eval₂_sub, eval₂_mul, eval₂_neg, eval₂_pow, eval₂_X,
      eval₂_ofNat, eval₂_one, eval₂_zero]
    decide
  intro hz
  apply monic_no_root_of_mod P hP 7 hm (1*r)
  norm_num [P,Polynomial.aeval_def]
  dsimp [factor56] at hz
  linear_combination 1*hz

def sideA (r : ℚ) : ℚ := r^5 + r^4 - 6*r^3 + 26*r^2 + 9*r + 9
def sideB (r : ℚ) : ℚ := 6*r^4 + 20*r^2 - 18
def sideC (r : ℚ) : ℚ := r^5 - r^4 - 6*r^3 - 26*r^2 + 9*r - 9

lemma sideB_ne (r : ℚ) : sideB r ≠ 0 := by
  have hh : sideB r = 2*factor0 r := by dsimp [sideB,factor0]; ring
  rw [hh]
  exact mul_ne_zero (by norm_num) (factor0_ne r)

def traceB (r : ℚ) : ℚ := 2*(sideA r^2-sideC r^2)/sideB r^2

def traceC (r : ℚ) : ℚ := 2*(sideA r^2+sideC r^2)/sideB r^2-1

def exceptional0 (r : ℚ) : ℚ := 3*(traceB r) - 2*(traceC r)
lemma exceptional0_ne {r : ℚ} (hr : r ≠ 0) : exceptional0 r ≠ 0 := by
  have he : exceptional0 r * sideB r^2 = -8 * r * (factor1 r) * (factor2 r) := by
    dsimp only [exceptional0,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor1,factor2]
    ring
  have hn : -8 * r * (factor1 r) * (factor2 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-8 : ℚ) ≠ 0) hr) (factor1_ne r)) (factor2_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional1 (r : ℚ) : ℚ := 3*(traceB r) - (traceC r) + 3
lemma exceptional1_ne {r : ℚ} (hr : r ≠ 0) : exceptional1 r ≠ 0 := by
  have he : exceptional1 r * sideB r^2 = -4 * (factor3 r) * (factor4 r) * (factor5 r) * (factor6 r) := by
    dsimp only [exceptional1,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor3,factor4,factor5,factor6]
    ring
  have hn : -4 * (factor3 r) * (factor4 r) * (factor5 r) * (factor6 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-4 : ℚ) ≠ 0) (factor3_ne r)) (factor4_ne r)) (factor5_ne r)) (factor6_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional2 (r : ℚ) : ℚ := (traceB r) - (traceC r) - 1
lemma exceptional2_ne {r : ℚ} (hr : r ≠ 0) : exceptional2 r ≠ 0 := by
  have he : exceptional2 r * sideB r^2 = -4 * (factor7 r)^2 := by
    dsimp only [exceptional2,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor7]
    ring
  have hn : -4 * (factor7 r)^2 ≠ 0 := (mul_ne_zero (by norm_num : (-4 : ℚ) ≠ 0) (pow_ne_zero 2 (factor7_ne r)))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional3 (r : ℚ) : ℚ := (traceC r) + 3
lemma exceptional3_ne {r : ℚ} (hr : r ≠ 0) : exceptional3 r ≠ 0 := by
  have he : exceptional3 r * sideB r^2 = 4 * (factor8 r) * (factor9 r) * (factor10 r) := by
    dsimp only [exceptional3,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor8,factor9,factor10]
    ring
  have hn : 4 * (factor8 r) * (factor9 r) * (factor10 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (factor8_ne r)) (factor9_ne r)) (factor10_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional4 (r : ℚ) : ℚ := 3*(traceB r) - (traceC r) - 9
lemma exceptional4_ne {r : ℚ} (hr : r ≠ 0) : exceptional4 r ≠ 0 := by
  have he : exceptional4 r * sideB r^2 = -4 * (factor11 r)^2 := by
    dsimp only [exceptional4,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor11]
    ring
  have hn : -4 * (factor11 r)^2 ≠ 0 := (mul_ne_zero (by norm_num : (-4 : ℚ) ≠ 0) (pow_ne_zero 2 (factor11_ne r)))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional5 (r : ℚ) : ℚ := (traceB r) - (traceC r) + 3
lemma exceptional5_ne {r : ℚ} (hr : r ≠ 0) : exceptional5 r ≠ 0 := by
  have he : exceptional5 r * sideB r^2 = -4 * (factor12 r) * (factor4 r) * (factor13 r) * (factor14 r) := by
    dsimp only [exceptional5,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor12,factor4,factor13,factor14]
    ring
  have hn : -4 * (factor12 r) * (factor4 r) * (factor13 r) * (factor14 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-4 : ℚ) ≠ 0) (factor12_ne r)) (factor4_ne r)) (factor13_ne r)) (factor14_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional6 (r : ℚ) : ℚ := (traceC r) - 9
lemma exceptional6_ne {r : ℚ} (hr : r ≠ 0) : exceptional6 r ≠ 0 := by
  have he : exceptional6 r * sideB r^2 = 4 * (factor15 r) * (factor16 r) := by
    dsimp only [exceptional6,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor15,factor16]
    ring
  have hn : 4 * (factor15 r) * (factor16 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (factor15_ne r)) (factor16_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional7 (r : ℚ) : ℚ := (traceC r) - 3
lemma exceptional7_ne {r : ℚ} (hr : r ≠ 0) : exceptional7 r ≠ 0 := by
  have he : exceptional7 r * sideB r^2 = 4 * (factor4 r) * (factor17 r) * (factor18 r) := by
    dsimp only [exceptional7,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor4,factor17,factor18]
    ring
  have hn : 4 * (factor4 r) * (factor17 r) * (factor18 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (factor4_ne r)) (factor17_ne r)) (factor18_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional8 (r : ℚ) : ℚ := (traceB r)
lemma exceptional8_ne {r : ℚ} (hr : r ≠ 0) : exceptional8 r ≠ 0 := by
  have he : exceptional8 r * sideB r^2 = 8 * r * (factor4 r)^2 * (factor19 r) := by
    dsimp only [exceptional8,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor4,factor19]
    ring
  have hn : 8 * r * (factor4 r)^2 * (factor19 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (8 : ℚ) ≠ 0) hr) (pow_ne_zero 2 (factor4_ne r))) (factor19_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional9 (r : ℚ) : ℚ := (traceC r)
lemma exceptional9_ne {r : ℚ} (hr : r ≠ 0) : exceptional9 r ≠ 0 := by
  have he : exceptional9 r * sideB r^2 = 4 * r^2 * (factor20 r)^2 := by
    dsimp only [exceptional9,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor20]
    ring
  have hn : 4 * r^2 * (factor20 r)^2 ≠ 0 := (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (pow_ne_zero 2 hr)) (pow_ne_zero 2 (factor20_ne r)))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional10 (r : ℚ) : ℚ := 3*(traceB r) + 2*(traceC r)
lemma exceptional10_ne {r : ℚ} (hr : r ≠ 0) : exceptional10 r ≠ 0 := by
  have he : exceptional10 r * sideB r^2 = 8 * r * (factor21 r) * (factor22 r) := by
    dsimp only [exceptional10,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor21,factor22]
    ring
  have hn : 8 * r * (factor21 r) * (factor22 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (8 : ℚ) ≠ 0) hr) (factor21_ne r)) (factor22_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional11 (r : ℚ) : ℚ := 3*(traceB r) + (traceC r) - 3
lemma exceptional11_ne {r : ℚ} (hr : r ≠ 0) : exceptional11 r ≠ 0 := by
  have he : exceptional11 r * sideB r^2 = 4 * (factor23 r) * (factor4 r) * (factor24 r) * (factor25 r) := by
    dsimp only [exceptional11,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor23,factor4,factor24,factor25]
    ring
  have hn : 4 * (factor23 r) * (factor4 r) * (factor24 r) * (factor25 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (factor23_ne r)) (factor4_ne r)) (factor24_ne r)) (factor25_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional12 (r : ℚ) : ℚ := (traceB r) + (traceC r) + 1
lemma exceptional12_ne {r : ℚ} (hr : r ≠ 0) : exceptional12 r ≠ 0 := by
  have he : exceptional12 r * sideB r^2 = 4 * (factor26 r)^2 := by
    dsimp only [exceptional12,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor26]
    ring
  have hn : 4 * (factor26 r)^2 ≠ 0 := (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (pow_ne_zero 2 (factor26_ne r)))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional13 (r : ℚ) : ℚ := 3*(traceB r) + (traceC r) + 9
lemma exceptional13_ne {r : ℚ} (hr : r ≠ 0) : exceptional13 r ≠ 0 := by
  have he : exceptional13 r * sideB r^2 = 4 * (factor27 r)^2 := by
    dsimp only [exceptional13,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor27]
    ring
  have hn : 4 * (factor27 r)^2 ≠ 0 := (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (pow_ne_zero 2 (factor27_ne r)))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional14 (r : ℚ) : ℚ := (traceB r) + (traceC r) - 3
lemma exceptional14_ne {r : ℚ} (hr : r ≠ 0) : exceptional14 r ≠ 0 := by
  have he : exceptional14 r * sideB r^2 = 4 * (factor4 r) * (factor28 r) * (factor29 r) * (factor30 r) := by
    dsimp only [exceptional14,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor4,factor28,factor29,factor30]
    ring
  have hn : 4 * (factor4 r) * (factor28 r) * (factor29 r) * (factor30 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (factor4_ne r)) (factor28_ne r)) (factor29_ne r)) (factor30_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional15 (r : ℚ) : ℚ := (traceB r) - 2
lemma exceptional15_ne {r : ℚ} (hr : r ≠ 0) : exceptional15 r ≠ 0 := by
  have he : exceptional15 r * sideB r^2 = 8 * (factor31 r) * (factor32 r) := by
    dsimp only [exceptional15,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor31,factor32]
    ring
  have hn : 8 * (factor31 r) * (factor32 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (by norm_num : (8 : ℚ) ≠ 0) (factor31_ne r)) (factor32_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional16 (r : ℚ) : ℚ := (traceB r) + 2
lemma exceptional16_ne {r : ℚ} (hr : r ≠ 0) : exceptional16 r ≠ 0 := by
  have he : exceptional16 r * sideB r^2 = 8 * (factor33 r) * (factor34 r) := by
    dsimp only [exceptional16,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor33,factor34]
    ring
  have hn : 8 * (factor33 r) * (factor34 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (by norm_num : (8 : ℚ) ≠ 0) (factor33_ne r)) (factor34_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional17 (r : ℚ) : ℚ := (traceC r) - 1
lemma exceptional17_ne {r : ℚ} (hr : r ≠ 0) : exceptional17 r ≠ 0 := by
  have he : exceptional17 r * sideB r^2 = 4 * (factor35 r) * (factor36 r) := by
    dsimp only [exceptional17,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor35,factor36]
    ring
  have hn : 4 * (factor35 r) * (factor36 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (factor35_ne r)) (factor36_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional18 (r : ℚ) : ℚ := (traceC r)^2 + 9*(traceB r) - 3*(traceC r)
lemma exceptional18_ne {r : ℚ} (hr : r ≠ 0) : exceptional18 r ≠ 0 := by
  have he : exceptional18 r * sideB r^4 = 16 * r * (factor4 r) * (factor37 r) * (factor38 r) := by
    dsimp only [exceptional18,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor4,factor37,factor38]
    ring
  have hn : 16 * r * (factor4 r) * (factor37 r) * (factor38 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (16 : ℚ) ≠ 0) hr) (factor4_ne r)) (factor37_ne r)) (factor38_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional19 (r : ℚ) : ℚ := -(traceC r)^2 + 9*(traceB r) + 3*(traceC r)
lemma exceptional19_ne {r : ℚ} (hr : r ≠ 0) : exceptional19 r ≠ 0 := by
  have he : exceptional19 r * sideB r^4 = -16 * r * (factor4 r) * (factor39 r) * (factor40 r) := by
    dsimp only [exceptional19,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor4,factor39,factor40]
    ring
  have hn : -16 * r * (factor4 r) * (factor39 r) * (factor40 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-16 : ℚ) ≠ 0) hr) (factor4_ne r)) (factor39_ne r)) (factor40_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional20 (r : ℚ) : ℚ := (traceC r)^3 + 27*(traceB r)^2 - 18*(traceC r)^2 - 27*(traceC r)
lemma exceptional20_ne {r : ℚ} (hr : r ≠ 0) : exceptional20 r ≠ 0 := by
  have he : exceptional20 r * sideB r^6 = 64 * r^2 * (factor41 r) * (factor42 r) * (factor43 r) * (factor44 r) := by
    dsimp only [exceptional20,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor41,factor42,factor43,factor44]
    ring
  have hn : 64 * r^2 * (factor41 r) * (factor42 r) * (factor43 r) * (factor44 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (64 : ℚ) ≠ 0) (pow_ne_zero 2 hr)) (factor41_ne r)) (factor42_ne r)) (factor43_ne r)) (factor44_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional21 (r : ℚ) : ℚ := 9*(traceB r)^2 - 5*(traceC r)^2 + 6*(traceC r) + 27
lemma exceptional21_ne {r : ℚ} (hr : r ≠ 0) : exceptional21 r ≠ 0 := by
  have he : exceptional21 r * sideB r^4 = -16 * (factor4 r) * (factor45 r) * (factor46 r) := by
    dsimp only [exceptional21,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor4,factor45,factor46]
    ring
  have hn : -16 * (factor4 r) * (factor45 r) * (factor46 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-16 : ℚ) ≠ 0) (factor4_ne r)) (factor45_ne r)) (factor46_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional22 (r : ℚ) : ℚ := (traceB r)*(traceC r) + (traceC r) - 3
lemma exceptional22_ne {r : ℚ} (hr : r ≠ 0) : exceptional22 r ≠ 0 := by
  have he : exceptional22 r * sideB r^4 = 16 * (factor4 r) * (factor47 r) * (factor48 r) := by
    dsimp only [exceptional22,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor4,factor47,factor48]
    ring
  have hn : 16 * (factor4 r) * (factor47 r) * (factor48 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (16 : ℚ) ≠ 0) (factor4_ne r)) (factor47_ne r)) (factor48_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional23 (r : ℚ) : ℚ := 3*(traceB r)^2 + (traceC r)^2 + 2*(traceC r) - 15
lemma exceptional23_ne {r : ℚ} (hr : r ≠ 0) : exceptional23 r ≠ 0 := by
  have he : exceptional23 r * sideB r^4 = 16 * (factor4 r) * (factor49 r) * (factor50 r) := by
    dsimp only [exceptional23,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor4,factor49,factor50]
    ring
  have hn : 16 * (factor4 r) * (factor49 r) * (factor50 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (16 : ℚ) ≠ 0) (factor4_ne r)) (factor49_ne r)) (factor50_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional24 (r : ℚ) : ℚ := (traceB r)*(traceC r) - (traceC r) + 3
lemma exceptional24_ne {r : ℚ} (hr : r ≠ 0) : exceptional24 r ≠ 0 := by
  have he : exceptional24 r * sideB r^4 = 16 * (factor4 r) * (factor51 r) * (factor52 r) := by
    dsimp only [exceptional24,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor4,factor51,factor52]
    ring
  have hn : 16 * (factor4 r) * (factor51 r) * (factor52 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (16 : ℚ) ≠ 0) (factor4_ne r)) (factor51_ne r)) (factor52_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional25 (r : ℚ) : ℚ := (traceB r)^2*(traceC r) - (traceC r)^2 - 6*(traceC r) + 3
lemma exceptional25_ne {r : ℚ} (hr : r ≠ 0) : exceptional25 r ≠ 0 := by
  have he : exceptional25 r * sideB r^6 = -64 * (factor53 r) * (factor54 r) * (factor55 r) * (factor56 r) := by
    dsimp only [exceptional25,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp only [sideA,sideB,sideC,factor53,factor54,factor55,factor56]
    ring
  have hn : -64 * (factor53 r) * (factor54 r) * (factor55 r) * (factor56 r) ≠ 0 := (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-64 : ℚ) ≠ 0) (factor53_ne r)) (factor54_ne r)) (factor55_ne r)) (factor56_ne r))
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

def exceptional : Fin 26 → ℚ → ℚ :=
  ![exceptional0,exceptional1,exceptional2,exceptional3,exceptional4,exceptional5,exceptional6,exceptional7,exceptional8,exceptional9,exceptional10,exceptional11,exceptional12,exceptional13,exceptional14,exceptional15,exceptional16,exceptional17,exceptional18,exceptional19,exceptional20,exceptional21,exceptional22,exceptional23,exceptional24,exceptional25]

lemma exceptional_ne {r : ℚ} (hr : r ≠ 0) (i : Fin 26) : exceptional i r ≠ 0 := by
  fin_cases i
  · exact exceptional0_ne hr
  · exact exceptional1_ne hr
  · exact exceptional2_ne hr
  · exact exceptional3_ne hr
  · exact exceptional4_ne hr
  · exact exceptional5_ne hr
  · exact exceptional6_ne hr
  · exact exceptional7_ne hr
  · exact exceptional8_ne hr
  · exact exceptional9_ne hr
  · exact exceptional10_ne hr
  · exact exceptional11_ne hr
  · exact exceptional12_ne hr
  · exact exceptional13_ne hr
  · exact exceptional14_ne hr
  · exact exceptional15_ne hr
  · exact exceptional16_ne hr
  · exact exceptional17_ne hr
  · exact exceptional18_ne hr
  · exact exceptional19_ne hr
  · exact exceptional20_ne hr
  · exact exceptional21_ne hr
  · exact exceptional22_ne hr
  · exact exceptional23_ne hr
  · exact exceptional24_ne hr
  · exact exceptional25_ne hr

#print axioms sideB_ne
#print axioms exceptional_ne


/- Arithmetic determinant certificates for twelve times the eight template
points, in the rational basis (1,z), where z²+traceB*z+traceC=0. -/

def coordA (r : ℚ) : Fin 8 → ℚ :=
  ![0,3*traceC r+9,9-traceC r,18,9-3*traceC r,6,0,9-3*traceC r]

def coordB (r : ℚ) : Fin 8 → ℚ :=
  ![0,3*traceB r+6,6-traceB r,6,12-3*traceB r,6,12,-3*traceB r]

def quadNorm (r x y : ℚ) : ℚ := x^2-traceB r*x*y+traceC r*y^2

def triangle (r : ℚ) (i j k : Fin 8) : ℚ :=
  (coordA r j-coordA r i)*(coordB r k-coordB r i)-
  (coordB r j-coordB r i)*(coordA r k-coordA r i)

def det3 (a b c d e f g h i : ℚ) : ℚ :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

def circle (r : ℚ) (i j k l : Fin 8) : ℚ :=
  det3 (coordA r j-coordA r i) (coordB r j-coordB r i)
    (quadNorm r (coordA r j-coordA r i) (coordB r j-coordB r i))
    (coordA r k-coordA r i) (coordB r k-coordB r i)
    (quadNorm r (coordA r k-coordA r i) (coordB r k-coordB r i))
    (coordA r l-coordA r i) (coordB r l-coordB r i)
    (quadNorm r (coordA r l-coordA r i) (coordB r l-coordB r i))

private lemma triangle_0_1_2_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 1 2 ≠ 0 := by
  have he : triangle r 0 1 2 = -12 * (exceptional0 r) := by
    dsimp [triangle,coordA,coordB,exceptional0]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-12 : ℚ) ≠ 0) (exceptional0_ne hr))

private lemma triangle_0_1_3_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 1 3 ≠ 0 := by
  have he : triangle r 0 1 3 = -18 * (exceptional1 r) := by
    dsimp [triangle,coordA,coordB,exceptional1]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional1_ne hr))

private lemma triangle_0_1_4_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 1 4 ≠ 0 := by
  have he : triangle r 0 1 4 = -54 * (exceptional2 r) := by
    dsimp [triangle,coordA,coordB,exceptional2]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-54 : ℚ) ≠ 0) (exceptional2_ne hr))

private lemma triangle_0_1_5_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 1 5 ≠ 0 := by
  have he : triangle r 0 1 5 = -18 * (exceptional2 r) := by
    dsimp [triangle,coordA,coordB,exceptional2]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional2_ne hr))

private lemma triangle_0_1_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 1 6 ≠ 0 := by
  have he : triangle r 0 1 6 = 36 * (exceptional3 r) := by
    dsimp [triangle,coordA,coordB,exceptional3]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) (exceptional3_ne hr))

private lemma triangle_0_1_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 1 7 ≠ 0 := by
  have he : triangle r 0 1 7 = -18 * (exceptional1 r) := by
    dsimp [triangle,coordA,coordB,exceptional1]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional1_ne hr))

private lemma triangle_0_2_3_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 2 3 ≠ 0 := by
  have he : triangle r 0 2 3 = 6 * (exceptional4 r) := by
    dsimp [triangle,coordA,coordB,exceptional4]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (6 : ℚ) ≠ 0) (exceptional4_ne hr))

private lemma triangle_0_2_4_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 2 4 ≠ 0 := by
  have he : triangle r 0 2 4 = -6 * (exceptional4 r) := by
    dsimp [triangle,coordA,coordB,exceptional4]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-6 : ℚ) ≠ 0) (exceptional4_ne hr))

private lemma triangle_0_2_5_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 2 5 ≠ 0 := by
  have he : triangle r 0 2 5 = 6 * (exceptional5 r) := by
    dsimp [triangle,coordA,coordB,exceptional5]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (6 : ℚ) ≠ 0) (exceptional5_ne hr))

private lemma triangle_0_2_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 2 6 ≠ 0 := by
  have he : triangle r 0 2 6 = -12 * (exceptional6 r) := by
    dsimp [triangle,coordA,coordB,exceptional6]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-12 : ℚ) ≠ 0) (exceptional6_ne hr))

private lemma triangle_0_2_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 2 7 ≠ 0 := by
  have he : triangle r 0 2 7 = -18 * (exceptional5 r) := by
    dsimp [triangle,coordA,coordB,exceptional5]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional5_ne hr))

private lemma triangle_0_3_4_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 3 4 ≠ 0 := by
  have he : triangle r 0 3 4 = -18 * (exceptional4 r) := by
    dsimp [triangle,coordA,coordB,exceptional4]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional4_ne hr))

private lemma triangle_0_3_5_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 3 5 ≠ 0 := by
  have he : triangle r 0 3 5 = 72 := by
    dsimp [triangle,coordA,coordB,]
    ring
  rw [he]
  exact (by norm_num : (72 : ℚ) ≠ 0)

private lemma triangle_0_3_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 3 6 ≠ 0 := by
  have he : triangle r 0 3 6 = 216 := by
    dsimp [triangle,coordA,coordB,]
    ring
  rw [he]
  exact (by norm_num : (216 : ℚ) ≠ 0)

private lemma triangle_0_3_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 3 7 ≠ 0 := by
  have he : triangle r 0 3 7 = -18 * (exceptional1 r) := by
    dsimp [triangle,coordA,coordB,exceptional1]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional1_ne hr))

private lemma triangle_0_4_5_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 4 5 ≠ 0 := by
  have he : triangle r 0 4 5 = 18 * (exceptional2 r) := by
    dsimp [triangle,coordA,coordB,exceptional2]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (18 : ℚ) ≠ 0) (exceptional2_ne hr))

private lemma triangle_0_4_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 4 6 ≠ 0 := by
  have he : triangle r 0 4 6 = -36 * (exceptional7 r) := by
    dsimp [triangle,coordA,coordB,exceptional7]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-36 : ℚ) ≠ 0) (exceptional7_ne hr))

private lemma triangle_0_4_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 4 7 ≠ 0 := by
  have he : triangle r 0 4 7 = 36 * (exceptional7 r) := by
    dsimp [triangle,coordA,coordB,exceptional7]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) (exceptional7_ne hr))

private lemma triangle_0_5_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 5 6 ≠ 0 := by
  have he : triangle r 0 5 6 = 72 := by
    dsimp [triangle,coordA,coordB,]
    ring
  rw [he]
  exact (by norm_num : (72 : ℚ) ≠ 0)

private lemma triangle_0_5_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 5 7 ≠ 0 := by
  have he : triangle r 0 5 7 = -18 * (exceptional5 r) := by
    dsimp [triangle,coordA,coordB,exceptional5]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional5_ne hr))

private lemma triangle_0_6_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 0 6 7 ≠ 0 := by
  have he : triangle r 0 6 7 = 36 * (exceptional7 r) := by
    dsimp [triangle,coordA,coordB,exceptional7]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) (exceptional7_ne hr))

private lemma triangle_1_2_3_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 2 3 ≠ 0 := by
  have he : triangle r 1 2 3 = 36 * (exceptional8 r) := by
    dsimp [triangle,coordA,coordB,exceptional8]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) (exceptional8_ne hr))

private lemma triangle_1_2_4_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 2 4 ≠ 0 := by
  have he : triangle r 1 2 4 = -24 * (exceptional9 r) := by
    dsimp [triangle,coordA,coordB,exceptional9]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-24 : ℚ) ≠ 0) (exceptional9_ne hr))

private lemma triangle_1_2_5_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 2 5 ≠ 0 := by
  have he : triangle r 1 2 5 = -12 * (exceptional8 r) := by
    dsimp [triangle,coordA,coordB,exceptional8]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-12 : ℚ) ≠ 0) (exceptional8_ne hr))

private lemma triangle_1_2_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 2 6 ≠ 0 := by
  have he : triangle r 1 2 6 = -12 * (exceptional10 r) := by
    dsimp [triangle,coordA,coordB,exceptional10]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-12 : ℚ) ≠ 0) (exceptional10_ne hr))

private lemma triangle_1_2_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 2 7 ≠ 0 := by
  have he : triangle r 1 2 7 = 24 * (exceptional9 r) := by
    dsimp [triangle,coordA,coordB,exceptional9]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (24 : ℚ) ≠ 0) (exceptional9_ne hr))

private lemma triangle_1_3_4_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 3 4 ≠ 0 := by
  have he : triangle r 1 3 4 = -18 * (exceptional11 r) := by
    dsimp [triangle,coordA,coordB,exceptional11]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional11_ne hr))

private lemma triangle_1_3_5_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 3 5 ≠ 0 := by
  have he : triangle r 1 3 5 = -36 * (exceptional8 r) := by
    dsimp [triangle,coordA,coordB,exceptional8]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-36 : ℚ) ≠ 0) (exceptional8_ne hr))

private lemma triangle_1_3_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 3 6 ≠ 0 := by
  have he : triangle r 1 3 6 = -18 * (exceptional11 r) := by
    dsimp [triangle,coordA,coordB,exceptional11]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional11_ne hr))

private lemma triangle_1_3_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 3 7 ≠ 0 := by
  have he : triangle r 1 3 7 = -18 * (exceptional1 r) := by
    dsimp [triangle,coordA,coordB,exceptional1]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional1_ne hr))

private lemma triangle_1_4_5_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 4 5 ≠ 0 := by
  have he : triangle r 1 4 5 = -18 * (exceptional2 r) := by
    dsimp [triangle,coordA,coordB,exceptional2]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional2_ne hr))

private lemma triangle_1_4_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 4 6 ≠ 0 := by
  have he : triangle r 1 4 6 = -18 * (exceptional11 r) := by
    dsimp [triangle,coordA,coordB,exceptional11]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional11_ne hr))

private lemma triangle_1_4_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 4 7 ≠ 0 := by
  have he : triangle r 1 4 7 = 72 * (exceptional9 r) := by
    dsimp [triangle,coordA,coordB,exceptional9]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (72 : ℚ) ≠ 0) (exceptional9_ne hr))

private lemma triangle_1_5_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 5 6 ≠ 0 := by
  have he : triangle r 1 5 6 = -18 * (exceptional12 r) := by
    dsimp [triangle,coordA,coordB,exceptional12]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional12_ne hr))

private lemma triangle_1_5_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 5 7 ≠ 0 := by
  have he : triangle r 1 5 7 = 18 * (exceptional12 r) := by
    dsimp [triangle,coordA,coordB,exceptional12]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (18 : ℚ) ≠ 0) (exceptional12_ne hr))

private lemma triangle_1_6_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 1 6 7 ≠ 0 := by
  have he : triangle r 1 6 7 = 54 * (exceptional12 r) := by
    dsimp [triangle,coordA,coordB,exceptional12]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (54 : ℚ) ≠ 0) (exceptional12_ne hr))

private lemma triangle_2_3_4_ne {r : ℚ} (hr : r ≠ 0) : triangle r 2 3 4 ≠ 0 := by
  have he : triangle r 2 3 4 = -6 * (exceptional4 r) := by
    dsimp [triangle,coordA,coordB,exceptional4]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-6 : ℚ) ≠ 0) (exceptional4_ne hr))

private lemma triangle_2_3_5_ne {r : ℚ} (hr : r ≠ 0) : triangle r 2 3 5 ≠ 0 := by
  have he : triangle r 2 3 5 = 12 * (exceptional8 r) := by
    dsimp [triangle,coordA,coordB,exceptional8]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (12 : ℚ) ≠ 0) (exceptional8_ne hr))

private lemma triangle_2_3_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 2 3 6 ≠ 0 := by
  have he : triangle r 2 3 6 = 6 * (exceptional13 r) := by
    dsimp [triangle,coordA,coordB,exceptional13]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (6 : ℚ) ≠ 0) (exceptional13_ne hr))

private lemma triangle_2_3_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 2 3 7 ≠ 0 := by
  have he : triangle r 2 3 7 = -6 * (exceptional13 r) := by
    dsimp [triangle,coordA,coordB,exceptional13]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-6 : ℚ) ≠ 0) (exceptional13_ne hr))

private lemma triangle_2_4_5_ne {r : ℚ} (hr : r ≠ 0) : triangle r 2 4 5 ≠ 0 := by
  have he : triangle r 2 4 5 = -6 * (exceptional14 r) := by
    dsimp [triangle,coordA,coordB,exceptional14]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-6 : ℚ) ≠ 0) (exceptional14_ne hr))

private lemma triangle_2_4_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 2 4 6 ≠ 0 := by
  have he : triangle r 2 4 6 = -18 * (exceptional14 r) := by
    dsimp [triangle,coordA,coordB,exceptional14]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional14_ne hr))

private lemma triangle_2_4_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 2 4 7 ≠ 0 := by
  have he : triangle r 2 4 7 = 24 * (exceptional9 r) := by
    dsimp [triangle,coordA,coordB,exceptional9]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (24 : ℚ) ≠ 0) (exceptional9_ne hr))

private lemma triangle_2_5_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 2 5 6 ≠ 0 := by
  have he : triangle r 2 5 6 = 6 * (exceptional14 r) := by
    dsimp [triangle,coordA,coordB,exceptional14]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (6 : ℚ) ≠ 0) (exceptional14_ne hr))

private lemma triangle_2_5_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 2 5 7 ≠ 0 := by
  have he : triangle r 2 5 7 = 6 * (exceptional5 r) := by
    dsimp [triangle,coordA,coordB,exceptional5]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (6 : ℚ) ≠ 0) (exceptional5_ne hr))

private lemma triangle_2_6_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 2 6 7 ≠ 0 := by
  have he : triangle r 2 6 7 = 6 * (exceptional13 r) := by
    dsimp [triangle,coordA,coordB,exceptional13]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (6 : ℚ) ≠ 0) (exceptional13_ne hr))

private lemma triangle_3_4_5_ne {r : ℚ} (hr : r ≠ 0) : triangle r 3 4 5 ≠ 0 := by
  have he : triangle r 3 4 5 = -36 * (exceptional15 r) := by
    dsimp [triangle,coordA,coordB,exceptional15]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-36 : ℚ) ≠ 0) (exceptional15_ne hr))

private lemma triangle_3_4_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 3 4 6 ≠ 0 := by
  have he : triangle r 3 4 6 = -18 * (exceptional11 r) := by
    dsimp [triangle,coordA,coordB,exceptional11]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-18 : ℚ) ≠ 0) (exceptional11_ne hr))

private lemma triangle_3_4_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 3 4 7 ≠ 0 := by
  have he : triangle r 3 4 7 = 36 * (exceptional3 r) := by
    dsimp [triangle,coordA,coordB,exceptional3]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) (exceptional3_ne hr))

private lemma triangle_3_5_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 3 5 6 ≠ 0 := by
  have he : triangle r 3 5 6 = -72 := by
    dsimp [triangle,coordA,coordB,]
    ring
  rw [he]
  exact (by norm_num : (-72 : ℚ) ≠ 0)

private lemma triangle_3_5_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 3 5 7 ≠ 0 := by
  have he : triangle r 3 5 7 = 36 * (exceptional16 r) := by
    dsimp [triangle,coordA,coordB,exceptional16]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) (exceptional16_ne hr))

private lemma triangle_3_6_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 3 6 7 ≠ 0 := by
  have he : triangle r 3 6 7 = 18 * (exceptional13 r) := by
    dsimp [triangle,coordA,coordB,exceptional13]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (18 : ℚ) ≠ 0) (exceptional13_ne hr))

private lemma triangle_4_5_6_ne {r : ℚ} (hr : r ≠ 0) : triangle r 4 5 6 ≠ 0 := by
  have he : triangle r 4 5 6 = 18 * (exceptional14 r) := by
    dsimp [triangle,coordA,coordB,exceptional14]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (18 : ℚ) ≠ 0) (exceptional14_ne hr))

private lemma triangle_4_5_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 4 5 7 ≠ 0 := by
  have he : triangle r 4 5 7 = -36 * (exceptional17 r) := by
    dsimp [triangle,coordA,coordB,exceptional17]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-36 : ℚ) ≠ 0) (exceptional17_ne hr))

private lemma triangle_4_6_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 4 6 7 ≠ 0 := by
  have he : triangle r 4 6 7 = -36 * (exceptional7 r) := by
    dsimp [triangle,coordA,coordB,exceptional7]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-36 : ℚ) ≠ 0) (exceptional7_ne hr))

private lemma triangle_5_6_7_ne {r : ℚ} (hr : r ≠ 0) : triangle r 5 6 7 ≠ 0 := by
  have he : triangle r 5 6 7 = 18 * (exceptional12 r) := by
    dsimp [triangle,coordA,coordB,exceptional12]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (18 : ℚ) ≠ 0) (exceptional12_ne hr))

private lemma triangle_sorted_cases : ∀ i j k : Fin 8, i < j → j < k →
    (i = 0 ∧ j = 1 ∧ k = 2) ∨
    (i = 0 ∧ j = 1 ∧ k = 3) ∨
    (i = 0 ∧ j = 1 ∧ k = 4) ∨
    (i = 0 ∧ j = 1 ∧ k = 5) ∨
    (i = 0 ∧ j = 1 ∧ k = 6) ∨
    (i = 0 ∧ j = 1 ∧ k = 7) ∨
    (i = 0 ∧ j = 2 ∧ k = 3) ∨
    (i = 0 ∧ j = 2 ∧ k = 4) ∨
    (i = 0 ∧ j = 2 ∧ k = 5) ∨
    (i = 0 ∧ j = 2 ∧ k = 6) ∨
    (i = 0 ∧ j = 2 ∧ k = 7) ∨
    (i = 0 ∧ j = 3 ∧ k = 4) ∨
    (i = 0 ∧ j = 3 ∧ k = 5) ∨
    (i = 0 ∧ j = 3 ∧ k = 6) ∨
    (i = 0 ∧ j = 3 ∧ k = 7) ∨
    (i = 0 ∧ j = 4 ∧ k = 5) ∨
    (i = 0 ∧ j = 4 ∧ k = 6) ∨
    (i = 0 ∧ j = 4 ∧ k = 7) ∨
    (i = 0 ∧ j = 5 ∧ k = 6) ∨
    (i = 0 ∧ j = 5 ∧ k = 7) ∨
    (i = 0 ∧ j = 6 ∧ k = 7) ∨
    (i = 1 ∧ j = 2 ∧ k = 3) ∨
    (i = 1 ∧ j = 2 ∧ k = 4) ∨
    (i = 1 ∧ j = 2 ∧ k = 5) ∨
    (i = 1 ∧ j = 2 ∧ k = 6) ∨
    (i = 1 ∧ j = 2 ∧ k = 7) ∨
    (i = 1 ∧ j = 3 ∧ k = 4) ∨
    (i = 1 ∧ j = 3 ∧ k = 5) ∨
    (i = 1 ∧ j = 3 ∧ k = 6) ∨
    (i = 1 ∧ j = 3 ∧ k = 7) ∨
    (i = 1 ∧ j = 4 ∧ k = 5) ∨
    (i = 1 ∧ j = 4 ∧ k = 6) ∨
    (i = 1 ∧ j = 4 ∧ k = 7) ∨
    (i = 1 ∧ j = 5 ∧ k = 6) ∨
    (i = 1 ∧ j = 5 ∧ k = 7) ∨
    (i = 1 ∧ j = 6 ∧ k = 7) ∨
    (i = 2 ∧ j = 3 ∧ k = 4) ∨
    (i = 2 ∧ j = 3 ∧ k = 5) ∨
    (i = 2 ∧ j = 3 ∧ k = 6) ∨
    (i = 2 ∧ j = 3 ∧ k = 7) ∨
    (i = 2 ∧ j = 4 ∧ k = 5) ∨
    (i = 2 ∧ j = 4 ∧ k = 6) ∨
    (i = 2 ∧ j = 4 ∧ k = 7) ∨
    (i = 2 ∧ j = 5 ∧ k = 6) ∨
    (i = 2 ∧ j = 5 ∧ k = 7) ∨
    (i = 2 ∧ j = 6 ∧ k = 7) ∨
    (i = 3 ∧ j = 4 ∧ k = 5) ∨
    (i = 3 ∧ j = 4 ∧ k = 6) ∨
    (i = 3 ∧ j = 4 ∧ k = 7) ∨
    (i = 3 ∧ j = 5 ∧ k = 6) ∨
    (i = 3 ∧ j = 5 ∧ k = 7) ∨
    (i = 3 ∧ j = 6 ∧ k = 7) ∨
    (i = 4 ∧ j = 5 ∧ k = 6) ∨
    (i = 4 ∧ j = 5 ∧ k = 7) ∨
    (i = 4 ∧ j = 6 ∧ k = 7) ∨
    (i = 5 ∧ j = 6 ∧ k = 7) := by decide

lemma triangle_sorted_ne {r : ℚ} (hr : r ≠ 0) (i j k : Fin 8)
    (hij : i < j) (hjk : j < k) : triangle r i j k ≠ 0 := by
  rcases triangle_sorted_cases i j k hij hjk with
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩
  · exact triangle_0_1_2_ne hr
  · exact triangle_0_1_3_ne hr
  · exact triangle_0_1_4_ne hr
  · exact triangle_0_1_5_ne hr
  · exact triangle_0_1_6_ne hr
  · exact triangle_0_1_7_ne hr
  · exact triangle_0_2_3_ne hr
  · exact triangle_0_2_4_ne hr
  · exact triangle_0_2_5_ne hr
  · exact triangle_0_2_6_ne hr
  · exact triangle_0_2_7_ne hr
  · exact triangle_0_3_4_ne hr
  · exact triangle_0_3_5_ne hr
  · exact triangle_0_3_6_ne hr
  · exact triangle_0_3_7_ne hr
  · exact triangle_0_4_5_ne hr
  · exact triangle_0_4_6_ne hr
  · exact triangle_0_4_7_ne hr
  · exact triangle_0_5_6_ne hr
  · exact triangle_0_5_7_ne hr
  · exact triangle_0_6_7_ne hr
  · exact triangle_1_2_3_ne hr
  · exact triangle_1_2_4_ne hr
  · exact triangle_1_2_5_ne hr
  · exact triangle_1_2_6_ne hr
  · exact triangle_1_2_7_ne hr
  · exact triangle_1_3_4_ne hr
  · exact triangle_1_3_5_ne hr
  · exact triangle_1_3_6_ne hr
  · exact triangle_1_3_7_ne hr
  · exact triangle_1_4_5_ne hr
  · exact triangle_1_4_6_ne hr
  · exact triangle_1_4_7_ne hr
  · exact triangle_1_5_6_ne hr
  · exact triangle_1_5_7_ne hr
  · exact triangle_1_6_7_ne hr
  · exact triangle_2_3_4_ne hr
  · exact triangle_2_3_5_ne hr
  · exact triangle_2_3_6_ne hr
  · exact triangle_2_3_7_ne hr
  · exact triangle_2_4_5_ne hr
  · exact triangle_2_4_6_ne hr
  · exact triangle_2_4_7_ne hr
  · exact triangle_2_5_6_ne hr
  · exact triangle_2_5_7_ne hr
  · exact triangle_2_6_7_ne hr
  · exact triangle_3_4_5_ne hr
  · exact triangle_3_4_6_ne hr
  · exact triangle_3_4_7_ne hr
  · exact triangle_3_5_6_ne hr
  · exact triangle_3_5_7_ne hr
  · exact triangle_3_6_7_ne hr
  · exact triangle_4_5_6_ne hr
  · exact triangle_4_5_7_ne hr
  · exact triangle_4_6_7_ne hr
  · exact triangle_5_6_7_ne hr

private lemma circle_0_1_2_3_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 2 3 ≠ 0 := by
  have he : circle r 0 1 2 3 = 72 * (exceptional4 r) * (exceptional18 r) := by
    dsimp [circle,coordA,coordB,exceptional4,exceptional18,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (72 : ℚ) ≠ 0) (exceptional4_ne hr)) (exceptional18_ne hr))

private lemma circle_0_1_2_4_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 2 4 ≠ 0 := by
  have he : circle r 0 1 2 4 = 216 * (exceptional9 r) * (exceptional4 r) * (exceptional2 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional4,exceptional2,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (216 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional4_ne hr)) (exceptional2_ne hr))

private lemma circle_0_1_2_5_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 2 5 ≠ 0 := by
  have he : circle r 0 1 2 5 = -72 * (exceptional2 r) * (exceptional19 r) := by
    dsimp [circle,coordA,coordB,exceptional2,exceptional19,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (exceptional2_ne hr)) (exceptional19_ne hr))

private lemma circle_0_1_2_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 2 6 ≠ 0 := by
  have he : circle r 0 1 2 6 = -144 * (exceptional20 r) := by
    dsimp [circle,coordA,coordB,exceptional20,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-144 : ℚ) ≠ 0) (exceptional20_ne hr))

private lemma circle_0_1_2_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 2 7 ≠ 0 := by
  have he : circle r 0 1 2 7 = -72 * (exceptional9 r) * (exceptional21 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional21,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional21_ne hr))

private lemma circle_0_1_3_4_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 3 4 ≠ 0 := by
  have he : circle r 0 1 3 4 = 324 * (exceptional7 r) * (exceptional4 r) * (exceptional2 r) := by
    dsimp [circle,coordA,coordB,exceptional7,exceptional4,exceptional2,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (324 : ℚ) ≠ 0) (exceptional7_ne hr)) (exceptional4_ne hr)) (exceptional2_ne hr))

private lemma circle_0_1_3_5_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 3 5 ≠ 0 := by
  have he : circle r 0 1 3 5 = -648 * (exceptional2 r) * (exceptional11 r) := by
    dsimp [circle,coordA,coordB,exceptional2,exceptional11,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional2_ne hr)) (exceptional11_ne hr))

private lemma circle_0_1_3_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 3 6 ≠ 0 := by
  have he : circle r 0 1 3 6 = -648 * (exceptional21 r) := by
    dsimp [circle,coordA,coordB,exceptional21,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional21_ne hr))

private lemma circle_0_1_3_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 3 7 ≠ 0 := by
  have he : circle r 0 1 3 7 = -324 * (exceptional3 r) * (exceptional1 r) * (exceptional14 r) := by
    dsimp [circle,coordA,coordB,exceptional3,exceptional1,exceptional14,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-324 : ℚ) ≠ 0) (exceptional3_ne hr)) (exceptional1_ne hr)) (exceptional14_ne hr))

private lemma circle_0_1_4_5_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 4 5 ≠ 0 := by
  have he : circle r 0 1 4 5 = -324 * (exceptional3 r) * (exceptional2 r)^2 := by
    dsimp [circle,coordA,coordB,exceptional3,exceptional2,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-324 : ℚ) ≠ 0) (exceptional3_ne hr)) (pow_ne_zero 2 (exceptional2_ne hr)))

private lemma circle_0_1_4_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 4 6 ≠ 0 := by
  have he : circle r 0 1 4 6 = -648 * (exceptional2 r) * (exceptional19 r) := by
    dsimp [circle,coordA,coordB,exceptional2,exceptional19,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional2_ne hr)) (exceptional19_ne hr))

private lemma circle_0_1_4_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 4 7 ≠ 0 := by
  have he : circle r 0 1 4 7 = -648 * (exceptional9 r) * (exceptional2 r) * (exceptional11 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional2,exceptional11,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional2_ne hr)) (exceptional11_ne hr))

private lemma circle_0_1_5_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 5 6 ≠ 0 := by
  have he : circle r 0 1 5 6 = -1944 * (exceptional2 r) * (exceptional12 r) := by
    dsimp [circle,coordA,coordB,exceptional2,exceptional12,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-1944 : ℚ) ≠ 0) (exceptional2_ne hr)) (exceptional12_ne hr))

private lemma circle_0_1_5_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 5 7 ≠ 0 := by
  have he : circle r 0 1 5 7 = -324 * (exceptional7 r) * (exceptional2 r) * (exceptional12 r) := by
    dsimp [circle,coordA,coordB,exceptional7,exceptional2,exceptional12,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-324 : ℚ) ≠ 0) (exceptional7_ne hr)) (exceptional2_ne hr)) (exceptional12_ne hr))

private lemma circle_0_1_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 1 6 7 ≠ 0 := by
  have he : circle r 0 1 6 7 = 648 * (exceptional12 r) * (exceptional18 r) := by
    dsimp [circle,coordA,coordB,exceptional12,exceptional18,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (648 : ℚ) ≠ 0) (exceptional12_ne hr)) (exceptional18_ne hr))

private lemma circle_0_2_3_4_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 2 3 4 ≠ 0 := by
  have he : circle r 0 2 3 4 = -36 * (exceptional3 r) * (exceptional4 r)^2 := by
    dsimp [circle,coordA,coordB,exceptional3,exceptional4,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-36 : ℚ) ≠ 0) (exceptional3_ne hr)) (pow_ne_zero 2 (exceptional4_ne hr)))

private lemma circle_0_2_3_5_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 2 3 5 ≠ 0 := by
  have he : circle r 0 2 3 5 = 72 * (exceptional1 r) * (exceptional4 r) := by
    dsimp [circle,coordA,coordB,exceptional1,exceptional4,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (72 : ℚ) ≠ 0) (exceptional1_ne hr)) (exceptional4_ne hr))

private lemma circle_0_2_3_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 2 3 6 ≠ 0 := by
  have he : circle r 0 2 3 6 = 216 * (exceptional4 r) * (exceptional13 r) := by
    dsimp [circle,coordA,coordB,exceptional4,exceptional13,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (216 : ℚ) ≠ 0) (exceptional4_ne hr)) (exceptional13_ne hr))

private lemma circle_0_2_3_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 2 3 7 ≠ 0 := by
  have he : circle r 0 2 3 7 = 36 * (exceptional7 r) * (exceptional4 r) * (exceptional13 r) := by
    dsimp [circle,coordA,coordB,exceptional7,exceptional4,exceptional13,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) (exceptional7_ne hr)) (exceptional4_ne hr)) (exceptional13_ne hr))

private lemma circle_0_2_4_5_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 2 4 5 ≠ 0 := by
  have he : circle r 0 2 4 5 = 36 * (exceptional7 r) * (exceptional4 r) * (exceptional2 r) := by
    dsimp [circle,coordA,coordB,exceptional7,exceptional4,exceptional2,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) (exceptional7_ne hr)) (exceptional4_ne hr)) (exceptional2_ne hr))

private lemma circle_0_2_4_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 2 4 6 ≠ 0 := by
  have he : circle r 0 2 4 6 = -72 * (exceptional4 r) * (exceptional18 r) := by
    dsimp [circle,coordA,coordB,exceptional4,exceptional18,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (exceptional4_ne hr)) (exceptional18_ne hr))

private lemma circle_0_2_4_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 2 4 7 ≠ 0 := by
  have he : circle r 0 2 4 7 = -72 * (exceptional9 r) * (exceptional1 r) * (exceptional4 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional1,exceptional4,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional1_ne hr)) (exceptional4_ne hr))

private lemma circle_0_2_5_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 2 5 6 ≠ 0 := by
  have he : circle r 0 2 5 6 = 72 * (exceptional21 r) := by
    dsimp [circle,coordA,coordB,exceptional21,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (72 : ℚ) ≠ 0) (exceptional21_ne hr))

private lemma circle_0_2_5_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 2 5 7 ≠ 0 := by
  have he : circle r 0 2 5 7 = 36 * (exceptional3 r) * (exceptional5 r) * (exceptional11 r) := by
    dsimp [circle,coordA,coordB,exceptional3,exceptional5,exceptional11,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) (exceptional3_ne hr)) (exceptional5_ne hr)) (exceptional11_ne hr))

private lemma circle_0_2_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 2 6 7 ≠ 0 := by
  have he : circle r 0 2 6 7 = 72 * (exceptional13 r) * (exceptional19 r) := by
    dsimp [circle,coordA,coordB,exceptional13,exceptional19,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (72 : ℚ) ≠ 0) (exceptional13_ne hr)) (exceptional19_ne hr))

private lemma circle_0_3_4_5_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 3 4 5 ≠ 0 := by
  have he : circle r 0 3 4 5 = -648 * (exceptional4 r) * (exceptional2 r) := by
    dsimp [circle,coordA,coordB,exceptional4,exceptional2,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional4_ne hr)) (exceptional2_ne hr))

private lemma circle_0_3_4_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 3 4 6 ≠ 0 := by
  have he : circle r 0 3 4 6 = -648 * (exceptional1 r) * (exceptional4 r) := by
    dsimp [circle,coordA,coordB,exceptional1,exceptional4,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional1_ne hr)) (exceptional4_ne hr))

private lemma circle_0_3_4_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 3 4 7 ≠ 0 := by
  have he : circle r 0 3 4 7 = -648 * (exceptional4 r) * (exceptional22 r) := by
    dsimp [circle,coordA,coordB,exceptional4,exceptional22,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional4_ne hr)) (exceptional22_ne hr))

private lemma circle_0_3_5_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 3 5 6 ≠ 0 := by
  have he : circle r 0 3 5 6 = 5184 * (exceptional3 r) := by
    dsimp [circle,coordA,coordB,exceptional3,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (5184 : ℚ) ≠ 0) (exceptional3_ne hr))

private lemma circle_0_3_5_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 3 5 7 ≠ 0 := by
  have he : circle r 0 3 5 7 = 648 * (exceptional23 r) := by
    dsimp [circle,coordA,coordB,exceptional23,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (648 : ℚ) ≠ 0) (exceptional23_ne hr))

private lemma circle_0_3_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 3 6 7 ≠ 0 := by
  have he : circle r 0 3 6 7 = 648 * (exceptional11 r) * (exceptional13 r) := by
    dsimp [circle,coordA,coordB,exceptional11,exceptional13,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (648 : ℚ) ≠ 0) (exceptional11_ne hr)) (exceptional13_ne hr))

private lemma circle_0_4_5_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 4 5 6 ≠ 0 := by
  have he : circle r 0 4 5 6 = 648 * (exceptional2 r) * (exceptional11 r) := by
    dsimp [circle,coordA,coordB,exceptional2,exceptional11,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (648 : ℚ) ≠ 0) (exceptional2_ne hr)) (exceptional11_ne hr))

private lemma circle_0_4_5_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 4 5 7 ≠ 0 := by
  have he : circle r 0 4 5 7 = 648 * (exceptional2 r) * (exceptional24 r) := by
    dsimp [circle,coordA,coordB,exceptional2,exceptional24,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (648 : ℚ) ≠ 0) (exceptional2_ne hr)) (exceptional24_ne hr))

private lemma circle_0_4_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 4 6 7 ≠ 0 := by
  have he : circle r 0 4 6 7 = -1296 * (exceptional7 r) * (exceptional3 r) * (exceptional8 r) := by
    dsimp [circle,coordA,coordB,exceptional7,exceptional3,exceptional8,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-1296 : ℚ) ≠ 0) (exceptional7_ne hr)) (exceptional3_ne hr)) (exceptional8_ne hr))

private lemma circle_0_5_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 0 5 6 7 ≠ 0 := by
  have he : circle r 0 5 6 7 = 648 * (exceptional1 r) * (exceptional12 r) := by
    dsimp [circle,coordA,coordB,exceptional1,exceptional12,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (648 : ℚ) ≠ 0) (exceptional1_ne hr)) (exceptional12_ne hr))

private lemma circle_1_2_3_4_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 2 3 4 ≠ 0 := by
  have he : circle r 1 2 3 4 = -72 * (exceptional9 r) * (exceptional1 r) * (exceptional4 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional1,exceptional4,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional1_ne hr)) (exceptional4_ne hr))

private lemma circle_1_2_3_5_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 2 3 5 ≠ 0 := by
  have he : circle r 1 2 3 5 = -144 * (exceptional7 r) * (exceptional3 r) * (exceptional8 r) := by
    dsimp [circle,coordA,coordB,exceptional7,exceptional3,exceptional8,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-144 : ℚ) ≠ 0) (exceptional7_ne hr)) (exceptional3_ne hr)) (exceptional8_ne hr))

private lemma circle_1_2_3_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 2 3 6 ≠ 0 := by
  have he : circle r 1 2 3 6 = 72 * (exceptional13 r) * (exceptional19 r) := by
    dsimp [circle,coordA,coordB,exceptional13,exceptional19,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (72 : ℚ) ≠ 0) (exceptional13_ne hr)) (exceptional19_ne hr))

private lemma circle_1_2_3_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 2 3 7 ≠ 0 := by
  have he : circle r 1 2 3 7 = 72 * (exceptional9 r) * (exceptional11 r) * (exceptional13 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional11,exceptional13,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (72 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional11_ne hr)) (exceptional13_ne hr))

private lemma circle_1_2_4_5_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 2 4 5 ≠ 0 := by
  have he : circle r 1 2 4 5 = -72 * (exceptional9 r) * (exceptional2 r) * (exceptional11 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional2,exceptional11,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional2_ne hr)) (exceptional11_ne hr))

private lemma circle_1_2_4_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 2 4 6 ≠ 0 := by
  have he : circle r 1 2 4 6 = -72 * (exceptional9 r) * (exceptional21 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional21,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional21_ne hr))

private lemma circle_1_2_4_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 2 4 7 ≠ 0 := by
  have he : circle r 1 2 4 7 = -576 * (exceptional3 r) * (exceptional9 r)^2 := by
    dsimp [circle,coordA,coordB,exceptional3,exceptional9,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-576 : ℚ) ≠ 0) (exceptional3_ne hr)) (pow_ne_zero 2 (exceptional9_ne hr)))

private lemma circle_1_2_5_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 2 5 6 ≠ 0 := by
  have he : circle r 1 2 5 6 = -72 * (exceptional12 r) * (exceptional18 r) := by
    dsimp [circle,coordA,coordB,exceptional12,exceptional18,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (exceptional12_ne hr)) (exceptional18_ne hr))

private lemma circle_1_2_5_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 2 5 7 ≠ 0 := by
  have he : circle r 1 2 5 7 = -72 * (exceptional9 r) * (exceptional1 r) * (exceptional12 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional1,exceptional12,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional1_ne hr)) (exceptional12_ne hr))

private lemma circle_1_2_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 2 6 7 ≠ 0 := by
  have he : circle r 1 2 6 7 = -216 * (exceptional9 r) * (exceptional12 r) * (exceptional13 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional12,exceptional13,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-216 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional12_ne hr)) (exceptional13_ne hr))

private lemma circle_1_3_4_5_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 3 4 5 ≠ 0 := by
  have he : circle r 1 3 4 5 = -648 * (exceptional2 r) * (exceptional24 r) := by
    dsimp [circle,coordA,coordB,exceptional2,exceptional24,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional2_ne hr)) (exceptional24_ne hr))

private lemma circle_1_3_4_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 3 4 6 ≠ 0 := by
  have he : circle r 1 3 4 6 = -324 * (exceptional3 r) * (exceptional5 r) * (exceptional11 r) := by
    dsimp [circle,coordA,coordB,exceptional3,exceptional5,exceptional11,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-324 : ℚ) ≠ 0) (exceptional3_ne hr)) (exceptional5_ne hr)) (exceptional11_ne hr))

private lemma circle_1_3_4_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 3 4 7 ≠ 0 := by
  have he : circle r 1 3 4 7 = -648 * (exceptional9 r) * (exceptional23 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional23,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional23_ne hr))

private lemma circle_1_3_5_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 3 5 6 ≠ 0 := by
  have he : circle r 1 3 5 6 = -648 * (exceptional1 r) * (exceptional12 r) := by
    dsimp [circle,coordA,coordB,exceptional1,exceptional12,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional1_ne hr)) (exceptional12_ne hr))

private lemma circle_1_3_5_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 3 5 7 ≠ 0 := by
  have he : circle r 1 3 5 7 = -648 * (exceptional12 r) * (exceptional22 r) := by
    dsimp [circle,coordA,coordB,exceptional12,exceptional22,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional12_ne hr)) (exceptional22_ne hr))

private lemma circle_1_3_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 3 6 7 ≠ 0 := by
  have he : circle r 1 3 6 7 = -324 * (exceptional7 r) * (exceptional12 r) * (exceptional13 r) := by
    dsimp [circle,coordA,coordB,exceptional7,exceptional12,exceptional13,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-324 : ℚ) ≠ 0) (exceptional7_ne hr)) (exceptional12_ne hr)) (exceptional13_ne hr))

private lemma circle_1_4_5_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 4 5 6 ≠ 0 := by
  have he : circle r 1 4 5 6 = 324 * (exceptional7 r) * (exceptional2 r) * (exceptional12 r) := by
    dsimp [circle,coordA,coordB,exceptional7,exceptional2,exceptional12,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (324 : ℚ) ≠ 0) (exceptional7_ne hr)) (exceptional2_ne hr)) (exceptional12_ne hr))

private lemma circle_1_4_5_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 4 5 7 ≠ 0 := by
  have he : circle r 1 4 5 7 = -648 * (exceptional9 r) * (exceptional2 r) * (exceptional12 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional2,exceptional12,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional2_ne hr)) (exceptional12_ne hr))

private lemma circle_1_4_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 4 6 7 ≠ 0 := by
  have he : circle r 1 4 6 7 = -648 * (exceptional9 r) * (exceptional1 r) * (exceptional12 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional1,exceptional12,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional1_ne hr)) (exceptional12_ne hr))

private lemma circle_1_5_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 1 5 6 7 ≠ 0 := by
  have he : circle r 1 5 6 7 = -324 * (exceptional3 r) * (exceptional12 r)^2 := by
    dsimp [circle,coordA,coordB,exceptional3,exceptional12,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-324 : ℚ) ≠ 0) (exceptional3_ne hr)) (pow_ne_zero 2 (exceptional12_ne hr)))

private lemma circle_2_3_4_5_ne {r : ℚ} (hr : r ≠ 0) : circle r 2 3 4 5 ≠ 0 := by
  have he : circle r 2 3 4 5 = 72 * (exceptional4 r) * (exceptional22 r) := by
    dsimp [circle,coordA,coordB,exceptional4,exceptional22,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (72 : ℚ) ≠ 0) (exceptional4_ne hr)) (exceptional22_ne hr))

private lemma circle_2_3_4_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 2 3 4 6 ≠ 0 := by
  have he : circle r 2 3 4 6 = 36 * (exceptional7 r) * (exceptional4 r) * (exceptional13 r) := by
    dsimp [circle,coordA,coordB,exceptional7,exceptional4,exceptional13,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) (exceptional7_ne hr)) (exceptional4_ne hr)) (exceptional13_ne hr))

private lemma circle_2_3_4_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 2 3 4 7 ≠ 0 := by
  have he : circle r 2 3 4 7 = -72 * (exceptional9 r) * (exceptional4 r) * (exceptional13 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional4,exceptional13,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional4_ne hr)) (exceptional13_ne hr))

private lemma circle_2_3_5_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 2 3 5 6 ≠ 0 := by
  have he : circle r 2 3 5 6 = 72 * (exceptional11 r) * (exceptional13 r) := by
    dsimp [circle,coordA,coordB,exceptional11,exceptional13,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (72 : ℚ) ≠ 0) (exceptional11_ne hr)) (exceptional13_ne hr))

private lemma circle_2_3_5_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 2 3 5 7 ≠ 0 := by
  have he : circle r 2 3 5 7 = 72 * (exceptional13 r) * (exceptional24 r) := by
    dsimp [circle,coordA,coordB,exceptional13,exceptional24,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (72 : ℚ) ≠ 0) (exceptional13_ne hr)) (exceptional24_ne hr))

private lemma circle_2_3_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 2 3 6 7 ≠ 0 := by
  have he : circle r 2 3 6 7 = 36 * (exceptional3 r) * (exceptional13 r)^2 := by
    dsimp [circle,coordA,coordB,exceptional3,exceptional13,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) (exceptional3_ne hr)) (pow_ne_zero 2 (exceptional13_ne hr)))

private lemma circle_2_4_5_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 2 4 5 6 ≠ 0 := by
  have he : circle r 2 4 5 6 = -36 * (exceptional3 r) * (exceptional1 r) * (exceptional14 r) := by
    dsimp [circle,coordA,coordB,exceptional3,exceptional1,exceptional14,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-36 : ℚ) ≠ 0) (exceptional3_ne hr)) (exceptional1_ne hr)) (exceptional14_ne hr))

private lemma circle_2_4_5_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 2 4 5 7 ≠ 0 := by
  have he : circle r 2 4 5 7 = -72 * (exceptional9 r) * (exceptional23 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional23,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional23_ne hr))

private lemma circle_2_4_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 2 4 6 7 ≠ 0 := by
  have he : circle r 2 4 6 7 = -72 * (exceptional9 r) * (exceptional11 r) * (exceptional13 r) := by
    dsimp [circle,coordA,coordB,exceptional9,exceptional11,exceptional13,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-72 : ℚ) ≠ 0) (exceptional9_ne hr)) (exceptional11_ne hr)) (exceptional13_ne hr))

private lemma circle_2_5_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 2 5 6 7 ≠ 0 := by
  have he : circle r 2 5 6 7 = 36 * (exceptional7 r) * (exceptional12 r) * (exceptional13 r) := by
    dsimp [circle,coordA,coordB,exceptional7,exceptional12,exceptional13,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (36 : ℚ) ≠ 0) (exceptional7_ne hr)) (exceptional12_ne hr)) (exceptional13_ne hr))

private lemma circle_3_4_5_6_ne {r : ℚ} (hr : r ≠ 0) : circle r 3 4 5 6 ≠ 0 := by
  have he : circle r 3 4 5 6 = -648 * (exceptional23 r) := by
    dsimp [circle,coordA,coordB,exceptional23,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional23_ne hr))

private lemma circle_3_4_5_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 3 4 5 7 ≠ 0 := by
  have he : circle r 3 4 5 7 = -1296 * (exceptional25 r) := by
    dsimp [circle,coordA,coordB,exceptional25,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (by norm_num : (-1296 : ℚ) ≠ 0) (exceptional25_ne hr))

private lemma circle_3_4_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 3 4 6 7 ≠ 0 := by
  have he : circle r 3 4 6 7 = -648 * (exceptional13 r) * (exceptional24 r) := by
    dsimp [circle,coordA,coordB,exceptional13,exceptional24,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional13_ne hr)) (exceptional24_ne hr))

private lemma circle_3_5_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 3 5 6 7 ≠ 0 := by
  have he : circle r 3 5 6 7 = -648 * (exceptional12 r) * (exceptional13 r) := by
    dsimp [circle,coordA,coordB,exceptional12,exceptional13,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (-648 : ℚ) ≠ 0) (exceptional12_ne hr)) (exceptional13_ne hr))

private lemma circle_4_5_6_7_ne {r : ℚ} (hr : r ≠ 0) : circle r 4 5 6 7 ≠ 0 := by
  have he : circle r 4 5 6 7 = 648 * (exceptional12 r) * (exceptional22 r) := by
    dsimp [circle,coordA,coordB,exceptional12,exceptional22,quadNorm,det3]
    ring
  rw [he]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (648 : ℚ) ≠ 0) (exceptional12_ne hr)) (exceptional22_ne hr))

private lemma circle_sorted_cases : ∀ i j k l : Fin 8, i < j → j < k → k < l →
    (i = 0 ∧ j = 1 ∧ k = 2 ∧ l = 3) ∨
    (i = 0 ∧ j = 1 ∧ k = 2 ∧ l = 4) ∨
    (i = 0 ∧ j = 1 ∧ k = 2 ∧ l = 5) ∨
    (i = 0 ∧ j = 1 ∧ k = 2 ∧ l = 6) ∨
    (i = 0 ∧ j = 1 ∧ k = 2 ∧ l = 7) ∨
    (i = 0 ∧ j = 1 ∧ k = 3 ∧ l = 4) ∨
    (i = 0 ∧ j = 1 ∧ k = 3 ∧ l = 5) ∨
    (i = 0 ∧ j = 1 ∧ k = 3 ∧ l = 6) ∨
    (i = 0 ∧ j = 1 ∧ k = 3 ∧ l = 7) ∨
    (i = 0 ∧ j = 1 ∧ k = 4 ∧ l = 5) ∨
    (i = 0 ∧ j = 1 ∧ k = 4 ∧ l = 6) ∨
    (i = 0 ∧ j = 1 ∧ k = 4 ∧ l = 7) ∨
    (i = 0 ∧ j = 1 ∧ k = 5 ∧ l = 6) ∨
    (i = 0 ∧ j = 1 ∧ k = 5 ∧ l = 7) ∨
    (i = 0 ∧ j = 1 ∧ k = 6 ∧ l = 7) ∨
    (i = 0 ∧ j = 2 ∧ k = 3 ∧ l = 4) ∨
    (i = 0 ∧ j = 2 ∧ k = 3 ∧ l = 5) ∨
    (i = 0 ∧ j = 2 ∧ k = 3 ∧ l = 6) ∨
    (i = 0 ∧ j = 2 ∧ k = 3 ∧ l = 7) ∨
    (i = 0 ∧ j = 2 ∧ k = 4 ∧ l = 5) ∨
    (i = 0 ∧ j = 2 ∧ k = 4 ∧ l = 6) ∨
    (i = 0 ∧ j = 2 ∧ k = 4 ∧ l = 7) ∨
    (i = 0 ∧ j = 2 ∧ k = 5 ∧ l = 6) ∨
    (i = 0 ∧ j = 2 ∧ k = 5 ∧ l = 7) ∨
    (i = 0 ∧ j = 2 ∧ k = 6 ∧ l = 7) ∨
    (i = 0 ∧ j = 3 ∧ k = 4 ∧ l = 5) ∨
    (i = 0 ∧ j = 3 ∧ k = 4 ∧ l = 6) ∨
    (i = 0 ∧ j = 3 ∧ k = 4 ∧ l = 7) ∨
    (i = 0 ∧ j = 3 ∧ k = 5 ∧ l = 6) ∨
    (i = 0 ∧ j = 3 ∧ k = 5 ∧ l = 7) ∨
    (i = 0 ∧ j = 3 ∧ k = 6 ∧ l = 7) ∨
    (i = 0 ∧ j = 4 ∧ k = 5 ∧ l = 6) ∨
    (i = 0 ∧ j = 4 ∧ k = 5 ∧ l = 7) ∨
    (i = 0 ∧ j = 4 ∧ k = 6 ∧ l = 7) ∨
    (i = 0 ∧ j = 5 ∧ k = 6 ∧ l = 7) ∨
    (i = 1 ∧ j = 2 ∧ k = 3 ∧ l = 4) ∨
    (i = 1 ∧ j = 2 ∧ k = 3 ∧ l = 5) ∨
    (i = 1 ∧ j = 2 ∧ k = 3 ∧ l = 6) ∨
    (i = 1 ∧ j = 2 ∧ k = 3 ∧ l = 7) ∨
    (i = 1 ∧ j = 2 ∧ k = 4 ∧ l = 5) ∨
    (i = 1 ∧ j = 2 ∧ k = 4 ∧ l = 6) ∨
    (i = 1 ∧ j = 2 ∧ k = 4 ∧ l = 7) ∨
    (i = 1 ∧ j = 2 ∧ k = 5 ∧ l = 6) ∨
    (i = 1 ∧ j = 2 ∧ k = 5 ∧ l = 7) ∨
    (i = 1 ∧ j = 2 ∧ k = 6 ∧ l = 7) ∨
    (i = 1 ∧ j = 3 ∧ k = 4 ∧ l = 5) ∨
    (i = 1 ∧ j = 3 ∧ k = 4 ∧ l = 6) ∨
    (i = 1 ∧ j = 3 ∧ k = 4 ∧ l = 7) ∨
    (i = 1 ∧ j = 3 ∧ k = 5 ∧ l = 6) ∨
    (i = 1 ∧ j = 3 ∧ k = 5 ∧ l = 7) ∨
    (i = 1 ∧ j = 3 ∧ k = 6 ∧ l = 7) ∨
    (i = 1 ∧ j = 4 ∧ k = 5 ∧ l = 6) ∨
    (i = 1 ∧ j = 4 ∧ k = 5 ∧ l = 7) ∨
    (i = 1 ∧ j = 4 ∧ k = 6 ∧ l = 7) ∨
    (i = 1 ∧ j = 5 ∧ k = 6 ∧ l = 7) ∨
    (i = 2 ∧ j = 3 ∧ k = 4 ∧ l = 5) ∨
    (i = 2 ∧ j = 3 ∧ k = 4 ∧ l = 6) ∨
    (i = 2 ∧ j = 3 ∧ k = 4 ∧ l = 7) ∨
    (i = 2 ∧ j = 3 ∧ k = 5 ∧ l = 6) ∨
    (i = 2 ∧ j = 3 ∧ k = 5 ∧ l = 7) ∨
    (i = 2 ∧ j = 3 ∧ k = 6 ∧ l = 7) ∨
    (i = 2 ∧ j = 4 ∧ k = 5 ∧ l = 6) ∨
    (i = 2 ∧ j = 4 ∧ k = 5 ∧ l = 7) ∨
    (i = 2 ∧ j = 4 ∧ k = 6 ∧ l = 7) ∨
    (i = 2 ∧ j = 5 ∧ k = 6 ∧ l = 7) ∨
    (i = 3 ∧ j = 4 ∧ k = 5 ∧ l = 6) ∨
    (i = 3 ∧ j = 4 ∧ k = 5 ∧ l = 7) ∨
    (i = 3 ∧ j = 4 ∧ k = 6 ∧ l = 7) ∨
    (i = 3 ∧ j = 5 ∧ k = 6 ∧ l = 7) ∨
    (i = 4 ∧ j = 5 ∧ k = 6 ∧ l = 7) := by decide

lemma circle_sorted_ne {r : ℚ} (hr : r ≠ 0) (i j k l : Fin 8)
    (hij : i < j) (hjk : j < k) (hkl : k < l) : circle r i j k l ≠ 0 := by
  rcases circle_sorted_cases i j k l hij hjk hkl with
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩
  · exact circle_0_1_2_3_ne hr
  · exact circle_0_1_2_4_ne hr
  · exact circle_0_1_2_5_ne hr
  · exact circle_0_1_2_6_ne hr
  · exact circle_0_1_2_7_ne hr
  · exact circle_0_1_3_4_ne hr
  · exact circle_0_1_3_5_ne hr
  · exact circle_0_1_3_6_ne hr
  · exact circle_0_1_3_7_ne hr
  · exact circle_0_1_4_5_ne hr
  · exact circle_0_1_4_6_ne hr
  · exact circle_0_1_4_7_ne hr
  · exact circle_0_1_5_6_ne hr
  · exact circle_0_1_5_7_ne hr
  · exact circle_0_1_6_7_ne hr
  · exact circle_0_2_3_4_ne hr
  · exact circle_0_2_3_5_ne hr
  · exact circle_0_2_3_6_ne hr
  · exact circle_0_2_3_7_ne hr
  · exact circle_0_2_4_5_ne hr
  · exact circle_0_2_4_6_ne hr
  · exact circle_0_2_4_7_ne hr
  · exact circle_0_2_5_6_ne hr
  · exact circle_0_2_5_7_ne hr
  · exact circle_0_2_6_7_ne hr
  · exact circle_0_3_4_5_ne hr
  · exact circle_0_3_4_6_ne hr
  · exact circle_0_3_4_7_ne hr
  · exact circle_0_3_5_6_ne hr
  · exact circle_0_3_5_7_ne hr
  · exact circle_0_3_6_7_ne hr
  · exact circle_0_4_5_6_ne hr
  · exact circle_0_4_5_7_ne hr
  · exact circle_0_4_6_7_ne hr
  · exact circle_0_5_6_7_ne hr
  · exact circle_1_2_3_4_ne hr
  · exact circle_1_2_3_5_ne hr
  · exact circle_1_2_3_6_ne hr
  · exact circle_1_2_3_7_ne hr
  · exact circle_1_2_4_5_ne hr
  · exact circle_1_2_4_6_ne hr
  · exact circle_1_2_4_7_ne hr
  · exact circle_1_2_5_6_ne hr
  · exact circle_1_2_5_7_ne hr
  · exact circle_1_2_6_7_ne hr
  · exact circle_1_3_4_5_ne hr
  · exact circle_1_3_4_6_ne hr
  · exact circle_1_3_4_7_ne hr
  · exact circle_1_3_5_6_ne hr
  · exact circle_1_3_5_7_ne hr
  · exact circle_1_3_6_7_ne hr
  · exact circle_1_4_5_6_ne hr
  · exact circle_1_4_5_7_ne hr
  · exact circle_1_4_6_7_ne hr
  · exact circle_1_5_6_7_ne hr
  · exact circle_2_3_4_5_ne hr
  · exact circle_2_3_4_6_ne hr
  · exact circle_2_3_4_7_ne hr
  · exact circle_2_3_5_6_ne hr
  · exact circle_2_3_5_7_ne hr
  · exact circle_2_3_6_7_ne hr
  · exact circle_2_4_5_6_ne hr
  · exact circle_2_4_5_7_ne hr
  · exact circle_2_4_6_7_ne hr
  · exact circle_2_5_6_7_ne hr
  · exact circle_3_4_5_6_ne hr
  · exact circle_3_4_5_7_ne hr
  · exact circle_3_4_6_7_ne hr
  · exact circle_3_5_6_7_ne hr
  · exact circle_4_5_6_7_ne hr

#print axioms triangle_sorted_ne
#print axioms circle_sorted_ne


/- Connecting the arithmetic determinants to the real Euclidean plane. -/

open EuclideanGeometry

noncomputable def height (r : ℚ) : ℝ :=
  Real.sqrt (4*(traceC r : ℝ)-(traceB r : ℝ)^2)/2

noncomputable def realPoint (r : ℚ) (i : Fin 8) : ℝ² :=
  !₂[(coordA r i : ℝ)-(traceB r : ℝ)*(coordB r i : ℝ)/2,
    (coordB r i : ℝ)*height r]

lemma height_pos {r : ℚ} (hd : traceB r ^ 2 < 4*traceC r) : 0 < height r := by
  apply div_pos (Real.sqrt_pos.mpr ?_) (by norm_num)
  exact_mod_cast (sub_pos.mpr hd)

lemma height_sq {r : ℚ} (hd : traceB r ^ 2 < 4*traceC r) :
    height r ^ 2 = (traceC r : ℝ)-(traceB r : ℝ)^2/4 := by
  have hh : 0 ≤ 4*(traceC r : ℝ)-(traceB r : ℝ)^2 := by
    exact_mod_cast (sub_nonneg.mpr hd.le)
  have hs := Real.sq_sqrt hh
  dsimp [height]
  nlinarith [hs]

lemma realPoint_dist_sq {r : ℚ} (hd : traceB r ^ 2 < 4*traceC r) (i j : Fin 8) :
    dist (realPoint r i) (realPoint r j)^2 =
      (quadNorm r (coordA r j-coordA r i) (coordB r j-coordB r i) : ℝ) := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_two,Real.dist_eq, sq_abs]
  dsimp [realPoint,quadNorm]
  push_cast
  linear_combination ((coordB r j : ℝ)-(coordB r i : ℝ))^2 * height_sq hd

private lemma collinear_real_det {a b c : ℝ²} (h : Collinear ℝ {a,b,c}) :
    (b 0-a 0)*(c 1-a 1)-(b 1-a 1)*(c 0-a 0) = 0 := by
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem (by simp : a ∈ ({a,b,c} : Set ℝ²))).mp h
  obtain ⟨s,hs⟩ := hv b (by simp)
  obtain ⟨t,ht⟩ := hv c (by simp)
  subst b c
  simp
  ring

lemma sorted_not_collinear {r : ℚ} (hr : r ≠ 0)
    (hd : traceB r ^ 2 < 4*traceC r) (i j k : Fin 8) (hij : i < j) (hjk : j < k) :
    ¬Collinear ℝ {realPoint r i,realPoint r j,realPoint r k} := by
  intro hc
  have hh := collinear_real_det hc
  have he : (triangle r i j k : ℝ)*height r = 0 := by
    convert hh using 1
    dsimp [triangle,realPoint]
    push_cast
    ring
  have hn : (triangle r i j k : ℝ) ≠ 0 := by
    exact_mod_cast triangle_sorted_ne hr i j k hij hjk
  exact mul_ne_zero hn (ne_of_gt (height_pos hd)) he

private def realDet (a b c d e f g h i : ℝ) : ℝ :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

private lemma cospherical_real_det {a b c d : ℝ²} (h : Cospherical {a,b,c,d}) :
    realDet (b 0-a 0) (b 1-a 1) (dist a b^2)
      (c 0-a 0) (c 1-a 1) (dist a c^2)
      (d 0-a 0) (d 1-a 1) (dist a d^2) = 0 := by
  obtain ⟨o,r,h⟩ := h
  have ha := congrArg (fun z : ℝ => z^2) (h a (by simp))
  have hb := congrArg (fun z : ℝ => z^2) (h b (by simp))
  have hc := congrArg (fun z : ℝ => z^2) (h c (by simp))
  have hd := congrArg (fun z : ℝ => z^2) (h d (by simp))
  simp only [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two,Real.dist_eq,sq_abs] at ha hb hc hd ⊢
  unfold realDet
  linear_combination
    ((c 0-a 0)*(d 1-a 1)-(d 0-a 0)*(c 1-a 1)) * (hb-ha) +
    ((d 0-a 0)*(b 1-a 1)-(b 0-a 0)*(d 1-a 1)) * (hc-ha) +
    ((b 0-a 0)*(c 1-a 1)-(c 0-a 0)*(b 1-a 1)) * (hd-ha)

lemma sorted_not_cospherical {r : ℚ} (hr : r ≠ 0)
    (hd : traceB r ^ 2 < 4*traceC r) (i j k l : Fin 8)
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    ¬Cospherical {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
  intro hc
  have hh := cospherical_real_det hc
  simp only [realPoint_dist_sq hd] at hh
  have he : (circle r i j k l : ℝ)*height r = 0 := by
    convert hh using 1
    dsimp [circle,det3,realDet,realPoint]
    push_cast
    ring
  have hn : (circle r i j k l : ℝ) ≠ 0 := by
    exact_mod_cast circle_sorted_ne hr i j k l hij hjk hkl
  exact mul_ne_zero hn (ne_of_gt (height_pos hd)) he

lemma not_collinear {r : ℚ} (hr : r ≠ 0)
    (hd : traceB r ^ 2 < 4*traceC r) (i j k : Fin 8)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : ¬Collinear ℝ {realPoint r i,realPoint r j,realPoint r k} := by
  have horder : ∀ i j k : Fin 8, i ≠ j → i ≠ k → j ≠ k →
    (i < j ∧ j < k) ∨
    (i < k ∧ k < j) ∨
    (j < i ∧ i < k) ∨
    (j < k ∧ k < i) ∨
    (k < i ∧ i < j) ∨
    (k < j ∧ j < i) := by decide
  have ho := horder i j k hij hik hjk
  rcases ho with ⟨ha,hb⟩ |
    ⟨ha,hb⟩ |
    ⟨ha,hb⟩ |
    ⟨ha,hb⟩ |
    ⟨ha,hb⟩ |
    ⟨ha,hb⟩
  · have hset : ({realPoint r i,realPoint r j,realPoint r k} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_collinear hr hd i j k ha hb
  · have hset : ({realPoint r i,realPoint r k,realPoint r j} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_collinear hr hd i k j ha hb
  · have hset : ({realPoint r j,realPoint r i,realPoint r k} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_collinear hr hd j i k ha hb
  · have hset : ({realPoint r j,realPoint r k,realPoint r i} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_collinear hr hd j k i ha hb
  · have hset : ({realPoint r k,realPoint r i,realPoint r j} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_collinear hr hd k i j ha hb
  · have hset : ({realPoint r k,realPoint r j,realPoint r i} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_collinear hr hd k j i ha hb

lemma not_cospherical {r : ℚ} (hr : r ≠ 0)
    (hd : traceB r ^ 2 < 4*traceC r) (i j k l : Fin 8)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : ¬Cospherical {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
  have horder : ∀ i j k l : Fin 8, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    (i < j ∧ j < k ∧ k < l) ∨
    (i < j ∧ j < l ∧ l < k) ∨
    (i < k ∧ k < j ∧ j < l) ∨
    (i < k ∧ k < l ∧ l < j) ∨
    (i < l ∧ l < j ∧ j < k) ∨
    (i < l ∧ l < k ∧ k < j) ∨
    (j < i ∧ i < k ∧ k < l) ∨
    (j < i ∧ i < l ∧ l < k) ∨
    (j < k ∧ k < i ∧ i < l) ∨
    (j < k ∧ k < l ∧ l < i) ∨
    (j < l ∧ l < i ∧ i < k) ∨
    (j < l ∧ l < k ∧ k < i) ∨
    (k < i ∧ i < j ∧ j < l) ∨
    (k < i ∧ i < l ∧ l < j) ∨
    (k < j ∧ j < i ∧ i < l) ∨
    (k < j ∧ j < l ∧ l < i) ∨
    (k < l ∧ l < i ∧ i < j) ∨
    (k < l ∧ l < j ∧ j < i) ∨
    (l < i ∧ i < j ∧ j < k) ∨
    (l < i ∧ i < k ∧ k < j) ∨
    (l < j ∧ j < i ∧ i < k) ∨
    (l < j ∧ j < k ∧ k < i) ∨
    (l < k ∧ k < i ∧ i < j) ∨
    (l < k ∧ k < j ∧ j < i) := by decide
  have ho := horder i j k l hij hik hil hjk hjl hkl
  rcases ho with ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩ |
    ⟨ha,hb,hc⟩
  · have hset : ({realPoint r i,realPoint r j,realPoint r k,realPoint r l} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd i j k l ha hb hc
  · have hset : ({realPoint r i,realPoint r j,realPoint r l,realPoint r k} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd i j l k ha hb hc
  · have hset : ({realPoint r i,realPoint r k,realPoint r j,realPoint r l} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd i k j l ha hb hc
  · have hset : ({realPoint r i,realPoint r k,realPoint r l,realPoint r j} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd i k l j ha hb hc
  · have hset : ({realPoint r i,realPoint r l,realPoint r j,realPoint r k} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd i l j k ha hb hc
  · have hset : ({realPoint r i,realPoint r l,realPoint r k,realPoint r j} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd i l k j ha hb hc
  · have hset : ({realPoint r j,realPoint r i,realPoint r k,realPoint r l} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd j i k l ha hb hc
  · have hset : ({realPoint r j,realPoint r i,realPoint r l,realPoint r k} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd j i l k ha hb hc
  · have hset : ({realPoint r j,realPoint r k,realPoint r i,realPoint r l} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd j k i l ha hb hc
  · have hset : ({realPoint r j,realPoint r k,realPoint r l,realPoint r i} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd j k l i ha hb hc
  · have hset : ({realPoint r j,realPoint r l,realPoint r i,realPoint r k} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd j l i k ha hb hc
  · have hset : ({realPoint r j,realPoint r l,realPoint r k,realPoint r i} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd j l k i ha hb hc
  · have hset : ({realPoint r k,realPoint r i,realPoint r j,realPoint r l} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd k i j l ha hb hc
  · have hset : ({realPoint r k,realPoint r i,realPoint r l,realPoint r j} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd k i l j ha hb hc
  · have hset : ({realPoint r k,realPoint r j,realPoint r i,realPoint r l} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd k j i l ha hb hc
  · have hset : ({realPoint r k,realPoint r j,realPoint r l,realPoint r i} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd k j l i ha hb hc
  · have hset : ({realPoint r k,realPoint r l,realPoint r i,realPoint r j} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd k l i j ha hb hc
  · have hset : ({realPoint r k,realPoint r l,realPoint r j,realPoint r i} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd k l j i ha hb hc
  · have hset : ({realPoint r l,realPoint r i,realPoint r j,realPoint r k} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd l i j k ha hb hc
  · have hset : ({realPoint r l,realPoint r i,realPoint r k,realPoint r j} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd l i k j ha hb hc
  · have hset : ({realPoint r l,realPoint r j,realPoint r i,realPoint r k} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd l j i k ha hb hc
  · have hset : ({realPoint r l,realPoint r j,realPoint r k,realPoint r i} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd l j k i ha hb hc
  · have hset : ({realPoint r l,realPoint r k,realPoint r i,realPoint r j} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd l k i j ha hb hc
  · have hset : ({realPoint r l,realPoint r k,realPoint r j,realPoint r i} : Set ℝ²) = {realPoint r i,realPoint r j,realPoint r k,realPoint r l} := by
      ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto
    simpa only [hset] using sorted_not_cospherical hr hd l k j i ha hb hc

lemma realPoint_injective {r : ℚ} (hr : r ≠ 0)
    (hd : traceB r ^ 2 < 4*traceC r) : Function.Injective (realPoint r) := by
  intro i j he
  by_contra hij
  have hex : ∀ i j : Fin 8, ∃ k : Fin 8, i ≠ k ∧ j ≠ k := by decide
  obtain ⟨k,hik,hjk⟩ := hex i j
  have hc := not_collinear hr hd i j k hij hik hjk
  apply hc
  rw [he]
  simpa using (collinear_pair ℝ (realPoint r j) (realPoint r k))

lemma realPoint_general_position {r : ℚ} (hr : r ≠ 0)
    (hd : traceB r ^ 2 < 4*traceC r) : InGeneralPosition (Set.range (realPoint r)) := by
  constructor
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik
    exact not_collinear hr hd i j k (fun he => hij (he ▸ rfl))
      (fun he => hik (he ▸ rfl)) (fun he => hjk (he ▸ rfl))
  · intro Q hQ hcard hcos
    obtain ⟨a,b,c,e,hab,hac,hae,hbc,hbe,hce,hset⟩ := Set.ncard_eq_four.mp hcard
    subst Q
    obtain ⟨i,rfl⟩ := hQ (by simp : a ∈ ({a,b,c,e} : Set ℝ²))
    obtain ⟨j,rfl⟩ := hQ (by simp : b ∈ ({realPoint r i,b,c,e} : Set ℝ²))
    obtain ⟨k,rfl⟩ := hQ (by simp : c ∈ ({realPoint r i,realPoint r j,c,e} : Set ℝ²))
    obtain ⟨l,rfl⟩ := hQ (by simp : e ∈ ({realPoint r i,realPoint r j,realPoint r k,e} : Set ℝ²))
    exact not_cospherical hr hd i j k l
      (fun he => hab (he ▸ rfl)) (fun he => hac (he ▸ rfl))
      (fun he => hae (he ▸ rfl)) (fun he => hbc (he ▸ rfl))
      (fun he => hbe (he ▸ rfl)) (fun he => hce (he ▸ rfl)) hcos

#print axioms realPoint_general_position
#print axioms realPoint_injective


/- Rational squared lengths, conditional only on the explicit extra square. -/

def medianU (r : ℚ) : ℚ := r^5+3*r^4+26*r^3-18*r^2+9*r+27
def medianV (r : ℚ) : ℚ := -2*r*(r^4-10*r^2-27)
def medianW (r : ℚ) : ℚ := r^5-3*r^4+26*r^3+18*r^2+9*r-27

def extraPoly (r : ℚ) : ℚ :=
  r^16-76*r^14+1956*r^12+27308*r^10+67030*r^8+
    245772*r^6+158436*r^4-55404*r^2+6561

def normFactor0 (r : ℚ) : ℚ := (traceC r)

def normFactor1 (r : ℚ) : ℚ := (traceB r) + (traceC r) + 1

def normFactor2 (r : ℚ) : ℚ := -(traceB r) + (traceC r) + 1

def normFactor3 (r : ℚ) : ℚ := 3*(traceB r) + (traceC r) + 9

def normFactor4 (r : ℚ) : ℚ := -3*(traceB r) + (traceC r) + 9

def normFactor5 (r : ℚ) : ℚ := 3*(traceB r)^2 + (traceC r)^2 - 6*(traceC r) + 9

lemma normFactor0_square (r : ℚ) : IsSquare (normFactor0 r) := by
  refine ⟨medianV r / sideB r, ?_⟩
  dsimp [normFactor0,traceB,traceC]
  field_simp [sideB_ne r]
  dsimp [sideA,sideB,sideC,medianU,medianV,medianW]
  ring

lemma normFactor1_square (r : ℚ) : IsSquare (normFactor1 r) := by
  refine ⟨2*sideA r / sideB r, ?_⟩
  dsimp [normFactor1,traceB,traceC]
  field_simp [sideB_ne r]
  dsimp [sideA,sideB,sideC,medianU,medianV,medianW]
  ring

lemma normFactor2_square (r : ℚ) : IsSquare (normFactor2 r) := by
  refine ⟨2*sideC r / sideB r, ?_⟩
  dsimp [normFactor2,traceB,traceC]
  field_simp [sideB_ne r]
  dsimp [sideA,sideB,sideC,medianU,medianV,medianW]
  ring

lemma normFactor3_square (r : ℚ) : IsSquare (normFactor3 r) := by
  refine ⟨2*medianU r / sideB r, ?_⟩
  dsimp [normFactor3,traceB,traceC]
  field_simp [sideB_ne r]
  dsimp [sideA,sideB,sideC,medianU,medianV,medianW]
  ring

lemma normFactor4_square (r : ℚ) : IsSquare (normFactor4 r) := by
  refine ⟨2*medianW r / sideB r, ?_⟩
  dsimp [normFactor4,traceB,traceC]
  field_simp [sideB_ne r]
  dsimp [sideA,sideB,sideC,medianU,medianV,medianW]
  ring

lemma normFactor5_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (normFactor5 r) := by
  obtain ⟨q,hq⟩ := he
  refine ⟨4*(r^2-3)*q/sideB r^2, ?_⟩
  have hid : normFactor5 r * sideB r^4 = 16*(r^2-3)^2*extraPoly r := by
    dsimp [normFactor5,traceB,traceC]
    field_simp [sideB_ne r]
    dsimp [sideA,sideB,sideC,extraPoly]
    ring
  field_simp [sideB_ne r]
  nlinarith [hid,hq]

private lemma norm_0_1_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 1-coordA r 0) (coordB r 1-coordB r 0)) := by
  have hid : quadNorm r (coordA r 1-coordA r 0) (coordB r 1-coordB r 0) = 9 * (normFactor2 r) * (normFactor3 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor2,normFactor3]
    ring
  rw [hid]
  exact (IsSquare.mul (IsSquare.mul (by norm_num : IsSquare (9 : ℚ)) (normFactor2_square r)) (normFactor3_square r))

private lemma norm_0_2_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 2-coordA r 0) (coordB r 2-coordB r 0)) := by
  have hid : quadNorm r (coordA r 2-coordA r 0) (coordB r 2-coordB r 0) = 1 * (normFactor4 r)^2 := by
    dsimp [quadNorm,coordA,coordB,normFactor4]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (1 : ℚ)) (IsSquare.pow 2 (normFactor4_square r)))

private lemma norm_0_3_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 3-coordA r 0) (coordB r 3-coordB r 0)) := by
  have hid : quadNorm r (coordA r 3-coordA r 0) (coordB r 3-coordB r 0) = 36 * (normFactor4 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor4]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (36 : ℚ)) (normFactor4_square r))

private lemma norm_0_4_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 4-coordA r 0) (coordB r 4-coordB r 0)) := by
  have hid : quadNorm r (coordA r 4-coordA r 0) (coordB r 4-coordB r 0) = 9 * (normFactor4 r) * (normFactor2 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor4,normFactor2]
    ring
  rw [hid]
  exact (IsSquare.mul (IsSquare.mul (by norm_num : IsSquare (9 : ℚ)) (normFactor4_square r)) (normFactor2_square r))

private lemma norm_0_5_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 5-coordA r 0) (coordB r 5-coordB r 0)) := by
  have hid : quadNorm r (coordA r 5-coordA r 0) (coordB r 5-coordB r 0) = 36 * (normFactor2 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor2]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (36 : ℚ)) (normFactor2_square r))

private lemma norm_0_6_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 6-coordA r 0) (coordB r 6-coordB r 0)) := by
  have hid : quadNorm r (coordA r 6-coordA r 0) (coordB r 6-coordB r 0) = 144 * (normFactor0 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor0]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (144 : ℚ)) (normFactor0_square r))

private lemma norm_0_7_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 7-coordA r 0) (coordB r 7-coordB r 0)) := by
  have hid : quadNorm r (coordA r 7-coordA r 0) (coordB r 7-coordB r 0) = 9 * (normFactor5 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor5]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (9 : ℚ)) (normFactor5_square he))

private lemma norm_1_2_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 2-coordA r 1) (coordB r 2-coordB r 1)) := by
  have hid : quadNorm r (coordA r 2-coordA r 1) (coordB r 2-coordB r 1) = 16 * (normFactor0 r)^2 := by
    dsimp [quadNorm,coordA,coordB,normFactor0]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (16 : ℚ)) (IsSquare.pow 2 (normFactor0_square r)))

private lemma norm_1_3_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 3-coordA r 1) (coordB r 3-coordB r 1)) := by
  have hid : quadNorm r (coordA r 3-coordA r 1) (coordB r 3-coordB r 1) = 9 * (normFactor5 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor5]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (9 : ℚ)) (normFactor5_square he))

private lemma norm_1_4_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 4-coordA r 1) (coordB r 4-coordB r 1)) := by
  have hid : quadNorm r (coordA r 4-coordA r 1) (coordB r 4-coordB r 1) = 36 * (normFactor0 r) * (normFactor2 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor0,normFactor2]
    ring
  rw [hid]
  exact (IsSquare.mul (IsSquare.mul (by norm_num : IsSquare (36 : ℚ)) (normFactor0_square r)) (normFactor2_square r))

private lemma norm_1_5_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 5-coordA r 1) (coordB r 5-coordB r 1)) := by
  have hid : quadNorm r (coordA r 5-coordA r 1) (coordB r 5-coordB r 1) = 9 * (normFactor2 r) * (normFactor1 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor2,normFactor1]
    ring
  rw [hid]
  exact (IsSquare.mul (IsSquare.mul (by norm_num : IsSquare (9 : ℚ)) (normFactor2_square r)) (normFactor1_square r))

private lemma norm_1_6_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 6-coordA r 1) (coordB r 6-coordB r 1)) := by
  have hid : quadNorm r (coordA r 6-coordA r 1) (coordB r 6-coordB r 1) = 9 * (normFactor4 r) * (normFactor1 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor4,normFactor1]
    ring
  rw [hid]
  exact (IsSquare.mul (IsSquare.mul (by norm_num : IsSquare (9 : ℚ)) (normFactor4_square r)) (normFactor1_square r))

private lemma norm_1_7_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 7-coordA r 1) (coordB r 7-coordB r 1)) := by
  have hid : quadNorm r (coordA r 7-coordA r 1) (coordB r 7-coordB r 1) = 36 * (normFactor0 r) * (normFactor1 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor0,normFactor1]
    ring
  rw [hid]
  exact (IsSquare.mul (IsSquare.mul (by norm_num : IsSquare (36 : ℚ)) (normFactor0_square r)) (normFactor1_square r))

private lemma norm_2_3_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 3-coordA r 2) (coordB r 3-coordB r 2)) := by
  have hid : quadNorm r (coordA r 3-coordA r 2) (coordB r 3-coordB r 2) = 1 * (normFactor4 r) * (normFactor3 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor4,normFactor3]
    ring
  rw [hid]
  exact (IsSquare.mul (IsSquare.mul (by norm_num : IsSquare (1 : ℚ)) (normFactor4_square r)) (normFactor3_square r))

private lemma norm_2_4_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 4-coordA r 2) (coordB r 4-coordB r 2)) := by
  have hid : quadNorm r (coordA r 4-coordA r 2) (coordB r 4-coordB r 2) = 4 * (normFactor0 r) * (normFactor4 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor0,normFactor4]
    ring
  rw [hid]
  exact (IsSquare.mul (IsSquare.mul (by norm_num : IsSquare (4 : ℚ)) (normFactor0_square r)) (normFactor4_square r))

private lemma norm_2_5_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 5-coordA r 2) (coordB r 5-coordB r 2)) := by
  have hid : quadNorm r (coordA r 5-coordA r 2) (coordB r 5-coordB r 2) = 1 * (normFactor5 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor5]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (1 : ℚ)) (normFactor5_square he))

private lemma norm_2_6_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 6-coordA r 2) (coordB r 6-coordB r 2)) := by
  have hid : quadNorm r (coordA r 6-coordA r 2) (coordB r 6-coordB r 2) = 1 * (normFactor3 r)^2 := by
    dsimp [quadNorm,coordA,coordB,normFactor3]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (1 : ℚ)) (IsSquare.pow 2 (normFactor3_square r)))

private lemma norm_2_7_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 7-coordA r 2) (coordB r 7-coordB r 2)) := by
  have hid : quadNorm r (coordA r 7-coordA r 2) (coordB r 7-coordB r 2) = 4 * (normFactor0 r) * (normFactor3 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor0,normFactor3]
    ring
  rw [hid]
  exact (IsSquare.mul (IsSquare.mul (by norm_num : IsSquare (4 : ℚ)) (normFactor0_square r)) (normFactor3_square r))

private lemma norm_3_4_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 4-coordA r 3) (coordB r 4-coordB r 3)) := by
  have hid : quadNorm r (coordA r 4-coordA r 3) (coordB r 4-coordB r 3) = 9 * (normFactor4 r) * (normFactor1 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor4,normFactor1]
    ring
  rw [hid]
  exact (IsSquare.mul (IsSquare.mul (by norm_num : IsSquare (9 : ℚ)) (normFactor4_square r)) (normFactor1_square r))

private lemma norm_3_5_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 5-coordA r 3) (coordB r 5-coordB r 3)) := by
  have hid : quadNorm r (coordA r 5-coordA r 3) (coordB r 5-coordB r 3) = 144 := by
    dsimp [quadNorm,coordA,coordB,]
    ring
  rw [hid]
  exact (by norm_num : IsSquare (144 : ℚ))

private lemma norm_3_6_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 6-coordA r 3) (coordB r 6-coordB r 3)) := by
  have hid : quadNorm r (coordA r 6-coordA r 3) (coordB r 6-coordB r 3) = 36 * (normFactor3 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor3]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (36 : ℚ)) (normFactor3_square r))

private lemma norm_3_7_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 7-coordA r 3) (coordB r 7-coordB r 3)) := by
  have hid : quadNorm r (coordA r 7-coordA r 3) (coordB r 7-coordB r 3) = 9 * (normFactor2 r) * (normFactor3 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor2,normFactor3]
    ring
  rw [hid]
  exact (IsSquare.mul (IsSquare.mul (by norm_num : IsSquare (9 : ℚ)) (normFactor2_square r)) (normFactor3_square r))

private lemma norm_4_5_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 5-coordA r 4) (coordB r 5-coordB r 4)) := by
  have hid : quadNorm r (coordA r 5-coordA r 4) (coordB r 5-coordB r 4) = 9 * (normFactor2 r)^2 := by
    dsimp [quadNorm,coordA,coordB,normFactor2]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (9 : ℚ)) (IsSquare.pow 2 (normFactor2_square r)))

private lemma norm_4_6_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 6-coordA r 4) (coordB r 6-coordB r 4)) := by
  have hid : quadNorm r (coordA r 6-coordA r 4) (coordB r 6-coordB r 4) = 9 * (normFactor5 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor5]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (9 : ℚ)) (normFactor5_square he))

private lemma norm_4_7_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 7-coordA r 4) (coordB r 7-coordB r 4)) := by
  have hid : quadNorm r (coordA r 7-coordA r 4) (coordB r 7-coordB r 4) = 144 * (normFactor0 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor0]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (144 : ℚ)) (normFactor0_square r))

private lemma norm_5_6_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 6-coordA r 5) (coordB r 6-coordB r 5)) := by
  have hid : quadNorm r (coordA r 6-coordA r 5) (coordB r 6-coordB r 5) = 36 * (normFactor1 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor1]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (36 : ℚ)) (normFactor1_square r))

private lemma norm_5_7_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 7-coordA r 5) (coordB r 7-coordB r 5)) := by
  have hid : quadNorm r (coordA r 7-coordA r 5) (coordB r 7-coordB r 5) = 9 * (normFactor1 r)^2 := by
    dsimp [quadNorm,coordA,coordB,normFactor1]
    ring
  rw [hid]
  exact (IsSquare.mul (by norm_num : IsSquare (9 : ℚ)) (IsSquare.pow 2 (normFactor1_square r)))

private lemma norm_6_7_square {r : ℚ} (he : IsSquare (extraPoly r)) :
    IsSquare (quadNorm r (coordA r 7-coordA r 6) (coordB r 7-coordB r 6)) := by
  have hid : quadNorm r (coordA r 7-coordA r 6) (coordB r 7-coordB r 6) = 9 * (normFactor1 r) * (normFactor3 r) := by
    dsimp [quadNorm,coordA,coordB,normFactor1,normFactor3]
    ring
  rw [hid]
  exact (IsSquare.mul (IsSquare.mul (by norm_num : IsSquare (9 : ℚ)) (normFactor1_square r)) (normFactor3_square r))

lemma sorted_norm_square {r : ℚ} (he : IsSquare (extraPoly r))
    (i j : Fin 8) (hij : i < j) :
    IsSquare (quadNorm r (coordA r j-coordA r i) (coordB r j-coordB r i)) := by
  fin_cases i <;> fin_cases j <;> norm_num at hij

  · exact norm_0_1_square he
  · exact norm_0_2_square he
  · exact norm_0_3_square he
  · exact norm_0_4_square he
  · exact norm_0_5_square he
  · exact norm_0_6_square he
  · exact norm_0_7_square he
  · exact norm_1_2_square he
  · exact norm_1_3_square he
  · exact norm_1_4_square he
  · exact norm_1_5_square he
  · exact norm_1_6_square he
  · exact norm_1_7_square he
  · exact norm_2_3_square he
  · exact norm_2_4_square he
  · exact norm_2_5_square he
  · exact norm_2_6_square he
  · exact norm_2_7_square he
  · exact norm_3_4_square he
  · exact norm_3_5_square he
  · exact norm_3_6_square he
  · exact norm_3_7_square he
  · exact norm_4_5_square he
  · exact norm_4_6_square he
  · exact norm_4_7_square he
  · exact norm_5_6_square he
  · exact norm_5_7_square he
  · exact norm_6_7_square he

lemma realPoint_rational_distances {r : ℚ} (hd : traceB r ^ 2 < 4*traceC r)
    (he : IsSquare (extraPoly r)) (i j : Fin 8) :
    ∃ q : ℚ, (q : ℝ) = dist (realPoint r i) (realPoint r j) := by
  suffices hs : ∀ i j : Fin 8, i < j →
      ∃ q : ℚ, (q : ℝ) = dist (realPoint r i) (realPoint r j) by
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact hs i j hij
    · exact ⟨0,by simp⟩
    · simpa only [dist_comm] using hs j i hji
  intro i j hij
  obtain ⟨q,hq⟩ := sorted_norm_square he i j hij
  refine ⟨|q|, ?_⟩
  have hs := realPoint_dist_sq hd i j
  rw [hq] at hs
  push_cast at hs ⊢
  nlinarith [abs_nonneg (q : ℝ),sq_abs (q : ℝ),
    dist_nonneg (x := realPoint r i) (y := realPoint r j)]

#print axioms realPoint_rational_distances


/- Exact area criterion; the inequalities rule out all degenerate parameters. -/

def areaPoly (r : ℚ) : ℚ :=
  128*r^2*(r^2-9)*(r^2-1)*(r^2+1)*(r^2+9)*
    (r^4-22*r^2+9)*(r^4+2*r^2+9)

lemma trace_discriminant_identity (r : ℚ) :
    (4*traceC r-traceB r^2)*sideB r^4 = 4*areaPoly r := by
  dsimp [traceB,traceC]
  field_simp [sideB_ne r]
  dsimp [sideA,sideB,sideC,areaPoly]
  ring

lemma nonreal_iff_area_pos (r : ℚ) :
    traceB r^2 < 4*traceC r ↔ 0 < areaPoly r := by
  have hb : 0 < sideB r^4 := pow_pos (sq_pos_of_ne_zero (sideB_ne r)) 2 |>.trans_eq (by ring)
  have hmul : 0 < (4*traceC r-traceB r^2)*sideB r^4 ↔ 0 < areaPoly r := by
    rw [trace_discriminant_identity]
    constructor <;> intro h <;> linarith
  rw [mul_pos_iff_of_pos_right hb,sub_pos] at hmul
  exact hmul

lemma area_positive {r : ℚ} (h1 : 1 < r) (h3 : r < 3) : 0 < areaPoly r := by
  have hr : 0 < r := by linarith
  have hlo : 1 < r^2 := by nlinarith
  have hhi : r^2 < 9 := by nlinarith
  have hs : 0 < r^2 := by positivity
  have h4 : r^4 < 9*r^2 := by
    nlinarith [mul_pos hs (show 0 < 9-r^2 by linarith)]
  have hmid : 0 < 22*r^2-r^4-9 := by nlinarith
  have he : areaPoly r =
      128*r^2*(9-r^2)*(r^2-1)*(r^2+1)*(r^2+9)*
        (22*r^2-r^4-9)*(r^4+2*r^2+9) := by
    dsimp [areaPoly]
    ring
  rw [he]
  have hlow : 0 < r^2-1 := by linarith
  have hupp : 0 < 9-r^2 := by linarith
  positivity

lemma nonreal_of_between_one_three {r : ℚ} (h1 : 1 < r) (h3 : r < 3) :
    traceB r^2 < 4*traceC r := (nonreal_iff_area_pos r).mpr (area_positive h1 h3)

lemma area_reciprocal_identity {r : ℚ} (hr : r ≠ 0) :
    areaPoly r = 128*r^6*(r^2+1)*(r^2+9)*(r^4+2*r^2+9)*
      ((r^2+9/r^2)-10)*((r^2+9/r^2)-22) := by
  dsimp [areaPoly]
  field_simp
  ring

lemma area_positive_iff {r : ℚ} (hr : r ≠ 0) :
    0 < areaPoly r ↔ r^2+9/r^2 < 10 ∨ 22 < r^2+9/r^2 := by
  rw [area_reciprocal_identity hr]
  have hpos : 0 < 128*r^6*(r^2+1)*(r^2+9)*(r^4+2*r^2+9) := by positivity
  rw [mul_assoc, mul_pos_iff_of_pos_left hpos, mul_pos_iff]
  constructor
  · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
    · right; linarith
    · left; linarith
  · rintro (h | h)
    · right; constructor <;> linarith
    · left; constructor <;> linarith

#print axioms nonreal_iff_area_pos
#print axioms area_positive_iff

end Erdos213.MedianGeometry


namespace Erdos213

open MedianGeometry

/-- A completely explicit conditional eight-point construction. This theorem
has an arithmetic existence hypothesis; it does not settle the conjecture. -/
lemma erdos213For_eight_of_median_parameter {r : ℚ} (hr : r ≠ 0)
    (ha : 0 < areaPoly r) (he : IsSquare (extraPoly r)) : Erdos213For 8 := by
  have hd := (nonreal_iff_area_pos r).mpr ha
  apply (erdos213For_iff_rational 8).mpr
  refine ⟨Set.range (realPoint r), Set.finite_range _, ?_,
    realPoint_general_position hr hd, ?_⟩
  · rw [Set.ncard_range_of_injective (realPoint_injective hr hd)]
    simp
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
    exact realPoint_rational_distances hd he i j

/-- The interval 1 < r < 3 is a convenient explicit positive-area region. -/
lemma erdos213For_eight_of_between_one_three {r : ℚ} (h1 : 1 < r) (h3 : r < 3)
    (he : IsSquare (extraPoly r)) : Erdos213For 8 :=
  erdos213For_eight_of_median_parameter (by linarith) (area_positive h1 h3) he

/-- The full reciprocal-parameter version of the sufficient condition. -/
lemma erdos213For_eight_of_extra_square {r : ℚ} (hr : r ≠ 0)
    (ha : r^2+9/r^2 < 10 ∨ 22 < r^2+9/r^2)
    (he : IsSquare (extraPoly r)) : Erdos213For 8 :=
  erdos213For_eight_of_median_parameter hr ((area_positive_iff hr).mpr ha) he

#print axioms erdos213For_eight_of_median_parameter
#print axioms erdos213For_eight_of_between_one_three
#print axioms erdos213For_eight_of_extra_square

end Erdos213
