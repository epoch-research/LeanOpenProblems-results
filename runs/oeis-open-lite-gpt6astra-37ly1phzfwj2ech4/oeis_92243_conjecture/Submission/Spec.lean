import FormalConjectures.Util.ProblemImports

/- Auxiliary analytic and sieve results used for the disproof. -/

/- BoundedMellin -/
section

open scoped Topology
open Complex MeasureTheory Set Filter Metric
namespace MaynardDevelopment
noncomputable section

/-- Mellin transform of a bounded function on `[1,infinity)`, shifted to converge for `re s>0`. -/
def boundedMellin (a : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), a t * (t : ℂ) ^ (-(s + 1))

lemma boundedMellin_integrable {a : ℝ → ℂ} (ha : Measurable a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t > 1, ‖a t‖ ≤ C) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t => a t * (t : ℂ) ^ (-(s + 1))) (Ioi (1 : ℝ)) := by
  have hmajor := (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) (by norm_num : (0 : ℝ) < 1)).const_mul C
  apply hmajor.mono'
  · exact (by fun_prop : Measurable (fun t => a t * (t : ℂ) ^ (-(s + 1)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 1 < t at ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < t)]
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    have he : -(s.re + 1) = -s.re - 1 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (hb t ht) (Real.rpow_nonneg (by linarith) _)

lemma boundedMellin_norm_le {a : ℝ → ℂ} (ha : Measurable a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t > 1, ‖a t‖ ≤ C) {s : ℂ} (hs : 0 < s.re) :
    ‖boundedMellin a s‖ ≤ C / s.re := by
  have hi := boundedMellin_integrable ha hC hb hs
  have hmajor := (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) (by norm_num : (0 : ℝ) < 1)).const_mul C
  calc
    _ ≤ ∫ t in Ioi (1 : ℝ), C * t ^ (-s.re - 1) := by
      apply norm_integral_le_of_norm_le hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 1 < t at ht
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < t)]
      simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
      have he : -(s.re + 1) = -s.re - 1 := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (hb t ht) (Real.rpow_nonneg (by linarith) _)
    _ = C / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) (by norm_num : (0 : ℝ) < 1)]
      simp only [Real.one_rpow]
      field_simp [hs.ne']
      ring

lemma boundedMellin_differentiableAt {a : ℝ → ℂ} (ha : Measurable a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t > 1, ‖a t‖ ≤ C) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (boundedMellin a) s := by
  let δ : ℝ := s.re / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let F : ℂ → ℝ → ℂ := fun w t => a t * (t : ℂ) ^ (-(w + 1))
  let F' : ℂ → ℝ → ℂ := fun w t => -((Real.log t : ℝ) : ℂ) * a t * (t : ℂ) ^ (-(w + 1))
  have hmeas (w : ℂ) : AEStronglyMeasurable (F w) (volume.restrict (Ioi (1 : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    dsimp [F]
    fun_prop
  have hmeas' (w : ℂ) : AEStronglyMeasurable (F' w) (volume.restrict (Ioi (1 : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    dsimp [F']
    fun_prop
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -δ - 1 < -1) (by norm_num : (0 : ℝ) < 1)).const_mul (C / δ)
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 1), ∀ w ∈ ball s (2 * δ),
      ‖F' w t‖ ≤ (C / δ) * t ^ (-δ - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 1 < t at ht
    intro w hw
    have htpos : 0 < t := by linarith
    have htw : 2 * δ ≤ w.re := by
      have hh := Complex.abs_re_le_norm (w - s)
      rw [mem_ball_iff_norm] at hw
      simp only [Complex.sub_re] at hh
      have hminus := neg_le_abs (w.re - s.re)
      dsimp [δ] at *
      linarith
    have hlog := Real.log_nonneg ht.le
    have htpow : t ^ (-(w.re + 1)) ≤ t ^ (-2 * δ - 1) :=
      Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)
    have hlogb := Real.log_le_rpow_div htpos.le hδ
    dsimp only [F']
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog,
      Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    calc
      _ ≤ (t ^ δ / δ) * C * t ^ (-2 * δ - 1) := by gcongr; exact hb t ht
      _ = (C / δ) * t ^ (-δ - 1) := by
        rw [div_eq_mul_inv, mul_assoc, mul_assoc]
        have he : δ + (-2 * δ - 1) = -δ - 1 := by ring
        rw [← he, Real.rpow_add htpos]
        ring
  have hdiff : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 1), ∀ w ∈ ball s (2 * δ),
      HasDerivAt (fun w => F w t) (F' w t) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 1 < t at ht
    intro w _
    have htpos : 0 < t := by linarith
    have hh := (((hasDerivAt_id w).add_const 1).neg.const_cpow
      (Or.inl (by exact_mod_cast htpos.ne' : (t : ℂ) ≠ 0))).const_mul (a t)
    convert hh using 1
    dsimp [F']
    rw [← Complex.ofReal_log htpos.le]
    ring
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds s (by positivity : 0 < 2 * δ)) (Eventually.of_forall hmeas)
    (boundedMellin_integrable ha hC hb hs) (hmeas' s) hbound hi hdiff
  exact hderiv.2.differentiableAt

end
end MaynardDevelopment
end

/- LargeSieve -/
section

open scoped BigOperators ComplexConjugate

namespace MaynardDevelopment

noncomputable section

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma gram_coefficient_bound (v : ι → E) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdiag : ∀ i, ‖v i‖ ^ 2 ≤ A)
    (hoff : ∀ i j, i ≠ j → ‖inner ℂ (v i) (v j)‖ ≤ B) (c : ι → ℂ) :
    ‖∑ i, c i • v i‖ ^ 2 ≤
      (A + B * Fintype.card ι) * ∑ i, ‖c i‖ ^ 2 := by
  classical
  have hinner (i j : ι) : ‖inner ℂ (v i) (v j)‖ ≤ B + if i = j then A else 0 := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, ← inner_self_re_eq_norm, inner_self_eq_norm_sq]
      linarith [hdiag i]
    · simpa [hij] using hoff i j hij
  have hnself (x : E) : ‖x‖ ^ 2 = ‖inner ℂ x x‖ := by
    rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq]
  have hcs : (∑ i, ‖c i‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : ι => ‖c i‖) (fun _ => (1 : ℝ))
    simpa [mul_comm] using hh
  have hcalc : (∑ i, ∑ j, ‖c i‖ * ‖c j‖ * (B + if i = j then A else 0)) =
      B * (∑ i, ‖c i‖) ^ 2 + A * (∑ i, ‖c i‖ ^ 2) := by
    have heq (i j : ι) : ‖c i‖ * ‖c j‖ * (B + if i = j then A else 0) =
        B * ‖c i‖ * ‖c j‖ + (if j = i then A * ‖c i‖ ^ 2 else 0) := by
      by_cases hh : i = j
      · subst j; simp; ring
      · simp [hh, Ne.symm hh]; ring
    simp_rw [heq, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [← Finset.mul_sum]
    ring
  calc
    ‖∑ i, c i • v i‖ ^ 2 = ‖∑ i, ∑ j, conj (c i) * c j * inner ℂ (v i) (v j)‖ := by
      rw [hnself]
      congr 1
      rw [sum_inner]
      simp_rw [inner_smul_left, inner_sum, inner_smul_right, Finset.mul_sum]
      simp only [mul_assoc]
    _ ≤ ∑ i, ∑ j, ‖c i‖ * ‖c j‖ * ‖inner ℂ (v i) (v j)‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      simpa [norm_mul] using norm_sum_le Finset.univ
        (fun j => conj (c i) * c j * inner ℂ (v i) (v j))
    _ ≤ ∑ i, ∑ j, ‖c i‖ * ‖c j‖ * (B + if i = j then A else 0) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hinner i j) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = B * (∑ i, ‖c i‖) ^ 2 + A * (∑ i, ‖c i‖ ^ 2) := hcalc
    _ ≤ B * ((Fintype.card ι : ℝ) * ∑ i, ‖c i‖ ^ 2) + A * (∑ i, ‖c i‖ ^ 2) := by
      gcongr
    _ = _ := by ring

/-- A coarse large-sieve inequality from pairwise Gram-matrix bounds. -/
lemma gram_bessel_bound (v : ι → E) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdiag : ∀ i, ‖v i‖ ^ 2 ≤ A)
    (hoff : ∀ i j, i ≠ j → ‖inner ℂ (v i) (v j)‖ ≤ B) (x : E) :
    (∑ i, ‖inner ℂ (v i) x‖ ^ 2) ≤ (A + B * Fintype.card ι) * ‖x‖ ^ 2 := by
  let c : ι → ℂ := fun i => inner ℂ (v i) x
  let y : E := ∑ i, c i • v i
  let S : ℝ := ∑ i, ‖c i‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hy := gram_coefficient_bound v hA hB hdiag hoff c
  have hinner : inner ℂ y x = (S : ℂ) := by
    dsimp only [y, S]
    simp only [sum_inner, inner_smul_left]
    change (∑ i, conj (c i) * c i) = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ)
    simp [RCLike.conj_mul]
  have hnorm : ‖inner ℂ y x‖ = S := by rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]
  have hCS : S ^ 2 ≤ ‖y‖ ^ 2 * ‖x‖ ^ 2 := by
    have hh := norm_inner_le_norm (𝕜 := ℂ) y x
    rw [hnorm] at hh
    have hh' := (sq_le_sq₀ hS (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hh
    simpa [mul_pow] using hh'
  have hy' : ‖y‖ ^ 2 * ‖x‖ ^ 2 ≤ (A + B * Fintype.card ι) * S * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hy (sq_nonneg _)
  change S ≤ (A + B * Fintype.card ι) * ‖x‖ ^ 2
  by_cases hS0 : S = 0
  · rw [hS0]
    positivity
  · have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
    nlinarith


lemma norm_sum_periodic_zero_le {f : ℕ → ℂ} {q : ℕ} (hq : 0 < q)
    (hf : Function.Periodic f q) (hs : (∑ n ∈ Finset.range q, f n) = 0)
    (hb : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) : ‖∑ n ∈ Finset.range N, f n‖ ≤ q := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : N < q
    · calc
        ‖∑ n ∈ Finset.range N, f n‖ ≤ ∑ n ∈ Finset.range N, ‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum (fun n _ => hb n)
        _ = (N : ℝ) := by simp
        _ ≤ (q : ℝ) := by exact_mod_cast hN.le
    · have hqN : q ≤ N := by omega
      have hsum : (∑ n ∈ Finset.range N, f n) = ∑ n ∈ Finset.range (N - q), f n := by
        conv_lhs => rw [← Nat.add_sub_of_le hqN, Finset.sum_range_add, hs, zero_add]
        apply Finset.sum_congr rfl
        intro n _
        simpa [Nat.add_comm] using hf n
      rw [hsum]
      exact ih (N - q) (Nat.sub_lt (by omega) hq)

lemma norm_sum_Ico_periodic_zero_le {f : ℕ → ℂ} {q : ℕ} (hq : 0 < q)
    (hf : Function.Periodic f q) (hs : (∑ n ∈ Finset.range q, f n) = 0)
    (hb : ∀ n, ‖f n‖ ≤ 1) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ico M (M + N), f n‖ ≤ 2 * (q : ℝ) := by
  rw [Finset.sum_Ico_eq_sub _ (by omega)]
  calc
    _ ≤ ‖∑ n ∈ Finset.range (M + N), f n‖ + ‖∑ n ∈ Finset.range M, f n‖ := norm_sub_le _ _
    _ ≤ (q : ℝ) + (q : ℝ) := add_le_add
      (norm_sum_periodic_zero_le hq hf hs hb (M + N))
      (norm_sum_periodic_zero_le hq hf hs hb M)
    _ = _ := by ring

/-- A deliberately coarse large sieve. Pairwise orthogonality over periods bounded by `Q`
gives an `N + 2 Q * card ι` bound, which is enough for a positive distribution exponent. -/
lemma periodic_family_large_sieve (f : ι → ℕ → ℂ) (Q : ℕ)
    (hb : ∀ i n, ‖f i n‖ ≤ 1)
    (ho : ∀ i j, i ≠ j → ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧
      Function.Periodic (fun n => conj (f i n) * f j n) q ∧
      (∑ n ∈ Finset.range q, conj (f i n) * f j n) = 0)
    (M N : ℕ) (a : Fin N → ℂ) :
    (∑ i, ‖∑ n : Fin N, a n * f i (M + n.val)‖ ^ 2) ≤
      ((N : ℝ) + 2 * (Q : ℝ) * Fintype.card ι) * ∑ n : Fin N, ‖a n‖ ^ 2 := by
  let v : ι → EuclideanSpace ℂ (Fin N) := fun i =>
    WithLp.toLp 2 (fun n : Fin N => conj (f i (M + n.val)))
  let x : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 a
  have hdiag (i : ι) : ‖v i‖ ^ 2 ≤ (N : ℝ) := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _n : Fin N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        simp only [v, RCLike.norm_conj]
        nlinarith [hb i (M + n.val), norm_nonneg (f i (M + n.val))]
      _ = _ := by simp
  have hoff (i j : ι) (hij : i ≠ j) : ‖inner ℂ (v i) (v j)‖ ≤ 2 * (Q : ℝ) := by
    obtain ⟨q, hq, hqQ, hp, hs⟩ := ho j i (Ne.symm hij)
    have hnorm (n : ℕ) : ‖conj (f j n) * f i n‖ ≤ 1 := by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_one₀ (hb j n) (norm_nonneg _) (hb i n)
    have hh := norm_sum_Ico_periodic_zero_le hq hp hs hnorm M N
    have heq : inner ℂ (v i) (v j) =
        ∑ n ∈ Finset.Ico M (M + N), conj (f j n) * f i n := by
      rw [PiLp.inner_apply, Finset.sum_Ico_eq_sum_range]
      simp only [v, RCLike.inner_apply, RCLike.conj_conj, Nat.add_sub_cancel_left]
      exact Fin.sum_univ_eq_sum_range (fun n => conj (f j (M + n)) * f i (M + n)) N
    rw [heq]
    exact hh.trans (by exact_mod_cast (Nat.mul_le_mul_left 2 hqQ))
  have heq (i : ι) : inner ℂ (v i) x = ∑ n : Fin N, a n * f i (M + n.val) := by
    rw [PiLp.inner_apply]
    simp [v, x, RCLike.inner_apply]
  have hlarge := gram_bessel_bound v (by positivity) (by positivity) hdiag hoff x
  simp_rw [heq] at hlarge
  simpa [x, PiLp.norm_sq_eq_of_L2] using hlarge


end
end MaynardDevelopment
end

/- PrimitiveCharacters -/
section

open scoped BigOperators ComplexConjugate
open DirichletCharacter

namespace MaynardDevelopment

noncomputable section

lemma sum_zmod_eq_sum_range {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ x : ZMod q, f x) = ∑ n ∈ Finset.range q, f (n : ZMod q) := by
  letI : CommRing (Fin q) := Fin.instCommRing q
  rw [← (ZMod.finEquiv q).toEquiv.sum_comp f]
  have heq (i : Fin q) : (ZMod.finEquiv q).toEquiv i = (i.val : ZMod q) := by
    have hh := map_natCast (ZMod.finEquiv q) i.val
    simpa only [Fin.cast_val_eq_self] using hh
  simp_rw [heq]
  exact Fin.sum_univ_eq_sum_range (fun n => f (n : ZMod q)) q

lemma primitive_exists_kernel_unit {q d : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hd : d ∣ q) (hlt : d < q) :
    ∃ u : (ZMod q)ˣ, ZMod.unitsMap hd u = 1 ∧ χ u ≠ 1 := by
  classical
  by_contra h
  push_neg at h
  have hf : χ.FactorsThrough d := (factorsThrough_iff_ker_unitsMap hd).mpr (by
    intro u hu
    change ZMod.unitsMap hd u = 1 at hu
    change χ.toUnitHom u = 1
    apply Units.ext
    simpa only [MulChar.coe_toUnitHom, Units.val_one] using h u hu)
  have hh : χ.conductor ≤ d := Nat.sInf_le hf
  rw [hχ] at hh
  omega

lemma unit_lift_gcd {q r : ℕ} [NeZero q] [NeZero r]
    (u : (ZMod q)ˣ) (hu : ZMod.unitsMap (Nat.gcd_dvd_left q r) u = 1) :
    ∃ w : (ZMod (q * r))ˣ,
      ZMod.castHom (dvd_mul_right q r) (ZMod q) w = u ∧
      ZMod.castHom (dvd_mul_left r q) (ZMod r) w = 1 := by
  have hmod : (u.val.val : ℕ) ≡ 1 [MOD Nat.gcd q r] := by
    apply (ZMod.eq_iff_modEq_nat (Nat.gcd q r)).mp
    have hh := congrArg Units.val hu
    simpa [ZMod.unitsMap_def] using hh
  obtain ⟨b, hbq, hbr⟩ := Nat.chineseRemainder' hmod
  have hub : (u.val.val).Coprime q := by
    apply (ZMod.isUnit_iff_coprime _ _).mp
    simpa using u.isUnit
  have hb1 : b.Coprime q := by
    change Nat.gcd b q = 1
    rw [hbq.gcd_eq]
    exact hub
  have hb2 : b.Coprime r := by
    change Nat.gcd b r = 1
    rw [hbr.gcd_eq]
    simp
  have hbu : IsUnit (b : ZMod (q * r)) := (ZMod.isUnit_iff_coprime _ _).mpr (hb1.mul_right hb2)
  refine ⟨hbu.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, map_natCast]
    have hh := (ZMod.eq_iff_modEq_nat q).mpr hbq
    simpa using hh
  · rw [IsUnit.unit_spec, map_natCast]
    have hh := (ZMod.eq_iff_modEq_nat r).mpr hbr
    simpa using hh

lemma correlation_sum_zero_of_separating_unit {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (u : (ZMod (q * r))ˣ)
    (hχ : χ (ZMod.castHom (dvd_mul_right q r) (ZMod q) u) ≠ 1)
    (hψ : ψ (ZMod.castHom (dvd_mul_left r q) (ZMod r) u) = 1) :
    (∑ x : ZMod (q * r),
      conj (χ (ZMod.castHom (dvd_mul_right q r) (ZMod q) x)) *
        ψ (ZMod.castHom (dvd_mul_left r q) (ZMod r) x)) = 0 := by
  let f : ZMod (q * r) → ℂ := fun x =>
    conj (χ (ZMod.castHom (dvd_mul_right q r) (ZMod q) x)) *
      ψ (ZMod.castHom (dvd_mul_left r q) (ZMod r) x)
  let c : ℂ := conj (χ (ZMod.castHom (dvd_mul_right q r) (ZMod q) u))
  have hc : c ≠ 1 := by
    intro hh
    apply hχ
    have := congrArg (starRingEnd ℂ) hh
    simpa [c] using this
  have hmul (x : ZMod (q * r)) : f (u * x) = c * f x := by
    simp only [f, c, map_mul, hψ, one_mul]
    ring
  apply eq_zero_of_mul_eq_self_left hc
  change c * (∑ x, f x) = ∑ x, f x
  rw [Finset.mul_sum]
  simp_rw [← hmul]
  exact u.mulLeft_bijective.sum_comp f

lemma primitive_correlation_zero_of_not_dvd {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) (hqr : ¬ q ∣ r) :
    (∑ n ∈ Finset.range (q * r), conj (χ (n : ZMod q)) * ψ (n : ZMod r)) = 0 := by
  have hlt : Nat.gcd q r < q := by
    have hle := Nat.gcd_le_left r (NeZero.pos q)
    have hne : Nat.gcd q r ≠ q := by
      intro hh
      apply hqr
      rw [← hh]
      exact Nat.gcd_dvd_right q r
    omega
  obtain ⟨u, hu, hχu⟩ := primitive_exists_kernel_unit χ hχ (Nat.gcd_dvd_left q r) hlt
  obtain ⟨w, hwq, hwr⟩ := unit_lift_gcd u hu
  have hh := correlation_sum_zero_of_separating_unit χ ψ w (by rwa [hwq]) (by rw [hwr, map_one])
  rw [sum_zmod_eq_sum_range] at hh
  simpa only [map_natCast] using hh

lemma primitive_correlation_periodic {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    Function.Periodic (fun n : ℕ => conj (χ (n : ZMod q)) * ψ (n : ZMod r)) (q * r) := by
  intro n
  simp [Nat.cast_add, Nat.cast_mul]

lemma same_level_correlation_zero {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hne : χ ≠ ψ) :
    (∑ n ∈ Finset.range q, conj (χ (n : ZMod q)) * ψ (n : ZMod q)) = 0 := by
  have hnon : χ⁻¹ * ψ ≠ 1 := by
    intro hh
    exact hne (inv_mul_eq_one.mp hh)
  have hh := MulChar.sum_eq_zero_of_ne_one hnon
  rw [sum_zmod_eq_sum_range] at hh
  simpa only [MulChar.mul_apply, ← MulChar.star_apply', RCLike.star_def] using hh


lemma primitive_correlation_zero_of_ne_level {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hqr : q ≠ r) :
    (∑ n ∈ Finset.range (q * r), conj (χ (n : ZMod q)) * ψ (n : ZMod r)) = 0 := by
  by_cases hdiv : q ∣ r
  · have hndiv : ¬ r ∣ q := fun hrq => hqr (Nat.dvd_antisymm hdiv hrq)
    have hh := primitive_correlation_zero_of_not_dvd ψ χ hψ hndiv
    have hh' := congrArg (starRingEnd ℂ) hh
    simpa only [map_sum, map_mul, RCLike.conj_conj, map_zero, mul_comm, Nat.mul_comm] using hh'
  · exact primitive_correlation_zero_of_not_dvd χ ψ hχ hdiv

/-- Primitive characters with positive level at most `Q`. -/
def PrimitiveUpTo (Q : ℕ) : Type :=
  Σ q : Fin (Q + 1), {χ : DirichletCharacter ℂ q.val // q.val ≠ 0 ∧ χ.IsPrimitive}

instance (Q : ℕ) : Fintype (PrimitiveUpTo Q) := by
  classical
  unfold PrimitiveUpTo
  infer_instance

def primitiveValue {Q : ℕ} (χ : PrimitiveUpTo Q) (n : ℕ) : ℂ :=
  χ.2.val (n : ZMod χ.1.val)

lemma primitiveValue_norm_le_one {Q : ℕ} (χ : PrimitiveUpTo Q) (n : ℕ) :
    ‖primitiveValue χ n‖ ≤ 1 := χ.2.val.norm_le_one _

lemma primitiveUpTo_card_le (Q : ℕ) : Fintype.card (PrimitiveUpTo Q) ≤ (Q + 1) ^ 2 := by
  classical
  unfold PrimitiveUpTo
  rw [Fintype.card_sigma]
  have hcard (q : Fin (Q + 1)) :
      Fintype.card {χ : DirichletCharacter ℂ q.val // q.val ≠ 0 ∧ χ.IsPrimitive} ≤ q.val := by
    by_cases hq : q.val = 0
    · haveI : IsEmpty {χ : DirichletCharacter ℂ q.val // q.val ≠ 0 ∧ χ.IsPrimitive} :=
        ⟨fun χ => χ.2.1 hq⟩
      simp [hq]
    · haveI : NeZero q.val := ⟨hq⟩
      calc
        _ ≤ Fintype.card (DirichletCharacter ℂ q.val) := Fintype.card_subtype_le _
        _ = q.val.totient := by
          simpa only [Nat.card_eq_fintype_card] using
            card_eq_totient_of_hasEnoughRootsOfUnity ℂ q.val
        _ ≤ q.val := Nat.totient_le _
  calc
    _ ≤ ∑ q : Fin (Q + 1), q.val := Finset.sum_le_sum (fun q _ => hcard q)
    _ ≤ ∑ _q : Fin (Q + 1), Q := Finset.sum_le_sum (fun q _ => by omega)
    _ ≤ (Q + 1) ^ 2 := by simp; nlinarith

lemma primitiveValue_orthogonal {Q : ℕ} (χ ψ : PrimitiveUpTo Q) (hne : χ ≠ ψ) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Q ^ 2 ∧
      Function.Periodic (fun n => conj (primitiveValue χ n) * primitiveValue ψ n) q ∧
      (∑ n ∈ Finset.range q, conj (primitiveValue χ n) * primitiveValue ψ n) = 0 := by
  classical
  rcases χ with ⟨q, χ, hq, hχ⟩
  rcases ψ with ⟨r, ψ, hr, hψ⟩
  haveI : NeZero q.val := ⟨hq⟩
  haveI : NeZero r.val := ⟨hr⟩
  by_cases hqr : q = r
  · subst r
    have hχψ : χ ≠ ψ := by
      intro hh
      subst ψ
      exact hne rfl
    refine ⟨q.val, Nat.pos_of_ne_zero hq, ?_, ?_, ?_⟩
    · have hqQ : q.val ≤ Q := by omega
      have hQ : 1 ≤ Q := by omega
      nlinarith
    · intro n
      simp [primitiveValue, Nat.cast_add]
    · exact same_level_correlation_zero χ ψ hχψ
  · refine ⟨q.val * r.val, Nat.mul_pos (Nat.pos_of_ne_zero hq) (Nat.pos_of_ne_zero hr), ?_,
      primitive_correlation_periodic χ ψ, ?_⟩
    · have hqQ : q.val ≤ Q := by omega
      have hrQ : r.val ≤ Q := by omega
      nlinarith
    · exact primitive_correlation_zero_of_ne_level χ ψ hχ hψ (fun hh => hqr (Fin.ext hh))

/-- A coarse but unconditional multiplicative large-sieve inequality.
The fourth-power modulus loss is harmless when only some positive distribution exponent is needed. -/
theorem primitive_character_large_sieve (Q M N : ℕ) (a : Fin N → ℂ) :
    (∑ χ : PrimitiveUpTo Q, ‖∑ n : Fin N, a n * primitiveValue χ (M + n.val)‖ ^ 2) ≤
      ((N : ℝ) + 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2) * ∑ n : Fin N, ‖a n‖ ^ 2 := by
  have hh := periodic_family_large_sieve (fun χ : PrimitiveUpTo Q => primitiveValue χ) (Q ^ 2)
    primitiveValue_norm_le_one (fun χ ψ h => primitiveValue_orthogonal χ ψ h) M N a
  have hc : (Fintype.card (PrimitiveUpTo Q) : ℝ) ≤ (Q + 1 : ℝ) ^ 2 := by
    exact_mod_cast primitiveUpTo_card_le Q
  refine hh.trans ?_
  push_cast
  gcongr


end
end MaynardDevelopment
end

/- TypeOne -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section

lemma sum_mul_abel (c f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, c n * f n) =
      (∑ n ∈ Finset.range N, c n) * f N -
      ∑ n ∈ Finset.range N, (∑ j ∈ Finset.range (n + 1), c j) * (f (n + 1) - f n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ] at ih ⊢
    rw [ih]
    ring

lemma norm_sum_mul_monotone_le (c : ℕ → ℂ) (f : ℕ → ℝ) (N : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (hf : Monotone f) (hf0 : 0 ≤ f 0)
    (hc : ∀ k ≤ N, ‖∑ n ∈ Finset.range k, c n‖ ≤ C) :
    ‖∑ n ∈ Finset.range N, c n * (f n : ℂ)‖ ≤ 2 * C * f N := by
  have hfnon (n : ℕ) : 0 ≤ f n := hf0.trans (hf (Nat.zero_le n))
  have hdiff (n : ℕ) : 0 ≤ f (n + 1) - f n := sub_nonneg.mpr (hf (Nat.le_succ n))
  rw [sum_mul_abel]
  calc
    _ ≤ ‖(∑ n ∈ Finset.range N, c n) * (f N : ℂ)‖ +
        ‖∑ n ∈ Finset.range N, (∑ j ∈ Finset.range (n + 1), c j) * ((f (n + 1) : ℂ) - f n)‖ := norm_sub_le _ _
    _ ≤ C * f N + ∑ n ∈ Finset.range N, C * (f (n + 1) - f n) := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hfnon N)]
        exact mul_le_mul_of_nonneg_right (hc N le_rfl) (hfnon N)
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hdiff n)]
        exact mul_le_mul_of_nonneg_right (hc (n + 1) (by simpa using Finset.mem_range.mp hn)) (hdiff n)
    _ ≤ 2 * C * f N := by
      rw [← Finset.mul_sum, Finset.sum_range_sub]
      nlinarith

lemma character_sum_interval_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ ((M + n : ℕ) : ZMod q)‖ ≤ 2 * (q : ℝ) := by
  have hp : Function.Periodic (fun n : ℕ => χ (n : ZMod q)) q := by
    intro n
    simp [Nat.cast_add]
  have hs := MulChar.sum_eq_zero_of_ne_one hχ
  rw [sum_zmod_eq_sum_range] at hs
  have hh := norm_sum_Ico_periodic_zero_le (NeZero.pos q) hp hs (fun n => χ.norm_le_one _) M N
  rw [Finset.sum_Ico_eq_sum_range] at hh
  simpa only [Nat.add_sub_cancel_left] using hh

/-- Elementary Type I input; no analytic information about L-functions is used. -/
lemma character_log_sum_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q) * (Real.log (n + 1 : ℝ) : ℂ)‖ ≤
      4 * (q : ℝ) * Real.log (N + 1 : ℝ) := by
  have hf : Monotone (fun n : ℕ => Real.log (n + 1 : ℝ)) := by
    intro m n hmn
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hh := norm_sum_mul_monotone_le (fun n => χ ((n + 1 : ℕ) : ZMod q))
    (fun n => Real.log (n + 1 : ℝ)) N (by positivity : 0 ≤ 2 * (q : ℝ)) hf (by simp)
    (fun k _ => by simpa only [Nat.add_comm] using character_sum_interval_le χ hχ 1 k)
  convert hh using 1 <;> ring

lemma sum_Icc_one_eq_sum_range {R : Type*} [AddCommMonoid R] (f : ℕ → R) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ n ∈ Finset.range N, f (n + 1) := by
  have hI : Finset.Icc 1 N = Finset.Ico 1 (1 + N) := by ext n; simp; omega
  rw [hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  simp only [Nat.add_comm]

lemma character_sum_Icc_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q)‖ ≤ 2 * (q : ℝ) := by
  rw [sum_Icc_one_eq_sum_range]
  simpa only [Nat.add_comm] using character_sum_interval_le χ hχ 1 N

lemma character_log_sum_Icc_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log n : ℂ)‖ ≤
      4 * (q : ℝ) * Real.log (N + 1 : ℝ) := by
  rw [sum_Icc_one_eq_sum_range]
  simpa only [Nat.cast_add, Nat.cast_one] using character_log_sum_le χ hχ N

lemma norm_sum_Icc_of_support {f : ℕ → ℂ} {X U : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n ∈ Finset.Icc 1 X, n ≤ U → ‖f n‖ ≤ C)
    (hf0 : ∀ n ∈ Finset.Icc 1 X, U < n → f n = 0) :
    ‖∑ n ∈ Finset.Icc 1 X, f n‖ ≤ (U : ℝ) * C := by
  have hcard : ((Finset.Icc 1 X).filter (fun n => n ≤ U)).card ≤ U := by
    calc
      _ ≤ (Finset.Icc 1 U).card := Finset.card_le_card (by
        intro n hn
        rcases Finset.mem_filter.mp hn with ⟨hn, hnU⟩
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, hnU⟩)
      _ = _ := by simp
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 X, if n ≤ U then C else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      split_ifs with hnU
      · exact hf n hn hnU
      · rw [hf0 n hn (Nat.lt_of_not_ge hnU), norm_zero]
    _ = (((Finset.Icc 1 X).filter (fun n => n ≤ U)).card : ℝ) * C := by
      rw [← Finset.sum_filter]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC

end
end MaynardDevelopment
end

/- LFunctionGrowth -/
section

open scoped BigOperators Topology
open Complex MeasureTheory Set Filter Metric
namespace MaynardDevelopment
noncomputable section

def characterPartial {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ (n : ZMod q)

lemma characterPartial_measurable {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Measurable (characterPartial χ) :=
  (measurable_from_nat (f := fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q))).comp Nat.measurable_floor

lemma characterPartial_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ‖characterPartial χ t‖ ≤ 2 * (q : ℝ) := character_sum_Icc_le χ hχ _

lemma characterPartial_bigO {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (0 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (2 * q)
  filter_upwards [] with n
  simpa using character_sum_Icc_le χ hχ n

lemma open_re_pos : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re

lemma preconnected_re_pos : IsPreconnected {z : ℂ | 0 < z.re} :=
  ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected

/-- Abel's integral continues a nonprincipal Dirichlet L-series to the right half-plane. -/
lemma LFunction_eq_boundedMellin {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    χ.LFunction s = s * boundedMellin (characterPartial χ) s := by
  have hf : AnalyticOnNhd ℂ χ.LFunction {z : ℂ | 0 < z.re} :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd open_re_pos
  have hg : AnalyticOnNhd ℂ (fun z => z * boundedMellin (characterPartial χ) z) {z : ℂ | 0 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ open_re_pos
    intro z hz
    exact (differentiableAt_id.mul (boundedMellin_differentiableAt (characterPartial_measurable χ)
      (by positivity : 0 ≤ 2 * (q : ℝ)) (fun t _ => characterPartial_norm_le χ hχ t) hz)).differentiableWithinAt
  have heq : χ.LFunction =ᶠ[𝓝 (2 : ℂ)] fun z => z * boundedMellin (characterPartial χ) z := by
    have hN : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hN] with z hz
    rw [χ.LFunction_eq_LSeries hz]
    exact LSeries_eq_mul_integral (fun n => χ (n : ZMod q)) (by norm_num : (0 : ℝ) ≤ 0)
      (by linarith : 0 < z.re) (χ.LSeriesSummable_of_one_lt_re hz) (characterPartial_bigO χ hχ)
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg preconnected_re_pos (by norm_num : (2 : ℂ) ∈ {z | 0 < z.re}) heq hs

lemma LFunction_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ ‖s‖ * (2 * (q : ℝ) / s.re) := by
  rw [LFunction_eq_boundedMellin χ hχ hs, norm_mul]
  exact mul_le_mul_of_nonneg_left (boundedMellin_norm_le (characterPartial_measurable χ)
    (by positivity) (fun t _ => characterPartial_norm_le χ hχ t) hs) (norm_nonneg _)

lemma LFunction_norm_le_half {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖χ.LFunction s‖ ≤ 4 * (q : ℝ) * ‖s‖ := by
  refine (LFunction_norm_le χ hχ (by linarith)).trans ?_
  have hh : 2 * (q : ℝ) / s.re ≤ 4 * q := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  calc
    _ ≤ ‖s‖ * (4 * q) := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ = _ := by ring

lemma norm_sum_Icc_le_of_bounded {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := Finset.sum_le_sum (fun n _ => hf n)
    _ = _ := by simp

lemma LSeries_norm_le_of_bounded {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries f s‖ ≤ ‖s‖ / (s.re - 1) := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with n
    simpa using norm_sum_Icc_le_of_bounded hf n
  rw [LSeries_eq_mul_integral f (by norm_num : (0 : ℝ) ≤ 1) hs
    (LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => hf n) hs) hO, norm_mul]
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -s.re < -1) (by norm_num : (0 : ℝ) < 1)
  have hbound : ‖∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1))‖ ≤
      1 / (s.re - 1) := by
    calc
      _ ≤ ∫ t in Ioi (1 : ℝ), t ^ (-s.re) := by
        apply norm_integral_le_of_norm_le hi
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        change 1 < t at ht
        have ht0 : 0 < t := by linarith
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hpartial : ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k‖ ≤ t :=
          (norm_sum_Icc_le_of_bounded hf _).trans (Nat.floor_le ht0.le)
        calc
          _ ≤ t * t ^ (-(s + 1)).re := mul_le_mul_of_nonneg_right hpartial (Real.rpow_nonneg ht0.le _)
          _ = t ^ (-s.re) := by
            nth_rw 1 [← Real.rpow_one t]
            rw [← Real.rpow_add ht0]
            congr 1
            simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
            ring
      _ = _ := by
        rw [integral_Ioi_rpow_of_lt (by linarith : -s.re < -1) (by norm_num : (0 : ℝ) < 1), Real.one_rpow]
        have hne : s.re - 1 ≠ 0 := by linarith
        have hne2 : -s.re + 1 ≠ 0 := by linarith
        field_simp [hne, hne2]
        ring
  calc
    _ ≤ ‖s‖ * (1 / (s.re - 1)) := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = _ := by ring

lemma LFunction_norm_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    (s.re - 1) / ‖s‖ ≤ ‖χ.LFunction s‖ := by
  let f : ℕ → ℂ := fun n => χ (n : ZMod q) * (ArithmeticFunction.moebius n : ℂ)
  have hf (n : ℕ) : ‖f n‖ ≤ 1 := by
    dsimp only [f]
    rw [norm_mul, Complex.norm_intCast]
    apply mul_le_one₀ (χ.norm_le_one _) (by positivity)
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have hb := LSeries_norm_le_of_bounded hf hs
  have hm := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hnorm := congrArg norm hm
  change ‖LSeries (fun n => χ (n : ZMod q)) s * LSeries f s‖ = ‖(1 : ℂ)‖ at hnorm
  rw [norm_mul, norm_one, ← χ.LFunction_eq_LSeries hs] at hnorm
  have hineq := mul_le_mul_of_nonneg_left hb (norm_nonneg (χ.LFunction s))
  rw [hnorm] at hineq
  have hs0 : 0 < s.re - 1 := by linarith
  have hsn : 0 < ‖s‖ := by
    apply norm_pos_iff.mpr
    intro hz
    norm_num [hz] at hs
  apply (div_le_iff₀ hsn).mpr
  have hh := (le_div_iff₀ hs0).mp (show (1 : ℝ) ≤ ‖χ.LFunction s‖ * ‖s‖ / (s.re - 1) by
    simpa only [mul_div_assoc] using hineq)
  simpa only [one_mul] using hh

end
end MaynardDevelopment
end

/- ZetaGrowth -/
section

open scoped BigOperators Topology
open Complex MeasureTheory Set Filter Metric
namespace MaynardDevelopment
noncomputable section

def natFraction (t : ℝ) : ℂ := ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)

lemma natFraction_measurable : Measurable natFraction := by unfold natFraction; fun_prop

lemma natFraction_norm_le {t : ℝ} (ht : 1 < t) : ‖natFraction t‖ ≤ 1 := by
  rw [natFraction, Complex.norm_real, Real.norm_eq_abs]
  have hfloor := Nat.floor_le (by linarith : 0 ≤ t)
  have hceil := Nat.lt_floor_add_one t
  rw [abs_of_nonneg (by linarith)]
  linarith

lemma riemannZeta_eq_boundedMellin {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * boundedMellin natFraction s := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℂ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with n
    simp
  have hrep := LSeries_eq_mul_integral (1 : ℕ → ℂ) (by norm_num : (0 : ℝ) ≤ 1) hs
    (LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by simp) hs) hO
  rw [LSeries_one_eq_riemannZeta hs] at hrep
  simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel] at hrep
  have hid (t : ℝ) (ht : 1 < t) : (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
    nth_rw 1 [← Complex.cpow_one (t : ℂ)]
    rw [← Complex.cpow_add _ _ (by exact_mod_cast (show t ≠ 0 by linarith))]
    congr 1
    ring
  have hi1 := integrableOn_Ioi_cpow_of_lt (a := -s) (by simpa using (show -s.re < -1 by linarith)) (by norm_num : (0 : ℝ) < 1)
  have hi2 := boundedMellin_integrable natFraction_measurable (by norm_num : (0 : ℝ) ≤ 1)
    (fun t ht => natFraction_norm_le ht) (by linarith : 0 < s.re)
  have hIntegral : (∫ t in Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) =
      (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s)) - boundedMellin natFraction s := by
    rw [boundedMellin, ← integral_sub hi1 hi2]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [← hid t ht]
    dsimp only [natFraction]
    push_cast
    ring
  have hIpow : (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s)) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt (by simpa using (show -s.re < -1 by linarith)) (by norm_num : (0 : ℝ) < 1)]
    simp only [Complex.ofReal_one, Complex.one_cpow]
    have hne : s - 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have hne' : -s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    field_simp [hne, hne']
    ring
  rw [hIntegral, hIpow] at hrep
  convert hrep using 1 <;> ring

lemma regularized_zeta_eq_boundedMellin {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunctionTrivChar₁ 1 s = s - s * (s - 1) * boundedMellin natFraction s := by
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) {z : ℂ | 0 < z.re} :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd open_re_pos
  have hg : AnalyticOnNhd ℂ (fun z => z - z * (z - 1) * boundedMellin natFraction z) {z : ℂ | 0 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ open_re_pos
    intro z hz
    exact (differentiableAt_id.sub ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
      (boundedMellin_differentiableAt natFraction_measurable (by norm_num : (0 : ℝ) ≤ 1)
        (fun t ht => natFraction_norm_le ht) hz))).differentiableWithinAt
  have heq : DirichletCharacter.LFunctionTrivChar₁ 1 =ᶠ[𝓝 (2 : ℂ)]
      fun z => z - z * (z - 1) * boundedMellin natFraction z := by
    have hN : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hN] with z hz
    have hz1 : z ≠ 1 := by intro h; norm_num [h] at hz
    simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1,
      DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]
    rw [riemannZeta_eq_boundedMellin hz]
    field_simp [sub_ne_zero.mpr hz1]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg preconnected_re_pos
    (by norm_num : (2 : ℂ) ∈ {z | 0 < z.re}) heq hs

lemma regularized_zeta_norm_le {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖DirichletCharacter.LFunctionTrivChar₁ 1 s‖ ≤ 3 * (‖s‖ + 1) ^ 2 := by
  have hs0 : 0 < s.re := by linarith
  have hB : ‖boundedMellin natFraction s‖ ≤ 2 := by
    refine (boundedMellin_norm_le natFraction_measurable (by norm_num : (0 : ℝ) ≤ 1)
      (fun t ht => natFraction_norm_le ht) hs0).trans ?_
    apply (div_le_iff₀ hs0).mpr
    linarith
  rw [regularized_zeta_eq_boundedMellin hs0]
  have hsm : ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s (1 : ℂ)
  calc
    _ ≤ ‖s‖ + ‖s * (s - 1) * boundedMellin natFraction s‖ := norm_sub_le _ _
    _ ≤ ‖s‖ + ‖s‖ * (‖s‖ + 1) * 2 := by simp only [norm_mul]; gcongr
    _ ≤ _ := by nlinarith [norm_nonneg s]

end
end MaynardDevelopment
end

/- RegularizedL -/
section

open scoped BigOperators Topology
open Complex Set Filter Metric
namespace MaynardDevelopment
noncomputable section

lemma regularized_trivial_eq_zeta_mul (q : ℕ) [NeZero q] (s : ℂ) :
    DirichletCharacter.LFunctionTrivChar₁ q s = DirichletCharacter.LFunctionTrivChar₁ 1 s *
      ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)) := by
  by_cases hs : s = 1
  · subst s
    simp [DirichletCharacter.LFunctionTrivChar₁, Complex.cpow_neg_one]
  · simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs,
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs, Nat.primeFactors_one,
      Finset.prod_empty, one_mul]
    ring

lemma trivial_euler_product_norm_le {q : ℕ} (hq : q ≠ 0) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ q := by
  calc
    _ ≤ ∏ p ∈ q.primeFactors, (p : ℝ) := by
      rw [norm_prod]
      apply Finset.prod_le_prod
      · intros; positivity
      · intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_le
        have hpn : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
          rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]
          simpa using Real.rpow_le_rpow_of_exponent_le hp1 (show -s.re ≤ 0 by linarith)
        calc
          _ ≤ 1 + ‖(p : ℂ) ^ (-s)‖ := by simpa using norm_sub_le (1 : ℂ) ((p : ℂ) ^ (-s))
          _ ≤ 2 := by linarith
          _ ≤ _ := by exact_mod_cast hpp.two_le
    _ ≤ (q : ℝ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)

lemma regularized_trivial_norm_le (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖DirichletCharacter.LFunctionTrivChar₁ q s‖ ≤ 3 * (q : ℝ) * (‖s‖ + 1) ^ 2 := by
  rw [regularized_trivial_eq_zeta_mul, norm_mul]
  calc
    _ ≤ (3 * (‖s‖ + 1) ^ 2) * q := mul_le_mul (regularized_zeta_norm_le hs)
      (trivial_euler_product_norm_le (NeZero.ne q) (by linarith)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Regularization removes the pole of a principal Dirichlet L-function. -/
def regularizedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q else χ.LFunction

lemma regularizedL_differentiable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ (regularizedL χ) := by
  unfold regularizedL
  split_ifs with hχ
  · exact DirichletCharacter.differentiable_LFunctionTrivChar₁ q
  · exact DirichletCharacter.differentiable_LFunction hχ

lemma regularizedL_factor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    regularizedL χ s = (if χ = 1 then s - 1 else 1) * χ.LFunction s := by
  by_cases hχ : χ = 1
  · subst χ
    simp [regularizedL, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs,
      DirichletCharacter.LFunctionTrivChar]
  · simp [regularizedL, hχ]

lemma regularizedL_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 ≤ s.re) :
    regularizedL χ s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    unfold regularizedL
    split_ifs with hχ
    · exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
    · exact χ.LFunction_ne_zero_of_one_le_re (.inl hχ) hs
  · rw [regularizedL_factor χ hs1]
    apply mul_ne_zero
    · split_ifs
      · exact sub_ne_zero.mpr hs1
      · exact one_ne_zero
    · exact χ.LFunction_ne_zero_of_one_le_re (.inr hs1) hs

lemma regularizedL_norm_upper {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖regularizedL χ s‖ ≤ 4 * (q : ℝ) * (‖s‖ + 1) ^ 2 := by
  unfold regularizedL
  split_ifs with hχ
  · exact (regularized_trivial_norm_le q hs).trans (by nlinarith [sq_nonneg (‖s‖ + 1), Nat.cast_nonneg (α := ℝ) q])
  · refine (LFunction_norm_le_half χ hχ hs).trans ?_
    have hh : ‖s‖ ≤ (‖s‖ + 1) ^ 2 := by nlinarith [norm_nonneg s]
    exact mul_le_mul_of_nonneg_left hh (by positivity)

lemma regularizedL_norm_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    (s.re - 1) ^ 2 / ‖s‖ ≤ ‖regularizedL χ s‖ := by
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hδ : 0 ≤ s.re - 1 := by linarith
  have hlow := LFunction_norm_lower χ hs
  rw [regularizedL_factor χ hs1, norm_mul]
  split_ifs with hχ
  · have hsm : s.re - 1 ≤ ‖s - 1‖ := by
      have hh := Complex.re_le_norm (s - 1)
      simpa using hh
    calc
      _ = (s.re - 1) * ((s.re - 1) / ‖s‖) := by ring
      _ ≤ _ := mul_le_mul hsm hlow (by positivity) (norm_nonneg _)
  · simp only [norm_one, one_mul]
    refine (div_le_div_of_nonneg_right (by nlinarith : (s.re - 1) ^ 2 ≤ s.re - 1) (norm_nonneg _)).trans hlow

lemma regularizedL_logDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (regularizedL χ) s = (if χ = 1 then 1 / (s - 1) else 0) + logDeriv χ.LFunction s := by
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  by_cases hχ : χ = 1
  · subst χ
    have heq : regularizedL (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s]
        fun z => (z - 1) * DirichletCharacter.LFunctionTrivChar q z := by
      filter_upwards [eventually_ne_nhds hs1] with z hz
      simpa using regularizedL_factor (1 : DirichletCharacter ℂ q) hz
    rw [logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
    have hh := logDeriv_mul (f := fun z : ℂ => z - 1) (g := DirichletCharacter.LFunctionTrivChar q) s (sub_ne_zero.mpr hs1)
      ((1 : DirichletCharacter ℂ q).LFunction_ne_zero_of_one_le_re (.inr hs1) hs.le)
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z - 1) s)
      ((1 : DirichletCharacter ℂ q).differentiableAt_LFunction s (.inl hs1))
    simpa [logDeriv_apply, DirichletCharacter.LFunctionTrivChar] using hh
  · simp [regularizedL, hχ]

end
end MaynardDevelopment
end

/- ComplexLogBounds -/
section

open scoped Topology
open Complex Metric Set Filter
namespace MaynardDevelopment
noncomputable section

lemma norm_mobius_le_one {u : ℂ} {A : ℝ} (hA : 0 < A) (hu : u.re ≤ A) :
    ‖u / ((2 * A : ℝ) - u)‖ ≤ 1 := by
  have hden : ((2 * A : ℝ) : ℂ) - u ≠ 0 := by
    intro hh
    have hre := congrArg Complex.re hh
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith
  rw [norm_div, div_le_one (norm_pos_iff.mpr hden)]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  nlinarith

/-- The center-derivative form of the Borel--Carathéodory inequality. -/
lemma norm_deriv_le_of_re_le {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R))
    (hb : ∀ z ∈ ball c R, (f z).re ≤ M) (hM : (f c).re < M) :
    ‖deriv f c‖ ≤ 2 * (M - (f c).re) / R := by
  let A : ℝ := M - (f c).re
  have hA : 0 < A := sub_pos.mpr hM
  let u : ℂ → ℂ := fun z => f z - f c
  let g : ℂ → ℂ := fun z => u z / ((2 * A : ℝ) - u z)
  have hu (z : ℂ) (hz : z ∈ ball c R) : (u z).re ≤ A := by
    dsimp [u, A]
    have := hb z hz
    simpa only [Complex.sub_re] using sub_le_sub_right this (f c).re
  have hden (z : ℂ) (hz : z ∈ ball c R) : ((2 * A : ℝ) : ℂ) - u z ≠ 0 := by
    intro hh
    have hre := congrArg Complex.re hh
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith [hu z hz]
  have hgd : DifferentiableOn ℂ g (ball c R) :=
    (hf.sub_const _).div ((differentiable_const ((2 * A : ℝ) : ℂ)).differentiableOn.sub (hf.sub_const _)) hden
  have hgc : g c = 0 := by simp [g, u]
  have hmaps : MapsTo g (ball c R) (closedBall (g c) 1) := by
    intro z hz
    rw [hgc, mem_closedBall_zero_iff]
    exact norm_mobius_le_one hA (hu z hz)
  have hsch := Complex.norm_deriv_le_div_of_mapsTo_ball hgd hmaps hR
  have hfc := hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hderiv : deriv g c = deriv f c / ((2 * A : ℝ) : ℂ) := by
    have hh := (hfc.hasDerivAt.sub_const (f c)).div
      ((hasDerivAt_const c (((2 * A : ℝ) : ℂ))).sub (hfc.hasDerivAt.sub_const (f c)))
      (hden c (mem_ball_self hR))
    change HasDerivAt g _ c at hh
    rw [hh.deriv]
    simp only [Pi.sub_apply, sub_self, sub_zero, zero_mul, mul_zero, zero_sub]
    field_simp
  rw [hderiv, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * A)] at hsch
  have hh := (div_le_iff₀ (by positivity : 0 < 2 * A)).mp hsch
  change ‖deriv f c‖ ≤ 2 * A / R
  convert hh using 1 <;> ring

lemma exists_log_norm_primitive {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hn : ∀ z ∈ ball c R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ g c = 0 ∧
      (∀ z ∈ ball c R, (g z).re = Real.log ‖f z‖ - Real.log ‖f c‖) ∧
      (∀ z ∈ ball c R, deriv g z = deriv f z / f z) := by
  have hf' : AnalyticOnNhd ℂ f (ball c R) := hf.analyticOnNhd isOpen_ball
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball c R) :=
    hf'.deriv.differentiableOn.div hf hn
  obtain ⟨G, hG⟩ := hd.isExactOn_ball
  let H : ℂ → ℂ := fun z => f z * Complex.exp (-G z)
  have hH (z : ℂ) (hz : z ∈ ball c R) : HasDerivAt H 0 z := by
    have hdf := (hf' z hz).differentiableAt.hasDerivAt
    have hh := hdf.mul ((Complex.hasDerivAt_exp (-G z)).comp z (hG z hz).neg)
    convert hh using 1
    dsimp only [Function.comp_apply, Pi.neg_apply]
    field_simp [hn z hz]
    ring
  have hconst (z : ℂ) (hz : z ∈ ball c R) : H z = H c := by
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
      (fun z hz => (hH z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hH z hz).deriv) hz (mem_ball_self hR)
  have hGd : DifferentiableOn ℂ G (ball c R) := fun z hz => (hG z hz).differentiableAt.differentiableWithinAt
  refine ⟨fun z => G z - G c, hGd.sub_const _,
    sub_self _, ?_, ?_⟩
  · intro z hz
    have hnorm := congrArg norm (hconst z hz)
    simp only [H, norm_mul, Complex.norm_exp, Complex.neg_re] at hnorm
    have hlog := congrArg Real.log hnorm
    rw [Real.log_mul (norm_ne_zero_iff.mpr (hn z hz)) (Real.exp_ne_zero _),
      Real.log_mul (norm_ne_zero_iff.mpr (hn c (mem_ball_self hR))) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp] at hlog
    simp only [Complex.sub_re]
    linarith
  · intro z hz
    exact ((hG z hz).sub_const _).deriv

/-- A zero-free disk gives logarithmic rather than polynomial control of the logarithmic derivative. -/
lemma norm_logDeriv_le_disk {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hn : ∀ z ∈ ball c R, f z ≠ 0)
    (hb : ∀ z ∈ ball c R, ‖f z‖ ≤ M) :
    ‖deriv f c / f c‖ ≤ 2 * (1 + Real.log M - Real.log ‖f c‖) / R := by
  obtain ⟨g, hgd, hgc, hre, hderiv⟩ := exists_log_norm_primitive hR hf hn
  have hfc : 0 < ‖f c‖ := norm_pos_iff.mpr (hn c (mem_ball_self hR))
  have hMc : Real.log ‖f c‖ ≤ Real.log M := Real.log_le_log hfc (hb c (mem_ball_self hR))
  have hh := norm_deriv_le_of_re_le hR hgd
    (M := 1 + Real.log M - Real.log ‖f c‖) (fun z hz => ?_) ?_
  · rw [hderiv c (mem_ball_self hR)] at hh
    simpa only [hgc, Complex.zero_re, sub_zero] using hh
  · rw [hre z hz]
    have hlog := Real.log_le_log (norm_pos_iff.mpr (hn z hz)) (hb z hz)
    linarith
  · rw [hgc, Complex.zero_re]
    linarith

end
end MaynardDevelopment
end

/- PartialZeros -/
section

open scoped Topology
open Complex Metric Set Filter Function MeromorphicOn
namespace MaynardDevelopment
noncomputable section

/-- Extract a prescribed finite collection of zeros, retaining analyticity on the larger domain. -/
lemma extract_partial_zeros {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (D : ℂ → ℤ) (hD : D.support.Finite) (hD0 : ∀ z, 0 ≤ D z)
    (hDf : ∀ z ∈ U, (D z : WithTop ℤ) ≤ meromorphicOrderAt f z) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ U, f z = (∏ᶠ a, (z - a) ^ D a) * g z) ∧
      (∀ z ∈ U, meromorphicOrderAt g z = -(D z : WithTop ℤ) + meromorphicOrderAt f z) := by
  let P : ℂ → ℂ := ∏ᶠ a, (· - a) ^ D a
  have hPa : AnalyticOnNhd ℂ P U := fun z _ => Function.FactorizedRational.analyticAt (hD0 z)
  have hPm : MeromorphicOn P U := hPa.meromorphicOn
  let g := toMeromorphicNFOn (P⁻¹ * f) U
  have hq : MeromorphicOn (P⁻¹ * f) U := hPm.inv.mul hf.meromorphicOn
  have hgn : MeromorphicNFOn g U := meromorphicNFOn_toMeromorphicNFOn _ _
  have horder (z : ℂ) (hz : z ∈ U) :
      meromorphicOrderAt g z = -(D z : WithTop ℤ) + meromorphicOrderAt f z := by
    rw [meromorphicOrderAt_congr (hq.toMeromorphicNFOn_eq_self_on_nhdsNE hz),
      meromorphicOrderAt_mul (hPm z hz).inv (hf z hz).meromorphicAt, meromorphicOrderAt_inv,
      Function.FactorizedRational.meromorphicOrderAt_eq D hD]
  have hga : AnalyticOnNhd ℂ g U := by
    intro z hz
    apply (hgn hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [horder z hz]
    have hh := add_le_add_left (hDf z hz) (-(D z : WithTop ℤ))
    simpa only [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero, add_comm] using hh
  refine ⟨g, hga, ?_, horder⟩
  intro z hz
  have hPne : ∀ᶠ w in 𝓝[≠] z, P w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hPm z hz)).mp
      (Function.FactorizedRational.meromorphicOrderAt_ne_top D)
  have heq : f =ᶠ[𝓝[≠] z] fun w => P w * g w := by
    filter_upwards [hq.toMeromorphicNFOn_eq_self_on_nhdsNE hz, hPne] with w hw hPw
    change g w = (P w)⁻¹ * f w at hw
    rw [hw, ← mul_assoc, mul_inv_cancel₀ hPw, one_mul]
  have hlimf : Tendsto f (𝓝[≠] z) (𝓝 (f z)) := (hf z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlimg : Tendsto (fun w => P w * g w) (𝓝[≠] z) (𝓝 (P z * g z)) := ((hPa z hz).mul (hga z hz)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have he : f z = P z * g z := tendsto_nhds_unique (hlimf.congr' heq) hlimg
  change f z = _ at he
  simpa only [P, Function.FactorizedRational.finprod_eq_fun hD] using he

/-- Strip precisely the zeros in a compact subset of an analytic domain. -/
lemma extract_zeros_on_compact {f : ℂ → ℂ} {U K : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hKU : K ⊆ U) (hK : IsCompact K)
    (hn : ∀ z ∈ K, meromorphicOrderAt f z ≠ ⊤) :
    let D := MeromorphicOn.divisor f K
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ U, f z = (∏ᶠ a, (z - a) ^ D a) * g z) ∧
      (∀ z ∈ K, g z ≠ 0) := by
  let D := MeromorphicOn.divisor f K
  have hfK : AnalyticOnNhd ℂ f K := hf.mono hKU
  have hD0 (z : ℂ) : 0 ≤ D z := hfK.divisor_nonneg z
  have hDf (z : ℂ) (hz : z ∈ U) : (D z : WithTop ℤ) ≤ meromorphicOrderAt f z := by
    by_cases hzK : z ∈ K
    · simp only [D, divisor_apply hfK.meromorphicOn hzK]
      lift meromorphicOrderAt f z to ℤ using hn z hzK with k hk
      simp
    · have hDzero : D z = 0 := D.apply_eq_zero_of_notMem hzK
      rw [hDzero, WithTop.coe_zero]
      exact (hf z hz).meromorphicOrderAt_nonneg
  obtain ⟨g, hga, heq, horder⟩ := extract_partial_zeros hf D (D.finiteSupport hK) hD0 hDf
  refine ⟨g, hga, heq, ?_⟩
  intro z hz
  apply (hga.meromorphicNFOn (hKU hz)).meromorphicOrderAt_eq_zero_iff.mp
  rw [horder z (hKU hz)]
  have hDord : meromorphicOrderAt f z = (D z : WithTop ℤ) := by
    simp only [D, divisor_apply hfK.meromorphicOn hz]
    lift meromorphicOrderAt f z to ℤ using hn z hz with k hk
    simp
  rw [hDord]
  simp only [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero]

end
end MaynardDevelopment
end

/- ZeroLogDerivative -/
section

open scoped BigOperators Topology
open Complex Metric Set Filter Function MeromorphicOn
namespace MaynardDevelopment
noncomputable section

lemma norm_factor_product_center {s : Finset ℂ} {k : ℂ → ℕ} {c : ℂ} {r : ℝ}
    (hs : ∀ a ∈ s, ‖a - c‖ ≤ r) :
    ‖∏ a ∈ s, (c - a) ^ k a‖ ≤ r ^ (∑ a ∈ s, k a) := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intros; positivity
  · intro a ha
    rw [norm_pow, norm_sub_rev]
    exact pow_le_pow_left₀ (norm_nonneg _) (hs a ha) _

lemma norm_factor_product_sphere {s : Finset ℂ} {k : ℂ → ℕ} {c z : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hs : ∀ a ∈ s, ‖a - c‖ ≤ r) (hz : ‖z - c‖ = 2 * r) :
    r ^ (∑ a ∈ s, k a) ≤ ‖∏ a ∈ s, (z - a) ^ k a‖ := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intros; positivity
  · intro a ha
    rw [norm_pow]
    apply pow_le_pow_left₀ hr
    have hh := norm_sub_le (z - c) (z - a)
    have heq : (z - c) - (z - a) = a - c := by ring
    have htri := norm_sub_le z a
    have hdist : ‖z - c‖ ≤ ‖z - a‖ + ‖a - c‖ := by
      convert norm_add_le (z - a) (a - c) using 1 <;> congr 1 <;> ring
    linarith [hs a ha]

lemma logDeriv_factor_product {s : Finset ℂ} {k : ℂ → ℕ} {c : ℂ}
    (hc : (∏ a ∈ s, (c - a) ^ k a) ≠ 0) :
    logDeriv (fun z => ∏ a ∈ s, (z - a) ^ k a) c = ∑ a ∈ s, (k a : ℂ) / (c - a) := by
  rw [logDeriv_prod s (fun a z => (z - a) ^ k a) c
    (Finset.prod_ne_zero_iff.mp hc) (fun _ _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro a _
  rw [logDeriv_fun_pow (by fun_prop)]
  simp [logDeriv_apply, div_eq_mul_inv]

lemma factored_logDeriv_bound {f g : ℂ → ℂ} {c : ℂ} {r M : ℝ} {s : Finset ℂ} {k : ℂ → ℕ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall c (2 * r)))
    (hg : AnalyticOnNhd ℂ g (closedBall c (2 * r)))
    (hs : ∀ a ∈ s, ‖a - c‖ ≤ r)
    (heq : ∀ z ∈ closedBall c (2 * r), f z = (∏ a ∈ s, (z - a) ^ k a) * g z)
    (hgn : ∀ z ∈ closedBall c r, g z ≠ 0) (hfc : f c ≠ 0)
    (hb : ∀ z ∈ closedBall c (2 * r), ‖f z‖ ≤ M) :
    ‖logDeriv f c - ∑ a ∈ s, (k a : ℂ) / (c - a)‖ ≤
      2 * (1 + Real.log M - Real.log ‖f c‖) / r := by
  let N := ∑ a ∈ s, k a
  let P : ℂ → ℂ := fun z => ∏ a ∈ s, (z - a) ^ k a
  have hc2 : c ∈ closedBall c (2 * r) := mem_closedBall_self (by positivity)
  have hc1 : c ∈ closedBall c r := mem_closedBall_self hr.le
  have hPcn : P c ≠ 0 := (mul_ne_zero_iff.mp (heq c hc2 ▸ hfc)).1
  have hgcn : g c ≠ 0 := hgn c hc1
  have hM : 0 < M := (norm_pos_iff.mpr hfc).trans_le (hb c hc2)
  have hpow : 0 < r ^ N := pow_pos hr _
  have hgbound : ∀ z ∈ closedBall c (2 * r), ‖g z‖ ≤ M / r ^ N := by
    have hgc : DiffContOnCl ℂ g (ball c (2 * r)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball c (by positivity : 2 * r ≠ 0)]
      exact hg.differentiableOn
    intro z hz
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hgc _
      (by rwa [closure_ball c (by positivity : 2 * r ≠ 0)])
    intro w hw
    rw [frontier_ball c (by positivity : 2 * r ≠ 0), mem_sphere_iff_norm] at hw
    have hw2 : w ∈ closedBall c (2 * r) := by rw [mem_closedBall_iff_norm, hw]
    have hPw : r ^ N ≤ ‖P w‖ := norm_factor_product_sphere hr.le hs hw
    have hfw := hb w hw2
    rw [heq w hw2, norm_mul] at hfw
    apply (le_div_iff₀ hpow).mpr
    change ‖P w‖ * ‖g w‖ ≤ M at hfw
    nlinarith [mul_le_mul_of_nonneg_right hPw (norm_nonneg (g w))]
  have hgcLower : ‖f c‖ ≤ r ^ N * ‖g c‖ := by
    rw [heq c hc2, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_factor_product_center hs) (norm_nonneg _)
  have hlogs : Real.log (M / r ^ N) - Real.log ‖g c‖ ≤ Real.log M - Real.log ‖f c‖ := by
    have hh := Real.log_le_log (norm_pos_iff.mpr hfc) hgcLower
    rw [Real.log_mul hpow.ne' (norm_ne_zero_iff.mpr hgcn)] at hh
    rw [Real.log_div hM.ne' hpow.ne']
    linarith
  have hinner : ball c r ⊆ closedBall c (2 * r) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hbound := norm_logDeriv_le_disk hr (hg.differentiableOn.mono hinner)
    (fun z hz => hgn z (ball_subset_closedBall hz)) (fun z hz => hgbound z (hinner hz))
  have hlocal : f =ᶠ[𝓝 c] fun z => P z * g z :=
    eventually_of_mem (closedBall_mem_nhds c (by positivity : 0 < 2 * r)) heq
  have hld : logDeriv f c = logDeriv P c + logDeriv g c := by
    rw [logDeriv_apply, hlocal.deriv_eq, hlocal.eq_of_nhds]
    exact logDeriv_mul c hPcn hgcn (by dsimp [P]; fun_prop) (hg c hc2).differentiableAt
  rw [hld, logDeriv_factor_product hPcn, add_sub_cancel_left]
  refine hbound.trans ?_
  apply (div_le_div_iff_of_pos_right hr).mpr
  linarith

/-- Local logarithmic derivative expansion, with an error logarithmic in the growth bound.
The proof strips the zeros in the inner half-disk; no global product formula is needed. -/
theorem disk_logDeriv_expansion {f : ℂ → ℂ} {c : ℂ} {r M : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall c (2 * r)))
    (hfc : f c ≠ 0) (hb : ∀ z ∈ closedBall c (2 * r), ‖f z‖ ≤ M) :
    ∃ s : Finset ℂ, ∃ k : ℂ → ℕ,
      (∀ a, a ∈ s ↔ a ∈ closedBall c r ∧ f a = 0) ∧
      (∀ a ∈ s, 0 < k a) ∧
      (∀ a ∈ s, meromorphicOrderAt f a = ((k a : ℤ) : WithTop ℤ)) ∧
      ‖logDeriv f c - ∑ a ∈ s, (k a : ℂ) / (c - a)‖ ≤
        2 * (1 + Real.log M - Real.log ‖f c‖) / r := by
  classical
  let K := closedBall c r
  let D := MeromorphicOn.divisor f K
  have hKU : K ⊆ closedBall c (2 * r) := closedBall_subset_closedBall (by linarith)
  have hfK : AnalyticOnNhd ℂ f K := hf.mono hKU
  have hD0 (z : ℂ) : 0 ≤ D z := hfK.divisor_nonneg z
  have hcU : c ∈ closedBall c (2 * r) := mem_closedBall_self (by positivity)
  have hcorder : meromorphicOrderAt f c = 0 :=
    (hf.meromorphicNFOn hcU).meromorphicOrderAt_eq_zero_iff.mpr hfc
  have hn (z : ℂ) (hz : z ∈ K) : meromorphicOrderAt f z ≠ ⊤ :=
    hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c (2 * r)).isPreconnected hcU (hKU hz) (by rw [hcorder]; simp)
  have hDord (z : ℂ) (hz : z ∈ K) : (D z : WithTop ℤ) = meromorphicOrderAt f z := by
    simp only [D, divisor_apply hfK.meromorphicOn hz]
    lift meromorphicOrderAt f z to ℤ using hn z hz with j hj
    simp
  let s := (D.finiteSupport (isCompact_closedBall c r)).toFinset
  let k : ℂ → ℕ := fun z => (D z).toNat
  have hs (a : ℂ) : a ∈ s ↔ D a ≠ 0 := by
    simp only [s, Set.Finite.mem_toFinset, Function.mem_support]
  have hsK (a : ℂ) (ha : a ∈ s) : a ∈ K := D.supportWithinDomain ((hs a).mp ha)
  have hzero (a : ℂ) : a ∈ s ↔ a ∈ K ∧ f a = 0 := by
    constructor
    · intro ha
      refine ⟨hsK a ha, ?_⟩
      by_contra hfa
      have ho := (hfK.meromorphicNFOn (hsK a ha)).meromorphicOrderAt_eq_zero_iff.mpr hfa
      have hd := (hDord a (hsK a ha)).trans ho
      exact (hs a).mp ha (by exact_mod_cast hd)
    · rintro ⟨ha, hfa⟩
      apply (hs a).mpr
      intro hDa
      have ho : meromorphicOrderAt f a = 0 := by rw [← hDord a ha, hDa]; rfl
      exact ((hfK.meromorphicNFOn ha).meromorphicOrderAt_eq_zero_iff.mp ho) hfa
  have hkpos (a : ℂ) (ha : a ∈ s) : 0 < k a := by
    have hh := (hs a).mp ha
    have hh0 := hD0 a
    dsimp [k]
    omega
  have hkord (a : ℂ) (ha : a ∈ s) : meromorphicOrderAt f a = ((k a : ℤ) : WithTop ℤ) := by
    rw [← hDord a (hsK a ha)]
    dsimp [k]
    exact_mod_cast (Int.toNat_of_nonneg (hD0 a)).symm
  obtain ⟨g, hg, hfg, hgn⟩ := extract_zeros_on_compact hf hKU (isCompact_closedBall c r) hn
  have hprod (z : ℂ) : (∏ᶠ a, (z - a) ^ D a) = ∏ a ∈ s, (z - a) ^ k a := by
    have hsupp : Function.mulSupport (fun a => (z - a) ^ D a) ⊆ s := by
      intro a ha
      apply (hs a).mpr
      intro hDa
      simpa [Function.mem_mulSupport, hDa] using ha
    rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
    apply Finset.prod_congr rfl
    intro a _
    rw [← Int.toNat_of_nonneg (hD0 a), zpow_natCast]
  refine ⟨s, k, hzero, hkpos, hkord, ?_⟩
  apply factored_logDeriv_bound hr hf hg _ _ hgn hfc hb
  · intro a ha
    exact mem_closedBall_iff_norm.mp (hsK a ha)
  · intro z hz
    have hh := hfg z hz
    change f z = (∏ᶠ a, (z - a) ^ D a) * g z at hh
    rw [hprod] at hh
    exact hh

end
end MaynardDevelopment
end

/- ZeroContributions -/
section

open scoped BigOperators Topology
open Complex Metric Set Filter
namespace MaynardDevelopment
noncomputable section

def zeroContribution (c a : ℂ) : ℝ := (1 / (c - a)).re

lemma zeroContribution_nonneg {c a : ℂ} (h : a.re ≤ c.re) : 0 ≤ zeroContribution c a := by
  simp only [zeroContribution, one_div, Complex.inv_re, Complex.sub_re]
  exact div_nonneg (sub_nonneg.mpr h) (Complex.normSq_nonneg _)

lemma zeroContribution_formula (c a : ℂ) :
    zeroContribution c a = (c.re - a.re) / ((c.re - a.re) ^ 2 + (c.im - a.im) ^ 2) := by
  simp only [zeroContribution, one_div, Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  congr 1
  ring

lemma zeroContribution_same_im {c a : ℂ} (h : c.im = a.im) :
    zeroContribution c a = 1 / (c.re - a.re) := by
  have heq : c - a = ((c.re - a.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [h]
  simp only [zeroContribution, heq, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]

lemma natCast_div_re (k : ℕ) (c a : ℂ) :
    ((k : ℂ) / (c - a)).re = (k : ℝ) * zeroContribution c a := by
  simp only [div_eq_mul_inv, zeroContribution, one_mul, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]

/-- The real part of the logarithmic derivative is bounded above after subtracting any selected
zeros, with arbitrary multiplicities not exceeding their orders. -/
theorem neg_logDeriv_add_zeros_le {f : ℂ → ℂ} {c : ℂ} {r M : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall c (2 * r)))
    (hfc : f c ≠ 0) (hb : ∀ z ∈ closedBall c (2 * r), ‖f z‖ ≤ M)
    (hleft : ∀ a ∈ closedBall c r, f a = 0 → a.re ≤ c.re)
    (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZ : ∀ a ∈ Z, a ∈ closedBall c r ∧ f a = 0)
    (hm : ∀ a ∈ Z, ((m a : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f a) :
    -(logDeriv f c).re + ∑ a ∈ Z, (m a : ℝ) * zeroContribution c a ≤
      2 * (1 + Real.log M - Real.log ‖f c‖) / r := by
  obtain ⟨s, k, hs, hk, hord, hbound⟩ := disk_logDeriv_expansion hr hf hfc hb
  have hZs : Z ⊆ s := fun a ha => (hs a).mpr (hZ a ha)
  have hnon (a : ℂ) (ha : a ∈ s) : 0 ≤ zeroContribution c a :=
    zeroContribution_nonneg (hleft a ((hs a).mp ha).1 ((hs a).mp ha).2)
  have hm' (a : ℂ) (ha : a ∈ Z) : m a ≤ k a := by
    have hh := hm a ha
    rw [hord a (hZs ha)] at hh
    exact_mod_cast hh
  have hsum : (∑ a ∈ Z, (m a : ℝ) * zeroContribution c a) ≤
      ∑ a ∈ s, (k a : ℝ) * zeroContribution c a := by
    calc
      _ ≤ ∑ a ∈ Z, (k a : ℝ) * zeroContribution c a := by
        apply Finset.sum_le_sum
        intro a ha
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm' a ha) (hnon a (hZs ha))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hZs (fun a ha _ => mul_nonneg (Nat.cast_nonneg _) (hnon a ha))
  have hre := (neg_le_abs (logDeriv f c - ∑ a ∈ s, (k a : ℂ) / (c - a)).re).trans
    ((Complex.abs_re_le_norm _).trans hbound)
  simp only [Complex.sub_re, Complex.re_sum, natCast_div_re] at hre
  linarith

lemma meromorphicOrderAt_one_le_of_zero {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (ha : f a = 0) :
    (1 : WithTop ℤ) ≤ meromorphicOrderAt f a := by
  have hpos : 0 < meromorphicOrderAt f a := by
    have hnon := hf.meromorphicOrderAt_nonneg
    have hne : meromorphicOrderAt f a ≠ 0 := by
      intro h
      exact (hf.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h) ha
    exact lt_of_le_of_ne hnon (Ne.symm hne)
  by_cases htop : meromorphicOrderAt f a = ⊤
  · simp [htop]
  · lift meromorphicOrderAt f a to ℤ using htop with n hn
    exact_mod_cast (show (1 : ℤ) ≤ n by exact_mod_cast hpos)

end
end MaynardDevelopment
end

/- LocalLBounds -/
section

open scoped BigOperators Topology
open Complex Metric Set Filter
namespace MaynardDevelopment
noncomputable section

def Lheight (q : ℕ) (t : ℝ) : ℝ := 1 + Real.log q + Real.log (|t| + 3)

lemma Lheight_ge_one (q : ℕ) (t : ℝ) : 1 ≤ Lheight q t := by
  have h1 := Real.log_natCast_nonneg q
  have h2 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  dsimp [Lheight]
  linarith

lemma growth_log_error_bound {q T δ F : ℝ} (hq : 1 ≤ q) (hT : 3 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hF : δ ^ 2 / T ≤ F) :
    8 * (1 + Real.log (4 * q * (T + 1) ^ 2) - Real.log F) ≤
      64 * (1 + Real.log q + Real.log T + Real.log (1 / δ)) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hlogq := Real.log_nonneg hq
  have hlogT := Real.log_nonneg (show 1 ≤ T by linarith)
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hlogF := Real.log_le_log (show 0 < δ ^ 2 / T by positivity) hF
  rw [Real.log_div (pow_pos hδ 2).ne' hT0.ne', Real.log_pow] at hlogF
  have hlogTp : Real.log (T + 1) ≤ Real.log T + Real.log 2 := by
    have hh := Real.log_le_log (show 0 < T + 1 by positivity) (show T + 1 ≤ T * 2 by linarith)
    rwa [Real.log_mul hT0.ne' (by norm_num)] at hh
  have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [Real.log_mul (mul_pos (by norm_num) hq0).ne' (pow_pos (by positivity : 0 < T + 1) 2).ne',
    Real.log_mul (by norm_num) hq0.ne', Real.log_pow, one_div, Real.log_inv]
  norm_num only [Nat.cast_ofNat] at *
  nlinarith

lemma norm_le_im_add_three {c : ℂ} (hc : 0 ≤ c.re) (hc2 : c.re ≤ 2) :
    ‖c‖ ≤ |c.im| + 3 := by
  have hh := Complex.norm_le_abs_re_add_abs_im c
  rw [abs_of_nonneg hc] at hh
  linarith

/-- Local real-part estimate, retaining selected zeros with their multiplicities. -/
theorem regularizedL_neg_logDeriv_roots_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {c : ℂ} (hc : 1 < c.re) (hc2 : c.re ≤ 2)
    (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZ : ∀ a ∈ Z, a ∈ closedBall c (1 / 4) ∧ regularizedL χ a = 0)
    (hm : ∀ a ∈ Z, ((m a : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (regularizedL χ) a) :
    -(logDeriv (regularizedL χ) c).re + ∑ a ∈ Z, (m a : ℝ) * zeroContribution c a ≤
      64 * (Lheight q c.im + Real.log (1 / (c.re - 1))) := by
  let T : ℝ := |c.im| + 3
  let M : ℝ := 4 * (q : ℝ) * (T + 1) ^ 2
  have hc0 : 0 ≤ c.re := by linarith
  have hcn : ‖c‖ ≤ T := norm_le_im_add_three hc0 hc2
  have hT : 3 ≤ T := by dsimp [T]; linarith [abs_nonneg c.im]
  have hcf : regularizedL χ c ≠ 0 := regularizedL_ne_zero χ hc.le
  have hlow : (c.re - 1) ^ 2 / T ≤ ‖regularizedL χ c‖ := by
    calc
      _ ≤ (c.re - 1) ^ 2 / ‖c‖ := div_le_div_of_nonneg_left (sq_nonneg _)
        (norm_pos_iff.mpr (by intro h; norm_num [h] at hc)) hcn
      _ ≤ _ := regularizedL_norm_lower χ hc hc2
  have hfa : AnalyticOnNhd ℂ (regularizedL χ) (closedBall c (2 * (1 / 4))) := by
    intro z _
    exact (regularizedL_differentiable χ).analyticAt z
  have hb : ∀ z ∈ closedBall c (2 * (1 / 4)), ‖regularizedL χ z‖ ≤ M := by
    intro z hz
    rw [mem_closedBall_iff_norm] at hz
    have hre := Complex.abs_re_le_norm (z - c)
    have hneg := neg_le_abs (z.re - c.re)
    simp only [Complex.sub_re] at hre
    have hzre : 1 / 2 ≤ z.re := by linarith
    have hnorm : ‖z‖ + 1 ≤ T + 1 := by
      have hh := norm_add_le (z - c) c
      have hcN := Complex.norm_le_abs_re_add_abs_im c
      rw [abs_of_nonneg hc0] at hcN
      have hh' : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by simpa using hh
      dsimp [T]
      linarith
    refine (regularizedL_norm_upper χ hzre).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hnorm _) (by positivity)
  have hleft : ∀ a ∈ closedBall c (1 / 4), regularizedL χ a = 0 → a.re ≤ c.re := by
    intro a _ ha
    by_contra h
    exact (regularizedL_ne_zero χ (by linarith)) ha
  have hh := neg_logDeriv_add_zeros_le (by norm_num : (0 : ℝ) < 1 / 4) hfa hcf hb hleft Z m hZ hm
  have hErr := growth_log_error_bound (by exact_mod_cast NeZero.pos q : (1 : ℝ) ≤ q)
    hT (by linarith : 0 < c.re - 1) (by linarith : c.re - 1 ≤ 1) hlow
  refine hh.trans ?_
  convert hErr using 1 <;> dsimp [M, T, Lheight] <;> ring

lemma LFunction_neg_logDeriv_roots_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {c : ℂ} (hc : 1 < c.re) (hc2 : c.re ≤ 2)
    (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZ : ∀ a ∈ Z, a ∈ closedBall c (1 / 4) ∧ regularizedL χ a = 0)
    (hm : ∀ a ∈ Z, ((m a : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (regularizedL χ) a) :
    -(logDeriv χ.LFunction c).re + ∑ a ∈ Z, (m a : ℝ) * zeroContribution c a ≤
      (if χ = 1 then zeroContribution c 1 else 0) +
      64 * (Lheight q c.im + Real.log (1 / (c.re - 1))) := by
  have hh := regularizedL_neg_logDeriv_roots_le χ hc hc2 Z m hZ hm
  rw [regularizedL_logDeriv χ hc, Complex.add_re] at hh
  by_cases hχ : χ = 1
  · simp only [hχ, if_true] at hh ⊢
    dsimp only [zeroContribution] at hh ⊢
    linarith
  · simp only [hχ, if_false, Complex.zero_re, zero_add] at hh ⊢
    exact hh

end
end MaynardDevelopment
end

/- ZeroFreeArithmetic -/
section

open scoped BigOperators Topology
open Complex Metric Set Filter
namespace MaynardDevelopment
noncomputable section

def Lscale (q : ℕ) (t : ℝ) : ℝ := 1 / (1048576 * Lheight q t)

lemma Lscale_pos (q : ℕ) (t : ℝ) : 0 < Lscale q t := by
  have hh := Lheight_ge_one q t
  unfold Lscale
  positivity

lemma Lscale_le (q : ℕ) (t : ℝ) : Lscale q t ≤ 1 / 1048576 := by
  unfold Lscale
  apply one_div_le_one_div_of_le (by norm_num)
  linarith [Lheight_ge_one q t]

lemma Lheight_zero_le (q : ℕ) (t : ℝ) : Lheight q 0 ≤ Lheight q t := by
  unfold Lheight
  simp only [abs_zero, zero_add]
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (show 3 ≤ |t|+3 by linarith [abs_nonneg t])
  linarith

lemma Lheight_double_le (q : ℕ) (t : ℝ) : Lheight q (2*t) ≤ 2 * Lheight q t := by
  have hlog : Real.log (|2*t|+3) ≤ Real.log (|t|+3) + Real.log 2 := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < |2*t|+3)
      (show |2*t|+3 ≤ (|t|+3)*2 by rw [abs_mul]; norm_num; linarith)
    rwa [Real.log_mul (by positivity : (|t|+3) ≠ 0) (by norm_num)] at hh
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hH := Lheight_ge_one q t
  unfold Lheight at *
  linarith

lemma Lheight_one_zero_le (q : ℕ) (t : ℝ) : Lheight 1 0 ≤ Lheight q t := by
  have hh := Lheight_zero_le q t
  have hl := Real.log_natCast_nonneg q
  simp only [Lheight, Nat.cast_one, Real.log_one, add_zero] at *
  linarith

lemma Lscale_log_bound (q : ℕ) (t : ℝ) :
    Real.log (1 / Lscale q t) ≤ 21 * Lheight q t := by
  have hH := Lheight_ge_one q t
  have hH0 : 0 < Lheight q t := by linarith
  have hlog := Real.log_le_sub_one_of_pos hH0
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlc : Real.log (1048576 : ℝ) ≤ 20 := by
    rw [show (1048576 : ℝ) = 2^20 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  simp only [Lscale, one_div_one_div]
  rw [Real.log_mul (by norm_num) hH0.ne']
  nlinarith

lemma Lscale_error_bound {q : ℕ} {t H : ℝ} (hH : H ≤ 2 * Lheight q t) :
    Lscale q t * (64 * (H + Real.log (1 / Lscale q t))) ≤ 1 / 512 := by
  have hpos := Lscale_pos q t
  have hlog := Lscale_log_bound q t
  have heq : Lscale q t * Lheight q t = 1 / 1048576 := by
    unfold Lscale
    have hn : Lheight q t ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (Lheight_ge_one q t))
    field_simp [hn]
  nlinarith

lemma zeroContribution_le_inv {c a : ℂ} (h : 0 < c.re-a.re) :
    zeroContribution c a ≤ 1 / (c.re-a.re) := by
  rw [zeroContribution_formula]
  apply (div_le_div_iff₀ (by positivity : 0 < (c.re-a.re)^2+(c.im-a.im)^2) h).mpr
  nlinarith [sq_nonneg (c.im-a.im)]

lemma zeroContribution_pole_half {δ t : ℝ} (hδ : 0 < δ) (ht : δ/2 ≤ |t|) :
    zeroContribution ((1+δ : ℝ) + I*((2*t : ℝ) : ℂ)) 1 ≤ 1 / (2*δ) := by
  rw [zeroContribution_formula]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero, Complex.one_re, Complex.add_im, Complex.mul_im,
    Complex.I_im, one_mul, zero_add, Complex.one_im, add_sub_cancel_left]
  apply (div_le_div_iff₀ (by positivity : 0 < δ^2+(2*t)^2) (by positivity : 0 < 2*δ)).mpr
  nlinarith [sq_abs t, sq_nonneg (|t|-δ/2)]

lemma zeroContribution_near_real_lower {δ : ℝ} {a : ℂ} (hδ : 0 < δ)
    (ha : 1-δ/100 ≤ a.re) (ha1 : a.re < 1) (hi : |a.im| ≤ δ/2) :
    3 / (4*δ) ≤ zeroContribution ((1+δ : ℝ) : ℂ) a := by
  rw [zeroContribution_formula]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_sub, neg_sq]
  have hx : 0 < 1+δ-a.re := by linarith
  have hi2 : a.im^2 ≤ δ^2/4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg a.im) hi 2
    rw [sq_abs] at hh
    nlinarith
  apply (div_le_div_iff₀ (by positivity : 0 < 4*δ)
    (by positivity : 0 < (1+δ-a.re)^2+a.im^2)).mpr
  have hu : (1+δ-a.re)^2 ≤ (101*δ/100)^2 := by
    apply pow_le_pow_left₀ hx.le (by linarith)
  nlinarith

lemma Lheight_mono_level {q r : ℕ} (hq : 0 < q) (hqr : q ≤ r) (t : ℝ) : Lheight q t ≤ Lheight r t := by
  have hh := Real.log_le_log (by exact_mod_cast hq : (0 : ℝ) < q) (by exact_mod_cast hqr : (q : ℝ) ≤ r)
  unfold Lheight
  linarith

lemma Lscale_antitone_level {q r : ℕ} (hq : 0 < q) (hqr : q ≤ r) (t : ℝ) : Lscale r t ≤ Lscale q t := by
  unfold Lscale
  apply one_div_le_one_div_of_le
  · have hh := Lheight_ge_one q t
    positivity
  · linarith [Lheight_mono_level hq hqr t]

end
end MaynardDevelopment
end

/- LConjugacy -/
section

open scoped BigOperators Topology
open Complex ComplexConjugate Set Filter
namespace MaynardDevelopment
noncomputable section

lemma natCast_cpow_conj (n : ℕ) (s : ℂ) :
    (n : ℂ) ^ (conj s) = conj ((n : ℂ) ^ s) := by
  have ha : (n : ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact ne_of_lt Real.pi_pos
  simpa using Complex.cpow_conj (n : ℂ) s ha

lemma LSeries_conjugate {f g : ℕ → ℂ} (hfg : ∀ n, g n = conj (f n)) (s : ℂ) :
    LSeries g (conj s) = conj (LSeries f s) := by
  unfold LSeries
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0 <;> simp [LSeries.term_def, hn, hfg, natCast_cpow_conj]

lemma LFunction_inverse_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    χ⁻¹.LFunction (conj s) = conj (χ.LFunction s) := by
  rw [χ.LFunction_eq_LSeries hs, χ⁻¹.LFunction_eq_LSeries (by simpa using hs)]
  exact LSeries_conjugate (fun n => (MulChar.star_apply' χ (n : ZMod q)).symm) s

lemma regularizedL_inverse_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    regularizedL χ⁻¹ (conj s) = conj (regularizedL χ s) := by
  have hf : AnalyticOnNhd ℂ (regularizedL χ) Set.univ :=
    fun z _ => (regularizedL_differentiable χ).analyticAt z
  have hg : AnalyticOnNhd ℂ (fun z => conj (regularizedL χ⁻¹ (conj z))) Set.univ := by
    intro z _
    apply Differentiable.analyticAt
    intro w
    simpa only [Function.comp_def, Complex.star_def, Complex.conj_conj] using ((regularizedL_differentiable χ⁻¹) (conj w)).star_star
  have heq : regularizedL χ =ᶠ[𝓝 (2 : ℂ)] fun z => conj (regularizedL χ⁻¹ (conj z)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    have hz1 : z ≠ 1 := by intro h; norm_num [h] at hz
    have hzc : conj z ≠ 1 := by
      intro h
      apply hz1
      simpa using congrArg conj h
    rw [regularizedL_factor χ hz1, regularizedL_factor χ⁻¹ hzc,
      LFunction_inverse_conj χ hz, map_mul, Complex.conj_conj]
    by_cases hχ : χ = 1 <;> simp [hχ]
  have hh := hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) heq (Set.mem_univ s)
  simpa using congrArg conj hh.symm

lemma real_character_inv {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) : χ⁻¹ = χ := by
  apply inv_eq_of_mul_eq_one_left
  simpa [pow_two] using hχ

lemma regularizedL_conj_of_real {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ^ 2 = 1) (s : ℂ) :
    regularizedL χ (conj s) = conj (regularizedL χ s) := by
  simpa [real_character_inv χ hχ] using regularizedL_inverse_conj χ s

end
end MaynardDevelopment
end

/- LPositivity -/
section

open scoped BigOperators Topology
open Complex ComplexConjugate Set Filter ArithmeticFunction
namespace MaynardDevelopment
noncomputable section

/-- Negative real logarithmic derivative of a Dirichlet L-function. -/
def negLDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℝ :=
  -(logDeriv χ.LFunction s).re

def mangoldtWeight (n : ℕ) (σ : ℝ) : ℝ := vonMangoldt n * (n : ℝ) ^ (-σ)
def dirichletPhase (n : ℕ) (t : ℝ) : ℂ := (n : ℂ) ^ (-(I * t))

lemma mangoldtWeight_nonneg (n : ℕ) (σ : ℝ) : 0 ≤ mangoldtWeight n σ :=
  mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma dirichletPhase_norm {n : ℕ} (hn : n ≠ 0) (t : ℝ) : ‖dirichletPhase n t‖ = 1 := by
  unfold dirichletPhase
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)]
  simp

lemma dirichletPhase_double (n : ℕ) (t : ℝ) : dirichletPhase n (2*t) = dirichletPhase n t ^ 2 := by
  unfold dirichletPhase
  rw [show -(I * ((2*t : ℝ) : ℂ)) = (2 : ℕ) * -(I * (t : ℂ)) by push_cast; ring,
    Complex.cpow_nat_mul]

lemma twisted_mangoldt_term {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) (σ t : ℝ) :
    LSeries.term (fun n : ℕ => χ n * (vonMangoldt n : ℂ)) (σ + I * t) n =
      (mangoldtWeight n σ : ℂ) * (χ n * dirichletPhase n t) := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_def, mangoldtWeight]
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
    neg_add, Complex.cpow_add _ _ (by exact_mod_cast hn)]
  simp only [mangoldtWeight, Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n),
    Complex.ofReal_neg, Complex.ofReal_natCast, dirichletPhase]
  ring

lemma negLDeriv_eq_tsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    negLDeriv χ (σ + I * t) =
      ∑' n : ℕ, mangoldtWeight n σ * (χ n * dirichletPhase n t).re := by
  have hs : 1 < ((σ : ℂ) + I * t).re := by simpa using hσ
  have heq := χ.LSeries_twist_vonMangoldt_eq hs
  rw [← χ.deriv_LFunction_eq_deriv_LSeries hs, ← χ.LFunction_eq_LSeries hs] at heq
  have hh := congrArg Complex.re heq
  rw [neg_div, Complex.neg_re] at hh
  change (LSeries (fun n : ℕ => χ n * (vonMangoldt n : ℂ)) (σ + I * t)).re = _ at hh
  unfold negLDeriv
  rw [logDeriv_apply]
  rw [← hh, LSeries]
  have hsum : Summable (LSeries.term (fun n : ℕ => χ n * (vonMangoldt n : ℂ)) (σ + I * t)) :=
    χ.LSeriesSummable_twist_vonMangoldt hs
  rw [Complex.re_tsum hsum]
  apply tsum_congr
  intro n
  rw [twisted_mangoldt_term]
  simp

lemma mangoldtPhase_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    Summable (fun n : ℕ => mangoldtWeight n σ * (χ n * dirichletPhase n t).re) := by
  have hs : 1 < ((σ : ℂ) + I * t).re := by simpa using hσ
  have hh := (Complex.hasSum_re (χ.LSeriesSummable_twist_vonMangoldt hs).hasSum).summable
  convert hh using 1
  funext n
  rw [show LSeries.term ((fun n : ℕ => χ n) * (fun n : ℕ => (vonMangoldt n : ℂ)))
      (σ + I * t) n = (mangoldtWeight n σ : ℂ) * (χ n * dirichletPhase n t) from twisted_mangoldt_term χ n σ t]
  simp

lemma principal_one_eval (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
  rw [Subsingleton.elim (n : ZMod 1) 1, map_one]

lemma trig_polynomial_nonneg {u : ℂ} (hu : ‖u‖ ≤ 1) :
    0 ≤ 3 + 4 * u.re + (u ^ 2).re := by
  have hh := Complex.sq_norm_sub_sq_re u
  have hn := norm_nonneg u
  simp only [pow_two, Complex.mul_re]
  nlinarith [sq_nonneg (u.re + 1)]

/-- The de la Vallée-Poussin positivity inequality. -/
lemma negLDeriv_trig_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * negLDeriv (1 : DirichletCharacter ℂ 1) σ +
      4 * negLDeriv χ (σ + I*t) + negLDeriv (χ ^ 2) (σ + I*((2*t : ℝ) : ℂ)) := by
  have hzero : (σ : ℂ) = σ + I * (0 : ℝ) := by simp
  nth_rw 1 [hzero]
  rw [negLDeriv_eq_tsum _ hσ, negLDeriv_eq_tsum _ hσ, negLDeriv_eq_tsum _ hσ,
    ← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add ((mangoldtPhase_summable _ hσ 0).mul_left 3) ((mangoldtPhase_summable χ hσ t).mul_left 4),
    ← Summable.tsum_add (((mangoldtPhase_summable _ hσ 0).mul_left 3).add ((mangoldtPhase_summable χ hσ t).mul_left 4))
      (mangoldtPhase_summable (χ^2) hσ (2*t))]
  apply tsum_nonneg
  intro n
  by_cases hn : n = 0
  · subst n
    simp [mangoldtWeight]
  have hu : ‖χ (n : ZMod q) * dirichletPhase n t‖ ≤ 1 := by
    rw [norm_mul, dirichletPhase_norm hn, mul_one]
    exact χ.norm_le_one _
  have hh := mul_nonneg (mangoldtWeight_nonneg n σ) (trig_polynomial_nonneg hu)
  rw [dirichletPhase_double, MulChar.pow_apply' χ (by norm_num : (2 : ℕ) ≠ 0), ← mul_pow,
    principal_one_eval]
  simpa [dirichletPhase, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using hh

lemma negLDeriv_real_eq_tsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) :
    negLDeriv χ σ = ∑' n : ℕ, mangoldtWeight n σ * (χ n).re := by
  simpa [dirichletPhase] using negLDeriv_eq_tsum χ hσ 0

lemma mangoldt_real_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) : Summable (fun n : ℕ => mangoldtWeight n σ * (χ n).re) := by
  simpa [dirichletPhase] using mangoldtPhase_summable χ hσ 0

lemma character_re_ge_neg_one {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    -1 ≤ (χ (n : ZMod q)).re := by
  have hh := (abs_le.mp (Complex.abs_re_le_norm (χ (n : ZMod q)))).1
  have hn := χ.norm_le_one (n : ZMod q)
  linarith

lemma real_character_im {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (n : ℕ) :
    (χ (n : ZMod q)).im = 0 := by
  have hh := MulChar.star_apply' χ (n : ZMod q)
  rw [real_character_inv χ hχ] at hh
  have hi := congrArg Complex.im hh
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

lemma negLDeriv_pair_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ negLDeriv (1 : DirichletCharacter ℂ 1) σ + negLDeriv χ σ := by
  rw [negLDeriv_real_eq_tsum _ hσ, negLDeriv_real_eq_tsum _ hσ,
    ← Summable.tsum_add (mangoldt_real_summable _ hσ) (mangoldt_real_summable χ hσ)]
  apply tsum_nonneg
  intro n
  rw [principal_one_eval, Complex.one_re, ← mul_add]
  exact mul_nonneg (mangoldtWeight_nonneg n σ) (by linarith [character_re_ge_neg_one χ n])

lemma negLDeriv_four_nonneg {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    (hχ : χ ^ 2 = 1) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ negLDeriv (1 : DirichletCharacter ℂ 1) σ + negLDeriv χ σ +
      negLDeriv ψ σ + negLDeriv (χ*ψ) σ := by
  rw [negLDeriv_real_eq_tsum _ hσ, negLDeriv_real_eq_tsum _ hσ,
    negLDeriv_real_eq_tsum _ hσ, negLDeriv_real_eq_tsum _ hσ,
    ← Summable.tsum_add (mangoldt_real_summable _ hσ) (mangoldt_real_summable χ hσ),
    ← Summable.tsum_add ((mangoldt_real_summable _ hσ).add (mangoldt_real_summable χ hσ))
      (mangoldt_real_summable ψ hσ),
    ← Summable.tsum_add (((mangoldt_real_summable _ hσ).add (mangoldt_real_summable χ hσ)).add
      (mangoldt_real_summable ψ hσ)) (mangoldt_real_summable (χ*ψ) hσ)]
  apply tsum_nonneg
  intro n
  rw [principal_one_eval, Complex.one_re, MulChar.mul_apply, Complex.mul_re, real_character_im χ hχ]
  have hh := mul_nonneg (mangoldtWeight_nonneg n σ)
    (mul_nonneg (show 0 ≤ 1+(χ (n : ZMod q)).re by linarith [character_re_ge_neg_one χ n])
      (show 0 ≤ 1+(ψ (n : ZMod q)).re by linarith [character_re_ge_neg_one ψ n]))
  nlinarith

end
end MaynardDevelopment
end

/- LZeroFree -/
section

open scoped BigOperators Topology
open Complex ComplexConjugate Metric Set Filter
namespace MaynardDevelopment
noncomputable section

lemma scaled_negLDeriv_roots_le {q r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    {t : ℝ} {c : ℂ} (hc : c.re = 1 + Lscale q t)
    (hH : Lheight r c.im ≤ 2 * Lheight q t)
    (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZ : ∀ a ∈ Z, a ∈ closedBall c (1/4) ∧ regularizedL χ a = 0)
    (hm : ∀ a ∈ Z, ((m a : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (regularizedL χ) a) :
    Lscale q t * (negLDeriv χ c + ∑ a ∈ Z, (m a : ℝ) * zeroContribution c a) ≤
      (if χ = 1 then Lscale q t * zeroContribution c 1 else 0) + 1/512 := by
  have hδ := Lscale_pos q t
  have hδb := Lscale_le q t
  have hh := LFunction_neg_logDeriv_roots_le χ (by linarith : 1 < c.re)
    (by linarith : c.re ≤ 2) Z m hZ hm
  have hhh := mul_le_mul_of_nonneg_left hh hδ.le
  have he := Lscale_error_bound hH
  have hd : c.re-1 = Lscale q t := by linarith
  rw [hd, mul_add] at hhh
  by_cases hχ : χ = 1 <;> simp only [hχ, if_true, if_false, mul_zero] at hhh ⊢ <;>
    dsimp only [negLDeriv] <;> linarith

lemma scaled_negLDeriv_le {q r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    {t : ℝ} {c : ℂ} (hc : c.re = 1 + Lscale q t)
    (hH : Lheight r c.im ≤ 2 * Lheight q t) :
    Lscale q t * negLDeriv χ c ≤
      (if χ = 1 then Lscale q t * zeroContribution c 1 else 0) + 1/512 := by
  simpa using scaled_negLDeriv_roots_le χ hc hH ∅ (fun _ => 0) (by simp) (by simp)

lemma scaled_negLDeriv_one_zero_le {q : ℕ} [NeZero q] {t : ℝ} :
    Lscale q t * negLDeriv (1 : DirichletCharacter ℂ 1) ((1+Lscale q t : ℝ) : ℂ) ≤ 1+1/512 := by
  have hh := scaled_negLDeriv_le (q := q) (1 : DirichletCharacter ℂ 1)
    (t := t) (c := ((1+Lscale q t : ℝ) : ℂ)) rfl
    (by simpa using (Lheight_one_zero_le q t).trans (by linarith [Lheight_ge_one q t]))
  rw [if_pos rfl, zeroContribution_same_im (by simp)] at hh
  simpa [(Lscale_pos q t).ne'] using hh

lemma scaled_negLDeriv_single_le {q r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    {t : ℝ} {c a : ℂ} (hc : c.re = 1 + Lscale q t)
    (hH : Lheight r c.im ≤ 2 * Lheight q t)
    (ha : a ∈ closedBall c (1/4)) (hz : regularizedL χ a = 0) :
    Lscale q t * (negLDeriv χ c + zeroContribution c a) ≤
      (if χ = 1 then Lscale q t * zeroContribution c 1 else 0) + 1/512 := by
  simpa using scaled_negLDeriv_roots_le χ hc hH {a} (fun _ => 1)
    (by simpa using And.intro ha hz)
    (by simpa using meromorphicOrderAt_one_le_of_zero ((regularizedL_differentiable χ).analyticAt a) hz)

lemma root_re_lt_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {a : ℂ}
    (ha : regularizedL χ a = 0) : a.re < 1 := by
  by_contra h
  exact regularizedL_ne_zero χ (le_of_not_gt h) ha

lemma close_root_in_disk {δ : ℝ} (hδ : 0 < δ) (hδb : δ ≤ 1/1048576)
    {a : ℂ} (ha : 1-δ/100 ≤ a.re) (ha1 : a.re < 1) :
    a ∈ closedBall (((1+δ : ℝ) : ℂ) + I*a.im) (1/4) := by
  rw [mem_closedBall_iff_norm]
  have heq : a - (((1+δ : ℝ) : ℂ) + I*a.im) = ((a.re-(1+δ) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith

lemma close_root_contribution {δ : ℝ} (hδ : 0 < δ) {a : ℂ}
    (ha : 1-δ/100 ≤ a.re) (ha1 : a.re < 1) :
    100/101 ≤ δ * zeroContribution (((1+δ : ℝ) : ℂ) + I*a.im) a := by
  rw [zeroContribution_same_im (by simp)]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  rw [mul_one_div]
  apply (le_div_iff₀ (by linarith : 0 < 1+δ-a.re)).mpr
  linarith

/-- A zero in the narrow region can only be a low-lying zero of a real character. -/
lemma near_one_zero_low_real_character {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {a : ℂ} (hz : regularizedL χ a = 0)
    (ha : 1 - Lscale q a.im / 100 ≤ a.re) :
    χ ^ 2 = 1 ∧ |a.im| < Lscale q a.im / 2 := by
  let δ := Lscale q a.im
  have hδ : 0 < δ := Lscale_pos q a.im
  have hδb : δ ≤ 1/1048576 := Lscale_le q a.im
  have ha1 := root_re_lt_one hz
  let c : ℂ := ((1+δ : ℝ) : ℂ) + I*a.im
  let c₂ : ℂ := ((1+δ : ℝ) : ℂ) + I*((2*a.im : ℝ) : ℂ)
  have hc : c.re = 1+δ := by simp [c]
  have hc₂ : c₂.re = 1+δ := by simp [c₂]
  have hH : Lheight q c.im ≤ 2*Lheight q a.im := by
    simp only [c, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add, add_zero]
    linarith [Lheight_ge_one q a.im]
  have hH₂ : Lheight q c₂.im ≤ 2*Lheight q a.im := by
    simpa [c₂] using Lheight_double_le q a.im
  have h₁ := scaled_negLDeriv_one_zero_le (q := q) (t := a.im)
  have h₂ := scaled_negLDeriv_single_le χ hc hH (close_root_in_disk hδ hδb ha ha1) hz
  rw [if_neg hχ, zero_add] at h₂
  have h₃ := scaled_negLDeriv_le (χ^2) hc₂ hH₂
  have hp := mul_nonneg hδ.le (negLDeriv_trig_nonneg χ (by linarith : 1 < 1+δ) a.im)
  have hr := close_root_contribution hδ ha ha1
  change 100/101 ≤ δ * zeroContribution c a at hr
  change 0 ≤ δ * (3 * negLDeriv (1 : DirichletCharacter ℂ 1) ((1+δ : ℝ) : ℂ) +
    4 * negLDeriv χ c + negLDeriv (χ^2) c₂) at hp
  change δ * negLDeriv (1 : DirichletCharacter ℂ 1) ((1+δ : ℝ) : ℂ) ≤ 1+1/512 at h₁
  change δ * (negLDeriv χ c + zeroContribution c a) ≤ 1/512 at h₂
  change δ * negLDeriv (χ^2) c₂ ≤ (if χ^2=1 then δ*zeroContribution c₂ 1 else 0)+1/512 at h₃
  have hsq : χ^2=1 := by
    by_contra hsq
    rw [if_neg hsq] at h₃
    nlinarith
  refine ⟨hsq, ?_⟩
  by_contra ht
  have hhalf := zeroContribution_pole_half hδ (le_of_not_gt ht)
  change zeroContribution c₂ 1 ≤ 1/(2*δ) at hhalf
  have hpole : δ * zeroContribution c₂ 1 ≤ 1/2 := by
    calc
      _ ≤ δ * (1/(2*δ)) := mul_le_mul_of_nonneg_left hhalf hδ.le
      _ = _ := by field_simp
  rw [if_pos hsq] at h₃
  nlinarith

lemma close_real_root_in_disk {δ : ℝ} (hδb : δ ≤ 1/1048576)
    {a : ℂ} (ha : 1-δ/100 ≤ a.re) (ha1 : a.re < 1) (hi : |a.im| ≤ δ/2) :
    a ∈ closedBall ((1+δ : ℝ) : ℂ) (1/4) := by
  rw [mem_closedBall_iff_norm]
  have hh := Complex.norm_le_abs_re_add_abs_im (a-((1+δ : ℝ) : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at hh
  have hδ : 0 < δ := by linarith [abs_nonneg a.im]
  rw [abs_of_nonpos (by linarith : a.re-(1+δ) ≤ 0)] at hh
  linarith

/-- In the narrow rectangle at the real axis, the total zero multiplicity is at most one. -/
lemma near_real_zero_total_order_le_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZ : ∀ a ∈ Z, 1-Lscale q t/100 ≤ a.re ∧ |a.im| ≤ Lscale q t/2 ∧ regularizedL χ a = 0)
    (hm : ∀ a ∈ Z, ((m a : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (regularizedL χ) a) :
    ∑ a ∈ Z, m a ≤ 1 := by
  let δ := Lscale q t
  have hδ : 0 < δ := Lscale_pos q t
  have hδb := Lscale_le q t
  have hZ' : ∀ a ∈ Z, a ∈ closedBall ((1+δ : ℝ) : ℂ) (1/4) ∧ regularizedL χ a = 0 := by
    intro a ha
    obtain ⟨haR, haI, haZ⟩ := hZ a ha
    exact ⟨close_real_root_in_disk hδb haR (root_re_lt_one haZ) haI, haZ⟩
  have hh := scaled_negLDeriv_roots_le χ (t := t) (c := ((1+δ : ℝ) : ℂ)) rfl
    (by simpa using (Lheight_zero_le q t).trans (by linarith [Lheight_ge_one q t])) Z m hZ' hm
  rw [if_neg hχ, zero_add] at hh
  have h₁ := scaled_negLDeriv_one_zero_le (q := q) (t := t)
  have hp := mul_nonneg hδ.le (negLDeriv_pair_nonneg χ (by linarith : 1 < 1+δ))
  have hsum : (3/4 : ℝ) * (∑ a ∈ Z, m a : ℕ) ≤
      δ * ∑ a ∈ Z, (m a : ℝ) * zeroContribution ((1+δ : ℝ) : ℂ) a := by
    rw [Nat.cast_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    obtain ⟨haR, haI, haZ⟩ := hZ a ha
    have hlow := zeroContribution_near_real_lower hδ haR (root_re_lt_one haZ) haI
    have hh' : 3/4 ≤ δ * zeroContribution ((1+δ : ℝ) : ℂ) a := by
      have hd := mul_le_mul_of_nonneg_left hlow hδ.le
      have heq : δ*(3/(4*δ)) = 3/4 := by field_simp
      rwa [heq] at hd
    nlinarith [Nat.cast_nonneg (α := ℝ) (m a)]
  change δ * (negLDeriv χ ((1+δ : ℝ) : ℂ) + _) ≤ 1/512 at hh
  change δ * negLDeriv (1 : DirichletCharacter ℂ 1) ((1+δ : ℝ) : ℂ) ≤ 1+1/512 at h₁
  by_contra h
  have hn : (2 : ℝ) ≤ (∑ a ∈ Z, m a : ℕ) := by exact_mod_cast (show 2 ≤ ∑ a ∈ Z, m a by omega)
  nlinarith

/-- Explicit zero-free region, apart from a possible real zero of a quadratic character. -/
theorem near_one_zero_is_real {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {a : ℂ} (hz : regularizedL χ a = 0)
    (ha : 1 - Lscale q a.im / 100 ≤ a.re) : χ ^ 2 = 1 ∧ a.im = 0 := by
  obtain ⟨hsq, hsmall⟩ := near_one_zero_low_real_character χ hχ hz ha
  refine ⟨hsq, ?_⟩
  by_contra hi
  have hne : a ≠ conj a := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.conj_im] at hh
    exact hi (by linarith)
  have hzc : regularizedL χ (conj a) = 0 := by rw [regularizedL_conj_of_real χ hsq, hz, map_zero]
  have hh := near_real_zero_total_order_le_one χ hχ a.im {a, conj a} (fun _ => 1)
    (by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · exact ⟨ha, hsmall.le, hz⟩
      · simpa using And.intro ha (And.intro hsmall.le hzc))
    (by
      intro b hb
      have hbz : regularizedL χ b = 0 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl <;> assumption
      simpa using meromorphicOrderAt_one_le_of_zero ((regularizedL_differentiable χ).analyticAt b) hbz)
  simp [hne] at hh

theorem near_one_zero_simple {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {a : ℂ} (hz : regularizedL χ a = 0)
    (ha : 1 - Lscale q a.im / 100 ≤ a.re) : meromorphicOrderAt (regularizedL χ) a = 1 := by
  have hlow := near_one_zero_low_real_character χ hχ hz ha
  have hnot : ¬ (2 : WithTop ℤ) ≤ meromorphicOrderAt (regularizedL χ) a := by
    intro h
    have hh := near_real_zero_total_order_le_one χ hχ a.im {a} (fun _ => 2)
      (by simpa using And.intro ha (And.intro hlow.2.le hz)) (by simpa using h)
    norm_num at hh
  have hpos := meromorphicOrderAt_one_le_of_zero ((regularizedL_differentiable χ).analyticAt a) hz
  have htop : meromorphicOrderAt (regularizedL χ) a ≠ ⊤ := by intro h; simp [h] at hnot
  lift meromorphicOrderAt (regularizedL χ) a to ℤ using htop with n hn
  norm_cast at hpos hnot ⊢
  have hn2 : ¬ (2 : ℤ) ≤ n := by
    intro hh
    apply hnot
    exact WithTop.coe_le_coe.mpr hh
  omega

lemma near_real_zero_unique {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {a b : ℂ} (haz : regularizedL χ a = 0) (hbz : regularizedL χ b = 0)
    (hai : a.im = 0) (hbi : b.im = 0)
    (ha : 1-Lscale q 0/100 ≤ a.re) (hb : 1-Lscale q 0/100 ≤ b.re) : a = b := by
  by_contra hne
  have hδ := Lscale_pos q 0
  have hh := near_real_zero_total_order_le_one χ hχ 0 {a,b} (fun _ => 1)
    (by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ⟨ha, by rw [hai, abs_zero]; positivity, haz⟩
      · exact ⟨hb, by rw [hbi, abs_zero]; positivity, hbz⟩)
    (by
      intro z hz
      have hzz : regularizedL χ z = 0 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      simpa using meromorphicOrderAt_one_le_of_zero ((regularizedL_differentiable χ).analyticAt z) hzz)
  simp [hne] at hh

end
end MaynardDevelopment
end

/- LandauPage -/
section

open scoped BigOperators Topology
open Complex ComplexConjugate Metric Set Filter DirichletCharacter
namespace MaynardDevelopment
noncomputable section

/-- Two distinct nonprincipal characters of the same modulus cannot both have a real zero
in the Page region, provided one character is quadratic. -/
lemma page_same_level {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hsq : χ^2=1) (hne : χ ≠ ψ)
    {a b : ℂ} (haz : regularizedL χ a = 0) (hbz : regularizedL ψ b = 0)
    (hai : a.im = 0) (hbi : b.im = 0)
    (ha : 1-Lscale q 0/100 ≤ a.re) (hb : 1-Lscale q 0/100 ≤ b.re) : False := by
  let δ := Lscale q 0
  let c : ℂ := ((1+δ : ℝ) : ℂ)
  have hδ : 0 < δ := Lscale_pos q 0
  have hδb : δ ≤ 1/1048576 := Lscale_le q 0
  have hH : Lheight q c.im ≤ 2*Lheight q 0 := by simp only [c, Complex.ofReal_im]; linarith [Lheight_ge_one q 0]
  have hai' : |a.im| ≤ δ/2 := by rw [hai, abs_zero]; positivity
  have hbi' : |b.im| ≤ δ/2 := by rw [hbi, abs_zero]; positivity
  have har := root_re_lt_one haz
  have hbr := root_re_lt_one hbz
  have h₁ := scaled_negLDeriv_one_zero_le (q := q) (t := 0)
  have h₂ := scaled_negLDeriv_single_le χ (t := 0) (c := c) rfl hH
    (close_real_root_in_disk hδb ha har hai') haz
  have h₃ := scaled_negLDeriv_single_le ψ (t := 0) (c := c) rfl hH
    (close_real_root_in_disk hδb hb hbr hbi') hbz
  have hpnon : χ*ψ ≠ 1 := by
    intro h
    have hh : ψ = χ⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [real_character_inv χ hsq] at hh
    exact hne hh.symm
  have h₄ := scaled_negLDeriv_le (χ*ψ) (t := 0) (c := c) rfl hH
  rw [if_neg hχ, zero_add] at h₂
  rw [if_neg hψ, zero_add] at h₃
  rw [if_neg hpnon, zero_add] at h₄
  have hp := mul_nonneg hδ.le (negLDeriv_four_nonneg χ ψ hsq (by linarith : 1 < 1+δ))
  have hra := zeroContribution_near_real_lower hδ ha har hai'
  have hrb := zeroContribution_near_real_lower hδ hb hbr hbi'
  have heq : δ*(3/(4*δ)) = 3/4 := by field_simp
  have hra' := mul_le_mul_of_nonneg_left hra hδ.le
  have hrb' := mul_le_mul_of_nonneg_left hrb hδ.le
  rw [heq] at hra' hrb'
  change δ * negLDeriv (1 : DirichletCharacter ℂ 1) c ≤ 1+1/512 at h₁
  change δ * (negLDeriv χ c + zeroContribution c a) ≤ 1/512 at h₂
  change δ * (negLDeriv ψ c + zeroContribution c b) ≤ 1/512 at h₃
  change δ * negLDeriv (χ*ψ) c ≤ 1/512 at h₄
  change 0 ≤ δ * (negLDeriv (1 : DirichletCharacter ℂ 1) c + negLDeriv χ c + negLDeriv ψ c + negLDeriv (χ*ψ) c) at hp
  nlinarith

lemma regularizedL_changeLevel_zero {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q ∣ r) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {a : ℂ} (ha : regularizedL χ a = 0) : regularizedL (changeLevel hqr χ) a = 0 := by
  have hn : changeLevel hqr χ ≠ 1 := hχ ∘ (changeLevel_eq_one_iff hqr).mp
  simp only [regularizedL, if_neg hχ] at ha
  simp only [regularizedL, if_neg hn, LFunction_changeLevel hqr χ (.inl hχ), ha, zero_mul]

lemma primitive_changeLevel_ne_of_not_dvd {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) (hqr : ¬ q ∣ r) :
    changeLevel (dvd_mul_right q r) χ ≠ changeLevel (dvd_mul_left r q) ψ := by
  have hlt : Nat.gcd q r < q := by
    have hle := Nat.gcd_le_left r (NeZero.pos q)
    have hne : Nat.gcd q r ≠ q := by
      intro h
      exact hqr (h ▸ Nat.gcd_dvd_right q r)
    omega
  obtain ⟨u, hu, hχu⟩ := primitive_exists_kernel_unit χ hχ (Nat.gcd_dvd_left q r) hlt
  obtain ⟨w, hwq, hwr⟩ := unit_lift_gcd u hu
  intro heq
  have hh := congrArg (fun θ : DirichletCharacter ℂ (q*r) => θ w) heq
  dsimp only at hh
  rw [changeLevel_eq_cast_of_dvd, changeLevel_eq_cast_of_dvd] at hh
  change χ (ZMod.castHom (dvd_mul_right q r) (ZMod q) w) = ψ (ZMod.castHom (dvd_mul_left r q) (ZMod r) w) at hh
  rw [hwq, hwr, map_one] at hh
  exact hχu hh

lemma primitive_changeLevel_ne_of_ne {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hqr : q ≠ r) :
    changeLevel (dvd_mul_right q r) χ ≠ changeLevel (dvd_mul_left r q) ψ := by
  by_cases hd : q ∣ r
  · have hnd : ¬ r ∣ q := fun h => hqr (Nat.dvd_antisymm hd h)
    have hh := primitive_changeLevel_ne_of_not_dvd ψ χ hψ hnd
    intro heq
    apply hh
    have hdiv : r*q ∣ q*r := by rw [Nat.mul_comm r q]
    apply changeLevel_injective hdiv
    simpa only [← changeLevel_trans] using heq.symm
  · exact primitive_changeLevel_ne_of_not_dvd χ ψ hχ hd

lemma page_distinct_levels {q r Q : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχp : χ.IsPrimitive) (hψp : ψ.IsPrimitive) (hqr : q ≠ r)
    (hqQ : q ≤ Q) (hrQ : r ≤ Q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {a b : ℂ} (haz : regularizedL χ a = 0) (hbz : regularizedL ψ b = 0)
    (hai : a.im = 0) (hbi : b.im = 0)
    (ha : 1-Lscale (Q^2) 0/100 ≤ a.re) (hb : 1-Lscale (Q^2) 0/100 ≤ b.re) : False := by
  have hqprod : q ≤ q*r := Nat.le_mul_of_pos_right _ (NeZero.pos r)
  have hprod : q*r ≤ Q^2 := by nlinarith
  have hsc := Lscale_antitone_level (NeZero.pos (q*r)) hprod 0
  have hscq := Lscale_antitone_level (NeZero.pos q) (hqprod.trans hprod) 0
  have hsq : χ^2=1 := (near_one_zero_is_real χ hχ haz (by rw [hai]; linarith)).1
  have hχ' : changeLevel (dvd_mul_right q r) χ ≠ 1 := hχ ∘ (changeLevel_eq_one_iff _).mp
  have hψ' : changeLevel (dvd_mul_left r q) ψ ≠ 1 := hψ ∘ (changeLevel_eq_one_iff _).mp
  have hsq' : (changeLevel (dvd_mul_right q r) χ)^2=1 := by rw [← map_pow, hsq, map_one]
  exact page_same_level _ _ hχ' hψ' hsq'
    (primitive_changeLevel_ne_of_ne χ ψ hχp hψp hqr)
    (regularizedL_changeLevel_zero _ χ hχ haz) (regularizedL_changeLevel_zero _ ψ hψ hbz)
    hai hbi (by linarith) (by linarith)

/-- A possible Page exception among primitive nonprincipal characters of conductor at most `Q`. -/
def PageExceptional (Q : ℕ) (χ : PrimitiveUpTo Q) : Prop :=
  letI : NeZero χ.1.val := ⟨χ.2.property.1⟩
  χ.2.val ≠ 1 ∧ ∃ β : ℝ, 1-Lscale (Q^2) 0/100 ≤ β ∧ regularizedL χ.2.val β = 0

/-- Landau--Page uniqueness with an explicit (non-optimal) absolute constant. -/
theorem page_exception_unique {Q : ℕ} {χ ψ : PrimitiveUpTo Q}
    (hχE : PageExceptional Q χ) (hψE : PageExceptional Q ψ) : χ = ψ := by
  rcases χ with ⟨q, χ, hq, hχ⟩
  rcases ψ with ⟨r, ψ, hr, hψ⟩
  letI : NeZero q.val := ⟨hq⟩
  letI : NeZero r.val := ⟨hr⟩
  obtain ⟨hχ1, a, ha, haz⟩ := hχE
  obtain ⟨hψ1, b, hb, hbz⟩ := hψE
  have hqQ : q.val ≤ Q := by omega
  have hrQ : r.val ≤ Q := by omega
  by_cases hqr : q = r
  · subst r
    have hq2 : q.val ≤ Q^2 := by have hh := NeZero.pos q.val; nlinarith
    have hsc := Lscale_antitone_level (NeZero.pos q.val) hq2 0
    have hsq : χ^2=1 := (near_one_zero_is_real χ hχ1 haz (by simpa using (show 1-Lscale q.val 0/100 ≤ a by linarith))).1
    have heq : χ=ψ := by
      by_contra hne
      exact page_same_level χ ψ hχ1 hψ1 hsq hne haz hbz rfl rfl (by simpa using (show 1-Lscale q.val 0/100 ≤ a by linarith))
        (by simpa using (show 1-Lscale q.val 0/100 ≤ b by linarith))
    subst ψ
    rfl
  · exact False.elim (page_distinct_levels χ ψ hχ hψ (fun h => hqr (Fin.ext h)) hqQ hrQ hχ1 hψ1 haz hbz
      rfl rfl ha hb)

end
end MaynardDevelopment
end

/- RealConductors -/
section

open scoped BigOperators Topology
open Complex Set Filter DirichletCharacter
namespace MaynardDevelopment
noncomputable section

lemma unit_kernel_eq_one_add_multiple {q d : ℕ} [NeZero q] (hd : d∣q) (u : (ZMod q)ˣ)
    (hu : ZMod.unitsMap hd u=1) : ∃ k : ℤ, (u : ZMod q)=1+(d : ZMod q)*k := by
  have hcast : ZMod.castHom hd (ZMod d) (u : ZMod q)=1 := by
    simpa [ZMod.unitsMap_def] using congrArg Units.val hu
  have hv : ((u.val.val : ℕ) : ZMod d)=1 := by
    rw [← ZMod.natCast_zmod_val (u : ZMod q),map_natCast] at hcast
    exact hcast
  have hdvd : (d : ℤ)∣(u.val.val : ℤ)-1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa using sub_eq_zero.mpr hv
  obtain ⟨k,hk⟩ := hdvd
  refine ⟨k,?_⟩
  have heq := congrArg (fun z : ℤ => (z : ZMod q)) hk
  push_cast at heq
  rw [ZMod.natCast_zmod_val] at heq
  linear_combination heq

lemma real_character_eq_one_of_square_unit {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ^2=1) (u : (ZMod q)ˣ) {v : ZMod q} (hv : v^2=(u : ZMod q)) : χ u=1 := by
  have hvu : IsUnit v := (isUnit_pow_iff (by norm_num : (2 : ℕ)≠0)).mp (hv.symm ▸ u.isUnit)
  have hh := congrArg (fun ψ : DirichletCharacter ℂ q => ψ v) hχ
  dsimp only at hh
  rw [MulChar.pow_apply' χ (by norm_num : (2 : ℕ)≠0),MulChar.one_apply hvu] at hh
  rw [← hv,map_pow]
  exact hh

lemma primitive_real_not_odd_prime_sq_dvd {q p : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hreal : χ^2=1) (hp : p.Prime) (hp2 : p≠2) : ¬ p^2∣q := by
  rintro ⟨r,rfl⟩
  have hr : 0<r := by have hh := NeZero.pos (p^2*r); nlinarith
  have hd : p*r∣p^2*r := ⟨p,by ring⟩
  have hlt : p*r<p^2*r := by have hh := hp.one_lt; have hpr := Nat.mul_pos hp.pos hr; nlinarith
  obtain ⟨u,hu,hχu⟩ := primitive_exists_kernel_unit χ hprim hd hlt
  obtain ⟨k,hk⟩ := unit_kernel_eq_one_add_multiple hd u hu
  obtain ⟨j,hj⟩ := (hp.odd_of_ne_two hp2).exists_bit1
  let v : ZMod (p^2*r) := 1+(j+1)*(p*r)*k
  have hn : (p : ZMod (p^2*r))^2*r=0 := by
    have hh : ((p^2*r : ℕ) : ZMod (p^2*r))=0 := ZMod.natCast_self _
    simpa only [Nat.cast_mul,Nat.cast_pow] using hh
  have hj' : (2 : ZMod (p^2*r))*(j+1)=p+1 := by
    have hh : 2*(j+1)=p+1 := by omega
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using congrArg (fun n : ℕ => (n : ZMod (p^2*r))) hh
  have hv : v^2=(u : ZMod (p^2*r)) := by
    rw [hk]
    dsimp [v]
    push_cast
    linear_combination (((j : ZMod (p^2*r))+1)^2*r*(k : ZMod (p^2*r))^2+(k : ZMod (p^2*r)))*hn +
      ((p : ZMod (p^2*r))*r*k)*hj'
  exact hχu (real_character_eq_one_of_square_unit χ hreal u hv)

lemma primitive_real_not_sixteen_dvd {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hreal : χ^2=1) : ¬ 16∣q := by
  rintro ⟨r,rfl⟩
  have hr : 0<r := by have hh := NeZero.pos (16*r); omega
  have hd : 8*r∣16*r := ⟨2,by ring⟩
  have hlt : 8*r<16*r := by omega
  obtain ⟨u,hu,hχu⟩ := primitive_exists_kernel_unit χ hprim hd hlt
  obtain ⟨k,hk⟩ := unit_kernel_eq_one_add_multiple hd u hu
  let v : ZMod (16*r) := 1+4*r*k
  have hn : (16 : ZMod (16*r))*r=0 := by
    have hh : ((16*r : ℕ) : ZMod (16*r))=0 := ZMod.natCast_self _
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh
  have hv : v^2=(u : ZMod (16*r)) := by
    rw [hk]
    dsimp [v]
    push_cast
    linear_combination ((r : ZMod (16*r))*(k : ZMod (16*r))^2)*hn
  exact hχu (real_character_eq_one_of_square_unit χ hreal u hv)

lemma primitive_real_factorization_le_three {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hreal : χ^2=1) (p : ℕ) : q.factorization p≤3 := by
  by_cases hp : p.Prime
  · by_contra hh
    have hd : p^4∣q := (hp.pow_dvd_iff_le_factorization (NeZero.ne q)).mpr (by omega)
    by_cases hp2 : p=2
    · subst p
      exact primitive_real_not_sixteen_dvd χ hprim hreal (by simpa using hd)
    · exact primitive_real_not_odd_prime_sq_dvd χ hprim hreal hp hp2
        ((pow_dvd_pow p (by norm_num : (2 : ℕ)≤4)).trans hd)
  · rw [Nat.factorization_eq_zero_of_not_prime q hp]
    omega

lemma primitive_real_bounded_prime_support {q B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hreal : χ^2=1)
    (hB : ∀ p ∈ q.primeFactors, p≤B) : q≤(B.factorial)^3 := by
  apply Nat.le_of_dvd (pow_pos (Nat.factorial_pos _) _)
  apply (Nat.factorization_le_iff_dvd (NeZero.ne q) (pow_ne_zero _ (Nat.factorial_pos B).ne')).mp
  intro p
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases hp : p.Prime
  · by_cases hdiv : p∣q
    · have hpB := hB p (Nat.mem_primeFactors.mpr ⟨hp,hdiv,NeZero.ne q⟩)
      have hpf : p∣B.factorial := Nat.dvd_factorial hp.pos hpB
      have hle := hp.factorization_pos_of_dvd (Nat.factorial_pos B).ne' hpf
      have hb := primitive_real_factorization_le_three χ hprim hreal p
      omega
    · rw [Nat.factorization_eq_zero_of_not_dvd hdiv]
      omega
  · rw [Nat.factorization_eq_zero_of_not_prime q hp]
    omega

end
end MaynardDevelopment
end

/- ZetaZeroFree -/
section

open scoped BigOperators Topology
open Complex ComplexConjugate Metric Set Filter
namespace MaynardDevelopment
noncomputable section

lemma regularized_zeta_ne_zero_disk {s : ℂ} (hs : ‖s-1‖ ≤ 1/4) :
    regularizedL (1 : DirichletCharacter ℂ 1) s ≠ 0 := by
  have hre := (abs_le.mp (Complex.abs_re_le_norm (s-1))).1
  simp only [Complex.sub_re, Complex.one_re] at hre
  have hsre : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h; simp [h] at hsre
  have hM := boundedMellin_norm_le natFraction_measurable (by norm_num : (0 : ℝ) ≤ 1)
    (fun t ht => natFraction_norm_le ht) hsre
  have hMn : ‖boundedMellin natFraction s‖ ≤ 2 := by
    refine hM.trans ?_
    apply (div_le_iff₀ hsre).mpr
    linarith
  have hprod : ‖(s-1) * boundedMellin natFraction s‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (s-1), norm_nonneg (boundedMellin natFraction s)]
  have hn : 1-(s-1)*boundedMellin natFraction s ≠ 0 := by
    intro h
    have heq : (s-1)*boundedMellin natFraction s = 1 := by linear_combination -h
    simpa [heq] using hprod
  simp only [regularizedL, if_true, regularized_zeta_eq_boundedMellin hsre]
  convert mul_ne_zero hs0 hn using 1 <;> ring

lemma scaled_pole_far_le {δ t : ℝ} (hδ : 0 < δ) (hδb : δ ≤ 1/1048576)
    (ht : 1/8 ≤ |t|) :
    δ * zeroContribution (((1+δ : ℝ) : ℂ) + I*t) 1 ≤ 1/512 := by
  rw [zeroContribution_formula]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero, Complex.one_re, Complex.add_im, Complex.mul_im,
    Complex.I_im, one_mul, zero_add, Complex.one_im, add_sub_cancel_left]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < δ^2+t^2)).mpr
  have ht2 : (1/8 : ℝ)^2 ≤ t^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/8) ht 2
  have hδ2 := pow_le_pow_left₀ hδ.le hδb 2
  nlinarith

/-- Explicit de la Vallée-Poussin zero-free region for regularized zeta. -/
theorem regularized_zeta_zero_free {a : ℂ} (ha : 1-Lscale 1 a.im/100 ≤ a.re) :
    regularizedL (1 : DirichletCharacter ℂ 1) a ≠ 0 := by
  intro hz
  let χ : DirichletCharacter ℂ 1 := 1
  let δ := Lscale 1 a.im
  have hδ : 0 < δ := Lscale_pos 1 a.im
  have hδb : δ ≤ 1/1048576 := Lscale_le 1 a.im
  have ha1 := root_re_lt_one hz
  by_cases ht : |a.im| < 1/8
  · apply regularized_zeta_ne_zero_disk (s := a) _ hz
    have hh := Complex.norm_le_abs_re_add_abs_im (a-1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at hh
    rw [abs_of_nonpos (by linarith : a.re-1 ≤ 0)] at hh
    change 1-δ/100 ≤ a.re at ha
    linarith
  have ht' : 1/8 ≤ |a.im| := le_of_not_gt ht
  let c : ℂ := ((1+δ : ℝ) : ℂ) + I*a.im
  let c₂ : ℂ := ((1+δ : ℝ) : ℂ) + I*((2*a.im : ℝ) : ℂ)
  have hc : c.re = 1+δ := by simp [c]
  have hc₂ : c₂.re = 1+δ := by simp [c₂]
  have hH : Lheight 1 c.im ≤ 2*Lheight 1 a.im := by
    simp only [c, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add]
    linarith [Lheight_ge_one 1 a.im]
  have hH₂ : Lheight 1 c₂.im ≤ 2*Lheight 1 a.im := by simpa [c₂] using Lheight_double_le 1 a.im
  have h₁ := scaled_negLDeriv_one_zero_le (q := 1) (t := a.im)
  have h₂ := scaled_negLDeriv_single_le χ hc hH (close_root_in_disk hδ hδb ha ha1) hz
  have h₃ := scaled_negLDeriv_le (χ^2) hc₂ hH₂
  have hp := mul_nonneg hδ.le (negLDeriv_trig_nonneg χ (by linarith : 1 < 1+δ) a.im)
  have hr := close_root_contribution hδ ha ha1
  have hpole := scaled_pole_far_le hδ hδb ht'
  have hpole₂ := scaled_pole_far_le hδ hδb (show 1/8 ≤ |2*a.im| by rw [abs_mul]; norm_num; linarith)
  change 100/101 ≤ δ * zeroContribution c a at hr
  change δ * zeroContribution c 1 ≤ 1/512 at hpole
  change δ * zeroContribution c₂ 1 ≤ 1/512 at hpole₂
  change 0 ≤ δ * (3 * negLDeriv χ ((1+δ : ℝ) : ℂ) + 4 * negLDeriv χ c + negLDeriv (χ^2) c₂) at hp
  change δ * negLDeriv χ ((1+δ : ℝ) : ℂ) ≤ 1+1/512 at h₁
  change δ * (negLDeriv χ c + zeroContribution c a) ≤ (if χ=1 then δ*zeroContribution c 1 else 0)+1/512 at h₂
  change δ * negLDeriv (χ^2) c₂ ≤ (if χ^2=1 then δ*zeroContribution c₂ 1 else 0)+1/512 at h₃
  rw [if_pos rfl] at h₂
  rw [if_pos (show χ^2=1 by simp [χ])] at h₃
  nlinarith

lemma trivial_euler_product_ne_zero {q : ℕ} {s : ℂ} (hs : 0 < s.re) :
    ∏ p ∈ q.primeFactors, (1-(p : ℂ)^(-s)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hnorm : ‖(p : ℂ)^(-s)‖ < 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by linarith)
  intro h
  have heq : (p : ℂ)^(-s) = 1 := by linear_combination -h
  simpa [heq] using hnorm

lemma principal_zero_free {q : ℕ} [NeZero q] {a : ℂ}
    (ha : 1-Lscale q a.im/100 ≤ a.re) : regularizedL (1 : DirichletCharacter ℂ q) a ≠ 0 := by
  have hsc := Lscale_antitone_level (by norm_num : 0 < 1) (NeZero.pos q) a.im
  have ha' : 1-Lscale 1 a.im/100 ≤ a.re := by linarith
  have hb := Lscale_le q a.im
  have ha0 : 0 < a.re := by linarith
  simp only [regularizedL, if_true]
  rw [regularized_trivial_eq_zeta_mul q]
  exact mul_ne_zero (by simpa [regularizedL] using regularized_zeta_zero_free ha') (trivial_euler_product_ne_zero ha0)

end
end MaynardDevelopment
end

/- InteriorLogBounds -/
section

open scoped Topology
open Complex Metric Set Filter
namespace MaynardDevelopment
noncomputable section

lemma norm_le_two_mul_of_re_le {f : ℂ → ℂ} {c z : ℂ} {R A : ℝ} (hR : 0 < R) (hA : 0 < A)
    (hf : DifferentiableOn ℂ f (ball c R)) (hfc : f c = 0)
    (hb : ∀ w ∈ ball c R, (f w).re ≤ A) (hz : ‖z-c‖ ≤ R/2) : ‖f z‖ ≤ 2*A := by
  let g : ℂ → ℂ := fun w => f w / ((2*A : ℝ) - f w)
  have hden (w : ℂ) (hw : w ∈ ball c R) : ((2*A : ℝ) : ℂ) - f w ≠ 0 := by
    intro hh
    have hre := congrArg Complex.re hh
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith [hb w hw]
  have hgd : DifferentiableOn ℂ g (ball c R) :=
    hf.div ((differentiable_const ((2*A : ℝ) : ℂ)).differentiableOn.sub hf) hden
  have hgc : g c = 0 := by simp [g, hfc]
  have hmaps : MapsTo g (ball c R) (closedBall (g c) 1) := by
    intro w hw
    rw [hgc, mem_closedBall_zero_iff]
    exact norm_mobius_le_one hA (hb w hw)
  have hzb : z ∈ ball c R := by rw [mem_ball_iff_norm]; linarith
  have hh := Complex.dist_le_div_mul_dist_of_mapsTo_ball hgd hmaps hzb
  rw [hgc, dist_zero_right, dist_eq_norm] at hh
  have hg : ‖g z‖ ≤ 1/2 := hh.trans (by
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hR).mpr
    linarith)
  dsimp only [g] at hg
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (hden z hzb))] at hg
  have hnorm := norm_sub_le (((2*A : ℝ) : ℂ)) (f z)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2*A)] at hnorm
  linarith

lemma norm_deriv_le_interior_of_re_le {f : ℂ → ℂ} {c z : ℂ} {R A : ℝ} (hR : 0 < R) (hA : 0 < A)
    (hf : DifferentiableOn ℂ f (ball c R)) (hfc : f c = 0)
    (hb : ∀ w ∈ ball c R, (f w).re ≤ A) (hz : ‖z-c‖ ≤ R/2) :
    ‖deriv f z‖ ≤ 16*A/R := by
  have hnorm := norm_le_two_mul_of_re_le hR hA hf hfc hb hz
  have hsub : ball z (R/2) ⊆ ball c R := by
    intro w hw
    rw [mem_ball_iff_norm] at hw ⊢
    have hh : ‖w-c‖ ≤ ‖w-z‖+‖z-c‖ := by simpa using norm_add_le (w-z) (z-c)
    linarith
  have hzb : z ∈ ball c R := by rw [mem_ball_iff_norm]; linarith
  have hh := norm_deriv_le_of_re_le (by linarith : 0 < R/2) (hf.mono hsub)
    (M := 2*A) (fun w hw => (hb w (hsub hw)).trans (by linarith)) (by linarith [hb z hzb])
  have hre := (abs_le.mp (Complex.abs_re_le_norm (f z))).1
  apply hh.trans
  apply (div_le_div_iff₀ (by linarith : 0 < R/2) hR).mpr
  nlinarith

lemma norm_logDeriv_le_interior {f : ℂ → ℂ} {c z : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hn : ∀ w ∈ ball c R, f w ≠ 0)
    (hb : ∀ w ∈ ball c R, ‖f w‖ ≤ M) (hz : ‖z-c‖ ≤ R/2) :
    ‖logDeriv f z‖ ≤ 16*(1+Real.log M-Real.log ‖f c‖)/R := by
  obtain ⟨g, hgd, hgc, hre, hderiv⟩ := exists_log_norm_primitive hR hf hn
  have hfc : 0 < ‖f c‖ := norm_pos_iff.mpr (hn c (mem_ball_self hR))
  have hMc : Real.log ‖f c‖ ≤ Real.log M := Real.log_le_log hfc (hb c (mem_ball_self hR))
  have hh := norm_deriv_le_interior_of_re_le hR (by linarith : 0 < 1+Real.log M-Real.log ‖f c‖)
    hgd hgc (fun w hw => ?_) hz
  · have hzb : z ∈ ball c R := by rw [mem_ball_iff_norm]; linarith
    rwa [hderiv z hzb, ← logDeriv_apply] at hh
  · rw [hre w hw]
    have hlog := Real.log_le_log (norm_pos_iff.mpr (hn w hw)) (hb w hw)
    linarith

end
end MaynardDevelopment
end

/- LStripBounds -/
section

open scoped BigOperators Topology
open Complex ComplexConjugate Metric Set Filter
namespace MaynardDevelopment
noncomputable section

lemma Lheight_mono_abs {q : ℕ} {t u : ℝ} (h : |t| ≤ |u|) : Lheight q t ≤ Lheight q u := by
  have hh := Real.log_le_log (by positivity : 0 < |t|+3) (by linarith : |t|+3 ≤ |u|+3)
  unfold Lheight
  linarith

lemma Lscale_antitone_abs {q : ℕ} {t u : ℝ} (h : |t| ≤ |u|) : Lscale q u ≤ Lscale q t := by
  unfold Lscale
  apply one_div_le_one_div_of_le
  · have hh := Lheight_ge_one q t
    positivity
  · linarith [Lheight_mono_abs (q := q) h]

def NoPageZero (Q : ℕ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ β : ℝ, 1-Lscale (Q^2) 0/100 ≤ β → regularizedL χ β ≠ 0

lemma noPageZero_of_not_exceptional {Q : ℕ} (χ : PrimitiveUpTo Q)
    (hχ : ¬ PageExceptional Q χ) :
    letI : NeZero χ.1.val := ⟨χ.2.property.1⟩
    NoPageZero Q χ.2.val := by
  letI : NeZero χ.1.val := ⟨χ.2.property.1⟩
  intro β hβ hz
  have hqQ : χ.1.val ≤ Q := by have hh := χ.1.isLt; omega
  have hq2 : χ.1.val ≤ Q^2 := by have hh := NeZero.pos χ.1.val; nlinarith
  have hsc := Lscale_antitone_level (NeZero.pos χ.1.val) hq2 0
  have hnon : χ.2.val ≠ 1 := by
    intro h
    simp only [h] at hz
    exact principal_zero_free (by simpa using (show 1-Lscale χ.1.val 0/100 ≤ β by linarith)) hz
  exact hχ ⟨hnon, β, hβ, hz⟩

lemma noPageZero_principal {q Q : ℕ} [NeZero q] (hqQ : q ≤ Q) :
    NoPageZero Q (1 : DirichletCharacter ℂ q) := by
  intro β hβ
  have hq2 : q ≤ Q^2 := by have hh := NeZero.pos q; nlinarith
  have hsc := Lscale_antitone_level (NeZero.pos q) hq2 0
  apply principal_zero_free
  simpa using (show 1-Lscale q 0/100 ≤ β by linarith)

lemma noPageZero_strip {q Q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hqQ : q ≤ Q) (hNP : NoPageZero Q χ) {T : ℝ} (hT : 0 ≤ T) {a : ℂ}
    (ha : 1-Lscale (Q^2) T/100 ≤ a.re) (hi : |a.im| ≤ T) : regularizedL χ a ≠ 0 := by
  have hq2 : q ≤ Q^2 := by have hh := NeZero.pos q; nlinarith
  have hsc₁ := Lscale_antitone_level (NeZero.pos q) hq2 a.im
  have hsc₂ := Lscale_antitone_abs (q := Q^2) (t := a.im) (u := T) (by simpa [abs_of_nonneg hT] using hi)
  have ha' : 1-Lscale q a.im/100 ≤ a.re := by linarith
  by_cases hχ : χ=1
  · subst χ
    exact principal_zero_free ha'
  intro hz
  have hai := (near_one_zero_is_real χ hχ hz ha').2
  have hsc₀ := Lscale_antitone_abs (q := Q^2) (t := 0) (u := T) (by simp)
  have ha₀ : 1-Lscale (Q^2) 0/100 ≤ a.re := by linarith
  have heq : a = (a.re : ℂ) := by apply Complex.ext <;> simp [hai]
  apply hNP a.re ha₀
  rwa [← heq]

lemma regularizedL_logDeriv_local_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {η : ℝ} (hη : 0 < η) (hηb : η ≤ 1/100) {z : ℂ}
    (hz : |z.re-1| ≤ η)
    (hn : ∀ w ∈ ball (((1+η : ℝ) : ℂ)+I*z.im) (4*η), regularizedL χ w ≠ 0) :
    ‖logDeriv (regularizedL χ) z‖ ≤ 32*(Lheight q z.im+Real.log (1/η))/η := by
  let c : ℂ := ((1+η : ℝ) : ℂ)+I*z.im
  let T : ℝ := |z.im|+3
  let M : ℝ := 4*(q : ℝ)*(T+1)^2
  have hc : c.re=1+η := by simp [c]
  have hcn : ‖c‖ ≤ T := by
    have hh := Complex.norm_le_abs_re_add_abs_im c
    simp only [c, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      zero_mul, Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, Complex.I_im, one_mul, zero_add, abs_of_pos (by linarith : 0 < 1+η)] at hh
    dsimp [T]
    linarith
  have hlow : η^2/T ≤ ‖regularizedL χ c‖ := by
    have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc; linarith
    calc
      _ ≤ η^2/‖c‖ := div_le_div_of_nonneg_left (sq_nonneg _) (norm_pos_iff.mpr hc0) hcn
      _ ≤ _ := by simpa [hc] using regularizedL_norm_lower χ (by linarith : 1<c.re) (by linarith : c.re≤2)
  have hb : ∀ w ∈ ball c (4*η), ‖regularizedL χ w‖ ≤ M := by
    intro w hw
    rw [mem_ball_iff_norm] at hw
    have hre := (abs_le.mp (Complex.abs_re_le_norm (w-c))).1
    simp only [Complex.sub_re, hc] at hre
    have hwre : 1/2 ≤ w.re := by linarith
    have hwn : ‖w‖ ≤ T := by
      have hh : ‖w‖ ≤ ‖w-c‖+‖c‖ := by simpa using norm_add_le (w-c) c
      have hcc := Complex.norm_le_abs_re_add_abs_im c
      simp only [c, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        zero_mul, Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.add_im,
        Complex.mul_im, Complex.I_im, one_mul, zero_add, abs_of_pos (by linarith : 0 < 1+η)] at hcc
      dsimp [T]
      linarith
    exact (regularizedL_norm_upper χ hwre).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : 0 ≤ ‖w‖+1) (by linarith : ‖w‖+1 ≤ T+1) 2) (by positivity))
  have hzc : ‖z-c‖ ≤ 4*η/2 := by
    have heq : z-c = ((z.re-1-η : ℝ) : ℂ) := by apply Complex.ext <;> simp [c] <;> ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    have hh := abs_le.mp hz
    rw [abs_le]
    constructor <;> linarith
  have hh := norm_logDeriv_le_interior (by positivity : 0 < 4*η)
    (regularizedL_differentiable χ).differentiableOn hn hb hzc
  have hErr := growth_log_error_bound (by exact_mod_cast NeZero.pos q : (1 : ℝ) ≤ q)
    (show 3 ≤ T by dsimp [T]; linarith [abs_nonneg z.im]) hη (by linarith : η ≤ 1) hlow
  change 8*(1+Real.log M-Real.log ‖regularizedL χ c‖) ≤ 64*(Lheight q z.im+Real.log (1/η)) at hErr
  refine hh.trans ?_
  apply (div_le_div_iff₀ (by positivity : 0 < 4*η) hη).mpr
  nlinarith

def stripWidth (Q : ℕ) (T : ℝ) : ℝ := Lscale (Q^2) (T+1)/1000

lemma stripWidth_pos (Q : ℕ) (T : ℝ) : 0 < stripWidth Q T := div_pos (Lscale_pos _ _) (by norm_num)

lemma stripWidth_le (Q : ℕ) (T : ℝ) : stripWidth Q T ≤ 1/100 := by
  have hh := Lscale_le (Q^2) (T+1)
  unfold stripWidth
  linarith

lemma stripWidth_log_bound (Q : ℕ) (T : ℝ) :
    Real.log (1/stripWidth Q T) ≤ 31*Lheight (Q^2) (T+1) := by
  have hH := Lheight_ge_one (Q^2) (T+1)
  have hH0 : 0 < Lheight (Q^2) (T+1) := by linarith
  have hlog := Real.log_le_sub_one_of_pos hH0
  have hlc : Real.log (1048576000 : ℝ) ≤ 30 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1048576000) (by norm_num : (1048576000 : ℝ) ≤ 2^30)
    rw [Real.log_pow] at hh
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have heq : 1/stripWidth Q T = 1048576000 * Lheight (Q^2) (T+1) := by
    unfold stripWidth Lscale
    field_simp
    ring
  rw [heq, Real.log_mul (by norm_num) hH0.ne']
  nlinarith

lemma stripWidth_mul_height (Q : ℕ) (T : ℝ) :
    stripWidth Q T * Lheight (Q^2) (T+1) = 1/1048576000 := by
  have hH : Lheight (Q^2) (T+1) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (Lheight_ge_one _ _))
  unfold stripWidth Lscale
  field_simp
  ring

/-- Uniform logarithmic-derivative control in an exception-free rectangle. -/
theorem regularizedL_logDeriv_strip_bound {q Q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hqQ : q ≤ Q) (hNP : NoPageZero Q χ) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : |z.re-1| ≤ stripWidth Q T) (hi : |z.im| ≤ T) :
    ‖logDeriv (regularizedL χ) z‖ ≤ 2000000000000 * (Lheight (Q^2) (T+1))^2 := by
  let η := stripWidth Q T
  have hη : 0 < η := stripWidth_pos _ _
  have hηb : η ≤ 1/100 := stripWidth_le _ _
  have hn : ∀ w ∈ ball (((1+η : ℝ) : ℂ)+I*z.im) (4*η), regularizedL χ w ≠ 0 := by
    intro w hw
    rw [mem_ball_iff_norm] at hw
    have hre := (abs_le.mp (Complex.abs_re_le_norm (w-(((1+η : ℝ) : ℂ)+I*z.im)))).1
    have him := Complex.abs_im_le_norm (w-(((1+η : ℝ) : ℂ)+I*z.im))
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      zero_mul, Complex.ofReal_im, mul_zero, sub_zero, add_zero] at hre
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add] at him
    apply noPageZero_strip χ hqQ hNP (show 0 ≤ T+1 by linarith)
    · have heq : Lscale (Q^2) (T+1)/100 = 10*η := by dsimp [η, stripWidth]; ring
      rw [heq]
      linarith
    · have hh : |w.im| ≤ |w.im-z.im|+|z.im| := by simpa using abs_add_le (w.im-z.im) z.im
      linarith
  have hh := regularizedL_logDeriv_local_bound χ hη hηb hz hn
  have hq2 : q ≤ Q^2 := by have hh := NeZero.pos q; nlinarith
  have hH : Lheight q z.im ≤ Lheight (Q^2) (T+1) := by
    refine (Lheight_mono_level (NeZero.pos q) hq2 z.im).trans (Lheight_mono_abs ?_)
    rw [abs_of_nonneg (by linarith : 0 ≤ T+1)]
    linarith
  have hlog := stripWidth_log_bound Q T
  have hηH := stripWidth_mul_height Q T
  change Real.log (1/η) ≤ _ at hlog
  change η * Lheight (Q^2) (T+1) = _ at hηH
  have hHpos := Lheight_ge_one (Q^2) (T+1)
  refine hh.trans ?_
  apply (div_le_iff₀ hη).mpr
  nlinarith [sq_nonneg (Lheight (Q^2) (T+1))]

end
end MaynardDevelopment
end

/- ExceptionalPrime -/
section

open scoped BigOperators Topology
open Complex Metric Set Filter DirichletCharacter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

def primitiveRegularizedL {Q : ℕ} (χ : PrimitiveUpTo Q) : ℂ → ℂ :=
  letI : NeZero χ.1.val := ⟨χ.2.property.1⟩
  regularizedL χ.2.val

lemma finite_character_zero_free_near_one (C : ℕ) :
    ∃ ε : ℝ, 0<ε ∧ ∀ β : ℝ, |β-1|<ε → ∀ χ : PrimitiveUpTo C, primitiveRegularizedL χ β ≠ 0 := by
  have hall : ∀ᶠ β : ℝ in 𝓝 1, ∀ χ : PrimitiveUpTo C, primitiveRegularizedL χ β ≠ 0 := by
    apply eventually_all.mpr
    intro χ
    letI : NeZero χ.1.val := ⟨χ.2.property.1⟩
    have hc : Continuous (fun β : ℝ => primitiveRegularizedL χ β) :=
      (regularizedL_differentiable χ.2.val).continuous.comp Complex.continuous_ofReal
    exact hc.continuousAt.eventually_ne (regularizedL_ne_zero χ.2.val (by norm_num : 1≤(1 : ℂ).re))
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp hall
  exact ⟨ε,hε,fun β hβ => he (by simpa [Real.dist_eq] using hβ)⟩

lemma page_width_tendsto_zero : Tendsto (fun Q : ℕ => Lscale (Q^2) 0/100) atTop (𝓝 0) := by
  have hlog : Tendsto (fun Q : ℕ => Real.log Q) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun Q : ℕ => Lheight (Q^2) 0) atTop atTop := by
    apply tendsto_atTop_mono (f := fun Q : ℕ => Real.log Q) _ hlog
    intro Q
    have hq := Real.log_natCast_nonneg Q
    have h3 := Real.log_nonneg (by norm_num : (1 : ℝ)≤3)
    simp only [Lheight,Nat.cast_pow,Real.log_pow,Nat.cast_ofNat,abs_zero,zero_add]
    linarith
  convert hh.const_div_atTop (1/104857600) using 1
  funext Q
  unfold Lscale
  ring

lemma page_exception_quadratic {Q : ℕ} (χ : PrimitiveUpTo Q) (hχ : PageExceptional Q χ) : χ.2.val^2=1 := by
  letI : NeZero χ.1.val := ⟨χ.2.property.1⟩
  obtain ⟨hχ1,β,hβ,hz⟩ := hχ
  have hqQ : χ.1.val≤Q := by have hh := χ.1.isLt; omega
  have hq2 : χ.1.val≤Q^2 := by have hh := NeZero.pos χ.1.val; nlinarith
  have hsc := Lscale_antitone_level (NeZero.pos χ.1.val) hq2 0
  exact (near_one_zero_is_real χ.2.val hχ1 hz (by simpa using (show 1-Lscale χ.1.val 0/100≤β by linarith))).1

lemma eventually_no_exception_bounded_support (B : ℕ) :
    ∀ᶠ Q : ℕ in atTop, ∀ χ : PrimitiveUpTo Q, PageExceptional Q χ →
      ¬ ∀ p ∈ χ.1.val.primeFactors, p≤B := by
  let C := B.factorial^3
  obtain ⟨ε,hε,hnear⟩ := finite_character_zero_free_near_one C
  have hw := page_width_tendsto_zero.eventually (eventually_lt_nhds hε)
  filter_upwards [hw] with Q hQ χ hχ hsupport
  letI : NeZero χ.1.val := ⟨χ.2.property.1⟩
  have hquad := page_exception_quadratic χ hχ
  have hqC : χ.1.val≤C := primitive_real_bounded_prime_support χ.2.val χ.2.property.2 hquad hsupport
  let ψ : PrimitiveUpTo C := ⟨⟨χ.1.val,by omega⟩,χ.2.val,χ.2.property⟩
  obtain ⟨hχ1,β,hβ,hz⟩ := hχ
  have hβ1 : β<1 := by simpa using root_re_lt_one hz
  have hb : |β-1|<ε := by rw [abs_of_neg (by linarith : β-1<0)]; linarith
  exact hnear β hb ψ hz

/-- The largest prime factor of the unique Page exception; `1` if there is no exception. -/
def exceptionPrime (Q : ℕ) : ℕ :=
  if h : ∃ χ : PrimitiveUpTo Q, PageExceptional Q χ then (Classical.choose h).1.val.primeFactors.sup id else 1

lemma exceptionPrime_eq_of_exception {Q : ℕ} (χ : PrimitiveUpTo Q) (hχ : PageExceptional Q χ) :
    exceptionPrime Q=χ.1.val.primeFactors.sup id := by
  have hex : ∃ χ : PrimitiveUpTo Q, PageExceptional Q χ := ⟨χ,hχ⟩
  rw [exceptionPrime,dif_pos hex]
  have heq := page_exception_unique (Classical.choose_spec hex) hχ
  rw [heq]

lemma exceptionPrime_prime_dvd {Q : ℕ} (χ : PrimitiveUpTo Q) (hχ : PageExceptional Q χ) :
    (exceptionPrime Q).Prime ∧ exceptionPrime Q∣χ.1.val := by
  letI : NeZero χ.1.val := ⟨χ.2.property.1⟩
  have hq1 : χ.1.val≠1 := by
    intro h
    exact hχ.1 (DirichletCharacter.level_one' χ.2.val h)
  obtain ⟨p,hp,hpq⟩ := Nat.exists_prime_and_dvd hq1
  have hn : χ.1.val.primeFactors.Nonempty := ⟨p,Nat.mem_primeFactors.mpr ⟨hp,hpq,NeZero.ne _⟩⟩
  rw [exceptionPrime_eq_of_exception χ hχ,← Finset.sup'_eq_sup hn id,← Finset.max'_eq_sup']
  exact ⟨Nat.prime_of_mem_primeFactors (Finset.max'_mem _ hn),
    Nat.dvd_of_mem_primeFactors (Finset.max'_mem _ hn)⟩

lemma exceptionPrime_eq_one_or_prime (Q : ℕ) : exceptionPrime Q=1 ∨ (exceptionPrime Q).Prime := by
  by_cases h : ∃ χ : PrimitiveUpTo Q, PageExceptional Q χ
  · exact .inr (exceptionPrime_prime_dvd (Classical.choose h) (Classical.choose_spec h)).1
  · exact .inl (by simp [exceptionPrime,h])

/-- A possible exceptional prime eventually avoids every fixed finite collection of primes. -/
theorem exceptionPrime_eventually_large (B : ℕ) :
    ∀ᶠ Q : ℕ in atTop, exceptionPrime Q=1 ∨ B<exceptionPrime Q := by
  filter_upwards [eventually_no_exception_bounded_support B] with Q hQ
  by_cases h : ∃ χ : PrimitiveUpTo Q, PageExceptional Q χ
  · right
    let χ := Classical.choose h
    have hχ : PageExceptional Q χ := Classical.choose_spec h
    rw [exceptionPrime_eq_of_exception χ hχ]
    by_contra hb
    apply hQ χ hχ
    intro p hp
    exact (Finset.le_sup (f := id) hp).trans (le_of_not_gt hb)
  · left
    simp [exceptionPrime,h]

def GoodModulus (Q n : ℕ) : Prop := exceptionPrime Q=1 ∨ ¬ exceptionPrime Q∣n

lemma goodModulus_no_exception {Q : ℕ} (χ : PrimitiveUpTo Q) {n : ℕ}
    (hn : GoodModulus Q n) (hqn : χ.1.val∣n) : ¬ PageExceptional Q χ := by
  intro hχ
  have hp := exceptionPrime_prime_dvd χ hχ
  rcases hn with h | h
  · exact hp.1.ne_one h
  · exact h (hp.2.trans hqn)

end
end MaynardDevelopment
end

/- PerronKernel -/
section

open scoped Topology
open Complex MeasureTheory Set Filter intervalIntegral
namespace MaynardDevelopment
noncomputable section

def triangleCut (t : ℝ) : ℂ := ((max (1-t) 0 : ℝ) : ℂ)
def perronKernel (s : ℂ) : ℂ := 1/(s*(s+1))

lemma triangleCut_continuous : Continuous triangleCut := by unfold triangleCut; fun_prop

lemma triangle_mellin_integrand (s : ℂ) {t : ℝ} (ht : 0<t) :
    (t : ℂ)^(s-1)*triangleCut t = (Ioc (0 : ℝ) 1).indicator (fun u : ℝ => (u : ℂ)^(s-1)-(u : ℂ)^s) t := by
  by_cases ht1 : t ≤ 1
  · rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht,ht1⟩)]
    simp only [triangleCut, max_eq_left (by linarith : (0 : ℝ) ≤ 1-t), Complex.ofReal_sub, Complex.ofReal_one]
    have hp : (t : ℂ)^(s-1)*(t : ℂ)=(t : ℂ)^s := by
      nth_rw 2 [← Complex.cpow_one (t : ℂ)]
      rw [← Complex.cpow_add _ _ (by exact_mod_cast ht.ne')]
      congr 1
      ring
    rw [mul_sub, mul_one, hp]
  · rw [indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => ht1 h.2)]
    simp [triangleCut, max_eq_right (by linarith : 1-t ≤ (0 : ℝ))]

lemma triangle_mellin_convergent {s : ℂ} (hs : 0<s.re) : MellinConvergent triangleCut s := by
  have h₁ := intervalIntegrable_cpow' (a := 0) (b := 1) (r := s-1) (by simp; linarith)
  have h₂ := intervalIntegrable_cpow' (a := 0) (b := 1) (r := s) (by linarith)
  have hh := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp (h₁.sub h₂)
  have hi := (hh.integrable_indicator measurableSet_Ioc).integrableOn (s := Ioi 0)
  exact hi.congr_fun (fun t ht => by simpa only [smul_eq_mul] using (triangle_mellin_integrand s ht).symm) measurableSet_Ioi

lemma mellin_triangle {s : ℂ} (hs : 0<s.re) : mellin triangleCut s = perronKernel s := by
  have h₁ := intervalIntegrable_cpow' (a := 0) (b := 1) (r := s-1) (by simp; linarith)
  have h₂ := intervalIntegrable_cpow' (a := 0) (b := 1) (r := s) (by linarith)
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hs1 : s+1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold mellin
  simp only [smul_eq_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => triangle_mellin_integrand s ht),
    setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr (fun _ h => h.1),
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), intervalIntegral.integral_sub h₁ h₂,
    integral_cpow (.inl (show -1 < (s-1).re by simp; linarith)),
    integral_cpow (.inl (show -1 < s.re by linarith))]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, sub_add_cancel, Complex.one_cpow,
    Complex.zero_cpow hs0, Complex.zero_cpow hs1, sub_zero, perronKernel]
  field_simp
  ring

lemma perronKernel_norm_le {σ d t : ℝ} (hd : 0<d) (hd1 : d≤1) (hσ : d≤σ) :
    ‖perronKernel ((σ : ℂ)+t*I)‖ ≤ (1/d^2)*(1+t^2)⁻¹ := by
  let s : ℂ := (σ : ℂ)+t*I
  have hs : 0<σ := lt_of_lt_of_le hd hσ
  have hn : ‖s‖^2 = σ^2+t^2 := by simp [s, Complex.sq_norm, Complex.normSq_apply]; ring
  have hn1 : ‖s+1‖^2 = (σ+1)^2+t^2 := by simp [s, Complex.sq_norm, Complex.normSq_apply]; ring
  have hnorm : ‖s‖ ≤ ‖s+1‖ := by nlinarith [norm_nonneg s, norm_nonneg (s+1)]
  have hden : d^2*(1+t^2) ≤ ‖s‖*‖s+1‖ := by
    have hdd : d^2≤1 := by nlinarith
    have hds : d^2≤σ^2 := pow_le_pow_left₀ hd.le hσ 2
    nlinarith [sq_nonneg t, mul_le_mul_of_nonneg_left hnorm (norm_nonneg s)]
  change ‖1/(s*(s+1))‖ ≤ _
  rw [norm_div, norm_one, norm_mul]
  calc
    _ ≤ 1/(d^2*(1+t^2)) := one_div_le_one_div_of_le (by positivity) hden
    _ = _ := by simp [one_div, mul_inv_rev, mul_comm]

lemma perronKernel_vertical_integrable {σ : ℝ} (hσ : 0<σ) : VerticalIntegrable perronKernel σ := by
  let d := min σ 1
  have hd : 0<d := lt_min hσ (by norm_num)
  have hd1 : d≤1 := min_le_right _ _
  have hds : d≤σ := min_le_left _ _
  have hbound := integrable_inv_one_add_sq.const_mul (1/d^2)
  apply hbound.mono'
  · apply Continuous.aestronglyMeasurable
    unfold perronKernel
    apply Continuous.div continuous_const
    · fun_prop
    · intro t
      apply mul_ne_zero
      · intro h
        have hh := congrArg Complex.re h
        simp at hh
        linarith
      · intro h
        have hh := congrArg Complex.re h
        simp at hh
        linarith
  · filter_upwards [] with t
    exact perronKernel_norm_le hd hd1 hds

/-- Inverse Mellin formula for the triangular Perron kernel. -/
theorem perronKernel_inverse {σ x : ℝ} (hσ : 0<σ) (hx : 0<x) :
    mellinInv σ perronKernel x = triangleCut x := by
  have hF : VerticalIntegrable (mellin triangleCut) σ := by
    apply (perronKernel_vertical_integrable hσ).congr
    filter_upwards [] with t
    symm
    exact mellin_triangle (by simpa using hσ)
  have hh := mellinInv_mellin_eq σ triangleCut hx (triangle_mellin_convergent (by simpa using hσ))
    hF (triangleCut_continuous.continuousAt)
  rw [← hh]
  unfold mellinInv
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [mellin_triangle (by simpa using hσ)]

end
end MaynardDevelopment
end

/- SmoothedPerron -/
section

open scoped Topology
open Complex MeasureTheory Set Filter
namespace MaynardDevelopment
noncomputable section

def perronIntegrand (f : ℕ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  (X : ℂ)^s * LSeries f s * perronKernel s

lemma positive_ratio_cpow (x y : ℝ) (hx : 0<x) (hy : 0<y) (s : ℂ) :
    ((x/y : ℝ) : ℂ)^(-s) = (y : ℂ)^s/(x : ℂ)^s := by
  have hn : (x : ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast hx.ne'))
  have hyr : (y : ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast hy.ne'))
  have hr : ((x/y : ℝ) : ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast (div_pos hx hy).ne'))
  have hh := Complex.mul_cpow_ofReal_nonneg (div_pos hx hy).le hy.le s
  rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hy.ne'] at hh
  rw [Complex.cpow_neg]
  apply (eq_div_iff hn).mpr
  rw [hh]
  field_simp

lemma perronTerm_norm_bound {σ : ℝ} (hσ : 0<σ) {X : ℝ} (hX : 0<X)
    (f : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    ‖(X : ℂ)^(σ+t*I) * LSeries.term f (σ+t*I) n * perronKernel (σ+t*I)‖ ≤
      ((X^σ)/(min σ 1)^2)*‖LSeries.term f σ n‖*(1+t^2)⁻¹ := by
  have hk := perronKernel_norm_le (lt_min hσ (by norm_num)) (min_le_right σ 1) (min_le_left σ 1) (t := t)
  have hn : ‖LSeries.term f (σ+t*I) n‖=‖LSeries.term f σ n‖ := by simp [LSeries.norm_term_eq]
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, hn]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ X^σ*‖LSeries.term f σ n‖*((1/(min σ 1)^2)*(1+t^2)⁻¹) :=
      mul_le_mul_of_nonneg_left hk (by positivity)
    _ = _ := by ring

lemma perronTerm_integrable {σ : ℝ} (hσ : 0<σ) {X : ℝ} (hX : 0<X)
    (f : ℕ → ℂ) (n : ℕ) :
    Integrable (fun t : ℝ => (X : ℂ)^(σ+t*I) * LSeries.term f (σ+t*I) n * perronKernel (σ+t*I)) := by
  apply (integrable_inv_one_add_sq.const_mul (((X^σ)/(min σ 1)^2)*‖LSeries.term f σ n‖)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold LSeries.term perronKernel
    by_cases hn : n = 0 <;> simp only [hn, if_true, if_false] <;> fun_prop
  · filter_upwards [] with t
    exact perronTerm_norm_bound hσ hX f n t

lemma perronTerm_integral_norm_summable {σ : ℝ} (hσ : 0<σ) {X : ℝ} (hX : 0<X)
    {f : ℕ → ℂ} (hf : LSeriesSummable f σ) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖(X : ℂ)^(σ+t*I) * LSeries.term f (σ+t*I) n * perronKernel (σ+t*I)‖) := by
  have hfn : Summable (fun n => ‖LSeries.term f σ n‖) := hf.norm
  apply ((hfn.mul_left ((X^σ)/(min σ 1)^2)).mul_right (∫ t : ℝ, (1+t^2)⁻¹)).of_nonneg_of_le
  · intro n
    exact integral_nonneg (fun t => norm_nonneg _)
  · intro n
    have hh := integral_mono (perronTerm_integrable hσ hX f n).norm
      (integrable_inv_one_add_sq.const_mul (((X^σ)/(min σ 1)^2)*‖LSeries.term f σ n‖))
      (perronTerm_norm_bound hσ hX f n)
    simpa only [integral_const_mul] using hh

lemma perronTerm_inverse {σ : ℝ} (hσ : 0<σ) {X : ℝ} (hX : 0<X)
    {f : ℕ → ℂ} (hf0 : f 0=0) (n : ℕ) :
    ((1/(2*Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, (X : ℂ)^(σ+t*I) * LSeries.term f (σ+t*I) n * perronKernel (σ+t*I)) =
      f n * triangleCut ((n : ℝ)/X) := by
  by_cases hn : n=0
  · subst n
    simp [LSeries.term_zero, hf0]
  have hn0 : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hh := perronKernel_inverse hσ (div_pos hn0 hX)
  unfold mellinInv at hh
  simp only [smul_eq_mul, Complex.real_smul] at hh
  have heq (t : ℝ) : (X : ℂ)^(σ+t*I) * LSeries.term f (σ+t*I) n * perronKernel (σ+t*I) =
      f n * ((((n : ℝ)/X : ℝ) : ℂ)^(-(σ+t*I)) * perronKernel (σ+t*I)) := by
    rw [LSeries.term_of_ne_zero hn, positive_ratio_cpow _ _ hn0 hX]
    push_cast
    ring
  simp_rw [heq]
  rw [integral_const_mul, ← mul_assoc, mul_comm _ (f n), mul_assoc, hh]

/-- Smoothed Perron inversion, assuming only absolute convergence on the chosen line. -/
theorem smoothed_perron {σ : ℝ} (hσ : 0<σ) {X : ℝ} (hX : 0<X)
    {f : ℕ → ℂ} (hf0 : f 0=0) (hf : LSeriesSummable f σ) :
    (∑' n : ℕ, f n * triangleCut ((n : ℝ)/X)) =
      ((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, perronIntegrand f X (σ+t*I) := by
  simp_rw [← perronTerm_inverse hσ hX hf0]
  rw [tsum_mul_left, integral_tsum_of_summable_integral_norm
    (perronTerm_integrable hσ hX f) (perronTerm_integral_norm_summable hσ hX hf)]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  simp only [perronIntegrand, LSeries, tsum_mul_right, tsum_mul_left]

end
end MaynardDevelopment
end

/- PerronBounds -/
section

open scoped Topology
open Complex MeasureTheory Set Filter
namespace MaynardDevelopment
noncomputable section

lemma perronKernel_norm_le_inv_sq {σ t : ℝ} (ht : t ≠ 0) :
    ‖perronKernel ((σ : ℂ)+t*I)‖ ≤ 1/t^2 := by
  have h₁ := Complex.abs_im_le_norm ((σ : ℂ)+t*I)
  have h₂ := Complex.abs_im_le_norm (((σ : ℂ)+t*I)+1)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, Complex.one_im] at h₁ h₂
  have hden : t^2 ≤ ‖((σ : ℂ)+t*I)‖*‖((σ : ℂ)+t*I)+1‖ := by
    have hh := mul_le_mul h₁ h₂ (abs_nonneg t) (norm_nonneg _)
    nlinarith [sq_abs t]
  rw [perronKernel, norm_div, norm_one, norm_mul]
  exact one_div_le_one_div_of_le (sq_pos_of_ne_zero ht) hden

lemma integral_inv_one_add_abs {T : ℝ} (hT : 0 ≤ T) :
    (∫ t : ℝ in -T..T, (1+|t|)⁻¹) = 2*Real.log (1+T) := by
  have hc : Continuous (fun t : ℝ => (1+|t|)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro t
    positivity
  have heq : (∫ t : ℝ in -T..0, (1+|t|)⁻¹)=(∫ t : ℝ in 0..T, (1+|t|)⁻¹) := by
    have hh := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := T) (fun t : ℝ => (1+|t|)⁻¹)
    simpa only [abs_neg, neg_zero] using hh.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), heq]
  have hint : (∫ t : ℝ in 0..T, (1+|t|)⁻¹)=Real.log (1+T) := by
    calc
      _ = ∫ t : ℝ in 0..T, (1+t)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hT] at ht
        simp only [abs_of_nonneg ht.1]
      _ = ∫ t : ℝ in 1..(1+T), t⁻¹ := by
        simpa using intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := T) (fun t : ℝ => t⁻¹) 1
      _ = _ := by
        rw [integral_inv]
        · simp
        · rw [uIcc_of_le (by linarith : (1 : ℝ) ≤ 1+T)]
          simp
  rw [hint]
  ring

lemma weighted_kernel_bound {σ t A : ℝ} (hσ : 1/2 ≤ σ) (hA : 0 ≤ A) {v : ℂ}
    (hv : ‖v‖ ≤ A*(1+|t|)) :
    ‖v * perronKernel ((σ : ℂ)+t*I)‖ ≤ 8*A/(1+|t|) := by
  have hk := perronKernel_norm_le (d := 1/2) (by norm_num) (by norm_num) hσ (t := t)
  norm_num at hk
  rw [norm_mul]
  calc
    _ ≤ (A*(1+|t|))*(4*(1+t^2)⁻¹) := mul_le_mul hv hk (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ (by positivity : 0 < 1+|t|)).mpr
      have hpos : 0 < 1+t^2 := by positivity
      have hh : (1+|t|)^2 ≤ 2*(1+t^2) := by nlinarith [sq_abs t, sq_nonneg (|t|-1)]
      have hhh := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*A by positivity)
      have heq : (A*(1+|t|)*(4/(1+t^2)))*(1+|t|) = 4*A*(1+|t|)^2/(1+t^2) := by ring
      rw [heq]
      exact (div_le_iff₀ hpos).mpr (by nlinarith)

lemma norm_weighted_vertical_integral_le {σ T X A : ℝ}
    (hσ : 1/2 ≤ σ) (hT : 0 ≤ T) (hX : 0<X) (hA : 0≤A) (F : ℂ → ℂ)
    (hF : ∀ t ∈ Icc (-T) T, ‖F (σ+t*I)‖ ≤ A*(1+|t|)) :
    ‖∫ t : ℝ in -T..T, (X : ℂ)^(σ+t*I)*F (σ+t*I)*perronKernel (σ+t*I)‖ ≤
      16*X^σ*A*Real.log (1+T) := by
  have hc : Continuous (fun t : ℝ => 8*X^σ*A/(1+|t|)) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro t
    positivity
  have hh := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T)
    (μ := volume) (f := fun t : ℝ => (X : ℂ)^(σ+t*I)*F (σ+t*I)*perronKernel (σ+t*I))
    (g := fun t : ℝ => 8*X^σ*A/(1+|t|)) ?_ (hc.intervalIntegrable _ _)
  · refine hh.trans_eq ?_
    simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul, integral_inv_one_add_abs hT]
    ring
  · filter_upwards [] with t ht
    rw [mul_assoc, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    have hb := weighted_kernel_bound hσ hA (hF t ⟨ht.1.le,ht.2⟩)
    calc
      _ ≤ X^σ*(8*A/(1+|t|)) := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hX.le _)
      _ = _ := by ring

/-- Cauchy-Goursat in a form useful for shifting a truncated vertical integral. -/
lemma norm_vertical_integral_le_horizontal {a b T : ℝ} (G : ℂ → ℂ)
    (hG : DifferentiableOn ℂ G (uIcc a b ×ℂ uIcc (-T) T)) :
    ‖∫ t : ℝ in -T..T, G (b+t*I)‖ ≤ ‖∫ t : ℝ in -T..T, G (a+t*I)‖ +
      ‖∫ x : ℝ in a..b, G (x+(-T)*I)‖ + ‖∫ x : ℝ in a..b, G (x+T*I)‖ := by
  have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
    ((a : ℂ)+(-T)*I) ((b : ℂ)+T*I) (by simpa using hG)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
    mul_one, zero_add, smul_eq_mul, Complex.neg_re, Complex.neg_im, neg_zero, Complex.ofReal_neg] at hh
  have heq : I*(∫ t : ℝ in -T..T, G (b+t*I)) =
      I*(∫ t : ℝ in -T..T, G (a+t*I)) - (∫ x : ℝ in a..b, G (x+(-T)*I)) +
      (∫ x : ℝ in a..b, G (x+T*I)) := by linear_combination hh
  calc
    _ = ‖I*(∫ t : ℝ in -T..T, G (b+t*I))‖ := by simp
    _ = _ := congrArg norm heq
    _ ≤ ‖I*(∫ t : ℝ in -T..T, G (a+t*I)) - (∫ x : ℝ in a..b, G (x+(-T)*I))‖ +
        ‖∫ x : ℝ in a..b, G (x+T*I)‖ := norm_add_le _ _
    _ ≤ _ := by
      have hb := norm_sub_le (I*(∫ t : ℝ in -T..T, G (a+t*I))) (∫ x : ℝ in a..b, G (x+(-T)*I))
      simp only [norm_mul, Complex.norm_I, one_mul] at hb
      linarith


end
end MaynardDevelopment
end

/- PerronTail -/
section

open scoped Topology
open Complex MeasureTheory Set Filter
namespace MaynardDevelopment
noncomputable section

def absoluteDirichletSum (f : ℕ → ℂ) (σ : ℝ) : ℝ := ∑' n : ℕ, ‖LSeries.term f σ n‖

lemma absoluteDirichletSum_nonneg (f : ℕ → ℂ) (σ : ℝ) : 0 ≤ absoluteDirichletSum f σ :=
  tsum_nonneg (fun _ => norm_nonneg _)

lemma LSeries_norm_le_vertical {f : ℕ → ℂ} {σ : ℝ} (hf : LSeriesSummable f σ) (t : ℝ) :
    ‖LSeries f (σ+t*I)‖ ≤ absoluteDirichletSum f σ := by
  have heq (n : ℕ) : ‖LSeries.term f (σ+t*I) n‖ = ‖LSeries.term f σ n‖ := by simp [LSeries.norm_term_eq]
  have hh := hf.norm
  have hsum : Summable (fun n : ℕ => ‖LSeries.term f (σ+t*I) n‖) := by simpa only [heq] using hh
  have hb := norm_tsum_le_tsum_norm hsum
  simpa only [heq] using hb

lemma LSeries_vertical_continuous {f : ℕ → ℂ} {σ : ℝ} (hf : LSeriesSummable f σ) :
    Continuous (fun t : ℝ => LSeries f (σ+t*I)) := by
  apply continuous_tsum (u := fun n : ℕ => ‖LSeries.term f σ n‖)
  · intro n
    by_cases hn : n=0
    · simp only [hn, LSeries.term_zero]
      exact continuous_const
    · simp only [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero (show (n : ℂ) ≠ 0 by exact_mod_cast hn)]
      exact continuous_const.div (by fun_prop) (fun t => Complex.exp_ne_zero _)
  · exact hf.norm
  · intro n t
    simp [LSeries.norm_term_eq]

lemma perronIntegrand_integrable {f : ℕ → ℂ} {σ X : ℝ} (hσ : 0<σ) (hX : 0<X)
    (hf : LSeriesSummable f σ) : Integrable (fun t : ℝ => perronIntegrand f X (σ+t*I)) := by
  have hbound := integrable_inv_one_add_sq.const_mul ((X^σ)*absoluteDirichletSum f σ/(min σ 1)^2)
  apply hbound.mono'
  · apply Continuous.aestronglyMeasurable
    have hL := LSeries_vertical_continuous hf
    unfold perronIntegrand perronKernel
    have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
    simp only [Complex.cpow_def_of_ne_zero hX0]
    apply Continuous.mul
    · exact (show Continuous (fun t : ℝ => Complex.exp (Complex.log (X : ℂ)*(σ+t*I))) by fun_prop).mul hL
    · apply Continuous.div continuous_const (by fun_prop)
      intro t
      apply mul_ne_zero <;> intro h <;> have hh := congrArg Complex.re h <;> simp at hh <;> linarith
  · filter_upwards [] with t
    rw [perronIntegrand, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    have hk := perronKernel_norm_le (lt_min hσ (by norm_num)) (min_le_right σ 1) (min_le_left σ 1) (t := t)
    calc
      _ ≤ X^σ*absoluteDirichletSum f σ*((1/(min σ 1)^2)*(1+t^2)⁻¹) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (LSeries_norm_le_vertical hf t) (Real.rpow_nonneg hX.le _)) hk
          (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hX.le _) (absoluteDirichletSum_nonneg _ _))
      _ = _ := by ring

lemma rpow_neg_two_eq (t : ℝ) : t^(-2 : ℝ)=1/t^2 := by
  rw [show (-2 : ℝ)=((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  simp [zpow_neg, one_div, zpow_ofNat]

lemma norm_integral_Ioi_le_inv_sq {g : ℝ → ℂ} {T C : ℝ} (hT : 0<T)
    (hb : ∀ t > T, ‖g t‖ ≤ C/t^2) : ‖∫ t : ℝ in Ioi T, g t‖ ≤ C/T := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ)< -1) hT).const_mul C
  calc
    _ ≤ ∫ t : ℝ in Ioi T, C*t^(-2 : ℝ) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa [rpow_neg_two_eq, div_eq_mul_inv] using hb t ht
    _ = C/T := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ)< -1) hT]
      norm_num [Real.rpow_neg_one]
      ring

lemma integral_tail_norm_le {g : ℝ → ℂ} {T C : ℝ} (hT : 0<T) (hg : Integrable g)
    (hb : ∀ t : ℝ, T ≤ |t| → ‖g t‖ ≤ C/t^2) :
    ‖(∫ t : ℝ, g t)-(∫ t : ℝ in -T..T, g t)‖ ≤ 2*C/T := by
  have hpos := norm_integral_Ioi_le_inv_sq hT (g := g) (C := C)
    (fun t ht => hb t (by rw [abs_of_pos (by linarith : 0<t)]; linarith))
  have hneg := norm_integral_Ioi_le_inv_sq hT (g := fun t => g (-t)) (C := C) (by
    intro t ht
    simpa using hb (-t) (by rw [abs_neg, abs_of_pos (by linarith : 0<t)]; linarith))
  rw [integral_comp_neg_Ioi] at hneg
  have heq := integral_add_compl measurableSet_Ioc hg (s := Ioc (-T) T)
  rw [compl_Ioc, setIntegral_union (Iic_disjoint_Ioi (by linarith : -T ≤ T)) measurableSet_Ioi
    hg.integrableOn hg.integrableOn, ← intervalIntegral.integral_of_le (by linarith : -T ≤ T)] at heq
  have hid : (∫ t : ℝ, g t)-(∫ t : ℝ in -T..T, g t) =
      (∫ t : ℝ in Iic (-T), g t)+(∫ t : ℝ in Ioi T, g t) := by linear_combination -heq
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  calc
    _ ≤ C/T+C/T := add_le_add hneg hpos
    _ = _ := by ring

lemma perronIntegrand_tail_bound {f : ℕ → ℂ} {σ X T : ℝ} (hσ : 0<σ) (hX : 0<X) (hT : 0<T)
    (hf : LSeriesSummable f σ) :
    ‖(∫ t : ℝ, perronIntegrand f X (σ+t*I))-(∫ t : ℝ in -T..T, perronIntegrand f X (σ+t*I))‖ ≤
      2*X^σ*absoluteDirichletSum f σ/T := by
  apply (integral_tail_norm_le hT (perronIntegrand_integrable hσ hX hf) (C := X^σ*absoluteDirichletSum f σ) ?_).trans_eq (by ring)
  intro t ht
  have ht0 : t ≠ 0 := by intro h; simp [h] at ht; linarith
  rw [perronIntegrand, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ X^σ*absoluteDirichletSum f σ*(1/t^2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (LSeries_norm_le_vertical hf t) (Real.rpow_nonneg hX.le _))
        (perronKernel_norm_le_inv_sq ht0) (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hX.le _) (absoluteDirichletSum_nonneg _ _))
    _ = _ := by ring

end
end MaynardDevelopment
end

/- PrimeError -/
section

open scoped Topology
open Complex MeasureTheory Set Filter ArithmeticFunction
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

def natZeta (n : ℕ) : ℂ := if n=0 then 0 else 1

def primeErrorCoeff {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n : ZMod q)*(vonMangoldt n : ℂ) - if χ=1 then natZeta n else 0

def zetaRegularPart (s : ℂ) : ℂ := 1-s*boundedMellin natFraction s

def primeErrorAnalytic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -logDeriv (regularizedL χ) s - if χ=1 then zetaRegularPart s else 0

lemma primeErrorCoeff_zero {q : ℕ} (χ : DirichletCharacter ℂ q) : primeErrorCoeff χ 0=0 := by
  simp [primeErrorCoeff, natZeta]

lemma natZeta_LSeriesSummable {s : ℂ} (hs : 1<s.re) : LSeriesSummable natZeta s := by
  apply (LSeriesSummable_congr s (g := 1) (fun {n} hn => by simp [natZeta,hn])).mpr
  exact LSeriesSummable_one_iff.mpr hs

lemma natZeta_LSeries {s : ℂ} (hs : 1<s.re) : LSeries natZeta s = riemannZeta s := by
  rw [LSeries_congr (g := 1) (fun {n} hn => by simp [natZeta,hn]), LSeries_one_eq_riemannZeta hs]

lemma primeErrorCoeff_LSeriesSummable {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (primeErrorCoeff χ) s := by
  change LSeriesSummable (fun n : ℕ => χ n*(vonMangoldt n : ℂ) - if χ=1 then natZeta n else 0) s
  by_cases hχ : χ=1
  · simp only [if_pos hχ]
    exact (χ.LSeriesSummable_twist_vonMangoldt hs).sub (natZeta_LSeriesSummable hs)
  · simp only [if_neg hχ, sub_zero]
    exact χ.LSeriesSummable_twist_vonMangoldt hs

lemma zetaRegularPart_eq {s : ℂ} (hs : 1<s.re) :
    zetaRegularPart s = riemannZeta s-1/(s-1) := by
  rw [riemannZeta_eq_boundedMellin hs, zetaRegularPart]
  have hn : s-1 ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  field_simp
  ring

lemma primeErrorAnalytic_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) : primeErrorAnalytic χ s = LSeries (primeErrorCoeff χ) s := by
  have ht := χ.LSeries_twist_vonMangoldt_eq hs
  rw [← χ.deriv_LFunction_eq_deriv_LSeries hs, ← χ.LFunction_eq_LSeries hs, neg_div, ← logDeriv_apply] at ht
  have hsum : LSeriesSummable (fun n : ℕ => χ n*(vonMangoldt n : ℂ)) s := χ.LSeriesSummable_twist_vonMangoldt hs
  by_cases hχ : χ=1
  · have hfun : primeErrorCoeff χ = (fun n : ℕ => χ n * (vonMangoldt n : ℂ))-natZeta := by
      funext n
      simp only [primeErrorCoeff, if_pos hχ, Pi.sub_apply]
    rw [hfun, LSeries_sub hsum (natZeta_LSeriesSummable hs),
      natZeta_LSeries hs]
    rw [primeErrorAnalytic, if_pos hχ, regularizedL_logDeriv χ hs, if_pos hχ, zetaRegularPart_eq hs]
    change -(1/(s-1)+logDeriv χ.LFunction s)-(riemannZeta s-1/(s-1)) = _
    have ht' : LSeries (fun n : ℕ => χ n*(vonMangoldt n : ℂ)) s = -logDeriv χ.LFunction s := ht
    rw [ht']
    ring
  · have hfun : primeErrorCoeff χ = (fun n : ℕ => χ n*(vonMangoldt n : ℂ)) := by
      funext n
      simp only [primeErrorCoeff, if_neg hχ, sub_zero]
    rw [hfun, primeErrorAnalytic, if_neg hχ, sub_zero, regularizedL_logDeriv χ hs, if_neg hχ, zero_add]
    exact ht.symm

lemma zetaRegularPart_differentiableAt {s : ℂ} (hs : 0<s.re) : DifferentiableAt ℂ zetaRegularPart s := by
  unfold zetaRegularPart
  exact (differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.mul
    (boundedMellin_differentiableAt natFraction_measurable (by norm_num : (0 : ℝ) ≤ 1)
      (fun t ht => natFraction_norm_le ht) hs))

lemma primeErrorAnalytic_differentiableAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0<s.re) (hn : regularizedL χ s ≠ 0) : DifferentiableAt ℂ (primeErrorAnalytic χ) s := by
  have ha := (regularizedL_differentiable χ).analyticAt s
  have hd : DifferentiableAt ℂ (logDeriv (regularizedL χ)) s := ha.deriv.differentiableAt.div ha.differentiableAt hn
  change DifferentiableAt ℂ (fun z => -logDeriv (regularizedL χ) z - if χ=1 then zetaRegularPart z else 0) s
  by_cases hχ : χ=1
  · simp only [if_pos hχ]
    exact hd.neg.sub (zetaRegularPart_differentiableAt hs)
  · simp only [if_neg hχ, sub_zero]
    exact hd.neg

lemma primeErrorAnalytic_norm_bound {q Q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hqQ : q≤Q) (hNP : NoPageZero Q χ) {T : ℝ} (hT : 0≤T) {s : ℂ}
    (hs : |s.re-1|≤stripWidth Q T) (hi : |s.im|≤T) :
    ‖primeErrorAnalytic χ s‖ ≤ (2000000000000*(Lheight (Q^2) (T+1))^2+5)*(1+|s.im|) := by
  have hd := regularizedL_logDeriv_strip_bound χ hqQ hNP hT hs hi
  have hη := stripWidth_le Q T
  have hre := abs_le.mp hs
  have hsre : 0<s.re := by linarith
  have hM : ‖boundedMellin natFraction s‖ ≤ 2 := by
    refine (boundedMellin_norm_le natFraction_measurable (by norm_num : (0 : ℝ) ≤ 1)
      (fun t ht => natFraction_norm_le ht) hsre).trans ?_
    apply (div_le_iff₀ hsre).mpr
    linarith
  have hsN : ‖s‖ ≤ 2+|s.im| := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hsre] at hh
    linarith
  have hzN : ‖zetaRegularPart s‖ ≤ 5+2*|s.im| := by
    have hh := norm_sub_le (1 : ℂ) (s*boundedMellin natFraction s)
    rw [norm_one,norm_mul] at hh
    unfold zetaRegularPart
    have hmul := mul_le_mul hsN hM (norm_nonneg _) (by positivity : 0≤2+|s.im|)
    linarith
  have hhh : ‖primeErrorAnalytic χ s‖ ≤ 2000000000000*(Lheight (Q^2) (T+1))^2+5+2*|s.im| := by
    unfold primeErrorAnalytic
    by_cases hχ : χ=1
    · rw [if_pos hχ]
      have hh := norm_sub_le (-logDeriv (regularizedL χ) s) (zetaRegularPart s)
      rw [norm_neg] at hh
      linarith
    · rw [if_neg hχ, sub_zero, norm_neg]
      linarith [abs_nonneg s.im]
  refine hhh.trans ?_
  have hH := Lheight_ge_one (Q^2) (T+1)
  nlinarith [abs_nonneg s.im, sq_nonneg (Lheight (Q^2) (T+1))]

end
end MaynardDevelopment
end

/- PrimeErrorMean -/
section

open scoped Topology
open Complex Set Filter ArithmeticFunction
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma absoluteDirichletSum_real_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0≤f n) {σ : ℝ}
    (hsum : LSeriesSummable (fun n => (f n : ℂ)) σ) :
    absoluteDirichletSum (fun n => (f n : ℂ)) σ = (LSeries (fun n => (f n : ℂ)) σ).re := by
  unfold absoluteDirichletSum LSeries
  rw [Complex.re_tsum hsum]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · subst n
    simp [LSeries.term_zero]
  rw [LSeries.term_of_ne_zero hn, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n),
    ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  exact abs_of_nonneg (div_nonneg (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))

lemma absoluteDirichletSum_mangoldt_eq {σ : ℝ} (hσ : 1<σ) :
    absoluteDirichletSum (fun n => (vonMangoldt n : ℂ)) σ = negLDeriv (1 : DirichletCharacter ℂ 1) σ := by
  rw [absoluteDirichletSum_real_nonneg (fun n => vonMangoldt_nonneg)
    (LSeriesSummable_vonMangoldt (by simpa using hσ))]
  have hh := LSeries_vonMangoldt_eq_deriv_riemannZeta_div (show 1<(σ : ℂ).re by simpa using hσ)
  have heq : (1 : DirichletCharacter ℂ 1).LFunction = riemannZeta := by
    exact DirichletCharacter.LFunction_modOne_eq
  rw [negLDeriv, heq, logDeriv_apply, hh, neg_div, Complex.neg_re]

lemma negLDeriv_one_real_le {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) :
    negLDeriv (1 : DirichletCharacter ℂ 1) σ ≤ 256/(σ-1) := by
  have hδ : 0<σ-1 := by linarith
  have hh := LFunction_neg_logDeriv_roots_le (1 : DirichletCharacter ℂ 1)
    (c := (σ : ℂ)) (by simpa using hσ) (by simpa using hσ2) ∅ (fun _ => 0) (by simp) (by simp)
  simp only [Finset.sum_empty, add_zero, if_true, Complex.ofReal_re, Complex.ofReal_im] at hh
  rw [zeroContribution_same_im (by simp)] at hh
  simp only [Complex.ofReal_re, Complex.one_re] at hh
  have hH : Lheight 1 0 ≤ 3 := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<3)
    simp only [Lheight, Nat.cast_one, Real.log_one, add_zero, abs_zero, zero_add]
    linarith
  have hl := Real.log_le_sub_one_of_pos (show 0<1/(σ-1) by positivity)
  have hinv : 1≤1/(σ-1) := (le_div_iff₀ hδ).mpr (by linarith)
  have ht : 256/(σ-1)=256*(1/(σ-1)) := by ring
  rw [ht]
  dsimp only [negLDeriv]
  linarith

lemma primeErrorCoeff_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖primeErrorCoeff χ n‖ ≤ vonMangoldt n+1 := by
  have hterm : ‖χ (n : ZMod q)*(vonMangoldt n : ℂ)‖ ≤ vonMangoldt n := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one _)
  have hz : ‖if χ=1 then natZeta n else (0 : ℂ)‖ ≤ 1 := by
    split_ifs <;> simp [natZeta] <;> split_ifs <;> norm_num
  exact (norm_sub_le _ _).trans (add_le_add hterm hz)

lemma absoluteDirichletSum_primeError_le {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1<σ) (hσ2 : σ≤2) : absoluteDirichletSum (primeErrorCoeff χ) σ ≤ 512/(σ-1) := by
  have hs : 1<(σ : ℂ).re := by simpa using hσ
  have hΛ := (LSeriesSummable_vonMangoldt hs).norm
  have h₁ := (LSeriesSummable_one_iff.mpr hs).norm
  have hbound : absoluteDirichletSum (primeErrorCoeff χ) σ ≤
      absoluteDirichletSum (fun n => (vonMangoldt n : ℂ)) σ + absoluteDirichletSum 1 σ := by
    rw [absoluteDirichletSum, absoluteDirichletSum, absoluteDirichletSum, ← hΛ.tsum_add h₁]
    apply Summable.tsum_le_tsum
    · intro n
      simp only [LSeries.norm_term_eq, Complex.ofReal_re]
      by_cases hn : n=0
      · simp [hn]
      · simp only [if_neg hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
          Pi.one_apply, norm_one, ← add_div]
        exact div_le_div_of_nonneg_right (primeErrorCoeff_norm_le χ n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · exact (primeErrorCoeff_LSeriesSummable χ hs).norm
    · exact hΛ.add h₁
  have hΛb := negLDeriv_one_real_le hσ hσ2
  rw [← absoluteDirichletSum_mangoldt_eq hσ] at hΛb
  have h₁b : absoluteDirichletSum 1 σ ≤ 2/(σ-1) := by
    have hh : absoluteDirichletSum 1 σ = (LSeries 1 σ).re := by
      exact absoluteDirichletSum_real_nonneg (f := fun _ => 1) (fun _ => by norm_num) (LSeriesSummable_one_iff.mpr hs)
    rw [hh]
    refine (Complex.re_le_norm _).trans ((LSeries_norm_le_of_bounded (f := 1) (fun n => by simp) hs).trans ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0<σ)]
    exact div_le_div_of_nonneg_right hσ2 (by linarith)
  have hδ : 0<σ-1 := by linarith
  calc
    _ ≤ 256/(σ-1)+2/(σ-1) := hbound.trans (add_le_add hΛb h₁b)
    _ ≤ _ := by rw [← add_div]; apply div_le_div_of_nonneg_right (by norm_num) hδ.le

end
end MaynardDevelopment
end

/- ConductorReduction -/
section

open scoped BigOperators Topology
open Complex Set Filter DirichletCharacter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma eq_changeLevel_primitive {q : ℕ} (χ : DirichletCharacter ℂ q) :
    χ=changeLevel χ.conductor_dvd_level χ.primitiveCharacter :=
  (χ.factorsThrough_conductor).choose_spec.choose_spec

lemma changeLevel_nat_apply_of_coprime {d q : ℕ} [NeZero q] (hd : d∣q)
    (ψ : DirichletCharacter ℂ d) {n : ℕ} (hn : n.Coprime q) :
    changeLevel hd ψ (n : ZMod q)=ψ (n : ZMod d) := by
  have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr hn
  have hh := changeLevel_eq_cast_of_dvd ψ hd hu.unit
  rw [hu.unit_spec] at hh
  change changeLevel hd ψ (n : ZMod q)=ψ (ZMod.castHom hd (ZMod d) (n : ZMod q)) at hh
  simpa only [map_natCast] using hh

lemma primitiveCharacter_nat_apply_of_coprime {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn : n.Coprime q) : χ.primitiveCharacter (n : ZMod χ.conductor)=χ (n : ZMod q) := by
  have hh := changeLevel_nat_apply_of_coprime χ.conductor_dvd_level χ.primitiveCharacter hn
  rw [← eq_changeLevel_primitive χ] at hh
  exact hh.symm

lemma primitiveCharacter_eq_one_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter=1 ↔ χ=1 := by
  have hh := changeLevel_eq_one_iff (χ := χ.primitiveCharacter) χ.conductor_dvd_level
  rw [← eq_changeLevel_primitive χ] at hh
  exact hh.symm

def asPrimitive (Q : ℕ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hqQ : q≤Q) : PrimitiveUpTo Q :=
  ⟨⟨χ.conductor,lt_of_le_of_lt ((Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level).trans hqQ) (Nat.lt_succ_self Q)⟩,
    χ.primitiveCharacter,χ.conductor_ne_zero (NeZero.ne q),χ.primitiveCharacter_isPrimitive⟩

lemma asPrimitive_value {Q q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hqQ : q≤Q)
    {n : ℕ} (hn : n.Coprime q) : primitiveValue (asPrimitive Q χ hqQ) n=χ (n : ZMod q) :=
  primitiveCharacter_nat_apply_of_coprime χ hn

lemma asPrimitive_injective {Q q : ℕ} [NeZero q] (hqQ : q≤Q) :
    Function.Injective (fun χ : DirichletCharacter ℂ q => asPrimitive Q χ hqQ) := by
  intro χ ψ h
  apply MulChar.ext
  intro u
  have hn : u.val.val.Coprime q := (ZMod.isUnit_iff_coprime _ _).mp (by simpa using u.isUnit)
  have hh := congrArg (fun ρ : PrimitiveUpTo Q => primitiveValue ρ u.val.val) h
  dsimp only at hh
  rw [asPrimitive_value χ hqQ hn,asPrimitive_value ψ hqQ hn,ZMod.natCast_zmod_val] at hh
  exact hh

lemma sum_asPrimitive_le {Q q : ℕ} [NeZero q] (hqQ : q≤Q) (f : PrimitiveUpTo Q → ℝ)
    (hf : ∀ χ, 0≤f χ) :
    (∑ χ : DirichletCharacter ℂ q, f (asPrimitive Q χ hqQ)) ≤
      ∑ ρ : PrimitiveUpTo Q, if ρ.1.val∣q then f ρ else 0 := by
  let g : PrimitiveUpTo Q → ℝ := fun ρ => if ρ.1.val∣q then f ρ else 0
  have heq : (∑ χ : DirichletCharacter ℂ q, f (asPrimitive Q χ hqQ)) =
      ∑ χ : DirichletCharacter ℂ q, g (asPrimitive Q χ hqQ) := by
    apply Finset.sum_congr rfl
    intro χ hχ
    simp only [g,asPrimitive,if_pos χ.conductor_dvd_level]
  rw [heq]
  change _≤∑ ρ : PrimitiveUpTo Q, g ρ
  rw [← Finset.sum_image (fun a ha b hb h => asPrimitive_injective hqQ h)]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro ρ hρ hρ'
  dsimp [g]
  split_ifs
  · exact hf ρ
  · exact le_rfl

lemma GoodModulus.of_dvd {Q n d : ℕ} (hn : GoodModulus Q n) (hd : d∣n) : GoodModulus Q d := by
  rcases hn with hn | hn
  · exact .inl hn
  · exact .inr (fun h => hn (h.trans hd))

lemma primitive_good_noPageZero {R Q : ℕ} (χ : PrimitiveUpTo Q) (hχR : χ.1.val≤R)
    (hg : GoodModulus R χ.1.val) :
    letI : NeZero χ.1.val := ⟨χ.2.property.1⟩
    NoPageZero R χ.2.val := by
  letI : NeZero χ.1.val := ⟨χ.2.property.1⟩
  let ψ : PrimitiveUpTo R := ⟨⟨χ.1.val,by omega⟩,χ.2.val,χ.2.property⟩
  have hne : ¬PageExceptional R ψ := goodModulus_no_exception ψ hg dvd_rfl
  exact noPageZero_of_not_exceptional ψ hne

end
end MaynardDevelopment
end

/- ImprimitiveError -/
section

open scoped BigOperators Topology
open Complex Set Filter DirichletCharacter ArithmeticFunction
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma primeErrorCoeff_difference {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    primeErrorCoeff χ n-primeErrorCoeff χ.primitiveCharacter n =
      (χ (n : ZMod q)-χ.primitiveCharacter (n : ZMod χ.conductor))*(vonMangoldt n : ℂ) := by
  simp only [primeErrorCoeff,primitiveCharacter_eq_one_iff χ]
  ring

lemma primeErrorCoeff_difference_eq_zero_of_coprime {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : n.Coprime q) :
    primeErrorCoeff χ n-primeErrorCoeff χ.primitiveCharacter n=0 := by
  rw [primeErrorCoeff_difference,primitiveCharacter_nat_apply_of_coprime χ hn,sub_self,zero_mul]

lemma primeErrorCoeff_difference_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖primeErrorCoeff χ n-primeErrorCoeff χ.primitiveCharacter n‖ ≤ vonMangoldt n := by
  by_cases hn : n.Coprime q
  · rw [primeErrorCoeff_difference_eq_zero_of_coprime χ hn,norm_zero]
    exact vonMangoldt_nonneg
  rw [primeErrorCoeff_difference, MulChar.map_nonunit χ (by simpa [ZMod.isUnit_iff_coprime] using hn),
    zero_sub,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg]
  exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.primitiveCharacter.norm_le_one _)

lemma primeErrorCoeff_difference_support {q X n : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hnX : n≤X) (hne : primeErrorCoeff χ n-primeErrorCoeff χ.primitiveCharacter n≠0) :
    n ∈ (Finset.range (q+1) ×ˢ Finset.range (Nat.log 2 X+1)).image (fun pk : ℕ×ℕ => pk.1^pk.2) := by
  have hncp : ¬n.Coprime q := fun h => hne (primeErrorCoeff_difference_eq_zero_of_coprime χ h)
  have hnΛ : vonMangoldt n≠0 := by
    intro h
    apply hne
    rw [primeErrorCoeff_difference,h,Complex.ofReal_zero,mul_zero]
  obtain ⟨p,k,hp,hk,hpn⟩ := (isPrimePow_nat_iff n).mp (vonMangoldt_ne_zero_iff.mp hnΛ)
  have hpq : p∣q := by
    by_contra h
    apply hncp
    rw [←hpn]
    exact (hp.coprime_iff_not_dvd.mpr h).pow_left k
  have hpqle : p≤q := Nat.le_of_dvd (NeZero.pos q) hpq
  have hkX : k≤Nat.log 2 X := Nat.le_log_of_pow_le (by norm_num)
    ((Nat.pow_le_pow_left hp.two_le k).trans (hpn ▸ hnX))
  apply Finset.mem_image.mpr
  refine ⟨(p,k),?_,hpn⟩
  simp only [Finset.mem_product,Finset.mem_range]
  exact ⟨by omega,by omega⟩

lemma norm_sum_le_support_card {α : Type*} [DecidableEq α] (s S : Finset α) (f : α → ℂ)
    {C : ℝ} (hC : 0≤C) (hf : ∀ a ∈ s, ‖f a‖≤C) (hs : ∀ a ∈ s, f a≠0 → a ∈ S) :
    ‖∑ a ∈ s, f a‖≤(S.card : ℝ)*C := by
  have hcard : (s.filter (fun a => a ∈ S)).card≤S.card := Finset.card_le_card (by
    intro a ha
    exact (Finset.mem_filter.mp ha).2)
  calc
    _ ≤ ∑ a ∈ s, ‖f a‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ s, if a ∈ S then C else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs with hmem
      · exact hf a ha
      · have hf0 : f a=0 := by by_contra h; exact hmem (hs a ha h)
        simp [hf0]
    _ = ((s.filter (fun a => a ∈ S)).card : ℝ)*C := by rw [← Finset.sum_filter]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC

lemma imprimitive_error_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℕ) :
    ‖(∑ n ∈ Finset.Icc 1 X, primeErrorCoeff χ n)-(∑ n ∈ Finset.Icc 1 X, primeErrorCoeff χ.primitiveCharacter n)‖ ≤
      (q+1 : ℝ)*(Nat.log 2 X+1 : ℝ)*Real.log (X+1 : ℝ) := by
  rw [←Finset.sum_sub_distrib]
  let S := (Finset.range (q+1) ×ˢ Finset.range (Nat.log 2 X+1)).image (fun pk : ℕ×ℕ => pk.1^pk.2)
  have hC : 0≤Real.log (X+1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X])
  have hh := norm_sum_le_support_card (Finset.Icc 1 X) S
    (fun n => primeErrorCoeff χ n-primeErrorCoeff χ.primitiveCharacter n) hC (by
      intro n hn
      have hn0 : 0<n := by have hh := (Finset.mem_Icc.mp hn).1; omega
      have hlog := Real.log_le_log (by exact_mod_cast hn0 : (0 : ℝ)<n)
        (show (n : ℝ)≤X+1 by
          have hh : (n : ℝ)≤X := by exact_mod_cast (Finset.mem_Icc.mp hn).2
          linarith)
      exact (primeErrorCoeff_difference_norm χ n).trans ((vonMangoldt_le_log (n := n)).trans hlog))
    (fun n hn hne => primeErrorCoeff_difference_support χ (Finset.mem_Icc.mp hn).2 hne)
  have hcard : S.card≤(q+1)*(Nat.log 2 X+1) := by
    exact Finset.card_image_le.trans (by simp)
  refine hh.trans ?_
  have hc : (S.card : ℝ)≤(q+1 : ℝ)*(Nat.log 2 X+1 : ℝ) := by exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right hc hC

end
end MaynardDevelopment
end

/- TotientBounds -/
section

open scoped BigOperators
open Filter

namespace MaynardDevelopment

lemma prod_ratio_le_card_add_one (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    (∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) ≤ (s.card : ℝ) + 1 := by
  induction s using Finset.induction_on_max with
  | h0 => simp
  | step a s hmax ih =>
    have ha : 2 ≤ a := hs a (Finset.mem_insert_self _ _)
    have hs' : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have has : a ∉ s := by intro h; exact (lt_irrefl a) (hmax a h)
    have hcard : s.card ≤ a - 2 := by
      have hsub : s ⊆ Finset.Ico 2 a := by
        intro p hp
        exact Finset.mem_Ico.mpr ⟨hs' p hp, hmax p hp⟩
      simpa using Finset.card_le_card hsub
    have har : (s.card : ℝ) + 2 ≤ (a : ℝ) := by exact_mod_cast (by omega : s.card + 2 ≤ a)
    have hapos : 0 < (a : ℝ) - 1 := by
      have : (2 : ℝ) ≤ a := by exact_mod_cast ha
      linarith
    rw [Finset.prod_insert has, Finset.card_insert_of_notMem has]
    push_cast
    calc
      (a : ℝ) / ((a : ℝ) - 1) * (∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) ≤
          (a : ℝ) / ((a : ℝ) - 1) * ((s.card : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (ih hs') (by positivity)
      _ ≤ ((s.card : ℝ) + 1) + 1 := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hapos).mpr
        nlinarith

lemma totient_ratio_le_primeFactors_card (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) / n.totient ≤ (n.primeFactors.card : ℝ) + 1 := by
  have hnpos := Nat.pos_of_ne_zero hn
  have htpos : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hnpos
  have hQ : ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℝ) =
      ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  simp only [Nat.cast_prod] at hQ
  have hQne : (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hh : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have he := congrArg (fun n : ℕ => (n : ℝ)) (Nat.totient_mul_prod_primeFactors n)
  simp only [Nat.cast_mul, Nat.cast_prod] at he
  have he' : (n.totient : ℝ) * (∏ p ∈ n.primeFactors, (p : ℝ)) =
      (n : ℝ) * (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) := by
    simpa only [Nat.cast_prod] using he.trans (congrArg (fun x : ℝ => (n : ℝ) * x) hQ)
  have hratio : (n : ℝ) / n.totient = ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
    rw [Finset.prod_div_distrib]
    apply (div_eq_div_iff htpos.ne' hQne).mpr
    nlinarith [he']
  rw [hratio]
  exact prod_ratio_le_card_add_one _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)

lemma primeFactors_card_log_bound (n K : ℕ) (hn : n ≠ 0) (hK : 1 ≤ K) :
    (n.primeFactors.card : ℝ) ≤ (K + 1 : ℝ) + Real.log n / Real.log (K + 1) := by
  classical
  let L := n.primeFactors.filter (fun p => K < p)
  let S := n.primeFactors.filter (fun p => ¬ K < p)
  have hS : S.card ≤ K + 1 := by
    have hsub : S ⊆ Finset.range (K + 1) := by
      intro p hp
      have hh := (Finset.mem_filter.mp hp).2
      exact Finset.mem_range.mpr (by omega)
    simpa using Finset.card_le_card hsub
  have hcard : n.primeFactors.card ≤ L.card + (K + 1) := by
    have heq := Finset.card_filter_add_card_filter_not (s := n.primeFactors) (fun p => K < p)
    change L.card + S.card = n.primeFactors.card at heq
    omega
  have hpow : (K + 1) ^ L.card ≤ n := by
    calc
      (K + 1) ^ L.card = ∏ _p ∈ L, (K + 1) := by simp
      _ ≤ ∏ p ∈ L, p := by
        apply Finset.prod_le_prod'
        intro p hp
        have := (Finset.mem_filter.mp hp).2
        omega
      _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
        ((Finset.prod_dvd_prod_of_subset L n.primeFactors id (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd n))
  have hpcast : ((K : ℝ) + 1) ^ L.card ≤ (n : ℝ) := by exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity : 0 < ((K : ℝ) + 1) ^ L.card) hpcast
  rw [Real.log_pow] at hlog
  have hKlog : 0 < Real.log (K + 1 : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < K + 1))
  have hcardR : (n.primeFactors.card : ℝ) ≤ (L.card : ℝ) + (K + 1 : ℝ) := by exact_mod_cast hcard
  have hdiv : (L.card : ℝ) ≤ Real.log n / Real.log (K + 1 : ℝ) :=
    (le_div_iff₀ hKlog).mpr hlog
  linarith

lemma totient_ratio_log_bound (n K : ℕ) (hn : n ≠ 0) (hK : 1 ≤ K) :
    (n : ℝ) / n.totient ≤ (K + 2 : ℝ) + Real.log n / Real.log (K + 1) := by
  have h₁ := totient_ratio_le_primeFactors_card n hn
  have h₂ := primeFactors_card_log_bound n K hn hK
  linarith

/-- A weak uniform totient estimate, sufficient to make logarithmic normalization errors vanish.
It requires only the fact that the prime divisors are distinct integers at least two. -/
lemma totient_ratio_uniform_small (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ X : ℝ, 1 < X ∧ ∀ x ≥ X, ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ x ^ C →
      (n : ℝ) / n.totient ≤ ε * Real.log x := by
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.exp (2 * (C + 1) / ε))
  have hK1 : 1 ≤ K := by
    have he := Real.exp_pos (2 * (C + 1) / ε)
    have hpos : (0 : ℝ) < K := lt_trans he hK
    exact_mod_cast (show (1 : ℕ) ≤ K by exact Nat.pos_iff_ne_zero.mp (by exact_mod_cast hpos) |> Nat.one_le_iff_ne_zero.mpr)
  have hKbig : 2 * (C + 1) / ε < Real.log (K + 1 : ℝ) := by
    have hh := Real.log_lt_log (Real.exp_pos (2 * (C + 1) / ε))
      (lt_trans hK (by norm_num : (K : ℝ) < (K + 1 : ℝ)))
    rwa [Real.log_exp] at hh
  have hlogK : 0 < Real.log (K + 1 : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < K + 1)
  have hCdiv : C / Real.log (K + 1 : ℝ) < ε / 2 := by
    apply (div_lt_iff₀ hlogK).mpr
    have hh := (div_lt_iff₀ hε).mp hKbig
    nlinarith
  let X := Real.exp (2 * (K + 2 : ℝ) / ε + 1)
  have hX : 1 < X := by
    apply Real.one_lt_exp_iff.mpr
    positivity
  refine ⟨X, hX, ?_⟩
  intro x hx n hn hnx
  have hx1 : 1 < x := lt_of_lt_of_le hX hx
  have hxpos : 0 < x := lt_trans (by norm_num) hx1
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogX : 2 * (K + 2 : ℝ) / ε + 1 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (2 * (K + 2 : ℝ) / ε + 1)) hx
    rwa [Real.log_exp] at hh
  have hA : (K + 2 : ℝ) ≤ ε / 2 * Real.log x := by
    have hh : 2 * (K + 2 : ℝ) / ε ≤ Real.log x := by linarith
    have := (div_le_iff₀ hε).mp hh
    nlinarith
  have hln : Real.log (n : ℝ) ≤ C * Real.log x := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hh := Real.log_le_log hnpos hnx
    rw [Real.log_rpow hxpos] at hh
    nlinarith
  calc
    (n : ℝ) / n.totient ≤ (K + 2 : ℝ) + Real.log n / Real.log (K + 1 : ℝ) :=
      totient_ratio_log_bound n K hn hK1
    _ ≤ (K + 2 : ℝ) + (C * Real.log x) / Real.log (K + 1 : ℝ) := by
      gcongr
    _ = (K + 2 : ℝ) + (C / Real.log (K + 1 : ℝ)) * Real.log x := by ring
    _ ≤ ε / 2 * Real.log x + ε / 2 * Real.log x :=
      add_le_add hA (mul_le_mul_of_nonneg_right hCdiv.le hlogx.le)
    _ = ε * Real.log x := by ring


lemma eventually_totient_ratio_le_rpow :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / n.totient ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := ((isLittleO_log_rpow_atTop (r := (1 / 4 : ℝ)) (by norm_num)).bound
    (show 0 < Real.log 2 / 2 by positivity))
  have hsmallN := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually hsmall
  have hpN : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hsmallN, hpN.eventually (eventually_ge_atTop 6), eventually_ge_atTop 2] with n hs hp hn
  have hn0 : n ≠ 0 := by omega
  have hnp : (0 : ℝ) ≤ n := by positivity
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  simp only [Real.norm_eq_abs, abs_of_nonneg hlogn, abs_of_nonneg (Real.rpow_nonneg hnp _)] at hs
  have hbound := totient_ratio_log_bound n 1 hn0 (by decide)
  norm_num at hbound
  have hdiv : Real.log (n : ℝ) / Real.log 2 ≤ (n : ℝ) ^ (1 / 4 : ℝ) / 2 := by
    apply (div_le_iff₀ hlog2).mpr
    nlinarith
  linarith

lemma summable_inv_totient_sq : Summable (fun n : ℕ => ((n.totient : ℝ)⁻¹) ^ 2) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply hsum.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_totient_ratio_le_rpow, eventually_ge_atTop 1] with n hn hn1
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn1
  have htp : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn1
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hnp)).mp
  calc
    (n.totient : ℝ)⁻¹ ^ 2 * (n : ℝ) ^ 2 = ((n : ℝ) / n.totient) ^ 2 := by ring
    _ ≤ ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
      exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hn
    _ = (n : ℝ) ^ (-3 / 2 : ℝ) * (n : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hnp.le,
        ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hnp]
      norm_num


end MaynardDevelopment
end

/- ConvolutionSums -/
section

open scoped BigOperators
namespace MaynardDevelopment

lemma sum_divisorsAntidiagonal_hyperbola {R : Type*} [AddCommMonoid R]
    (X : ℕ) (H : ℕ → ℕ → R) :
    (∑ n ∈ Finset.Icc 1 X, ∑ de ∈ n.divisorsAntidiagonal, H de.1 de.2) =
      ∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 (X / d), H d e := by
  rw [← Finset.sum_sigma (Finset.Icc 1 X) (fun n => n.divisorsAntidiagonal)
    (fun a => H a.2.1 a.2.2),
    ← Finset.sum_sigma (Finset.Icc 1 X) (fun d => Finset.Icc 1 (X / d)) (fun a => H a.1 a.2)]
  apply Finset.sum_bij (fun a _ => ⟨a.2.1, a.2.2⟩)
  · rintro ⟨n, d, e⟩ ha
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at ha ⊢
    have hd : 0 < d := by nlinarith [ha.2.1]
    have he : 0 < e := by nlinarith [ha.2.1]
    have hdX : d ≤ X := by nlinarith [ha.1.2, ha.2.1]
    exact ⟨⟨hd, hdX⟩, he, (Nat.le_div_iff_mul_le hd).mpr (by nlinarith [ha.2.1, ha.1.2])⟩
  · rintro ⟨n, d, e⟩ ha ⟨n', d', e'⟩ hb hh
    have heq : d = d' ∧ e = e' := by simpa only [Sigma.mk.inj_iff, heq_eq_eq] using hh
    rcases heq with ⟨rfl, rfl⟩
    have hn := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp ha).2).1
    have hn' := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hb).2).1
    cases hn.symm.trans hn'
    rfl
  · rintro ⟨d, e⟩ hb
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hb
    have hd : 0 < d := hb.1.1
    have he : 0 < e := hb.2.1
    have hde : d * e ≤ X := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hb.2.2
    refine ⟨⟨d * e, (d, e)⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal]
    exact ⟨⟨Nat.mul_pos hd he, hde⟩, trivial, (Nat.mul_pos hd he).ne'⟩
  · intros; rfl

lemma sum_convolution {R : Type*} [Semiring R] (X : ℕ) (f g : ArithmeticFunction R) :
    (∑ n ∈ Finset.Icc 1 X, (f * g) n) =
      ∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 (X / d), f d * g e := by
  simp only [ArithmeticFunction.mul_apply]
  exact sum_divisorsAntidiagonal_hyperbola X (fun d e => f d * g e)

lemma sum_convolution_weighted {R : Type*} [Semiring R]
    (X : ℕ) (f g : ArithmeticFunction R) (w : ℕ → R) :
    (∑ n ∈ Finset.Icc 1 X, (f * g) n * w n) =
      ∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 (X / d), f d * g e * w (d * e) := by
  have heq (n : ℕ) : (f * g) n * w n =
      ∑ de ∈ n.divisorsAntidiagonal, f de.1 * g de.2 * w (de.1 * de.2) := by
    rw [ArithmeticFunction.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro de hde
    rw [(Nat.mem_divisorsAntidiagonal.mp hde).1]
  simp only [heq]
  exact sum_divisorsAntidiagonal_hyperbola X (fun d e => f d * g e * w (d * e))

lemma sum_convolution_map_weighted {R S : Type*} [Semiring R] [Semiring S]
    (φ : R →+* S) (X : ℕ) (f g : ArithmeticFunction R) (w : ℕ → S) :
    (∑ n ∈ Finset.Icc 1 X, φ ((f * g) n) * w n) =
      ∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 (X / d), φ (f d) * φ (g e) * w (d * e) := by
  have heq (n : ℕ) : φ ((f * g) n) * w n =
      ∑ de ∈ n.divisorsAntidiagonal, φ (f de.1) * φ (g de.2) * w (de.1 * de.2) := by
    rw [ArithmeticFunction.mul_apply, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro de hde
    rw [(Nat.mem_divisorsAntidiagonal.mp hde).1, map_mul]
  simp only [heq]
  exact sum_divisorsAntidiagonal_hyperbola X (fun d e => φ (f d) * φ (g e) * w (d * e))

end MaynardDevelopment
end

/- DivisorMoments -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section

lemma card_divisors_mul_le (a b : ℕ) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have hsub : (a * b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun de => de.1 * de.2) := by
    intro n hn
    obtain ⟨d, e, hd, he, hde⟩ := exists_dvd_and_dvd_of_dvd_mul (Nat.dvd_of_mem_divisors hn)
    exact Finset.mem_image.mpr ⟨(d, e), Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨hd, ha⟩, Nat.mem_divisors.mpr ⟨he, hb⟩⟩, hde.symm⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by rw [Finset.card_product]))

lemma zeta_sq_apply (n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2) n = n.divisors.card := by
  rw [pow_two, ArithmeticFunction.coe_mul_zeta_apply]
  have hval (d : ℕ) (hd : d ∈ n.divisors) :
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) d = 1 := by
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
      (Nat.pos_of_mem_divisors hd).ne']
  simp only [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma card_divisors_sq_le_zeta_four (n : ℕ) :
    (n.divisors.card : ℝ) ^ 2 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 4) n := by
  have hfour : (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 4 =
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2 := by ring
  rw [hfour, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun d e => ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2) d *
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2) e)]
  simp only [zeta_sq_apply]
  calc
    _ = ∑ _d ∈ n.divisors, (n.divisors.card : ℝ) := by simp [pow_two]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      have he : d * (n / d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      have hh := card_divisors_mul_le d (n / d)
      rw [he] at hh
      exact_mod_cast hh

lemma harmonic_real_sum (X : ℕ) :
    (harmonic X : ℝ) = ∑ d ∈ Finset.Icc 1 X, (d : ℝ)⁻¹ := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  rfl

lemma harmonic_real_nonneg (X : ℕ) : 0 ≤ (harmonic X : ℝ) := by
  rw [harmonic_real_sum]
  positivity

lemma harmonic_real_mono {X Y : ℕ} (hXY : X ≤ Y) : (harmonic X : ℝ) ≤ harmonic Y := by
  rw [harmonic_real_sum, harmonic_real_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hXY)
  intros; positivity

lemma sum_zeta_pow_le (k X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (k + 1)) n) ≤
      (X : ℝ) * (harmonic X : ℝ) ^ k := by
  induction k generalizing X with
  | zero =>
    have hval (n : ℕ) (hn : n ∈ Finset.Icc 1 X) :
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n = 1 := by
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
        (show n ≠ 0 by have := (Finset.mem_Icc.mp hn).1; omega)]
    simp only [zero_add, pow_one, pow_zero, mul_one, Finset.sum_congr rfl hval]
    simp
  | succ k ih =>
    rw [pow_succ', sum_convolution]
    have heq (d : ℕ) (hd : d ∈ Finset.Icc 1 X) :
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) d = 1 := by
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
        (show d ≠ 0 by have := (Finset.mem_Icc.mp hd).1; omega)]
    calc
      _ = ∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 (X / d),
          ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (k + 1)) e := by
        apply Finset.sum_congr rfl
        intro d hd
        simp only [heq d hd, one_mul]
      _ ≤ ∑ d ∈ Finset.Icc 1 X, (X / d : ℕ) * (harmonic (X / d) : ℝ) ^ k :=
        Finset.sum_le_sum (fun d _ => ih (X / d))
      _ ≤ ∑ d ∈ Finset.Icc 1 X, ((X : ℝ) / d) * (harmonic X : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro d hd
        apply mul_le_mul
        · exact Nat.cast_div_le
        · exact pow_le_pow_left₀ (harmonic_real_nonneg _) (harmonic_real_mono (Nat.div_le_self X d)) _
        · exact pow_nonneg (harmonic_real_nonneg _) _
        · positivity
      _ = (X : ℝ) * (harmonic X : ℝ) ^ (k + 1) := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum, ← harmonic_real_sum]
        ring

lemma sum_card_divisors_sq_le (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (n.divisors.card : ℝ) ^ 2) ≤
      (X : ℝ) * (1 + Real.log X) ^ 3 := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 4) n :=
      Finset.sum_le_sum (fun n _ => card_divisors_sq_le_zeta_four n)
    _ ≤ (X : ℝ) * (harmonic X : ℝ) ^ 3 := sum_zeta_pow_le 3 X
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (harmonic_real_nonneg _) (harmonic_le_one_add_log X) _) (Nat.cast_nonneg X)

end
end MaynardDevelopment
end

/- TotientWeights -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section

def totientWeightSum (Q : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 Q, (n.totient : ℝ)⁻¹

lemma totientWeightSum_nonneg (Q : ℕ) : 0≤totientWeightSum Q := by unfold totientWeightSum; positivity

lemma totientWeightSum_log_bound (Q : ℕ) :
    totientWeightSum Q≤(3+Real.log Q/Real.log 2)*(1+Real.log Q) := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0≤3+Real.log Q/Real.log 2 := by have hh := Real.log_natCast_nonneg Q; positivity
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 Q, (3+Real.log Q/Real.log 2)*(n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : 0<n := by have hh := (Finset.mem_Icc.mp hn).1; omega
      have hnr : (0 : ℝ)<n := by exact_mod_cast hn0
      have hφ : (0 : ℝ)<n.totient := by exact_mod_cast Nat.totient_pos.mpr hn0
      have hr := totient_ratio_log_bound n 1 hn0.ne' (by norm_num)
      norm_num only [Nat.cast_one] at hr
      have hlog := Real.log_le_log hnr (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n : ℝ)≤Q)
      have hdiv := div_le_div_of_nonneg_right hlog hlog2.le
      have hrat : (n : ℝ)/n.totient ≤ 3+Real.log Q/Real.log 2 := by norm_num at hr; linarith
      calc
        _ = ((n : ℝ)/n.totient)/n := by field_simp
        _ ≤ (3+Real.log Q/Real.log 2)/n := div_le_div_of_nonneg_right hrat hnr.le
        _ = _ := by ring
    _ = (3+Real.log Q/Real.log 2)*(harmonic Q : ℝ) := by rw [←Finset.mul_sum,←harmonic_real_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log Q) hC

lemma totient_inverse_mul_le (d m : ℕ) (hd : 0<d) (hm : 0 < m) :
    ((d*m).totient : ℝ)⁻¹ ≤ (d.totient : ℝ)⁻¹*(m.totient : ℝ)⁻¹ := by
  have hφd : (0 : ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφm : (0 : ℝ)< m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hh : (d.totient : ℝ)*m.totient≤(d*m).totient := by exact_mod_cast Nat.totient_super_multiplicative d m
  simpa [one_div,mul_inv_rev,mul_comm] using one_div_le_one_div_of_le (mul_pos hφd hφm) hh

lemma totient_multiples_weight_le (Q d : ℕ) (hd : 0<d) :
    (∑ q ∈ Finset.Icc 1 Q, if d∣q then (q.totient : ℝ)⁻¹ else 0) ≤
      (d.totient : ℝ)⁻¹*totientWeightSum Q := by
  rw [←Finset.sum_filter]
  let S := (Finset.Icc 1 Q).filter (fun q => d∣q)
  have hqpos (q : ℕ) (hq : q ∈ S) : 0<q := by
    have hh := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  have hqdvd (q : ℕ) (hq : q ∈ S) : d∣q := (Finset.mem_filter.mp hq).2
  have heq (q : ℕ) (hq : q ∈ S) : d*(q/d)=q := Nat.mul_div_cancel' (hqdvd q hq)
  have hdivpos (q : ℕ) (hq : q ∈ S) : 0<q/d := Nat.div_pos (Nat.le_of_dvd (hqpos q hq) (hqdvd q hq)) hd
  have hinj : Set.InjOn (fun q : ℕ => q/d) S := by
    intro q hq r hr hqr
    dsimp only at hqr
    rw [←heq q hq,←heq r hr,hqr]
  have hsub : S.image (fun q : ℕ => q/d) ⊆ Finset.Icc 1 Q := by
    intro m hm
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hm
    apply Finset.mem_Icc.mpr
    exact ⟨hdivpos q hq, (Nat.div_le_self q d).trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2⟩
  change (∑ q ∈ S, (q.totient : ℝ)⁻¹)≤_
  calc
    _ ≤ ∑ q ∈ S, (d.totient : ℝ)⁻¹*((q/d).totient : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      have hh := totient_inverse_mul_le d (q/d) hd (hdivpos q hq)
      rwa [heq q hq] at hh
    _ = (d.totient : ℝ)⁻¹*∑ m ∈ S.image (fun q : ℕ => q/d), (m.totient : ℝ)⁻¹ := by
      rw [←Finset.mul_sum,Finset.sum_image hinj]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m hm hm' => by positivity)) (by positivity)

end
end MaynardDevelopment
end

/- CharacterDistributionMean -/
section

open scoped BigOperators Topology
open Complex Set Filter DirichletCharacter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

def primeCharacterError {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, primeErrorCoeff χ n

def primitiveErrorMean (R D X : ℕ) : ℝ :=
  ∑ χ : PrimitiveUpTo D, if GoodModulus R χ.1.val then
    (χ.1.val.totient : ℝ)⁻¹*‖primeCharacterError χ.2.val X‖ else 0

def characterErrorMean (R D X : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 D, if GoodModulus R q then
    (q.totient : ℝ)⁻¹*∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError χ X‖ else 0

def inducedErrorMean (R D X : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 D, if GoodModulus R q then
    (q.totient : ℝ)⁻¹*∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError χ.primitiveCharacter X‖ else 0

lemma inducedErrorMean_le (R D X : ℕ) :
    inducedErrorMean R D X ≤ totientWeightSum D*primitiveErrorMean R D X := by
  let f : PrimitiveUpTo D → ℝ := fun χ => if GoodModulus R χ.1.val then ‖primeCharacterError χ.2.val X‖ else 0
  have hf (χ : PrimitiveUpTo D) : 0 ≤ f χ := by dsimp [f]; split_ifs <;> positivity
  have hstep : inducedErrorMean R D X ≤ 
      ∑ q ∈ Finset.Icc 1 D, (q.totient : ℝ)⁻¹*∑ χ : PrimitiveUpTo D, if χ.1.val∣q then f χ else 0 := by
    apply Finset.sum_le_sum
    intro q hq
    have hq0 : q≠0 := by have hh := (Finset.mem_Icc.mp hq).1; omega
    letI : NeZero q := ⟨hq0⟩
    have hqD := (Finset.mem_Icc.mp hq).2
    by_cases hg : GoodModulus R q
    · simp only [if_pos hg]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have heq : (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError χ.primitiveCharacter X‖)=
          ∑ χ : DirichletCharacter ℂ q, f (asPrimitive D χ hqD) := by
        apply Finset.sum_congr rfl
        intro χ hχ
        have hgood := hg.of_dvd χ.conductor_dvd_level
        simp only [f,asPrimitive,if_pos hgood]
      rw [heq]
      exact sum_asPrimitive_le hqD f hf
    · rw [if_neg hg]
      apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro χ hχ
      split_ifs
      · exact hf χ
      · exact le_rfl
  refine hstep.trans ?_
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hstep₂ : (∑ χ : PrimitiveUpTo D, ∑ q ∈ Finset.Icc 1 D,
      (q.totient : ℝ)⁻¹*(if χ.1.val∣q then f χ else 0))  ≤ 
      ∑ χ : PrimitiveUpTo D, f χ*((χ.1.val.totient : ℝ)⁻¹*totientWeightSum D) := by
    apply Finset.sum_le_sum
    intro χ hχ
    have heq : (∑ q ∈ Finset.Icc 1 D, (q.totient : ℝ)⁻¹*(if χ.1.val∣q then f χ else 0)) =
        f χ*(∑ q ∈ Finset.Icc 1 D, if χ.1.val∣q then (q.totient : ℝ)⁻¹ else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs <;> ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (totient_multiples_weight_le D χ.1.val (Nat.pos_of_ne_zero χ.2.property.1)) (hf χ)
  refine hstep₂.trans_eq ?_
  rw [primitiveErrorMean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  dsimp [f]
  split_ifs <;> ring

lemma imprimitive_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℕ) :
    ‖primeCharacterError χ X‖ ≤ ‖primeCharacterError χ.primitiveCharacter X‖+
      (q+1 : ℝ)*(Nat.log 2 X+1 : ℝ)*Real.log (X+1 : ℝ) := by
  have hh := imprimitive_error_bound χ X
  change ‖primeCharacterError χ X-primeCharacterError χ.primitiveCharacter X‖ ≤ _ at hh
  have ht : ‖primeCharacterError χ X‖ ≤ ‖primeCharacterError χ X-primeCharacterError χ.primitiveCharacter X‖+
      ‖primeCharacterError χ.primitiveCharacter X‖ := by
    simpa using norm_add_le (primeCharacterError χ X-primeCharacterError χ.primitiveCharacter X) (primeCharacterError χ.primitiveCharacter X)
  linarith

lemma characterErrorMean_le_induced (R D X : ℕ) :
    characterErrorMean R D X ≤ inducedErrorMean R D X+
      (D+1 : ℝ)^2*(Nat.log 2 X+1 : ℝ)*Real.log (X+1 : ℝ) := by
  let E : ℕ → ℝ := fun q => (q+1 : ℝ)*(Nat.log 2 X+1 : ℝ)*Real.log (X+1 : ℝ)
  have hE (q : ℕ) : 0 ≤ E q := by
    dsimp [E]
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ X+1 by linarith [Nat.cast_nonneg (α := ℝ) X])
    positivity
  have hstep : characterErrorMean R D X ≤ inducedErrorMean R D X+∑ q ∈ Finset.Icc 1 D, E q := by
    unfold characterErrorMean inducedErrorMean
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro q hq
    have hq0 : 0<q := by have hh := (Finset.mem_Icc.mp hq).1; omega
    letI : NeZero q := ⟨hq0.ne'⟩
    by_cases hg : GoodModulus R q
    · simp only [if_pos hg]
      have hh : (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError χ X‖) ≤ 
          (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError χ.primitiveCharacter X‖)+(q.totient : ℝ)*E q := by
        have hi := Finset.sum_le_sum (s := Finset.univ) (fun (χ : DirichletCharacter ℂ q) hχ => imprimitive_norm_le χ X)
        rw [Finset.sum_add_distrib] at hi
        have hc : Fintype.card (DirichletCharacter ℂ q)=q.totient := by
          simpa [Nat.card_eq_fintype_card] using card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
        simpa only [Finset.sum_const,Finset.card_univ,hc,nsmul_eq_mul] using hi
      have hmul := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹)
      have hφ : (q.totient : ℝ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr hq0).ne'
      simpa [mul_add,←mul_assoc,hφ] using hmul
    · simp only [if_neg hg,zero_add]
      exact hE q
  refine hstep.trans (add_le_add le_rfl ?_)
  have hlog : 0 ≤ Real.log (X+1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X])
  calc
    _  ≤  ∑ _q ∈ Finset.Icc 1 D, (D+1 : ℝ)*(Nat.log 2 X+1 : ℝ)*Real.log (X+1 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqD : (q : ℝ) ≤ D := by exact_mod_cast (Finset.mem_Icc.mp hq).2
      dsimp [E]
      gcongr
    _ = (D : ℝ)*((D+1 : ℝ)*(Nat.log 2 X+1 : ℝ)*Real.log (X+1 : ℝ)) := by simp
    _ ≤ (D+1 : ℝ)*((D+1 : ℝ)*(Nat.log 2 X+1 : ℝ)*Real.log (X+1 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (hE D)
    _ = _ := by ring

lemma characterErrorMean_conductor_bound (R D X : ℕ) :
    characterErrorMean R D X ≤ totientWeightSum D*primitiveErrorMean R D X+
      (D+1 : ℝ)^2*(Nat.log 2 X+1 : ℝ)*Real.log (X+1 : ℝ) := by
  exact (characterErrorMean_le_induced R D X).trans (add_le_add (inducedErrorMean_le R D X) le_rfl)

end
end MaynardDevelopment
end

/- PerronShift -/
section

open scoped Topology
open Complex MeasureTheory Set Filter
namespace MaynardDevelopment
noncomputable section

lemma norm_weighted_horizontal_integral_le {a b T X A : ℝ} (hab : a≤b) (hlen : b-a≤1)
    (hT : 1≤T) (hX : 1≤X) (hA : 0≤A) (F : ℂ → ℂ) {u : ℝ} (hu : |u|=T)
    (hF : ∀ x ∈ Icc a b, ‖F (x+u*I)‖ ≤ A*(1+|u|)) :
    ‖∫ x : ℝ in a..b, (X : ℂ)^(x+u*I)*F (x+u*I)*perronKernel (x+u*I)‖ ≤ 2*A*X^b/T := by
  have hX0 : 0<X := by linarith
  have hT0 : 0<T := by linarith
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu; linarith
  have hk (x : ℝ) : ‖perronKernel (x+u*I)‖ ≤ 1/T^2 := by
    have hh := perronKernel_norm_le_inv_sq (σ := x) hu0
    rwa [← sq_abs u, hu] at hh
  have hbound (x : ℝ) (hx : x ∈ Icc a b) :
      ‖(X : ℂ)^(x+u*I)*F (x+u*I)*perronKernel (x+u*I)‖ ≤ 2*A*X^b/T := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    have hp := Real.rpow_le_rpow_of_exponent_le hX hx.2
    have hf : ‖F (x+u*I)‖ ≤ 2*A*T := by have hh := hF x hx; rw [hu] at hh; nlinarith
    calc
      _ ≤ X^b*(2*A*T)*(1/T^2) := mul_le_mul (mul_le_mul hp hf (norm_nonneg _) (Real.rpow_nonneg hX0.le _))
        (hk x) (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := 2*A*X^b/T)
    (fun x hx => hbound x (by rw [uIoc_of_le hab] at hx; exact ⟨hx.1.le,hx.2⟩))
  refine hh.trans ?_
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  exact mul_le_of_le_one_right (by positivity) hlen

lemma weighted_perron_differentiableOn {a b T X : ℝ} (ha : 1/2≤a) (hab : a≤b) (hX : 0<X)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (uIcc a b ×ℂ uIcc (-T) T)) :
    DifferentiableOn ℂ (fun s => (X : ℂ)^s*F s*perronKernel s) (uIcc a b ×ℂ uIcc (-T) T) := by
  have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  simp only [Complex.cpow_def_of_ne_zero hX0, perronKernel]
  apply DifferentiableOn.mul
  · exact (by fun_prop : Differentiable ℂ (fun s => Complex.exp (Complex.log (X : ℂ)*s))).differentiableOn.mul hF
  · apply DifferentiableOn.div (differentiable_const (1 : ℂ)).differentiableOn (by fun_prop)
    intro s hs
    have hre : a≤s.re := by have hh := hs.1; rw [uIcc_of_le hab] at hh; exact hh.1
    apply mul_ne_zero <;> intro h <;> have hh := congrArg Complex.re h <;> simp at hh <;> linarith

lemma norm_shifted_vertical_integral_le {a b T X A : ℝ} (ha : 1/2≤a) (hab : a≤b) (hlen : b-a≤1)
    (hT : 1≤T) (hX : 1≤X) (hA : 0≤A) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (uIcc a b ×ℂ uIcc (-T) T))
    (hbnd : ∀ z ∈ uIcc a b ×ℂ uIcc (-T) T, ‖F z‖ ≤ A*(1+|z.im|)) :
    ‖∫ t : ℝ in -T..T, (X : ℂ)^(b+t*I)*F (b+t*I)*perronKernel (b+t*I)‖ ≤
      16*X^a*A*Real.log (1+T)+4*A*X^b/T := by
  have hX0 : 0<X := by linarith
  have hT0 : 0≤T := by linarith
  have hrect (x t : ℝ) (hx : x ∈ Icc a b) (ht : t ∈ Icc (-T) T) :
      (x : ℂ)+t*I ∈ uIcc a b ×ℂ uIcc (-T) T := by
    simp only [mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, mul_one, zero_add, uIcc_of_le hab, uIcc_of_le (by linarith : -T≤T)]
    exact ⟨hx,ht⟩
  have h₁ := norm_weighted_vertical_integral_le ha hT0 hX0 hA F (by
    intro t ht
    simpa using hbnd ((a : ℂ)+t*I) (hrect a t ⟨le_rfl,hab⟩ ht))
  have h₂ := norm_weighted_horizontal_integral_le hab hlen hT hX hA F
    (u := -T) (by rw [abs_neg, abs_of_nonneg hT0]) (by
      intro x hx
      simpa using hbnd ((x : ℂ)+(-T : ℝ)*I) (hrect x (-T) hx ⟨le_rfl,by linarith⟩))
  have h₃ := norm_weighted_horizontal_integral_le hab hlen hT hX hA F
    (u := T) (abs_of_nonneg hT0) (by
      intro x hx
      simpa using hbnd ((x : ℂ)+T*I) (hrect x T hx ⟨by linarith,le_rfl⟩))
  have hh := norm_vertical_integral_le_horizontal (fun s => (X : ℂ)^s*F s*perronKernel s)
    (weighted_perron_differentiableOn ha hab hX0 F hF)
  simp only [Complex.ofReal_neg] at h₂
  dsimp only at hh
  refine hh.trans ?_
  calc
    _ ≤ (16*X^a*A*Real.log (1+T))+(2*A*X^b/T)+(2*A*X^b/T) := add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

/-- Quantitative smoothed Perron estimate from an analytic, polynomially bounded rectangle. -/
theorem smoothed_perron_shift_bound {a b T X A : ℝ} (ha : 1/2≤a) (hab : a≤b) (hlen : b-a≤1)
    (hT : 1≤T) (hX : 1≤X) (hA : 0≤A) {f : ℕ → ℂ} (hf0 : f 0=0) (hf : LSeriesSummable f b)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (uIcc a b ×ℂ uIcc (-T) T))
    (hbnd : ∀ z ∈ uIcc a b ×ℂ uIcc (-T) T, ‖F z‖ ≤ A*(1+|z.im|))
    (heq : ∀ t ∈ Icc (-T) T, F (b+t*I)=LSeries f (b+t*I)) :
    ‖∑' n : ℕ, f n*triangleCut ((n : ℝ)/X)‖ ≤
      16*X^a*A*Real.log (1+T)+(4*A+2*absoluteDirichletSum f b)*X^b/T := by
  have hb0 : 0<b := by linarith
  have hX0 : 0<X := by linarith
  have hT0 : 0<T := by linarith
  have hmain := norm_shifted_vertical_integral_le ha hab hlen hT hX hA F hF hbnd
  have heqI : (∫ t : ℝ in -T..T, (X : ℂ)^(b+t*I)*F (b+t*I)*perronKernel (b+t*I)) =
      ∫ t : ℝ in -T..T, perronIntegrand f X (b+t*I) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith : -T≤T)] at ht
    dsimp only [perronIntegrand]
    rw [heq t ht]
  rw [heqI] at hmain
  have htail := perronIntegrand_tail_bound hb0 hX0 hT0 hf
  have hnorm : ‖∫ t : ℝ, perronIntegrand f X (b+t*I)‖ ≤
      16*X^a*A*Real.log (1+T)+(4*A+2*absoluteDirichletSum f b)*X^b/T := by
    have hh : ‖∫ t : ℝ, perronIntegrand f X (b+t*I)‖ ≤
        ‖(∫ t : ℝ, perronIntegrand f X (b+t*I))-(∫ t : ℝ in -T..T, perronIntegrand f X (b+t*I))‖+
        ‖∫ t : ℝ in -T..T, perronIntegrand f X (b+t*I)‖ := by
      simpa using norm_add_le ((∫ t : ℝ, perronIntegrand f X (b+t*I))-(∫ t : ℝ in -T..T, perronIntegrand f X (b+t*I)))
        (∫ t : ℝ in -T..T, perronIntegrand f X (b+t*I))
    refine hh.trans ((add_le_add htail hmain).trans_eq ?_)
    ring
  rw [smoothed_perron hb0 hX0 hf0 hf, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0<1/(2*Real.pi))]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans hnorm
  apply (div_le_one (by positivity : 0<2*Real.pi)).mpr
  linarith [Real.pi_gt_three]

end
end MaynardDevelopment
end

/- SmallConductorSmooth -/
section

open scoped Topology
open Complex MeasureTheory Set Filter
namespace MaynardDevelopment
noncomputable section

def smoothedPrimeError {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℝ) : ℂ :=
  ∑' n : ℕ, primeErrorCoeff χ n*triangleCut ((n : ℝ)/X)

def stripAmplitude (Q : ℕ) (T : ℝ) : ℝ := 2000000000000*(Lheight (Q^2) (T+1))^2+5

lemma stripAmplitude_nonneg (Q : ℕ) (T : ℝ) : 0 ≤ stripAmplitude Q T := by unfold stripAmplitude; positivity

/-- Explicit smoothed character-sum estimate from the exception-free region. -/
theorem smoothedPrimeError_bound {q Q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hqQ : q≤Q) (hNP : NoPageZero Q χ) {T X σ : ℝ} (hT : 1≤T) (hX : 1≤X)
    (hσ : 1<σ) (hση : σ≤1+stripWidth Q T) :
    ‖smoothedPrimeError χ X‖ ≤
      16*X^(1-stripWidth Q T)*stripAmplitude Q T*Real.log (1+T)+
        (4*stripAmplitude Q T+1024/(σ-1))*X^σ/T := by
  let η := stripWidth Q T
  have hη : 0<η := stripWidth_pos Q T
  have hηb : η≤1/100 := stripWidth_le Q T
  have hσ2 : σ≤2 := by change σ≤1+η at hση; linarith
  have hrect (s : ℂ) (hs : s ∈ uIcc (1-η) σ ×ℂ uIcc (-T) T) : |s.re-1|≤η ∧ |s.im|≤T := by
    have hre := hs.1
    have him := hs.2
    rw [uIcc_of_le (by linarith : 1-η≤σ)] at hre
    rw [uIcc_of_le (by linarith : -T≤T)] at him
    rw [abs_le,abs_le]
    change σ≤1+η at hση
    exact ⟨⟨by linarith [hre.1],by linarith [hre.2]⟩,him⟩
  have hdiff : DifferentiableOn ℂ (primeErrorAnalytic χ) (uIcc (1-η) σ ×ℂ uIcc (-T) T) := by
    intro s hs
    obtain ⟨hre,him⟩ := hrect s hs
    have hsre := abs_le.mp hre
    apply (primeErrorAnalytic_differentiableAt χ (by linarith : 0<s.re) ?_).differentiableWithinAt
    apply noPageZero_strip χ hqQ hNP (show 0≤T+1 by linarith)
    · have heq : Lscale (Q^2) (T+1)/100=10*η := by dsimp [η,stripWidth]; ring
      rw [heq]
      linarith
    · linarith
  have hbound := smoothed_perron_shift_bound (a := 1-η) (b := σ) (T := T) (X := X)
    (A := stripAmplitude Q T) (by linarith) (by linarith) (by change σ≤1+η at hση; linarith)
    hT hX (stripAmplitude_nonneg Q T) (primeErrorCoeff_zero χ)
    (primeErrorCoeff_LSeriesSummable χ (by simpa using hσ)) (primeErrorAnalytic χ) hdiff
    (by
      intro s hs
      obtain ⟨hre,him⟩ := hrect s hs
      exact primeErrorAnalytic_norm_bound χ hqQ hNP (by linarith) hre him)
    (by
      intro t ht
      exact primeErrorAnalytic_eq_LSeries χ (by simpa using hσ))
  change ‖smoothedPrimeError χ X‖ ≤ _ at hbound
  refine hbound.trans ?_
  have habs := absoluteDirichletSum_primeError_le χ hσ hσ2
  have hh : 4*stripAmplitude Q T+2*absoluteDirichletSum (primeErrorCoeff χ) σ ≤
      4*stripAmplitude Q T+1024/(σ-1) := by calc
        _ ≤ 4*stripAmplitude Q T+2*(512/(σ-1)) := by linarith
        _ = _ := by ring
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh
    (Real.rpow_nonneg (by linarith : 0≤X) σ)) (by linarith : 0≤T)

end
end MaynardDevelopment
end

/- SmoothExponent -/
section

open scoped Topology
open Complex Set Filter
namespace MaynardDevelopment
noncomputable section

lemma height_exp_bound {Q : ℕ} {y : ℝ} (hy : 1≤y) (hQ : Real.log Q≤y) :
    Lheight (Q^2) (Real.exp y+1) ≤ 8*y := by
  have he : 1≤Real.exp y := Real.one_le_exp (by linarith)
  have hlog : Real.log (Real.exp y+4) ≤ y+4 := by
    have hh := Real.log_le_log (by positivity : 0<Real.exp y+4) (show Real.exp y+4 ≤ 5*Real.exp y by linarith)
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero y), Real.log_exp] at hh
    have hl5 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<5)
    linarith
  simp only [Lheight, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat,
    abs_of_pos (by positivity : 0<Real.exp y+1)]
  rw [show Real.exp y+1+3=Real.exp y+4 by ring]
  linarith

lemma stripWidth_mul_exp_parameter {Q : ℕ} {y : ℝ} (hy : 1≤y) (hQ : Real.log Q≤y) :
    1/10000000000 ≤ stripWidth Q (Real.exp y)*y := by
  have hh := height_exp_bound hy hQ
  have heq := stripWidth_mul_height Q (Real.exp y)
  have hp := stripWidth_pos Q (Real.exp y)
  nlinarith

lemma inv_sq_le_stripWidth {Q : ℕ} {y : ℝ} (hy : 10000000000≤y) (hQ : Real.log Q≤y) :
    1/y^2 ≤ stripWidth Q (Real.exp y) := by
  have hy0 : 0<y := by linarith
  have hh := stripWidth_mul_exp_parameter (Q := Q) (by linarith : 1≤y) hQ
  apply (div_le_iff₀ (sq_pos_of_pos hy0)).mpr
  nlinarith

lemma stripAmplitude_exp_bound {Q : ℕ} {y : ℝ} (hy : 1≤y) (hQ : Real.log Q≤y) :
    stripAmplitude Q (Real.exp y) ≤ 200000000000000*y^2 := by
  have hh := height_exp_bound hy hQ
  have hH := Lheight_ge_one (Q^2) (Real.exp y+1)
  have hsq := pow_le_pow_left₀ (by linarith : 0≤Lheight (Q^2) (Real.exp y+1)) hh 2
  unfold stripAmplitude
  nlinarith

lemma log_one_add_exp_le {y : ℝ} (hy : 1≤y) : Real.log (1+Real.exp y) ≤ 2*y := by
  have he : 1≤Real.exp y := Real.one_le_exp (by linarith)
  have hh := Real.log_le_log (by positivity : 0<1+Real.exp y) (show 1+Real.exp y≤2*Real.exp y by linarith)
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero y), Real.log_exp] at hh
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  linarith

/-- A quantitative exponentially decaying smoothed error, uniform up to logarithmic conductor. -/
theorem smoothedPrimeError_exp_bound {q Q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hqQ : q≤Q) (hNP : NoPageZero Q χ) {y : ℝ} (hy : 10000000000≤y) (hQ : Real.log Q≤y) :
    ‖smoothedPrimeError χ (Real.exp (y^2))‖ ≤
      10000000000000000*Real.exp (y^2)*y^3*Real.exp (-y/10000000000) := by
  have hy0 : 0<y := by linarith
  have hy1 : 1≤y := by linarith
  have hT : 1≤Real.exp y := Real.one_le_exp hy0.le
  have hX : 1≤Real.exp (y^2) := Real.one_le_exp (sq_nonneg y)
  let σ : ℝ := 1+1/y^2
  let η : ℝ := stripWidth Q (Real.exp y)
  let A : ℝ := stripAmplitude Q (Real.exp y)
  have hσ : 1<σ := by
    dsimp [σ]
    have hh : 0<1/y^2 := by positivity
    linarith
  have hση : σ≤1+η := by dsimp [σ,η]; linarith [inv_sq_le_stripWidth hy hQ]
  have hh := smoothedPrimeError_bound χ hqQ hNP hT hX hσ hση
  have hA : A≤200000000000000*y^2 := stripAmplitude_exp_bound hy1 hQ
  have hA0 : 0≤A := stripAmplitude_nonneg Q (Real.exp y)
  have hlog := log_one_add_exp_le hy1
  have hlog0 : 0≤Real.log (1+Real.exp y) := Real.log_nonneg (by linarith [Real.exp_pos y])
  have hηy := stripWidth_mul_exp_parameter (Q := Q) hy1 hQ
  have hpower : (Real.exp (y^2))^(1-η) ≤ Real.exp (y^2)*Real.exp (-y/10000000000) := by
    rw [← Real.exp_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change 1/10000000000≤η*y at hηy
    nlinarith
  have hpowerσ : (Real.exp (y^2))^σ ≤ 3*Real.exp (y^2) := by
    rw [← Real.exp_mul]
    have hid : y^2*σ=y^2+1 := by dsimp [σ]; field_simp
    rw [hid,Real.exp_add]
    nlinarith [Real.exp_one_lt_three,Real.exp_pos (y^2)]
  have hsig : 1024/(σ-1)=1024*y^2 := by dsimp [σ]; field_simp <;> ring
  have htail : 1/Real.exp y ≤ Real.exp (-y/10000000000) := by
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    linarith
  change ‖smoothedPrimeError χ (Real.exp (y^2))‖ ≤
    16*(Real.exp (y^2))^(1-η)*A*Real.log (1+Real.exp y)+(4*A+1024/(σ-1))*(Real.exp (y^2))^σ/Real.exp y at hh
  rw [hsig] at hh
  have hmain : 16*(Real.exp (y^2))^(1-η)*A*Real.log (1+Real.exp y) ≤
      6400000000000000*Real.exp (y^2)*y^3*Real.exp (-y/10000000000) := by
    calc
      _ ≤ 16*(Real.exp (y^2)*Real.exp (-y/10000000000))*(200000000000000*y^2)*(2*y) := by
        gcongr
      _ = _ := by ring
  have hsecond : (4*A+1024*y^2)*(Real.exp (y^2))^σ/Real.exp y ≤
      3000000000000000*Real.exp (y^2)*y^3*Real.exp (-y/10000000000) := by
    have hAA : 4*A+1024*y^2 ≤ 1000000000000000*y^2 := by nlinarith [sq_nonneg y]
    calc
      _ = (4*A+1024*y^2)*(Real.exp (y^2))^σ*(1/Real.exp y) := by ring
      _ ≤ (1000000000000000*y^2)*(3*Real.exp (y^2))*Real.exp (-y/10000000000) := by
        gcongr
      _ ≤ _ := by
        have hpow : y^2 ≤ y^3 := by nlinarith [sq_nonneg (y-1)]
        have hm := mul_le_mul_of_nonneg_right hpow
          (show 0≤3000000000000000*Real.exp (y^2)*Real.exp (-y/10000000000) by positivity)
        nlinarith
  refine hh.trans ?_
  have hepos : 0≤Real.exp (y^2)*y^3*Real.exp (-y/10000000000) := by positivity
  nlinarith

end
end MaynardDevelopment
end

/- SmoothLogSaving -/
section

open scoped Topology
open Complex Set Filter
namespace MaynardDevelopment
noncomputable section

lemma exp_smoothing_eventually_le (k : ℕ) :
    ∀ᶠ y : ℝ in atTop, 10000000000000000*y^(2*k+3)*Real.exp (-y/10000000000) ≤ 1 := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2*k+3 : ℕ)
    (1/10000000000) (by norm_num)).const_mul (10000000000000000 : ℝ)
  have hh := ht.eventually (eventually_lt_nhds (show (10000000000000000 : ℝ)*0<1 by norm_num))
  filter_upwards [hh] with y hy
  have heq : -(1/10000000000 : ℝ)*y = -y/10000000000 := by ring
  simpa only [Real.rpow_natCast, heq, mul_assoc] using hy.le

/-- Uniform arbitrary logarithmic savings for the smoothed sum, excluding the Page exception. -/
theorem smoothedPrimeError_log_saving (k : ℕ) :
    ∃ X₀ : ℝ, 1≤X₀ ∧ ∀ (q Q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ),
      X₀≤X → q≤Q → Real.log Q≤Real.sqrt (Real.log X) → NoPageZero Q χ →
      ‖smoothedPrimeError χ X‖ ≤ X/(Real.log X)^k := by
  obtain ⟨B,hB⟩ := eventually_atTop.mp (exp_smoothing_eventually_le k)
  let Y : ℝ := max B 10000000000
  have hY : 10000000000≤Y := le_max_right _ _
  have hY0 : 0≤Y := by linarith
  refine ⟨Real.exp (Y^2), Real.one_le_exp (sq_nonneg _), ?_⟩
  intro q Q hq χ X hX hqQ hQ hNP
  have hX1 : 1≤X := (Real.one_le_exp (sq_nonneg _)).trans hX
  have hX0 : 0<X := by linarith
  have hlog : Y^2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos (Y^2)) hX
    simpa using hh
  let y := Real.sqrt (Real.log X)
  have hyY : Y≤y := Real.le_sqrt_of_sq_le hlog
  have hy : 10000000000≤y := hY.trans hyY
  have hy0 : 0<y := by linarith
  have hyB : B≤y := (le_max_left _ _).trans hyY
  have hybound := hB y hyB
  have heq : y^2=Real.log X := Real.sq_sqrt (Real.log_nonneg hX1)
  have hXeq : Real.exp (y^2)=X := by rw [heq,Real.exp_log hX0]
  have hh := smoothedPrimeError_exp_bound χ hqQ hNP hy hQ
  rw [hXeq] at hh
  refine hh.trans ?_
  apply (le_div_iff₀ (pow_pos (by rw [← heq]; positivity : 0<Real.log X) k)).mpr
  rw [← heq]
  have hpow : y^3*(y^2)^k=y^(2*k+3) := by rw [← pow_mul,← pow_add]; congr 1; omega
  have hmul := mul_le_mul_of_nonneg_left hybound hX0.le
  calc
    _ = X*(10000000000000000*y^(2*k+3)*Real.exp (-y/10000000000)) := by rw [← hpow]; ring
    _ ≤ X := by simpa using hmul

end
end MaynardDevelopment
end

/- Unsmoothing -/
section

open scoped BigOperators Topology
open Complex Set Filter
namespace MaynardDevelopment
noncomputable section

def weightedHead (f : ℕ → ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.Icc 1 N, f n*((N-n : ℕ) : ℂ)

lemma smoothed_sum_nat {f : ℕ → ℂ} (hf0 : f 0=0) {N : ℕ} (hN : 0<N) :
    (∑' n : ℕ, f n*triangleCut ((n : ℝ)/N)) = ∑ n ∈ Finset.Icc 1 N, f n*triangleCut ((n : ℝ)/N) := by
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n=0
  · simp [hn0,hf0]
  have hnN : N<n := by simp only [Finset.mem_Icc] at hn; omega
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hr : (1 : ℝ) ≤ (n : ℝ)/N := (le_div_iff₀ hN0).mpr (by simpa using (show (N : ℝ)≤n by exact_mod_cast hnN.le))
  simp [triangleCut,max_eq_right (by linarith : 1-(n : ℝ)/N≤0)]

lemma weightedHead_eq_smoothed {f : ℕ → ℂ} (hf0 : f 0=0) {N : ℕ} (hN : 0<N) :
    weightedHead f N = (N : ℂ)*(∑' n : ℕ, f n*triangleCut ((n : ℝ)/N)) := by
  rw [smoothed_sum_nat hf0 hN, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN := (Finset.mem_Icc.mp hn).2
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hr : (n : ℝ)/N≤1 := (div_le_one hN0).mpr (by exact_mod_cast hnN)
  rw [triangleCut, max_eq_left (by linarith : (0 : ℝ)≤1-(n : ℝ)/N), Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast, Nat.cast_sub hnN]
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

lemma weightedHead_difference (f : ℕ → ℂ) (N h : ℕ) :
    weightedHead f (N+h)-weightedHead f N = (h : ℂ)*(∑ n ∈ Finset.Icc 1 N, f n)+
      ∑ n ∈ Finset.Ioc N (N+h), f n*((N+h-n : ℕ) : ℂ) := by
  have hsplit : Finset.Icc 1 (N+h)=Finset.Icc 1 N ∪ Finset.Ioc N (N+h) := by
    ext n
    simp only [Finset.mem_union,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have hdis : Disjoint (Finset.Icc 1 N) (Finset.Ioc N (N+h)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have h₁ := (Finset.mem_Icc.mp hn).2
    have h₂ := (Finset.mem_Ioc.mp hn').1
    omega
  unfold weightedHead
  rw [hsplit,Finset.sum_union hdis]
  have heq : (∑ n ∈ Finset.Icc 1 N, f n*((N+h-n : ℕ) : ℂ)) =
      (h : ℂ)*(∑ n ∈ Finset.Icc 1 N, f n)+(∑ n ∈ Finset.Icc 1 N, f n*((N-n : ℕ) : ℂ)) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hsub : N+h-n=h+(N-n) := by have hh := (Finset.mem_Icc.mp hn).2; omega
    rw [hsub,Nat.cast_add]
    ring
  rw [heq]
  ring

lemma weightedHead_difference_norm (f : ℕ → ℂ) (N h : ℕ) {B : ℝ} (hB : 0≤B)
    (hb : ∀ n ∈ Finset.Ioc N (N+h), ‖f n‖≤B) :
    (h : ℝ)*‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤ ‖weightedHead f (N+h)‖+‖weightedHead f N‖+(h : ℝ)^2*B := by
  let tail := ∑ n ∈ Finset.Ioc N (N+h), f n*((N+h-n : ℕ) : ℂ)
  have htail : ‖tail‖≤(h : ℝ)^2*B := by
    calc
      _ ≤ ∑ n ∈ Finset.Ioc N (N+h), ‖f n*((N+h-n : ℕ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc N (N+h), B*(h : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hsub : N+h-n≤h := by have hh := (Finset.mem_Ioc.mp hn).1; omega
        rw [norm_mul,Complex.norm_natCast]
        exact mul_le_mul (hb n hn) (by exact_mod_cast hsub) (Nat.cast_nonneg _) hB
      _ = _ := by simp; ring
  have hid : (h : ℂ)*(∑ n ∈ Finset.Icc 1 N, f n)=weightedHead f (N+h)-weightedHead f N-tail := by
    have hh := weightedHead_difference f N h
    dsimp [tail]
    linear_combination -hh
  have hn := norm_sub_le (weightedHead f (N+h)-weightedHead f N) tail
  have hn' := norm_sub_le (weightedHead f (N+h)) (weightedHead f N)
  have hh : (h : ℝ)*‖∑ n ∈ Finset.Icc 1 N, f n‖=‖(h : ℂ)*(∑ n ∈ Finset.Icc 1 N, f n)‖ := by simp
  rw [hh,hid]
  linarith

lemma primeError_unsmoothing {q : ℕ} (χ : DirichletCharacter ℂ q) {N h : ℕ} (hN : 0<N) (hh : 0<h) :
    (h : ℝ)*‖∑ n ∈ Finset.Icc 1 N, primeErrorCoeff χ n‖ ≤
      ((N+h : ℕ) : ℝ)*‖smoothedPrimeError χ (N+h : ℕ)‖+(N : ℝ)*‖smoothedPrimeError χ N‖+
        (h : ℝ)^2*(Real.log (N+h : ℕ)+1) := by
  have hB : 0≤Real.log (N+h : ℕ)+1 := by linarith [Real.log_natCast_nonneg (N+h)]
  have hb (n : ℕ) (hn : n ∈ Finset.Ioc N (N+h)) : ‖primeErrorCoeff χ n‖≤Real.log (N+h : ℕ)+1 := by
    have hn0 : 0<n := by have ht := (Finset.mem_Ioc.mp hn).1; omega
    have hlog := Real.log_le_log (by exact_mod_cast hn0 : (0 : ℝ)<n)
      (by exact_mod_cast (Finset.mem_Ioc.mp hn).2 : (n : ℝ)≤(N+h : ℕ))
    refine (primeErrorCoeff_norm_le χ n).trans ?_
    have hΛ := ArithmeticFunction.vonMangoldt_le_log (n := n)
    linarith
  have hi := weightedHead_difference_norm (primeErrorCoeff χ) N h hB hb
  rw [weightedHead_eq_smoothed (primeErrorCoeff_zero χ) (by omega : 0<N+h),
    weightedHead_eq_smoothed (primeErrorCoeff_zero χ) hN, norm_mul,norm_mul,
    Complex.norm_natCast,Complex.norm_natCast] at hi
  exact hi

end
end MaynardDevelopment
end

/- SharpLogSaving -/
section

open scoped BigOperators Topology
open Complex Set Filter
namespace MaynardDevelopment
noncomputable section

lemma unsmoothing_numeric (k : ℕ) {n h L R s₀ s₁ : ℝ} (hn : 0<n) (hh : 0<h) (hL : 1≤L)
    (hupper : h*L^(k+1)≤n) (hlower : n≤2*h*L^(k+1))
    (hs₀ : s₀≤n/L^(2*k+4)) (hs₁ : s₁≤2*n/L^(2*k+4))
    (hmain : h*R≤2*n*s₁+n*s₀+h^2*(3*L)) : R≤13*n/L^k := by
  have hL0 : 0<L := by linarith
  have hratio : n/L^(2*k+4) ≤ 2*h/L^k := by
    apply (div_le_div_iff₀ (pow_pos hL0 _) (pow_pos hL0 _)).mpr
    have hp : L^(k+1)≤L^(k+4) := pow_le_pow_right₀ hL (by omega)
    have hnn : n≤2*h*L^(k+4) := hlower.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    have hmul := mul_le_mul_of_nonneg_right hnn (pow_nonneg hL0.le k)
    have heq : L^(2*k+4)=L^k*L^(k+4) := by rw [← pow_add]; congr 1; omega
    rw [heq]
    nlinarith
  have htail : h*L≤n/L^k := by
    apply (le_div_iff₀ (pow_pos hL0 k)).mpr
    rw [pow_succ] at hupper
    nlinarith
  have hs₀' : s₀≤2*h/L^k := hs₀.trans hratio
  have hs₁' : s₁≤4*h/L^k := by
    have hm := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ)≤2 by norm_num)
    have heq : 2*(n/L^(2*k+4))=2*n/L^(2*k+4) := by ring
    rw [heq] at hm
    exact hs₁.trans (hm.trans_eq (by ring))
  have hm₀ := mul_le_mul_of_nonneg_left hs₀' hn.le
  have hm₁ := mul_le_mul_of_nonneg_left hs₁' (show 0≤2*n by positivity)
  have hm₂ := mul_le_mul_of_nonneg_left htail (show 0≤3*h by positivity)
  have hbound : h*R≤h*(13*n/L^k) := by
    have heq : 2*n*(4*h/L^k)+n*(2*h/L^k)+3*h*(n/L^k)=h*(13*n/L^k) := by ring
    rw [← heq]
    nlinarith
  nlinarith

lemma eventually_log_power_small (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, 1≤Real.log x ∧ 2*(Real.log x)^(k+1)≤x := by
  have ht := (Real.isLittleO_pow_exp_atTop (n := k+1)).bound (show (0 : ℝ)<1/2 by norm_num)
  have hl := Real.tendsto_log_atTop.eventually ht
  filter_upwards [hl,eventually_ge_atTop (Real.exp 1)] with x hx hx1
  have hx0 : 0<x := lt_of_lt_of_le (Real.exp_pos 1) hx1
  have hlog : 1≤Real.log x := by simpa using Real.log_le_log (Real.exp_pos 1) hx1
  simp only [Real.exp_log hx0, Real.norm_eq_abs, abs_of_pos hx0,
    abs_of_nonneg (pow_nonneg (by linarith : 0≤Real.log x) _)] at hx
  exact ⟨hlog,by linarith⟩

/-- Arbitrary logarithmic saving for prime-character sums, away from the Page exception. -/
theorem primeError_log_saving (k : ℕ) :
    ∃ N₀ : ℕ, ∀ (q Q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ),
      N₀≤N → q≤Q → Real.log Q≤Real.sqrt (Real.log N) → NoPageZero Q χ →
      ‖∑ n ∈ Finset.Icc 1 N, primeErrorCoeff χ n‖ ≤ 13*(N : ℝ)/(Real.log N)^k := by
  obtain ⟨X₀,hX₀,hSmooth⟩ := smoothedPrimeError_log_saving (2*k+4)
  obtain ⟨B,hB⟩ := eventually_atTop.mp (eventually_log_power_small k)
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt (max X₀ (max B 2))
  refine ⟨N₀,?_⟩
  intro q Q hq χ N hN hqQ hQ hNP
  have hNcast : (N₀ : ℝ)≤N := by exact_mod_cast hN
  have hNX : X₀≤(N : ℝ) := by have hh := le_max_left X₀ (max B 2); linarith
  have hNB : B≤(N : ℝ) := by have hh := (le_max_left B 2).trans (le_max_right X₀ (max B 2)); linarith
  have hN2 : (2 : ℝ)<N := by have hh := (le_max_right B 2).trans (le_max_right X₀ (max B 2)); linarith
  have hN0 : 0<N := by exact_mod_cast (show (0 : ℝ)<N by linarith)
  let L : ℝ := Real.log N
  obtain ⟨hL,hsmall⟩ := hB N hNB
  change 1≤L at hL
  change 2*L^(k+1)≤(N : ℝ) at hsmall
  have hL0 : 0<L := by linarith
  have hLp : 0<L^(k+1) := pow_pos hL0 _
  have hr : (2 : ℝ)≤(N : ℝ)/L^(k+1) := (le_div_iff₀ hLp).mpr hsmall
  let h : ℕ := ⌊(N : ℝ)/L^(k+1)⌋₊
  have hh1 : 1≤h := by
    apply Nat.le_floor
    norm_num only [Nat.cast_one]
    linarith
  have hh0 : 0<h := by omega
  have hh0r : (0 : ℝ)<h := by exact_mod_cast hh0
  have hh1r : (1 : ℝ)≤h := by exact_mod_cast hh1
  have hfloor : (h : ℝ)≤(N : ℝ)/L^(k+1) := Nat.floor_le (by positivity)
  have hfloor' : (N : ℝ)/L^(k+1)<(h : ℝ)+1 := Nat.lt_floor_add_one _
  have hupper : (h : ℝ)*L^(k+1)≤N := (le_div_iff₀ hLp).mp hfloor
  have hlower : (N : ℝ)≤2*(h : ℝ)*L^(k+1) := by
    apply (div_le_iff₀ hLp).mp
    linarith
  have hhN : h≤N := by
    have hpow : (1 : ℝ)≤L^(k+1) := one_le_pow₀ hL
    have hhN' : (h : ℝ)≤N := by nlinarith
    exact_mod_cast hhN'
  have hNh : ((N+h : ℕ) : ℝ)≤2*N := by exact_mod_cast (show N+h≤2*N by omega)
  have hNNh : (N : ℝ)≤(N+h : ℕ) := by exact_mod_cast (Nat.le_add_right N h)
  have hlog : L≤Real.log (N+h : ℕ) := Real.log_le_log (by exact_mod_cast hN0) hNNh
  have hQ' : Real.log Q≤Real.sqrt (Real.log (N+h : ℕ)) := hQ.trans (Real.sqrt_le_sqrt hlog)
  have hs₀ := hSmooth q Q χ N hNX hqQ hQ hNP
  have hs₁ := hSmooth q Q χ (N+h : ℕ) (hNX.trans hNNh) hqQ hQ' hNP
  have hs₁' : ‖smoothedPrimeError χ (N+h : ℕ)‖≤2*(N : ℝ)/L^(2*k+4) := by
    refine hs₁.trans ?_
    calc
      _ ≤ ((N+h : ℕ) : ℝ)/L^(2*k+4) := div_le_div_of_nonneg_left (by positivity)
        (pow_pos hL0 _) (pow_le_pow_left₀ hL0.le hlog _)
      _ ≤ _ := div_le_div_of_nonneg_right hNh (pow_nonneg hL0.le _)
  have hlogB : Real.log (N+h : ℕ)+1≤3*L := by
    have hh := Real.log_le_log (by exact_mod_cast (show 0<N+h by omega) : (0 : ℝ)<(N+h : ℕ)) hNh
    rw [Real.log_mul (by norm_num) (by exact_mod_cast hN0.ne' : (N : ℝ)≠0)] at hh
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    dsimp [L] at *
    linarith
  have hmain := primeError_unsmoothing χ hN0 hh0
  have hmain' : (h : ℝ)*‖∑ n ∈ Finset.Icc 1 N, primeErrorCoeff χ n‖ ≤
      2*(N : ℝ)*‖smoothedPrimeError χ (N+h : ℕ)‖+(N : ℝ)*‖smoothedPrimeError χ N‖+(h : ℝ)^2*(3*L) := by
    refine hmain.trans ?_
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hNh (norm_nonneg _)) le_rfl)
      (mul_le_mul_of_nonneg_left hlogB (sq_nonneg _))
  exact unsmoothing_numeric k (by exact_mod_cast hN0) hh0r hL hupper hlower hs₀ hs₁' hmain'

end
end MaynardDevelopment
end

/- Vaughan -/
section

open scoped BigOperators ArithmeticFunction
namespace MaynardDevelopment
noncomputable section

/-- Cut off an arithmetic function at a fixed height. -/
def arithHead {R : Type*} [Zero R] (f : ArithmeticFunction R) (U : ℕ) : ArithmeticFunction R :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

@[simp] lemma arithHead_apply {R : Type*} [Zero R] (f : ArithmeticFunction R) (U n : ℕ) :
    arithHead f U n = if n ≤ U then f n else 0 := rfl

lemma arithTail_apply {R : Type*} [AddGroup R] (f : ArithmeticFunction R) (U n : ℕ) :
    (f - arithHead f U) n = if U < n then f n else 0 := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply]
  change f n + -(if n ≤ U then f n else 0) = _
  by_cases hn : n ≤ U
  · simp [hn, not_lt_of_ge hn]
  · simp [hn, Nat.lt_of_not_ge hn]

/-- Vaughan's identity in the ring of arithmetic functions. -/
theorem vaughan_identity (U V : ℕ) :
    ArithmeticFunction.vonMangoldt =
      arithHead (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U * ArithmeticFunction.log -
      arithHead (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U * ArithmeticFunction.zeta *
        arithHead ArithmeticFunction.vonMangoldt V + arithHead ArithmeticFunction.vonMangoldt V +
      ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        arithHead (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) * ArithmeticFunction.zeta *
        (ArithmeticFunction.vonMangoldt - arithHead ArithmeticFunction.vonMangoldt V) := by
  have hm : (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * ArithmeticFunction.zeta = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  symm
  calc
    _ = ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * ArithmeticFunction.zeta) *
        ArithmeticFunction.vonMangoldt -
        ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * ArithmeticFunction.zeta) *
        arithHead ArithmeticFunction.vonMangoldt V + arithHead ArithmeticFunction.vonMangoldt V := by
      rw [← ArithmeticFunction.zeta_mul_vonMangoldt]
      ring
    _ = _ := by rw [hm]; ring

lemma arithHead_mul_eq_zero {R : Type*} [Semiring R] (f g : ArithmeticFunction R)
    (U V n : ℕ) (hn : U * V < n) : (arithHead f U * arithHead g V) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro de hde
  have heq := (Nat.mem_divisorsAntidiagonal.mp hde).1
  simp only [arithHead_apply]
  by_cases hd : de.1 ≤ U
  · by_cases he : de.2 ≤ V
    · have hh := Nat.mul_le_mul hd he
      omega
    · simp [he]
  · simp [hd]

lemma arithHead_moebius_abs_le (U n : ℕ) :
    |arithHead (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U n| ≤ 1 := by
  rw [arithHead_apply]
  split_ifs
  · simpa only [ArithmeticFunction.intCoe_apply, ← Int.cast_abs, Int.cast_one] using
      (Int.cast_le.mpr (ArithmeticFunction.abs_moebius_le_one (n := n)) :
        ((|ArithmeticFunction.moebius n| : ℤ) : ℝ) ≤ (1 : ℤ))
  · norm_num

lemma arithHead_vonMangoldt_nonneg (V n : ℕ) :
    0 ≤ arithHead ArithmeticFunction.vonMangoldt V n := by
  rw [arithHead_apply]
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

lemma arithHead_vonMangoldt_le (V n : ℕ) :
    arithHead ArithmeticFunction.vonMangoldt V n ≤ ArithmeticFunction.vonMangoldt n := by
  rw [arithHead_apply]
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

lemma arithHead_moebius_mul_vonMangoldt_abs_le_log (U V n : ℕ) :
    |(arithHead (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
      arithHead ArithmeticFunction.vonMangoldt V) n| ≤ Real.log n := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal'
    (fun d e => arithHead (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U d *
      arithHead ArithmeticFunction.vonMangoldt V e)]
  calc
    _ ≤ ∑ d ∈ n.divisors,
        |arithHead (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U (n / d) *
          arithHead ArithmeticFunction.vonMangoldt V d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d := by
      apply Finset.sum_le_sum
      intro d _
      rw [abs_mul, abs_of_nonneg (arithHead_vonMangoldt_nonneg V d)]
      calc
        _ ≤ arithHead ArithmeticFunction.vonMangoldt V d :=
          mul_le_of_le_one_left (arithHead_vonMangoldt_nonneg V d) (arithHead_moebius_abs_le U _)
        _ ≤ _ := arithHead_vonMangoldt_le V d
    _ = _ := ArithmeticFunction.vonMangoldt_sum

end
end MaynardDevelopment
end

/- Bilinear -/
section

open scoped BigOperators

namespace MaynardDevelopment
noncomputable section

lemma sum_norm_mul_le_sqrt {ι : Type*} [Fintype ι] (u v : ι → ℂ)
    {A B : ℝ} (hA : (∑ i, ‖u i‖ ^ 2) ≤ A) (hB : (∑ i, ‖v i‖ ^ 2) ≤ B) :
    (∑ i, ‖u i * v i‖) ≤ Real.sqrt (A * B) := by
  have hA0 : 0 ≤ A := (Finset.sum_nonneg (fun _ _ => sq_nonneg _)).trans hA
  have hB0 : 0 ≤ B := (Finset.sum_nonneg (fun _ _ => sq_nonneg _)).trans hB
  apply Real.le_sqrt_of_sq_le
  simp_rw [norm_mul]
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖u i‖)
    (fun i => ‖v i‖)).trans (mul_le_mul hA hB (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hA0)

/-- A rectangular bilinear estimate from two finite frame bounds. -/
lemma frame_bilinear {ι μ ν : Type*} [Fintype ι] [Fintype μ] [Fintype ν]
    (f : ι → μ → ℂ) (g : ι → ν → ℂ) (a : μ → ℂ) (b : ν → ℂ)
    {A B : ℝ}
    (hA : (∑ i, ‖∑ m, a m * f i m‖ ^ 2) ≤ A * ∑ m, ‖a m‖ ^ 2)
    (hB : (∑ i, ‖∑ n, b n * g i n‖ ^ 2) ≤ B * ∑ n, ‖b n‖ ^ 2) :
    (∑ i, ‖∑ m, ∑ n, a m * b n * (f i m * g i n)‖) ≤
      Real.sqrt (A * B * (∑ m, ‖a m‖ ^ 2) * ∑ n, ‖b n‖ ^ 2) := by
  have heq (i : ι) : (∑ m, ∑ n, a m * b n * (f i m * g i n)) =
      (∑ m, a m * f i m) * (∑ n, b n * g i n) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  simp_rw [heq]
  convert sum_norm_mul_le_sqrt _ _ hA hB using 1 <;> congr 1 <;> ring

lemma primitiveValue_mul {Q : ℕ} (χ : PrimitiveUpTo Q) (m n : ℕ) :
    primitiveValue χ (m * n) = primitiveValue χ m * primitiveValue χ n := by
  simp only [primitiveValue, Nat.cast_mul, map_mul]

lemma primitive_character_bilinear (Q M N U V : ℕ) (a : Fin M → ℂ) (b : Fin N → ℂ) :
    (∑ χ : PrimitiveUpTo Q,
      ‖∑ m : Fin M, ∑ n : Fin N,
        a m * b n * primitiveValue χ ((U + m.val) * (V + n.val))‖) ≤
      Real.sqrt (((M : ℝ) + 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2) *
        ((N : ℝ) + 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2) *
        (∑ m, ‖a m‖ ^ 2) * ∑ n, ‖b n‖ ^ 2) := by
  simp_rw [primitiveValue_mul]
  exact frame_bilinear _ _ a b (primitive_character_large_sieve Q U M a)
    (primitive_character_large_sieve Q V N b)

lemma inv_totient_le_of_level {q Q : ℕ} {R : ℝ}
    (hq : q ≠ 0) (hqQ : q ≤ Q) (hR : 0 < R) (hRq : R ≤ q) :
    ((q.totient : ℝ)⁻¹) ≤ (3 + Real.log Q / Real.log 2) / R := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hlog : Real.log (q : ℝ) ≤ Real.log Q := Real.log_le_log hqp (by exact_mod_cast hqQ)
  have hh := totient_ratio_log_bound q 1 hq (by decide)
  norm_num at hh
  have hbound : (q : ℝ) / q.totient ≤ 3 + Real.log Q / Real.log 2 :=
    hh.trans (by gcongr)
  apply (le_div_iff₀ hR).mpr
  calc
    ((q.totient : ℝ)⁻¹) * R ≤ ((q.totient : ℝ)⁻¹) * q := by gcongr
    _ = (q : ℝ) / q.totient := by ring
    _ ≤ _ := hbound

/-- The loss from a reciprocal-totient weight on a dyadic conductor block. -/
lemma primitive_character_bilinear_weighted (Q M N U V : ℕ) (R : ℝ) (hR : 0 < R)
    (a : Fin M → ℂ) (b : Fin N → ℂ) :
    (∑ χ : PrimitiveUpTo Q, if R ≤ (χ.1.val : ℝ) then
      ((χ.1.val.totient : ℝ)⁻¹) *
      ‖∑ m : Fin M, ∑ n : Fin N,
        a m * b n * primitiveValue χ ((U + m.val) * (V + n.val))‖ else 0) ≤
      ((3 + Real.log Q / Real.log 2) / R) *
      Real.sqrt (((M : ℝ) + 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2) *
        ((N : ℝ) + 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2) *
        (∑ m, ‖a m‖ ^ 2) * ∑ n, ‖b n‖ ^ 2) := by
  have hc : 0 ≤ (3 + Real.log (Q : ℝ) / Real.log 2) / R := by
    have : 0 ≤ Real.log (Q : ℝ) := by
      rcases Q with _ | Q
      · simp
      · apply Real.log_nonneg; exact_mod_cast (Nat.succ_le_succ (Nat.zero_le Q))
    positivity
  calc
    _ ≤ ∑ χ : PrimitiveUpTo Q, ((3 + Real.log Q / Real.log 2) / R) *
        ‖∑ m : Fin M, ∑ n : Fin N,
          a m * b n * primitiveValue χ ((U + m.val) * (V + n.val))‖ := by
      apply Finset.sum_le_sum
      intro χ _
      split_ifs with hχ
      · exact mul_le_mul_of_nonneg_right
          (inv_totient_le_of_level χ.2.property.1 (by omega) hR hχ) (norm_nonneg _)
      · positivity
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (primitive_character_bilinear Q M N U V a b) hc

lemma primitive_weighted_sum_le (Q : ℕ) (R : ℝ) (hR : 0 < R)
    (t : PrimitiveUpTo Q → ℝ) (ht : ∀ χ, 0 ≤ t χ) {B : ℝ}
    (hB : (∑ χ, t χ) ≤ B) :
    (∑ χ : PrimitiveUpTo Q, if R ≤ (χ.1.val : ℝ) then
      ((χ.1.val.totient : ℝ)⁻¹) * t χ else 0) ≤
      ((3 + Real.log Q / Real.log 2) / R) * B := by
  have hc : 0 ≤ (3 + Real.log (Q : ℝ) / Real.log 2) / R := by
    have : 0 ≤ Real.log (Q : ℝ) := by
      rcases Q with _ | Q
      · simp
      · apply Real.log_nonneg; exact_mod_cast (Nat.succ_le_succ (Nat.zero_le Q))
    positivity
  calc
    _ ≤ ∑ χ : PrimitiveUpTo Q, ((3 + Real.log Q / Real.log 2) / R) * t χ := by
      apply Finset.sum_le_sum
      intro χ _
      split_ifs with hχ
      · exact mul_le_mul_of_nonneg_right
          (inv_totient_le_of_level χ.2.property.1 (by omega) hR hχ) (ht χ)
      · exact mul_nonneg hc (ht χ)
    _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hB hc

end
end MaynardDevelopment
end

/- CharacterMean -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section

/-- The reciprocal-totient weighted mean over primitive characters with conductor at least `R`. -/
def primitiveMean {Q : ℕ} (R : ℝ) (f : PrimitiveUpTo Q → ℂ) : ℝ :=
  ∑ χ : PrimitiveUpTo Q, if R ≤ (χ.1.val : ℝ) then ((χ.1.val.totient : ℝ)⁻¹) * ‖f χ‖ else 0

lemma primitiveMean_nonneg {Q : ℕ} (R : ℝ) (f : PrimitiveUpTo Q → ℂ) :
    0 ≤ primitiveMean R f := by
  apply Finset.sum_nonneg
  intro χ _
  split_ifs <;> positivity

@[simp] lemma primitiveMean_zero (Q : ℕ) (R : ℝ) :
    primitiveMean R (fun _ : PrimitiveUpTo Q => 0) = 0 := by simp [primitiveMean]

lemma primitiveMean_sum {Q : ℕ} {α : Type*} (R : ℝ) (s : Finset α)
    (f : α → PrimitiveUpTo Q → ℂ) :
    primitiveMean R (fun χ => ∑ j ∈ s, f j χ) ≤ ∑ j ∈ s, primitiveMean R (f j) := by
  unfold primitiveMean
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro χ _
  by_cases hχ : R ≤ (χ.1.val : ℝ)
  · simp only [hχ, if_true, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
  · simp [hχ]

lemma primitiveMean_add {Q : ℕ} (R : ℝ) (f g : PrimitiveUpTo Q → ℂ) :
    primitiveMean R (fun χ => f χ + g χ) ≤ primitiveMean R f + primitiveMean R g := by
  unfold primitiveMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro χ _
  split_ifs
  · rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
  · simp

lemma primitiveMean_sub {Q : ℕ} (R : ℝ) (f g : PrimitiveUpTo Q → ℂ) :
    primitiveMean R (fun χ => f χ - g χ) ≤ primitiveMean R f + primitiveMean R g := by
  unfold primitiveMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro χ _
  split_ifs
  · rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
  · simp

lemma primitiveMean_le_card_mul {Q : ℕ} (R : ℝ) {f : PrimitiveUpTo Q → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ χ, R ≤ (χ.1.val : ℝ) → ‖f χ‖ ≤ C) :
    primitiveMean R f ≤ (Q + 1 : ℝ) ^ 2 * C := by
  have hφ (χ : PrimitiveUpTo Q) : ((χ.1.val.totient : ℝ)⁻¹) ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero χ.2.property.1)
  calc
    _ ≤ ∑ _χ : PrimitiveUpTo Q, C := by
      apply Finset.sum_le_sum
      intro χ _
      split_ifs with hh
      · calc
          _ ≤ ‖f χ‖ := mul_le_of_le_one_left (norm_nonneg _) (hφ χ)
          _ ≤ _ := hf χ hh
      · exact hC
    _ = (Fintype.card (PrimitiveUpTo Q) : ℝ) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast primitiveUpTo_card_le Q) hC

lemma primitive_nonprincipal_of_one_lt_level {Q : ℕ} (χ : PrimitiveUpTo Q)
    (hq : 1 < χ.1.val) : χ.2.val ≠ 1 := by
  intro hh
  have hc := χ.2.property.2
  change χ.2.val.conductor = χ.1.val at hc
  rw [hh, DirichletCharacter.conductor_one χ.2.property.1] at hc
  omega

end
end MaynardDevelopment
end

/- TypeOneGlobal -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section

lemma convolution_character_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X : ℕ) (f g : ArithmeticFunction ℝ) :
    (∑ n ∈ Finset.Icc 1 X, (((f * g) n : ℝ) : ℂ) * χ (n : ZMod q)) =
      ∑ d ∈ Finset.Icc 1 X, (f d : ℂ) * χ (d : ZMod q) *
        ∑ e ∈ Finset.Icc 1 (X / d), (g e : ℂ) * χ (e : ZMod q) := by
  refine (sum_convolution_map_weighted Complex.ofRealHom X f g (fun n => χ (n : ZMod q))).trans ?_
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  change (f d : ℂ) * (g e : ℂ) * χ ((d * e : ℕ) : ZMod q) = _
  simp only [Nat.cast_mul, map_mul]
  ring

lemma zeta_character_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) n : ℝ) : ℂ) *
      χ (n : ZMod q)) = ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) := by
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hn0]

lemma convolution_zeta_character_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (X U : ℕ) (f : ArithmeticFunction ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n ∈ Finset.Icc 1 X, |f n| ≤ C) (hf0 : ∀ n, U < n → f n = 0) :
    ‖∑ n ∈ Finset.Icc 1 X, (((f * ArithmeticFunction.zeta) n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
      2 * (U : ℝ) * q * C := by
  rw [convolution_character_sum]
  simp only [zeta_character_sum]
  have hh : ‖∑ d ∈ Finset.Icc 1 X, (f d : ℂ) * χ (d : ZMod q) *
      ∑ e ∈ Finset.Icc 1 (X / d), χ (e : ZMod q)‖ ≤ (U : ℝ) * (C * (2 * q)) := by
    apply norm_sum_Icc_of_support (by positivity)
    · intro n hn _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hprod : |f n| * ‖χ (n : ZMod q)‖ ≤ C := by
        exact (mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _)).trans (hf n hn)
      exact mul_le_mul hprod (character_sum_Icc_le χ hχ (X / n)) (norm_nonneg _) hC
    · intro n _ hn
      rw [hf0 n hn, Complex.ofReal_zero, zero_mul, zero_mul]
  convert hh using 1 <;> ring

lemma convolution_log_character_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (X U : ℕ) (f : ArithmeticFunction ℝ)
    (hf : ∀ n, |f n| ≤ 1) (hf0 : ∀ n, U < n → f n = 0) :
    ‖∑ n ∈ Finset.Icc 1 X, (((f * ArithmeticFunction.log) n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
      4 * (U : ℝ) * q * Real.log (X + 1 : ℝ) := by
  rw [convolution_character_sum]
  have hlogX : 0 ≤ Real.log (X + 1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X])
  have hh : ‖∑ d ∈ Finset.Icc 1 X, (f d : ℂ) * χ (d : ZMod q) *
      ∑ e ∈ Finset.Icc 1 (X / d), (ArithmeticFunction.log e : ℂ) * χ (e : ZMod q)‖ ≤
      (U : ℝ) * (4 * q * Real.log (X + 1 : ℝ)) := by
    apply norm_sum_Icc_of_support (by positivity)
    · intro n _ _
      rw [norm_mul]
      have hprod : ‖(f n : ℂ) * χ (n : ZMod q)‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_one₀ (hf n) (norm_nonneg _) (χ.norm_le_one _)
      have hsum : ‖∑ e ∈ Finset.Icc 1 (X / n), (ArithmeticFunction.log e : ℂ) * χ (e : ZMod q)‖ ≤
          4 * q * Real.log (X + 1 : ℝ) := by
        have hs := character_log_sum_Icc_le χ hχ (X / n)
        simp only [ArithmeticFunction.log_apply]
        simp_rw [mul_comm (Complex.ofReal _) (χ _)]
        refine hs.trans ?_
        gcongr
        exact_mod_cast Nat.div_le_self X n
      exact (mul_le_of_le_one_left (norm_nonneg _) hprod).trans hsum
    · intro n _ hn
      rw [hf0 n hn, Complex.ofReal_zero, zero_mul, zero_mul]
  convert hh using 1 <;> ring

lemma head_vonMangoldt_character_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (X V : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 X, (arithHead ArithmeticFunction.vonMangoldt V n : ℂ) * χ (n : ZMod q)‖ ≤
      (V : ℝ) * Real.log (X + 1 : ℝ) := by
  apply norm_sum_Icc_of_support (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X]))
  · intro n hn _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (arithHead_vonMangoldt_nonneg V n)]
    refine (mul_le_of_le_one_right (arithHead_vonMangoldt_nonneg V n) (χ.norm_le_one _)).trans ?_
    refine ((arithHead_vonMangoldt_le V n).trans ArithmeticFunction.vonMangoldt_le_log).trans ?_
    apply Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
    exact_mod_cast (show n ≤ X + 1 by have := (Finset.mem_Icc.mp hn).2; omega)
  · intro n _ hn
    simp [arithHead_apply, not_le.mpr hn]

def vaughanI (U V : ℕ) : ArithmeticFunction ℝ :=
  arithHead (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U * ArithmeticFunction.log -
    arithHead (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U * ArithmeticFunction.zeta *
      arithHead ArithmeticFunction.vonMangoldt V + arithHead ArithmeticFunction.vonMangoldt V

lemma arith_sub_apply {R : Type*} [AddGroup R] (f g : ArithmeticFunction R) (n : ℕ) :
    (f - g) n = f n - g n := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, sub_eq_add_neg]
  rfl

lemma vaughan_typeI_pointwise {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (X U V : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 X, (vaughanI U V n : ℂ) * χ (n : ZMod q)‖ ≤
      (4 * (U : ℝ) * q + 2 * U * V * q + V) * Real.log (X + 1 : ℝ) := by
  let f := arithHead (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U
  let g := arithHead ArithmeticFunction.vonMangoldt V
  have hlog : 0 ≤ Real.log (X + 1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X])
  have h1 := convolution_log_character_bound χ hχ X U f (arithHead_moebius_abs_le U)
    (fun n hn => by simp [f, arithHead_apply, not_le.mpr hn])
  have h2 := convolution_zeta_character_bound χ hχ X (U * V) (f * g)
    (Real.log (X + 1 : ℝ)) hlog (fun n hn => ?_) (fun n hn => arithHead_mul_eq_zero _ _ U V n hn)
  · have h3 := head_vonMangoldt_character_bound χ X V
    have heq : f * ArithmeticFunction.zeta * g = (f * g) * ArithmeticFunction.zeta := by ring
    have hdecomp (n : ℕ) : vaughanI U V n =
        (f * ArithmeticFunction.log) n - ((f * g) * ArithmeticFunction.zeta) n + g n := by
      change (f * ArithmeticFunction.log - f * ArithmeticFunction.zeta * g + g) n = _
      rw [ArithmeticFunction.add_apply, arith_sub_apply, heq]
    simp only [hdecomp, Complex.ofReal_add, Complex.ofReal_sub, add_mul, sub_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    calc
      _ ≤ ‖∑ n ∈ Finset.Icc 1 X, (((f * ArithmeticFunction.log) n : ℝ) : ℂ) * χ (n : ZMod q)‖ +
          ‖∑ n ∈ Finset.Icc 1 X, ((((f * g) * ArithmeticFunction.zeta) n : ℝ) : ℂ) * χ (n : ZMod q)‖ +
          ‖∑ n ∈ Finset.Icc 1 X, (g n : ℂ) * χ (n : ZMod q)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ 4 * (U : ℝ) * q * Real.log (X + 1 : ℝ) +
          2 * (U * V : ℕ) * q * Real.log (X + 1 : ℝ) + (V : ℝ) * Real.log (X + 1 : ℝ) :=
        add_le_add (add_le_add h1 h2) h3
      _ = _ := by push_cast; ring
  · refine (arithHead_moebius_mul_vonMangoldt_abs_le_log U V n).trans ?_
    apply Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
    exact_mod_cast (show n ≤ X + 1 by have := (Finset.mem_Icc.mp hn).2; omega)

/-- The elementary part of Vaughan's identity has power-saving total size for small `U,V,Q`. -/
theorem vaughan_typeI_mean (Q U V X : ℕ) (R : ℝ) (hR : 1 < R) :
    primitiveMean R (fun χ : PrimitiveUpTo Q => ∑ n ∈ Finset.Icc 1 X,
      (vaughanI U V n : ℂ) * primitiveValue χ n) ≤
      (Q + 1 : ℝ) ^ 2 * ((4 * (U : ℝ) * Q + 2 * U * V * Q + V) * Real.log (X + 1 : ℝ)) := by
  have hlog : 0 ≤ Real.log (X + 1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X])
  apply primitiveMean_le_card_mul R (by positivity)
  intro χ hχ
  have hq : 1 < χ.1.val := by
    have : (1 : ℝ) < χ.1.val := hR.trans_le hχ
    exact_mod_cast this
  haveI : NeZero χ.1.val := ⟨χ.2.property.1⟩
  have hh := vaughan_typeI_pointwise χ.2.val (primitive_nonprincipal_of_one_lt_level χ hq) X U V
  refine hh.trans ?_
  have hqQ : (χ.1.val : ℝ) ≤ Q := by exact_mod_cast (show χ.1.val ≤ Q by omega)
  gcongr

end
end MaynardDevelopment
end

/- DyadicBilinear -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section

variable {ι μ ν : Type*} [Fintype ι] [Fintype μ] [Fintype ν]

def energy (a : μ → ℂ) : ℝ := ∑ m, ‖a m‖ ^ 2

lemma energy_nonneg (a : μ → ℂ) : 0 ≤ energy a :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

def FrameBound (f : ι → μ → ℂ) (A : ℝ) : Prop :=
  ∀ a : μ → ℂ, energy (fun i => ∑ m, a m * f i m) ≤ A * energy a

lemma frame_product (f : ι → μ → ℂ) (g : ι → ν → ℂ) (a : μ → ℂ) (b : ν → ℂ)
    {A B : ℝ} (hA : FrameBound f A) (hB : FrameBound g B) :
    (∑ i, ‖(∑ m, a m * f i m) * (∑ n, b n * g i n)‖) ≤
      Real.sqrt (A * B * energy a * energy b) := by
  convert sum_norm_mul_le_sqrt _ _ (hA a) (hB b) using 1
  congr 1
  ring

lemma FrameBound.fin_left {L R : ℕ} {g : ι → Fin (L + R) → ℂ} {B : ℝ}
    (hB : FrameBound g B) : FrameBound (fun i (n : Fin L) => g i (Fin.castAdd R n)) B := by
  intro b
  have hh := hB (Fin.addCases b (fun _ => 0))
  simpa [energy, Fin.sum_univ_add] using hh

lemma FrameBound.fin_right {L R : ℕ} {g : ι → Fin (L + R) → ℂ} {B : ℝ}
    (hB : FrameBound g B) : FrameBound (fun i (n : Fin R) => g i (Fin.natAdd L n)) B := by
  intro b
  have hh := hB (Fin.addCases (fun _ => 0) b)
  simpa [energy, Fin.sum_univ_add] using hh

lemma energy_mask_add (a : μ → ℂ) (p : μ → Prop) [DecidablePred p] :
    energy (fun m => if p m then a m else 0) +
      energy (fun m => if p m then 0 else a m) = energy a := by
  rw [energy, energy, ← Finset.sum_add_distrib, energy]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : p m <;> simp [hm]

lemma energy_fin_add {L R : ℕ} (b : Fin (L + R) → ℂ) :
    energy b = energy (fun n => b (Fin.castAdd R n)) + energy (fun n => b (Fin.natAdd L n)) := by
  exact Fin.sum_univ_add _

def prefixBilinear {N : ℕ} (f : ι → μ → ℂ) (g : ι → Fin N → ℂ)
    (a : μ → ℂ) (b : Fin N → ℂ) (k : μ → ℕ) (i : ι) : ℂ :=
  ∑ m, a m * f i m * ∑ n : Fin N, if n.val < k m then b n * g i n else 0

lemma prefixBilinear_one (f : ι → μ → ℂ) (g : ι → Fin 1 → ℂ)
    (a : μ → ℂ) (b : Fin 1 → ℂ) (k : μ → ℕ) (i : ι) :
    prefixBilinear f g a b k i =
      (∑ m, (if 0 < k m then a m else 0) * f i m) * (∑ n, b n * g i n) := by
  simp only [prefixBilinear, Fin.sum_univ_one, Fin.val_zero, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : 0 < k m <;> simp [hm]

lemma prefixBilinear_split {H : ℕ} (f : ι → μ → ℂ) (g : ι → Fin (H + H) → ℂ)
    (a : μ → ℂ) (b : Fin (H + H) → ℂ) (k : μ → ℕ) (i : ι) :
    prefixBilinear f g a b k i =
      (∑ m, (if k m < H then 0 else a m) * f i m) *
        (∑ n : Fin H, b (Fin.castAdd H n) * g i (Fin.castAdd H n)) +
      prefixBilinear f (fun i n => g i (Fin.castAdd H n))
        (fun m => if k m < H then a m else 0) (fun n => b (Fin.castAdd H n)) k i +
      prefixBilinear f (fun i n => g i (Fin.natAdd H n))
        (fun m => if k m < H then 0 else a m) (fun n => b (Fin.natAdd H n)) (fun m => k m - H) i := by
  simp only [prefixBilinear, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [Fin.sum_univ_add]
  by_cases hm : k m < H
  · have hright (n : Fin H) : ¬ (Fin.natAdd H n).val < k m := by simp only [Fin.val_natAdd]; omega
    simp only [hm, if_true, hright, if_false, Finset.sum_const_zero, add_zero, zero_mul, zero_add,
      Fin.val_castAdd]
  · have hleft (n : Fin H) : (Fin.castAdd H n).val < k m := by simp only [Fin.val_castAdd]; omega
    have hright (n : Fin H) : (Fin.natAdd H n).val < k m ↔ n.val < k m - H := by
      simp only [Fin.val_natAdd]; omega
    simp only [hm, if_false, hleft, if_true, hright, zero_mul, zero_add, mul_zero, add_zero]
    ring

lemma sqrt_pair_bound {C x y u v : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (C * x * u) + Real.sqrt (C * y * v) ≤
      Real.sqrt (C * (x + y) * (u + v)) := by
  have h1 := Real.sq_sqrt (show 0 ≤ C * x * u by positivity)
  have h2 := Real.sq_sqrt (show 0 ≤ C * y * v by positivity)
  have h3 := sq_nonneg (Real.sqrt (x * v) - Real.sqrt (y * u))
  have h4 := Real.sq_sqrt (mul_nonneg hx hv)
  have h5 := Real.sq_sqrt (mul_nonneg hy hu)
  have hcros : Real.sqrt (C * x * u) * Real.sqrt (C * y * v) =
      C * (Real.sqrt (x * v) * Real.sqrt (y * u)) := by
    calc
      _ = Real.sqrt ((C * x * u) * (C * y * v)) := (Real.sqrt_mul (by positivity) _).symm
      _ = Real.sqrt (C ^ 2 * ((x * v) * (y * u))) := by congr 1; ring
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC, Real.sqrt_mul (mul_nonneg hx hv)]
  apply Real.le_sqrt_of_sq_le
  nlinarith [mul_nonneg hC (show 0 ≤ x * v + y * u -
    2 * (Real.sqrt (x * v) * Real.sqrt (y * u)) by nlinarith)]

lemma energy_mask_le (a : μ → ℂ) (p : μ → Prop) [DecidablePred p] :
    energy (fun m => if p m then a m else 0) ≤ energy a := by
  have hh := energy_mask_add a p
  linarith [energy_nonneg (fun m => if p m then 0 else a m)]

/-- Dyadic decomposition handles an arbitrary row-dependent prefix cutoff at a logarithmic cost.
No monotonicity of the cutoff is needed. -/
theorem frame_prefix_power (d : ℕ) {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (f : ι → μ → ℂ) (hA : FrameBound f A) :
    ∀ (g : ι → Fin (2 ^ d) → ℂ), FrameBound g B →
    ∀ (a : μ → ℂ) (b : Fin (2 ^ d) → ℂ) (k : μ → ℕ),
      (∑ i, ‖prefixBilinear f g a b k i‖) ≤
        (d + 1 : ℝ) * Real.sqrt (A * B * energy a * energy b) := by
  induction d with
  | zero =>
    intro g hB a b k
    simp only [prefixBilinear_one]
    have hh := frame_product f g (fun m => if 0 < k m then a m else 0) b hA hB
    simp only [Nat.cast_zero, zero_add, one_mul]
    refine hh.trans ?_
    have he := energy_mask_le a (fun m => 0 < k m)
    gcongr
    exact energy_nonneg b
  | succ d ih =>
    rw [show 2 ^ (d + 1) = 2 ^ d + 2 ^ d by ring]
    intro g hB a b k
    let aL : μ → ℂ := fun m => if k m < 2 ^ d then a m else 0
    let aR : μ → ℂ := fun m => if k m < 2 ^ d then 0 else a m
    let bL : Fin (2 ^ d) → ℂ := fun n => b (Fin.castAdd (2 ^ d) n)
    let bR : Fin (2 ^ d) → ℂ := fun n => b (Fin.natAdd (2 ^ d) n)
    let gL : ι → Fin (2 ^ d) → ℂ := fun i n => g i (Fin.castAdd (2 ^ d) n)
    let gR : ι → Fin (2 ^ d) → ℂ := fun i n => g i (Fin.natAdd (2 ^ d) n)
    have heA : energy aL + energy aR = energy a := energy_mask_add a (fun m => k m < 2 ^ d)
    have heB : energy bL + energy bR = energy b := (energy_fin_add b).symm
    have haR : energy aR ≤ energy a := by linarith [energy_nonneg aL]
    have hbL : energy bL ≤ energy b := by linarith [energy_nonneg bR]
    have hsplit (i : ι) : prefixBilinear f g a b k i =
        (∑ m, aR m * f i m) * (∑ n, bL n * gL i n) +
        prefixBilinear f gL aL bL k i +
        prefixBilinear f gR aR bR (fun m => k m - 2 ^ d) i :=
      prefixBilinear_split f g a b k i
    have hprod := frame_product f gL aR bL hA hB.fin_left
    have hleft := ih gL hB.fin_left aL bL k
    have hright := ih gR hB.fin_right aR bR (fun m => k m - 2 ^ d)
    have hpair := sqrt_pair_bound (mul_nonneg hA0 hB0)
      (energy_nonneg aL) (energy_nonneg aR) (energy_nonneg bL) (energy_nonneg bR)
    rw [heA, heB] at hpair
    have hrect : Real.sqrt (A * B * energy aR * energy bL) ≤
        Real.sqrt (A * B * energy a * energy b) := by
      gcongr
      · exact energy_nonneg bL
      · exact mul_nonneg (mul_nonneg hA0 hB0) (energy_nonneg a)
    calc
      _ ≤ (∑ i, ‖(∑ m, aR m * f i m) * (∑ n, bL n * gL i n)‖) +
          (∑ i, ‖prefixBilinear f gL aL bL k i‖) +
          (∑ i, ‖prefixBilinear f gR aR bR (fun m => k m - 2 ^ d) i‖) := by
        simp only [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro i _
        rw [hsplit]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ Real.sqrt (A * B * energy aR * energy bL) +
          (d + 1 : ℝ) * Real.sqrt (A * B * energy aL * energy bL) +
          (d + 1 : ℝ) * Real.sqrt (A * B * energy aR * energy bR) :=
        add_le_add (add_le_add hprod hleft) hright
      _ ≤ Real.sqrt (A * B * energy a * energy b) +
          (d + 1 : ℝ) * Real.sqrt (A * B * energy a * energy b) := by
        nlinarith [mul_le_mul_of_nonneg_left hpair (by positivity : 0 ≤ (d + 1 : ℝ))]
      _ = _ := by push_cast; ring


lemma FrameBound.fin_append_zero {N : ℕ} {g : ι → Fin N → ℂ} {B : ℝ}
    (hB : FrameBound g B) (hB0 : 0 ≤ B) (R : ℕ) :
    FrameBound (fun i => Fin.addCases (g i) (fun _ : Fin R => 0)) B := by
  intro b
  have hh := hB (fun n => b (Fin.castAdd R n))
  have he : energy (fun n => b (Fin.castAdd R n)) ≤ energy b := by
    rw [energy_fin_add b]
    linarith [energy_nonneg (fun n => b (Fin.natAdd N n))]
  have hh' := hh.trans (mul_le_mul_of_nonneg_left he hB0)
  simpa only [energy, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, mul_zero,
    Finset.sum_const_zero, add_zero] using hh'

/-- The dyadic prefix bound for an interval of arbitrary length. -/
theorem frame_prefix {N : ℕ} (d : ℕ) (hN : N ≤ 2 ^ d)
    {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (f : ι → μ → ℂ) (g : ι → Fin N → ℂ) (hA : FrameBound f A) (hB : FrameBound g B)
    (a : μ → ℂ) (b : Fin N → ℂ) (k : μ → ℕ) :
    (∑ i, ‖prefixBilinear f g a b k i‖) ≤
      (d + 1 : ℝ) * Real.sqrt (A * B * energy a * energy b) := by
  let R := 2 ^ d - N
  have hNR : N + R = 2 ^ d := Nat.add_sub_of_le hN
  let g' : ι → Fin (N + R) → ℂ := fun i => Fin.addCases (g i) (fun _ => 0)
  let b' : Fin (N + R) → ℂ := Fin.addCases b (fun _ => 0)
  have hBp : FrameBound g' B := hB.fin_append_zero hB0 R
  have hh := frame_prefix_power d hA0 hB0 f hA
  rw [← hNR] at hh
  have hbound := hh g' hBp a b' k
  have he : energy b' = energy b := by simp [energy, b', Fin.sum_univ_add]
  have heq (i : ι) : prefixBilinear f g' a b' k i = prefixBilinear f g a b k i := by
    simp only [prefixBilinear, Fin.sum_univ_add, b', g', Fin.addCases_left, Fin.addCases_right,
      zero_mul, ite_self, Finset.sum_const_zero, add_zero, Fin.val_castAdd]
  simpa only [heq, he] using hbound

lemma primitive_character_frame (Q M N : ℕ) :
    FrameBound (fun χ : PrimitiveUpTo Q => fun n : Fin N => primitiveValue χ (M + n.val))
      ((N : ℝ) + 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2) :=
  primitive_character_large_sieve Q M N

/-- Bilinear character sums with arbitrary row-dependent prefix lengths. -/
theorem primitive_character_prefix (Q M N U V d : ℕ) (hN : N ≤ 2 ^ d)
    (a : Fin M → ℂ) (b : Fin N → ℂ) (k : Fin M → ℕ) :
    (∑ χ : PrimitiveUpTo Q, ‖∑ m : Fin M, ∑ n : Fin N,
      if n.val < k m then a m * b n * primitiveValue χ ((U + m.val) * (V + n.val)) else 0‖) ≤
      (d + 1 : ℝ) * Real.sqrt (((M : ℝ) + 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2) *
        ((N : ℝ) + 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2) * energy a * energy b) := by
  have hh := frame_prefix d hN (by positivity) (by positivity)
    (fun χ : PrimitiveUpTo Q => fun m : Fin M => primitiveValue χ (U + m.val))
    (fun χ : PrimitiveUpTo Q => fun n : Fin N => primitiveValue χ (V + n.val))
    (primitive_character_frame Q U M) (primitive_character_frame Q V N) a b k
  have heq (χ : PrimitiveUpTo Q) :
      (∑ m : Fin M, ∑ n : Fin N, if n.val < k m then
        a m * b n * primitiveValue χ ((U + m.val) * (V + n.val)) else 0) =
      prefixBilinear (fun χ m => primitiveValue χ (U + m.val))
        (fun χ n => primitiveValue χ (V + n.val)) a b k χ := by
    simp only [prefixBilinear, Finset.mul_sum, primitiveValue_mul]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    by_cases hnk : n.val < k m <;> simp only [hnk, if_true, if_false, mul_zero]
    ring
  simpa only [heq] using hh


/-- A reciprocal-totient weighted hyperbola estimate for a rectangle in the positive quadrant. -/
theorem primitive_character_hyperbola (Q M N U V X : ℕ) (hU : 0 < U)
    (R : ℝ) (hR : 0 < R) (a : Fin M → ℂ) (b : Fin N → ℂ) :
    (∑ χ : PrimitiveUpTo Q, if R ≤ (χ.1.val : ℝ) then ((χ.1.val.totient : ℝ)⁻¹) *
      ‖∑ m : Fin M, ∑ n : Fin N, if (U + m.val) * (V + n.val) ≤ X then
        a m * b n * primitiveValue χ ((U + m.val) * (V + n.val)) else 0‖ else 0) ≤
      ((3 + Real.log Q / Real.log 2) / R) * (Nat.log 2 N + 2 : ℝ) *
      Real.sqrt (((M : ℝ) + 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2) *
        ((N : ℝ) + 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2) * energy a * energy b) := by
  let k : Fin M → ℕ := fun m => X / (U + m.val) + 1 - V
  have hk (m : Fin M) (n : Fin N) :
      (U + m.val) * (V + n.val) ≤ X ↔ n.val < k m := by
    rw [Nat.mul_comm (U + m.val), ← Nat.le_div_iff_mul_le (by omega : 0 < U + m.val)]
    dsimp [k]
    omega
  simp_rw [hk]
  have hh := primitive_character_prefix Q M N U V (Nat.log 2 N + 1)
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) N).le a b k
  have hw := primitive_weighted_sum_le Q R hR _ (fun _ => norm_nonneg _) hh
  convert hw using 1 <;> push_cast <;> ring


end
end MaynardDevelopment
end

/- TypeTwo -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section

def vaughanM (U : ℕ) : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
    arithHead (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) * ArithmeticFunction.zeta

def vaughanL (V : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.vonMangoldt - arithHead ArithmeticFunction.vonMangoldt V

lemma vaughanM_abs_le (U n : ℕ) : |vaughanM U n| ≤ (n.divisors.card : ℝ) := by
  rw [vaughanM, ArithmeticFunction.coe_mul_zeta_apply]
  calc
    _ ≤ ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        arithHead (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      rw [arithTail_apply]
      split_ifs
      · simpa only [ArithmeticFunction.intCoe_apply, ← Int.cast_abs, Int.cast_one] using
          (Int.cast_le.mpr (ArithmeticFunction.abs_moebius_le_one (n := d)) :
            ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) ≤ (1 : ℤ))
      · norm_num
    _ = _ := by simp

lemma vaughanM_eq_zero {U n : ℕ} (hn : n ≤ U) : vaughanM U n = 0 := by
  rw [vaughanM, ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  rw [arithTail_apply, if_neg]
  exact not_lt.mpr ((Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
    (Nat.dvd_of_mem_divisors hd)).trans hn)

lemma vaughanL_nonneg (V n : ℕ) : 0 ≤ vaughanL V n := by
  rw [vaughanL, arithTail_apply]
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

lemma vaughanL_le_log (V n : ℕ) : vaughanL V n ≤ Real.log n := by
  rw [vaughanL, arithTail_apply]
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_le_log
  · exact ArithmeticFunction.vonMangoldt_nonneg.trans ArithmeticFunction.vonMangoldt_le_log

lemma vaughanL_eq_zero {V n : ℕ} (hn : n ≤ V) : vaughanL V n = 0 := by
  rw [vaughanL, arithTail_apply, if_neg (not_lt.mpr hn)]

lemma sum_fin_eq_sum_Ico {R : Type*} [AddCommMonoid R] (f : ℕ → R) (U N : ℕ) :
    (∑ n : Fin N, f (U + n.val)) = ∑ n ∈ Finset.Ico U (U + N), f n := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  exact Fin.sum_univ_eq_sum_range (fun n => f (U + n)) N

lemma vaughanM_energy (U K N : ℕ) (hK : 0 < K) :
    energy (fun n : Fin N => (vaughanM U (K + n.val) : ℂ)) ≤
      (K + N : ℝ) * (1 + Real.log (K + N : ℝ)) ^ 3 := by
  rw [energy]
  calc
    _ ≤ ∑ n : Fin N, ((K + n.val).divisors.card : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n _
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr (vaughanM_abs_le U _)
    _ = ∑ n ∈ Finset.Ico K (K + N), (n.divisors.card : ℝ) ^ 2 :=
      sum_fin_eq_sum_Ico (fun n => (n.divisors.card : ℝ) ^ 2) K N
    _ ≤ ∑ n ∈ Finset.Icc 1 (K + N), (n.divisors.card : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Ico_subset_Icc_self.trans (Finset.Icc_subset_Icc hK le_rfl)
      · intros; positivity
    _ ≤ _ := by simpa only [Nat.cast_add] using sum_card_divisors_sq_le (K + N)

lemma vaughanL_energy (V K N : ℕ) (hK : 0 < K) :
    energy (fun n : Fin N => (vaughanL V (K + n.val) : ℂ)) ≤
      (N : ℝ) * (Real.log (K + N : ℝ)) ^ 2 := by
  have hbound (n : Fin N) : ‖(vaughanL V (K + n.val) : ℂ)‖ ≤ Real.log (K + N : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (vaughanL_nonneg V _)]
    refine (vaughanL_le_log V _).trans ?_
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < K + n.val))
    exact_mod_cast (show K + n.val ≤ K + N by omega)
  calc
    _ ≤ ∑ _n : Fin N, (Real.log (K + N : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro n _
      apply (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hbound n))).mpr (hbound n)
    _ = _ := by simp

lemma typeII_root_bound {M N D E F X L : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hDM : D ≤ M) (hDN : D ≤ N) (hMN : M * N ≤ X) (hL : 1 ≤ L)
    (hME : E ≤ 2 * M * L ^ 3) (hNF : F ≤ N * L ^ 2) :
    Real.sqrt ((M + D) * (N + D) * E * F) ≤ 4 * X * L ^ 3 := by
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hME' : E ≤ 2 * M * L ^ 4 := hME.trans (by
    apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by decide : 3 ≤ 4))
    positivity)
  have hNF' : F ≤ 2 * N * L ^ 2 := hNF.trans (by nlinarith [sq_nonneg L])
  calc
    _ ≤ Real.sqrt ((2 * M) * (2 * N) * (2 * M * L ^ 4) * (2 * N * L ^ 2)) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul _ hNF' hF (by positivity)
      apply mul_le_mul _ hME' hE (by positivity)
      apply mul_le_mul (by linarith : M + D ≤ 2 * M) (by linarith : N + D ≤ 2 * N)
        (by positivity) (by positivity)
    _ = Real.sqrt ((4 * (M * N) * L ^ 3) ^ 2) := by congr 1; ring
    _ = 4 * (M * N) * L ^ 3 := Real.sqrt_sq (by positivity)
    _ ≤ _ := by gcongr

/-- A Type II block bound in the long-variable range. -/
theorem vaughan_typeII_block (Q M N U V X : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hMN : M * N ≤ X)
    (hDM : 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2 ≤ M)
    (hDN : 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2 ≤ N)
    (R : ℝ) (hR : 0 < R) :
    (∑ χ : PrimitiveUpTo Q, if R ≤ (χ.1.val : ℝ) then ((χ.1.val.totient : ℝ)⁻¹) *
      ‖∑ m : Fin M, ∑ n : Fin N, if (M + m.val) * (N + n.val) ≤ X then
        (vaughanM U (M + m.val) : ℂ) * (vaughanL V (N + n.val) : ℂ) *
          primitiveValue χ ((M + m.val) * (N + n.val)) else 0‖ else 0) ≤
      ((3 + Real.log Q / Real.log 2) / R) * (Nat.log 2 X + 2 : ℝ) *
        (4 * (X : ℝ) * (1 + Real.log (2 * X : ℝ)) ^ 3) := by
  let a : Fin M → ℂ := fun m => vaughanM U (M + m.val)
  let b : Fin N → ℂ := fun n => vaughanL V (N + n.val)
  have hh := primitive_character_hyperbola Q M N M N X hM R hR a b
  have hMX : M ≤ X := (Nat.le_mul_of_pos_right M hN).trans hMN
  have hNX : N ≤ X := (Nat.le_mul_of_pos_left N hM).trans hMN
  have hXp : 0 < X := hM.trans_le hMX
  let L : ℝ := 1 + Real.log (2 * X : ℝ)
  have hL : 1 ≤ L := by
    dsimp [L]
    have : 0 ≤ Real.log (2 * X : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * X))
    linarith
  have hML : 1 + Real.log (M + M : ℝ) ≤ L := by
    dsimp [L]
    gcongr
    exact_mod_cast (by omega : M + M ≤ 2 * X)
  have hNL : Real.log (N + N : ℝ) ≤ L := by
    have hh' : Real.log (N + N : ℝ) ≤ Real.log (2 * X : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < N + N))
      exact_mod_cast (by omega : N + N ≤ 2 * X)
    dsimp [L]
    linarith
  have hMEn : energy a ≤ 2 * (M : ℝ) * L ^ 3 := by
    have he := vaughanM_energy U M M hM
    change energy a ≤ _ at he
    calc
      _ ≤ (M + M : ℝ) * (1 + Real.log (M + M : ℝ)) ^ 3 := he
      _ ≤ (M + M : ℝ) * L ^ 3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ ((harmonic_real_nonneg (M + M)).trans
          (by simpa only [Nat.cast_add] using harmonic_le_one_add_log (M + M))) hML _) (by positivity)
      _ = _ := by ring
  have hNEn : energy b ≤ (N : ℝ) * L ^ 2 := by
    refine (vaughanL_energy V N N hN).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ _ hNL
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N + N))
  have hroot := typeII_root_bound (X := (X : ℝ)) (Nat.cast_nonneg M) (Nat.cast_nonneg N) (by positivity)
    (energy_nonneg a) (energy_nonneg b) hDM hDN (by exact_mod_cast hMN) hL hMEn hNEn
  refine hh.trans ?_
  have hlog : (Nat.log 2 N : ℝ) ≤ Nat.log 2 X := by exact_mod_cast Nat.log_mono_right hNX
  have hc : 0 ≤ (3 + Real.log (Q : ℝ) / Real.log 2) / R := by
    have hlogQ : 0 ≤ Real.log (Q : ℝ) := ArithmeticFunction.vonMangoldt_nonneg.trans ArithmeticFunction.vonMangoldt_le_log
    positivity
  apply mul_le_mul _ hroot (Real.sqrt_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith) hc

end
end MaynardDevelopment
end

/- DyadicIntervals -/
section

open scoped BigOperators
namespace MaynardDevelopment

lemma sum_Ico_dyadic {R : Type*} [AddCommMonoid R] (f : ℕ → R) (U d : ℕ) :
    (∑ n ∈ Finset.Ico U (U * 2 ^ d), f n) =
      ∑ j ∈ Finset.range d, ∑ n ∈ Finset.Ico (U * 2 ^ j) (U * 2 ^ (j + 1)), f n := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ← ih]
    symm
    apply Finset.sum_Ico_consecutive
    · exact Nat.le_mul_of_pos_right U (by positivity)
    · rw [pow_succ, ← Nat.mul_assoc]
      exact Nat.le_mul_of_pos_right _ (by decide)

lemma sum_Ico_dyadic_fin {R : Type*} [AddCommMonoid R] (f : ℕ → R) (U d : ℕ) :
    (∑ n ∈ Finset.Ico U (U * 2 ^ d), f n) =
      ∑ j ∈ Finset.range d, ∑ n : Fin (U * 2 ^ j), f (U * 2 ^ j + n.val) := by
  rw [sum_Ico_dyadic]
  apply Finset.sum_congr rfl
  intro j _
  rw [sum_fin_eq_sum_Ico]
  congr 1
  ring

lemma sum_Icc_eq_sum_Ico_of_support {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (X U E : ℕ) (hU : 0 < U) (hE : X < E)
    (hlo : ∀ n < U, f n = 0) (hhi : ∀ n, X < n → f n = 0) :
    (∑ n ∈ Finset.Icc 1 X, f n) = ∑ n ∈ Finset.Ico U E, f n := by
  have hleft : (∑ n ∈ Finset.Icc 1 X, f n) = ∑ n ∈ Finset.range E, f n := by
    apply Finset.sum_subset
    · intro n hn
      have := Finset.mem_Icc.mp hn
      exact Finset.mem_range.mpr (by omega)
    · intro n hn hnot
      by_cases hn0 : n = 0
      · subst n; exact hlo 0 hU
      · exact hhi n (by simp only [Finset.mem_Icc] at hnot; omega)
  have hright : (∑ n ∈ Finset.Ico U E, f n) = ∑ n ∈ Finset.range E, f n := by
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
    · intro n hn hnot
      exact hlo n (by simp only [Finset.mem_range] at hn; simp only [Finset.mem_Ico] at hnot; omega)
  exact hleft.trans hright.symm

/-- Partition a supported hyperbola sum into full dyadic rectangles. -/
lemma sum_hyperbola_dyadic {R : Type*} [AddCommMonoid R]
    (F : ℕ → ℕ → R) (X U V d : ℕ) (hU : 0 < U) (hV : 0 < V) (hX : X < 2 ^ d)
    (hloU : ∀ m < U, ∀ n, F m n = 0) (hloV : ∀ n < V, ∀ m, F m n = 0)
    (hhi : ∀ m n, X < m * n → F m n = 0) :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 (X / m), F m n) =
      ∑ j ∈ Finset.range d, ∑ l ∈ Finset.range d,
        ∑ m : Fin (U * 2 ^ j), ∑ n : Fin (V * 2 ^ l),
          F (U * 2 ^ j + m.val) (V * 2 ^ l + n.val) := by
  have hUend : X < U * 2 ^ d := hX.trans_le (Nat.le_mul_of_pos_left _ hU)
  have hVend : X < V * 2 ^ d := hX.trans_le (Nat.le_mul_of_pos_left _ hV)
  have hrect (m : ℕ) (hm : m ∈ Finset.Icc 1 X) :
      (∑ n ∈ Finset.Icc 1 (X / m), F m n) = ∑ n ∈ Finset.Icc 1 X, F m n := by
    have hmp : 0 < m := (Finset.mem_Icc.mp hm).1
    apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (Nat.div_le_self X m))
    intro n hn hnnot
    have hn' : ¬ n ≤ X / m := by
      simp only [Finset.mem_Icc] at hn hnnot
      tauto
    apply hhi m n
    rw [← not_le]
    intro hmn
    apply hn'
    exact (Nat.le_div_iff_mul_le hmp).mpr (by simpa [Nat.mul_comm] using hmn)
  calc
    _ = ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X, F m n := Finset.sum_congr rfl hrect
    _ = ∑ m ∈ Finset.Ico U (U * 2 ^ d), ∑ n ∈ Finset.Icc 1 X, F m n := by
      apply sum_Icc_eq_sum_Ico_of_support _ X U _ hU hUend
      · intro m hm; simp [hloU m hm]
      · intro m hm
        apply Finset.sum_eq_zero
        intro n hn
        apply hhi m n
        exact hm.trans_le (Nat.le_mul_of_pos_right m (Finset.mem_Icc.mp hn).1)
    _ = ∑ m ∈ Finset.Ico U (U * 2 ^ d), ∑ n ∈ Finset.Ico V (V * 2 ^ d), F m n := by
      apply Finset.sum_congr rfl
      intro m hm
      apply sum_Icc_eq_sum_Ico_of_support _ X V _ hV hVend
      · intro n hn; exact hloV n hn m
      · intro n hn
        exact hhi m n (hn.trans_le (Nat.le_mul_of_pos_left n
          (hU.trans_le (Finset.mem_Ico.mp hm).1)))
    _ = _ := by
      rw [sum_Ico_dyadic_fin]
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [sum_Ico_dyadic_fin]
      rw [Finset.sum_comm]

end MaynardDevelopment
end

/- TypeTwoGlobal -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section

/-- The full Type II term of Vaughan's identity, averaged over large primitive conductors. -/
theorem vaughan_typeII_mean (Q U V X : ℕ) (hU : 0 < U) (hV : 0 < V)
    (hDU : 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2 ≤ U)
    (hDV : 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2 ≤ V)
    (R : ℝ) (hR : 0 < R) :
    primitiveMean R (fun χ : PrimitiveUpTo Q => ∑ n ∈ Finset.Icc 1 X,
      (((vaughanM U * vaughanL V) n : ℝ) : ℂ) * primitiveValue χ n) ≤
      (Nat.log 2 X + 1 : ℝ) ^ 2 *
        (((3 + Real.log Q / Real.log 2) / R) * (Nat.log 2 X + 2 : ℝ) *
          (4 * (X : ℝ) * (1 + Real.log (2 * X : ℝ)) ^ 3)) := by
  let d := Nat.log 2 X + 1
  let H : PrimitiveUpTo Q → ℕ → ℕ → ℂ := fun χ m n =>
    if m * n ≤ X then (vaughanM U m : ℂ) * (vaughanL V n : ℂ) * primitiveValue χ (m * n) else 0
  let block : ℕ → ℕ → PrimitiveUpTo Q → ℂ := fun j l χ =>
    ∑ m : Fin (U * 2 ^ j), ∑ n : Fin (V * 2 ^ l), H χ (U * 2 ^ j + m.val) (V * 2 ^ l + n.val)
  let C : ℝ := ((3 + Real.log Q / Real.log 2) / R) * (Nat.log 2 X + 2 : ℝ) *
    (4 * (X : ℝ) * (1 + Real.log (2 * X : ℝ)) ^ 3)
  have hC : 0 ≤ C := by
    have hlogQ : 0 ≤ Real.log (Q : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg.trans ArithmeticFunction.vonMangoldt_le_log
    have hlogX : 0 ≤ Real.log (2 * X : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (ArithmeticFunction.vonMangoldt_nonneg.trans (ArithmeticFunction.vonMangoldt_le_log (n := 2 * X)))
    dsimp [C]
    positivity
  have hdecomp (χ : PrimitiveUpTo Q) :
      (∑ n ∈ Finset.Icc 1 X, (((vaughanM U * vaughanL V) n : ℝ) : ℂ) * primitiveValue χ n) =
      ∑ j ∈ Finset.range d, ∑ l ∈ Finset.range d, block j l χ := by
    refine (sum_convolution_map_weighted Complex.ofRealHom X (vaughanM U) (vaughanL V) (primitiveValue χ)).trans ?_
    have hH : (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 (X / m),
        (vaughanM U m : ℂ) * (vaughanL V n : ℂ) * primitiveValue χ (m * n)) =
        ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 (X / m), H χ m n := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      have hmn : m * n ≤ X := by
        simpa only [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le (Finset.mem_Icc.mp hm).1).mp (Finset.mem_Icc.mp hn).2
      simp only [H, hmn, if_true]
    change (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 (X / m),
      (vaughanM U m : ℂ) * (vaughanL V n : ℂ) * primitiveValue χ (m * n)) = _
    rw [hH]
    exact sum_hyperbola_dyadic (H χ) X U V d hU hV
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) X)
      (fun m hm n => by simp [H, vaughanM_eq_zero hm.le])
      (fun n hn m => by simp [H, vaughanL_eq_zero hn.le])
      (fun m n hmn => by simp [H, not_le.mpr hmn])
  have hblock (j l : ℕ) : primitiveMean R (block j l) ≤ C := by
    have hM : 0 < U * 2 ^ j := by positivity
    have hN : 0 < V * 2 ^ l := by positivity
    have hUM : U ≤ U * 2 ^ j := Nat.le_mul_of_pos_right U (by positivity)
    have hVN : V ≤ V * 2 ^ l := Nat.le_mul_of_pos_right V (by positivity)
    by_cases hprod : (U * 2 ^ j) * (V * 2 ^ l) ≤ X
    · exact vaughan_typeII_block Q _ _ U V X hM hN hprod
        (hDU.trans (by exact_mod_cast hUM)) (hDV.trans (by exact_mod_cast hVN)) R hR
    · have heq : block j l = fun _ => 0 := by
        funext χ
        apply Finset.sum_eq_zero
        intro m _
        apply Finset.sum_eq_zero
        intro n _
        have hh : ¬ (U * 2 ^ j + m.val) * (V * 2 ^ l + n.val) ≤ X := by
          intro hh
          exact hprod ((Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_add_right _ _)).trans hh)
        simp only [H, hh, if_false]
      rw [heq, primitiveMean_zero]
      exact hC
  simp only [hdecomp]
  calc
    _ ≤ ∑ j ∈ Finset.range d, primitiveMean R (fun χ => ∑ l ∈ Finset.range d, block j l χ) :=
      primitiveMean_sum R (Finset.range d) _
    _ ≤ ∑ j ∈ Finset.range d, ∑ l ∈ Finset.range d, primitiveMean R (block j l) :=
      Finset.sum_le_sum (fun j _ => primitiveMean_sum R (Finset.range d) (block j))
    _ ≤ ∑ _j ∈ Finset.range d, ∑ _l ∈ Finset.range d, C := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum (fun l _ => hblock j l)
    _ = _ := by simp [d, C]; ring

end
end MaynardDevelopment
end

/- VaughanMean -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section

lemma vaughan_identity_split (U V : ℕ) : ArithmeticFunction.vonMangoldt =
    vaughanI U V + vaughanM U * vaughanL V := vaughan_identity U V

/-- An unconditional large-conductor mean estimate. Small conductors are deliberately absent. -/
theorem vonMangoldt_primitive_mean (Q U V X : ℕ) (hU : 0 < U) (hV : 0 < V)
    (hDU : 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2 ≤ U)
    (hDV : 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2 ≤ V)
    (R : ℝ) (hR : 1 < R) :
    primitiveMean R (fun χ : PrimitiveUpTo Q => ∑ n ∈ Finset.Icc 1 X,
      (ArithmeticFunction.vonMangoldt n : ℂ) * primitiveValue χ n) ≤
      (Q + 1 : ℝ) ^ 2 * ((4 * (U : ℝ) * Q + 2 * U * V * Q + V) * Real.log (X + 1 : ℝ)) +
      (Nat.log 2 X + 1 : ℝ) ^ 2 *
        (((3 + Real.log Q / Real.log 2) / R) * (Nat.log 2 X + 2 : ℝ) *
          (4 * (X : ℝ) * (1 + Real.log (2 * X : ℝ)) ^ 3)) := by
  have heq (χ : PrimitiveUpTo Q) :
      (∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) * primitiveValue χ n) =
      (∑ n ∈ Finset.Icc 1 X, (vaughanI U V n : ℂ) * primitiveValue χ n) +
      ∑ n ∈ Finset.Icc 1 X, (((vaughanM U * vaughanL V) n : ℝ) : ℂ) * primitiveValue χ n := by
    rw [vaughan_identity_split U V]
    simp only [ArithmeticFunction.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
  simp only [heq]
  exact (primitiveMean_add R _ _).trans (add_le_add (vaughan_typeI_mean Q U V X R hR)
    (vaughan_typeII_mean Q U V X hU hV hDU hDV R (lt_trans (by norm_num) hR)))

lemma log_nat_le_log_add_one (X : ℕ) : Real.log (X : ℝ) ≤ Real.log (X + 1 : ℝ) := by
  rcases X with _ | X
  · simp
  · apply Real.log_le_log (by positivity)
    linarith

lemma natural_log_two_bound (X : ℕ) : (Nat.log 2 X : ℝ) ≤ 2 * Real.log (X + 1 : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hh := Real.natLog_le_logb X 2
  rw [Real.logb] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hlogX := Real.log_nonneg (show (1 : ℝ) ≤ X + 1 by linarith [Nat.cast_nonneg (α := ℝ) X])
  have hX := log_nat_le_log_add_one X
  have hh' := (le_div_iff₀ hlog2).mp hh
  have hprod := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (α := ℝ) (Nat.log 2 X))
  nlinarith

lemma log_double_nat_bound (X : ℕ) :
    1 + Real.log (2 * X : ℝ) ≤ 2 * (1 + Real.log (X + 1 : ℝ)) := by
  rcases X with _ | X
  · norm_num
  · rw [Real.log_mul (by norm_num) (by positivity)]
    have hX := log_nat_le_log_add_one (X + 1)
    have hlogX := Real.log_nonneg (show (1 : ℝ) ≤ (X + 1 : ℕ) + 1 by
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) X])
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    push_cast at hX hlogX ⊢
    nlinarith

lemma vaughan_cutoff_polynomial (Q : ℕ) :
    let U : ℕ := 2 * (Q + 1) ^ 4
    (Q + 1 : ℝ) ^ 2 * (4 * (U : ℝ) * Q + 2 * U * U * Q + U) ≤ 18 * (Q + 1 : ℝ) ^ 11 := by
  dsimp only
  push_cast
  let a : ℝ := Q + 1
  have ha : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) Q]
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have hQa : (Q : ℝ) ≤ a := by dsimp [a]; linarith
  have h4 := pow_le_pow_right₀ ha (by decide : 4 ≤ 9)
  have h5 := pow_le_pow_right₀ ha (by decide : 5 ≤ 9)
  have hfirst : 8 * a ^ 4 * (Q : ℝ) ≤ 8 * a ^ 9 := by
    calc
      _ ≤ 8 * a ^ 4 * a := by gcongr
      _ = 8 * a ^ 5 := by ring
      _ ≤ _ := by gcongr
  have hsecond : 8 * a ^ 8 * (Q : ℝ) ≤ 8 * a ^ 9 := by
    calc
      _ ≤ 8 * a ^ 8 * a := by gcongr
      _ = _ := by ring
  have hsum : 4 * (2 * a ^ 4) * (Q : ℝ) + 2 * (2 * a ^ 4) * (2 * a ^ 4) * Q + 2 * a ^ 4 ≤
      18 * a ^ 9 := by nlinarith
  calc
    _ ≤ a ^ 2 * (18 * a ^ 9) := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by dsimp [a]; ring

/-- A simple quantitative consequence of the coarse large sieve and Vaughan's identity. -/
theorem vonMangoldt_primitive_mean_coarse (Q X : ℕ) (R : ℝ) (hR : 1 < R) :
    primitiveMean R (fun χ : PrimitiveUpTo Q => ∑ n ∈ Finset.Icc 1 X,
      (ArithmeticFunction.vonMangoldt n : ℂ) * primitiveValue χ n) ≤
      18 * (Q + 1 : ℝ) ^ 11 * Real.log (X + 1 : ℝ) +
      256 * ((3 + Real.log Q / Real.log 2) / R) * X * (1 + Real.log (X + 1 : ℝ)) ^ 6 := by
  let U : ℕ := 2 * (Q + 1) ^ 4
  have hU : 0 < U := by dsimp [U]; positivity
  have hDU : 2 * (Q : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2 ≤ U := by
    dsimp [U]
    push_cast
    calc
      _ ≤ 2 * (Q + 1 : ℝ) ^ 2 * (Q + 1 : ℝ) ^ 2 := by gcongr; linarith
      _ = _ := by ring
  have hh := vonMangoldt_primitive_mean Q U U X hU hU hDU hDU R hR
  have hlogX : 0 ≤ Real.log (X + 1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X])
  have hpoly := vaughan_cutoff_polynomial Q
  change (Q + 1 : ℝ) ^ 2 * (4 * (U : ℝ) * Q + 2 * U * U * Q + U) ≤ _ at hpoly
  have hI : (Q + 1 : ℝ) ^ 2 *
      ((4 * (U : ℝ) * Q + 2 * U * U * Q + U) * Real.log (X + 1 : ℝ)) ≤
      18 * (Q + 1 : ℝ) ^ 11 * Real.log (X + 1 : ℝ) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hpoly hlogX
  let L : ℝ := 1 + Real.log (X + 1 : ℝ)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hd1 : (Nat.log 2 X + 1 : ℝ) ≤ 2 * L := by have := natural_log_two_bound X; dsimp [L]; linarith
  have hd2 : (Nat.log 2 X + 2 : ℝ) ≤ 2 * L := by have := natural_log_two_bound X; dsimp [L]; linarith
  have hdouble : 1 + Real.log (2 * X : ℝ) ≤ 2 * L := log_double_nat_bound X
  have hdouble0 : 0 ≤ 1 + Real.log (2 * X : ℝ) := by
    have hh' := Real.log_natCast_nonneg (2 * X)
    push_cast at hh'
    linarith
  have hc : 0 ≤ (3 + Real.log (Q : ℝ) / Real.log 2) / R := by
    have := Real.log_natCast_nonneg Q
    have : 0 < R := lt_trans (by norm_num) hR
    positivity
  have hII : (Nat.log 2 X + 1 : ℝ) ^ 2 *
      (((3 + Real.log Q / Real.log 2) / R) * (Nat.log 2 X + 2 : ℝ) *
        (4 * (X : ℝ) * (1 + Real.log (2 * X : ℝ)) ^ 3)) ≤
      256 * ((3 + Real.log Q / Real.log 2) / R) * X * L ^ 6 := by
    calc
      _ ≤ (2 * L) ^ 2 * (((3 + Real.log Q / Real.log 2) / R) * (2 * L) *
          (4 * (X : ℝ) * (2 * L) ^ 3)) := by gcongr
      _ = _ := by ring
  exact hh.trans (add_le_add hI hII)

end
end MaynardDevelopment
end

/- CombinedCharacterMean -/
section

open scoped BigOperators Topology
open Complex Set Filter DirichletCharacter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

def restrictPrimitive {D R : ℕ} (χ : {χ : PrimitiveUpTo D // χ.1.val ≤ R}) : PrimitiveUpTo R :=
  ⟨⟨χ.val.1.val,by have hh := χ.property; omega⟩,χ.val.2⟩

lemma restrictPrimitive_injective (D R : ℕ) : Function.Injective (@restrictPrimitive D R) := by
  rintro ⟨⟨q,χ⟩,hq⟩ ⟨⟨r,ψ⟩,hr⟩ h
  have hval : q.val=r.val := congrArg (fun ρ : PrimitiveUpTo R => ρ.1.val) h
  have hqr : q=r := Fin.ext hval
  subst r
  have hχψ : χ=ψ := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  subst ψ
  rfl

lemma primitiveUpTo_small_card (D R : ℕ) :
    (Finset.univ.filter (fun χ : PrimitiveUpTo D => χ.1.val ≤ R)).card ≤ (R+1)^2 := by
  have hc := Fintype.card_le_of_injective (@restrictPrimitive D R) (restrictPrimitive_injective D R)
  have hh : Fintype.card {χ : PrimitiveUpTo D // χ.1.val ≤ R} =
      (Finset.univ.filter (fun χ : PrimitiveUpTo D => χ.1.val ≤ R)).card := Fintype.card_subtype _
  rw [hh] at hc
  exact hc.trans (primitiveUpTo_card_le R)

lemma primitiveErrorMean_split {R D X : ℕ} (hR : 1<R) {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ χ : PrimitiveUpTo D, χ.1.val<R → GoodModulus R χ.1.val → ‖primeCharacterError χ.2.val X‖ ≤ C) :
    primitiveErrorMean R D X ≤ (R+1 : ℝ)^2*C+
      primitiveMean (R : ℝ) (fun χ : PrimitiveUpTo D => ∑ n ∈ Finset.Icc 1 X,
        (ArithmeticFunction.vonMangoldt n : ℂ)*primitiveValue χ n) := by
  let f := fun χ : PrimitiveUpTo D => ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*primitiveValue χ n
  have hstep : primitiveErrorMean R D X ≤
      (∑ χ : PrimitiveUpTo D, if χ.1.val ≤ R then C else 0)+primitiveMean (R : ℝ) f := by
    unfold primitiveErrorMean primitiveMean
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro χ hχ
    have hφ : (χ.1.val.totient : ℝ)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero χ.2.property.1)
    by_cases hg : GoodModulus R χ.1.val
    · rw [if_pos hg]
      by_cases hr : (R : ℝ) ≤ χ.1.val
      · rw [if_pos hr]
        have hlevel : R ≤ χ.1.val := by exact_mod_cast hr
        have hnon := primitive_nonprincipal_of_one_lt_level χ (by omega)
        have heq : primeCharacterError χ.2.val X=f χ := by
          simp [primeCharacterError,primeErrorCoeff,hnon,f,primitiveValue,mul_comm]
        rw [heq]
        have hpos : 0 ≤ (if χ.1.val ≤ R then C else 0) := by split_ifs <;> positivity
        linarith
      · rw [if_neg hr,add_zero]
        have hlevel : χ.1.val<R := by exact_mod_cast (lt_of_not_ge hr)
        rw [if_pos hlevel.le]
        exact (mul_le_of_le_one_left (norm_nonneg _) hφ).trans (hsmall χ hlevel hg)
    · rw [if_neg hg]
      have hpos : 0 ≤ (if χ.1.val ≤ R then C else 0) := by split_ifs <;> positivity
      have hpos' : 0 ≤ (if (R : ℝ) ≤ χ.1.val then (χ.1.val.totient : ℝ)⁻¹*‖f χ‖ else 0) := by split_ifs <;> positivity
      linarith
  refine hstep.trans (add_le_add ?_ le_rfl)
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast primitiveUpTo_small_card D R) hC

/-- Combined small- and large-conductor mean estimate. -/
theorem primitiveErrorMean_bound (k : ℕ) :
    ∃ X₀ : ℕ, ∀ R D X : ℕ, X₀ ≤ X → 1<R → Real.log R ≤ Real.sqrt (Real.log X) →
      primitiveErrorMean R D X ≤
        (R+1 : ℝ)^2*(13*X/(Real.log X)^k)+18*(D+1 : ℝ)^11*Real.log (X+1 : ℝ)+
          256*((3+Real.log D/Real.log 2)/(R : ℝ))*X*(1+Real.log (X+1 : ℝ))^6 := by
  obtain ⟨X₀,hX₀⟩ := primeError_log_saving k
  refine ⟨X₀,?_⟩
  intro R D X hX hR hlogR
  have hC : 0 ≤ 13*(X : ℝ)/(Real.log X)^k := by
    have hh := Real.log_natCast_nonneg X
    positivity
  have hsmall := primitiveErrorMean_split (D := D) (X := X) hR hC (by
    intro χ hχ hg
    letI : NeZero χ.1.val := ⟨χ.2.property.1⟩
    exact hX₀ χ.1.val R χ.2.val X hX hχ.le hlogR (primitive_good_noPageZero χ hχ.le hg))
  have hlarge := vonMangoldt_primitive_mean_coarse D X (R : ℝ) (by exact_mod_cast hR)
  exact (hsmall.trans (add_le_add le_rfl hlarge)).trans_eq (by ring)

end
end MaynardDevelopment
end

/- MeanEnvelope -/
section

open scoped BigOperators Topology
open Complex Set Filter
namespace MaynardDevelopment
noncomputable section

lemma log_nat_add_one_le_twice {N : ℕ} (hL : 1 ≤ Real.log N) :
    Real.log (N+1 : ℝ) ≤ 2*Real.log N := by
  have hN : 0<N := by
    by_contra h
    have hn : N=0 := by omega
    simp [hn] at hL
    linarith
  have hNr : (1 : ℝ)≤N := by exact_mod_cast hN
  have hh := Real.log_le_log (by positivity : (0 : ℝ)<N+1) (show (N : ℝ)+1 ≤ 2*N by linarith)
  rw [Real.log_mul (by norm_num) (by exact_mod_cast hN.ne' : (N : ℝ)≠0)] at hh
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  linarith

lemma modulus_power_bounds {D N : ℕ} (hD : (D+1)^22 ≤ N) :
    D ≤ N ∧ (D+1 : ℝ)^11 ≤ Real.sqrt N ∧ (D+1 : ℝ)^2 ≤ Real.sqrt N := by
  have hbase : (1 : ℝ) ≤ D+1 := by linarith [Nat.cast_nonneg (α := ℝ) D]
  have hpow : (D+1 : ℝ)^22 ≤ N := by exact_mod_cast hD
  have hs : (D+1 : ℝ)^11 ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    simpa only [←pow_mul] using hpow
  have hDN : D ≤ N := by
    have hh : D+1 ≤ (D+1)^22 := by
      have hh := pow_le_pow_right₀ (show 1 ≤ D+1 by omega) (show 1 ≤ 22 by omega)
      simpa using hh
    omega
  exact ⟨hDN,hs,(pow_le_pow_right₀ hbase (by norm_num : (2 : ℕ) ≤ 11)).trans hs⟩

/-- A scalar envelope for the total character error, for a small positive power of the modulus. -/
theorem characterErrorMean_envelope (k : ℕ) :
    ∃ X₀ : ℕ, ∀ R D X : ℕ, X₀ ≤ X → 1<R → Real.log R ≤ Real.sqrt (Real.log X) →
      1 ≤ Real.log X → (D+1)^22 ≤ X →
      characterErrorMean R D X ≤
        130*(R+1 : ℝ)^2*X*(Real.log X)^2/(Real.log X)^k+
          400*Real.sqrt X*(Real.log X)^3+10000000*X*(Real.log X)^9/(R : ℝ) := by
  obtain ⟨X₀,hX₀⟩ := primitiveErrorMean_bound k
  refine ⟨X₀,?_⟩
  intro R D X hX hR hlogR hL hD
  let L : ℝ := Real.log X
  have hL0 : 0<L := by dsimp [L]; linarith
  have hR0 : (0 : ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hlogX : 0 ≤ Real.log (X+1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X])
  have hlogXp := log_nat_add_one_le_twice hL
  have hX0 : 0<X := by
    by_contra h
    have hh : X=0 := by omega
    simp [hh] at hL
    linarith
  obtain ⟨hDX,hpow,hpow2⟩ := modulus_power_bounds hD
  have hlogD : Real.log D ≤ L := by
    by_cases hD0 : D=0
    · simp [hD0,L]; linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hD0) (by exact_mod_cast hDX)
  have hhalf : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2 : 0<Real.log 2 := by linarith
  have hratio : 3+Real.log D/Real.log 2 ≤ 5*L := by
    have hh := (div_le_iff₀ hl2).mpr (show Real.log D ≤ (2*L)*Real.log 2 by nlinarith)
    dsimp [L] at *
    linarith
  have hrat0 : 0 ≤ 3+Real.log D/Real.log 2 := by have hh := Real.log_natCast_nonneg D; positivity
  have hφ : totientWeightSum D ≤ 10*L^2 := by
    refine (totientWeightSum_log_bound D).trans ?_
    have hh := mul_le_mul hratio (show 1+Real.log D ≤ 2*L by dsimp [L] at *; linarith)
      (by linarith [Real.log_natCast_nonneg D] : 0 ≤ 1+Real.log D) (by positivity : 0 ≤ 5*L)
    nlinarith
  have hdepth : (Nat.log 2 X+1 : ℝ) ≤ 5*L := by
    have hh := natural_log_two_bound X
    dsimp [L] at *
    linarith
  have hLp : 1+Real.log (X+1 : ℝ) ≤ 3*L := by dsimp [L] at *; linarith
  have hprim := hX₀ R D X hX hR hlogR
  have hmean := characterErrorMean_conductor_bound R D X
  have htot : characterErrorMean R D X ≤ 10*L^2*
      ((R+1 : ℝ)^2*(13*X/L^k)+18*(D+1 : ℝ)^11*Real.log (X+1 : ℝ)+
        256*((3+Real.log D/Real.log 2)/(R : ℝ))*X*(1+Real.log (X+1 : ℝ))^6)+
      (D+1 : ℝ)^2*(Nat.log 2 X+1 : ℝ)*Real.log (X+1 : ℝ) := by
    refine hmean.trans (add_le_add ?_ le_rfl)
    exact mul_le_mul hφ hprim (by unfold primitiveErrorMean; apply Finset.sum_nonneg; intros; split_ifs <;> positivity) (by positivity)
  have hmain : 10*L^2*((R+1 : ℝ)^2*(13*X/L^k))=130*(R+1 : ℝ)^2*X*L^2/L^k := by ring
  have htypeI : 10*L^2*(18*(D+1 : ℝ)^11*Real.log (X+1 : ℝ)) ≤ 360*Real.sqrt X*L^3 := by
    calc
      _ ≤ 10*L^2*(18*Real.sqrt X*(2*L)) := by gcongr
      _ = _ := by ring
  have htypeII : 10*L^2*(256*((3+Real.log D/Real.log 2)/(R : ℝ))*X*(1+Real.log (X+1 : ℝ))^6) ≤
      10000000*X*L^9/(R : ℝ) := by
    calc
      _ ≤ 10*L^2*(256*((5*L)/(R : ℝ))*X*(3*L)^6) := by gcongr
      _ = 9331200*X*L^9/(R : ℝ) := by ring
      _ ≤ _ := by gcongr; norm_num
  have himp : (D+1 : ℝ)^2*(Nat.log 2 X+1 : ℝ)*Real.log (X+1 : ℝ) ≤ 10*Real.sqrt X*L^3 := by
    calc
      _ ≤ Real.sqrt X*(5*L)*(2*L) := by gcongr
      _ = 10*Real.sqrt X*L^2 := by ring
      _ ≤ _ := by gcongr <;> first | exact hL | norm_num
  change characterErrorMean R D X ≤ 130*(R+1 : ℝ)^2*X*L^2/L^k+400*Real.sqrt X*L^3+10000000*X*L^9/(R : ℝ)
  rw [mul_add,mul_add,hmain] at htot
  have hp : 0 ≤ Real.sqrt X*L^3 := by positivity
  linarith

end
end MaynardDevelopment
end

/- DistributionCutoff -/
section

open scoped Topology
open Complex Set Filter
namespace MaynardDevelopment
noncomputable section

def conductorCutoff (A X : ℕ) : ℕ := ⌊(Real.log X)^(A+12)⌋₊+1

lemma eventually_log_polynomial_le_sqrt (B : ℕ) (hB : 0<B) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ Real.log (3*L^B) ≤ Real.sqrt L := by
  have hBr : (0 : ℝ)<B := by exact_mod_cast hB
  have hε : 0<1/(2*(B : ℝ)) := by positivity
  have hl := (isLittleO_log_rpow_atTop (show (0 : ℝ)<1/2 by norm_num)).bound hε
  filter_upwards [hl,eventually_ge_atTop (16 : ℝ)] with L hlog hL
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0<L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hL1),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _),←Real.sqrt_eq_rpow] at hlog
  have hs : (4 : ℝ) ≤ Real.sqrt L := Real.le_sqrt_of_sq_le (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_left hlog hBr.le
  have heq : (B : ℝ)*(1/(2*(B : ℝ))*Real.sqrt L)=Real.sqrt L/2 := by field_simp
  rw [heq] at hmul
  refine ⟨hL1,?_⟩
  rw [Real.log_mul (by norm_num) (pow_pos hL0 _).ne',Real.log_pow]
  have hl3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<3)
  linarith

lemma conductorCutoff_eventual_bounds (A : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      1<conductorCutoff A X ∧ Real.log (conductorCutoff A X) ≤ Real.sqrt (Real.log X) ∧
        (Real.log X)^(A+12) ≤ (conductorCutoff A X : ℝ) ∧
        (conductorCutoff A X+1 : ℝ) ≤ 3*(Real.log X)^(A+12) ∧ 1 ≤ Real.log X := by
  have ht : Tendsto (fun X : ℕ => Real.log X) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_log_polynomial_le_sqrt (A+12) (by omega)),ht.eventually_ge_atTop 2] with X hL hL2
  have hpow1 : (1 : ℝ) ≤ (Real.log X)^(A+12) := one_le_pow₀ hL.1
  have hpow2 : (2 : ℝ) ≤ (Real.log X)^(A+12) := by
    have hh : Real.log X ≤ (Real.log X)^(A+12) := by
      simpa using pow_le_pow_right₀ hL.1 (show 1 ≤ A+12 by omega)
    linarith
  have hfloor := Nat.floor_le (show 0 ≤ (Real.log X)^(A+12) by positivity)
  have hfloor' := Nat.lt_floor_add_one ((Real.log X)^(A+12))
  have hRlower : (Real.log X)^(A+12) ≤ (conductorCutoff A X : ℝ) := by
    simpa only [conductorCutoff,Nat.cast_add,Nat.cast_one] using hfloor'.le
  have hRupper : (conductorCutoff A X+1 : ℝ) ≤ 3*(Real.log X)^(A+12) := by
    simp only [conductorCutoff,Nat.cast_add,Nat.cast_one]
    linarith
  have hR : 1<conductorCutoff A X := by
    have hh : (1 : ℝ)<conductorCutoff A X := by linarith
    exact_mod_cast hh
  refine ⟨hR,?_,hRlower,hRupper,hL.1⟩
  have hlog := Real.log_le_log (by exact_mod_cast (show 0<conductorCutoff A X by omega) : (0 : ℝ)<conductorCutoff A X)
    (show (conductorCutoff A X : ℝ) ≤ 3*(Real.log X)^(A+12) by linarith)
  exact hlog.trans hL.2

lemma conductorCutoff_tendsto_atTop (A : ℕ) : Tendsto (conductorCutoff A) atTop atTop := by
  have ht : Tendsto (fun X : ℕ => Real.log X) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_atTop.mpr
  intro B
  apply eventually_atTop.mp
  filter_upwards [conductorCutoff_eventual_bounds A,ht.eventually_ge_atTop (B : ℝ)] with X hX hB
  have hh : Real.log X ≤ (Real.log X)^(A+12) := by
    simpa using pow_le_pow_right₀ hX.2.2.2.2 (show 1 ≤ A+12 by omega)
  have hr : (B : ℝ) ≤ conductorCutoff A X := hB.trans (hh.trans hX.2.2.1)
  exact_mod_cast hr

lemma eventually_log_pow_le_sqrt (A : ℕ) :
    ∀ᶠ X : ℕ in atTop, (Real.log X)^(A+3) ≤ Real.sqrt X := by
  have hh := (isLittleO_log_rpow_rpow_atTop (A+3 : ℕ) (show (0 : ℝ)<1/2 by norm_num)).bound (by norm_num : (0 : ℝ)<1)
  have ht := tendsto_natCast_atTop_atTop.eventually hh
  filter_upwards [ht] with X hX
  simpa only [Real.rpow_natCast,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg X) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) _),one_mul,←Real.sqrt_eq_rpow,abs_of_nonneg (Real.sqrt_nonneg _)] using hX

lemma log_power_ratio_le {L : ℝ} (hL : 1 ≤ L) {a b c : ℕ} (hab : a+c ≤ b) :
    L^a/L^b ≤ 1/L^c := by
  have hL0 : 0<L := by linarith
  apply (div_le_div_iff₀ (pow_pos hL0 _) (pow_pos hL0 _)).mpr
  rw [←pow_add,one_mul]
  exact pow_le_pow_right₀ hL hab

end
end MaynardDevelopment
end

/- WeakCharacterDistribution -/
section

open scoped Topology
open Complex Set Filter
namespace MaynardDevelopment
noncomputable section

/-- A weak Bombieri--Vinogradov estimate at a fixed positive level, excluding one prime.
The power condition is deliberately non-optimal. -/
theorem characterErrorMean_log_saving (A : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ D : ℕ, (D+1)^22 ≤ X →
      characterErrorMean (conductorCutoff A X) D X ≤ 20000000*(X : ℝ)/(Real.log X)^A := by
  obtain ⟨X₀,hX₀⟩ := characterErrorMean_envelope (3*(A+12))
  filter_upwards [eventually_ge_atTop X₀,conductorCutoff_eventual_bounds A,eventually_log_pow_le_sqrt A]
    with X hX hR hpow D hD
  let L : ℝ := Real.log X
  let R := conductorCutoff A X
  have hL : 1 ≤ L := hR.2.2.2.2
  have hL0 : 0<L := by linarith
  have hR0 : (0 : ℝ)<R := by exact_mod_cast (show 0<R by exact lt_trans (by norm_num) hR.1)
  have hRlo : L^(A+12) ≤ (R : ℝ) := hR.2.2.1
  have hRhi : (R+1 : ℝ) ≤ 3*L^(A+12) := hR.2.2.2.1
  have hh := hX₀ R D X hX hR.1 hR.2.1 hL hD
  change characterErrorMean R D X ≤ 130*(R+1 : ℝ)^2*X*L^2/L^(3*(A+12))+
    400*Real.sqrt X*L^3+10000000*X*L^9/(R : ℝ) at hh
  have hsmall : 130*(R+1 : ℝ)^2*X*L^2/L^(3*(A+12)) ≤ 1170*X/L^A := by
    calc
      _ ≤ 130*(3*L^(A+12))^2*X*L^2/L^(3*(A+12)) := by gcongr
      _ = 1170*X*(L^(2*(A+12)+2)/L^(3*(A+12))) := by
        rw [pow_add,show 2*(A+12)=(A+12)*2 by omega,pow_mul]
        ring
      _ ≤ 1170*X*(1/L^A) := mul_le_mul_of_nonneg_left (log_power_ratio_le hL (by omega)) (by positivity)
      _ = _ := by ring
  have hlarge : 10000000*X*L^9/(R : ℝ) ≤ 10000000*X/L^A := by
    calc
      _ ≤ 10000000*X*L^9/L^(A+12) := div_le_div_of_nonneg_left (by positivity) (pow_pos hL0 _) hRlo
      _ = 10000000*X*(L^9/L^(A+12)) := by ring
      _ ≤ 10000000*X*(1/L^A) := mul_le_mul_of_nonneg_left (log_power_ratio_le hL (by omega)) (by positivity)
      _ = _ := by ring
  have hpower : 400*Real.sqrt X*L^3 ≤ 400*X/L^A := by
    apply (le_div_iff₀ (pow_pos hL0 _)).mpr
    calc
      _ = 400*Real.sqrt X*L^(A+3) := by rw [pow_add]; ring
      _ ≤ 400*Real.sqrt X*Real.sqrt X := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) X)]
  refine hh.trans ((add_le_add (add_le_add hsmall hpower) hlarge).trans ?_)
  rw [←add_div,←add_div]
  apply div_le_div_of_nonneg_right _ (pow_nonneg hL0.le _)
  nlinarith [Nat.cast_nonneg (α := ℝ) X]

end
end MaynardDevelopment
end

/- ProgressionDistribution -/
section

open scoped BigOperators Topology
open Complex Set Filter DirichletCharacter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

def progressionSum {q : ℕ} (a : ZMod q) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt.residueClass a n

def progressionError {q : ℕ} (a : ZMod q) (X : ℕ) : ℝ := progressionSum a X-(X : ℝ)/q.totient

def progressionWorst (q X : ℕ) : ℝ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    Finset.univ.sup' Finset.univ_nonempty (fun a : (ZMod q)ˣ => |progressionError (a : ZMod q) X|)

lemma principal_inv_unit_eval {q : ℕ} {a : ZMod q} (ha : IsUnit a) : (1 : DirichletCharacter ℂ q) a⁻¹=1 := by
  obtain ⟨u,rfl⟩ := ha
  have hi : IsUnit ((u : ZMod q)⁻¹) := by simpa using (u⁻¹).isUnit
  exact MulChar.one_apply hi

lemma primeErrorCoeff_orthogonality {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (n : ℕ) :
    (∑ χ : DirichletCharacter ℂ q, χ a⁻¹*primeErrorCoeff χ n) =
      (∑ χ : DirichletCharacter ℂ q, χ a⁻¹*χ n*(ArithmeticFunction.vonMangoldt n : ℂ))-natZeta n := by
  simp only [primeErrorCoeff,mul_sub,Finset.sum_sub_distrib,mul_ite,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,if_true,principal_inv_unit_eval ha,one_mul,mul_assoc]

lemma progressionError_character_identity {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (X : ℕ) :
    (progressionError a X : ℂ)=(q.totient : ℂ)⁻¹*∑ χ : DirichletCharacter ℂ q, χ a⁻¹*primeCharacterError χ X := by
  have hsumζ : (∑ n ∈ Finset.Icc 1 X, natZeta n)=(X : ℂ) := by
    have hval : ∀ n ∈ Finset.Icc 1 X, natZeta n=1 := by
      intro n hn
      have hn0 : n≠0 := by have hh := (Finset.mem_Icc.mp hn).1; omega
      simp [natZeta,hn0]
    simp only [Finset.sum_congr rfl hval,Finset.sum_const,Nat.card_Icc, nsmul_eq_mul]
    simp
  simp only [primeCharacterError,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum]
  simp_rw [primeErrorCoeff_orthogonality ha]
  rw [Finset.sum_sub_distrib,hsumζ,mul_sub,Finset.mul_sum]
  simp_rw [←ArithmeticFunction.vonMangoldt.residueClass_apply ha]
  simp only [progressionError,progressionSum,Complex.ofReal_sub,Complex.ofReal_sum,Complex.ofReal_div,
    Complex.ofReal_natCast,Complex.ofReal_mul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]

lemma progressionError_le_character_mean {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (X : ℕ) :
    |progressionError a X| ≤ (q.totient : ℝ)⁻¹*∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError χ X‖ := by
  rw [←Real.norm_eq_abs,←Complex.norm_real,progressionError_character_identity ha,norm_mul,norm_inv,Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ a⁻¹*primeCharacterError χ X‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro χ hχ
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

lemma progressionWorst_nonneg (q X : ℕ) : 0 ≤ progressionWorst q X := by
  unfold progressionWorst
  split_ifs with hq
  · exact le_rfl
  · haveI : NeZero q := ⟨hq⟩
    exact (abs_nonneg (progressionError (1 : ZMod q) X)).trans
      (Finset.le_sup' (fun a : (ZMod q)ˣ => |progressionError (a : ZMod q) X|) (Finset.mem_univ (1 : (ZMod q)ˣ)))

lemma progressionError_le_worst {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (X : ℕ) :
    |progressionError a X| ≤ progressionWorst q X := by
  rw [progressionWorst,dif_neg (NeZero.ne q)]
  obtain ⟨u,rfl⟩ := ha
  exact Finset.le_sup' (fun a : (ZMod q)ˣ => |progressionError (a : ZMod q) X|) (Finset.mem_univ u)

lemma progressionWorst_le_character_mean {q : ℕ} [NeZero q] (X : ℕ) :
    progressionWorst q X ≤ (q.totient : ℝ)⁻¹*∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError χ X‖ := by
  rw [progressionWorst,dif_neg (NeZero.ne q)]
  apply Finset.sup'_le
  intro a ha
  exact progressionError_le_character_mean a.isUnit X

/-- Unweighted positive-level distribution for primes in progressions, with one prime omitted. -/
theorem progressionWorst_log_saving (A : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ D : ℕ, (D+1)^22 ≤ X →
      (∑ q ∈ Finset.Icc 1 D, if GoodModulus (conductorCutoff A X) q then progressionWorst q X else 0) ≤
        20000000*(X : ℝ)/(Real.log X)^A := by
  filter_upwards [characterErrorMean_log_saving A] with X hX D hD
  refine le_trans ?_ (hX D hD)
  unfold characterErrorMean
  apply Finset.sum_le_sum
  intro q hq
  have hq0 : q≠0 := by have hh := (Finset.mem_Icc.mp hq).1; omega
  letI : NeZero q := ⟨hq0⟩
  split_ifs
  · exact progressionWorst_le_character_mean X
  · exact le_rfl

end
end MaynardDevelopment
end

/- ProgressionTrivial -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section

lemma card_residue_interval {q : ℕ} [NeZero q] (a : ZMod q) (X : ℕ) :
    ((Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q)=a)).card ≤ X/q+1 := by
  classical
  calc
    _ ≤ (Finset.range (X/q+1)).card := ?_
    _ = _ := Finset.card_range _
  apply Finset.card_le_card_of_injOn (fun n : ℕ => n/q)
  · intro n hn
    change n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q)=a) at hn
    apply Finset.mem_range.mpr
    have hnX := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hnX)
  · intro n hn m hm he
    change n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q)=a) at hn
    change m ∈ (Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q)=a) at hm
    have hr : n % q=m % q := (ZMod.natCast_eq_natCast_iff' n m q).mp
      ((Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm)
    have hn' := Nat.mod_add_div n q
    have hm' := Nat.mod_add_div m q
    change n/q=m/q at he
    rw [hr, he] at hn'
    omega

lemma progressionSum_nonneg {q : ℕ} (a : ZMod q) (X : ℕ) : 0 ≤ progressionSum a X := by
  apply Finset.sum_nonneg
  intro n hn
  unfold ArithmeticFunction.vonMangoldt.residueClass
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

lemma progressionSum_trivial {q : ℕ} [NeZero q] (a : ZMod q) (X : ℕ) :
    progressionSum a X ≤ ((X/q : ℕ)+1 : ℝ)*Real.log (X+1) := by
  classical
  have he : progressionSum a X = ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q)=a),
      ArithmeticFunction.vonMangoldt n := by
    simp [progressionSum, ArithmeticFunction.vonMangoldt.residueClass, Finset.sum_filter, Set.indicator_apply]
  rw [he]
  calc
    _ ≤ ∑ _n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q)=a), Real.log (X+1) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hn'.1) (by exact_mod_cast (by omega : n ≤ X+1)))
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by have hh : (0 : ℝ) ≤ X := Nat.cast_nonneg X; linarith))
      exact_mod_cast card_residue_interval a X

lemma progressionError_trivial {q : ℕ} [NeZero q] (a : ZMod q) (X : ℕ) :
    |progressionError a X| ≤ ((X/q : ℕ)+1 : ℝ)*Real.log (X+1)+(X : ℝ)/q.totient := by
  unfold progressionError
  exact (abs_sub _ _).trans (by
    rw [abs_of_nonneg (progressionSum_nonneg a X), abs_of_nonneg (by positivity : 0 ≤ (X : ℝ)/q.totient)]
    exact add_le_add (progressionSum_trivial a X) le_rfl)

lemma progressionWorst_trivial {q : ℕ} [NeZero q] (X : ℕ) :
    progressionWorst q X ≤ ((X/q : ℕ)+1 : ℝ)*Real.log (X+1)+(X : ℝ)/q.totient := by
  rw [progressionWorst,dif_neg (NeZero.ne q)]
  apply Finset.sup'_le
  intro a ha
  exact progressionError_trivial (a : ZMod q) X

lemma progressionWorst_harmonic {q : ℕ} [NeZero q] (X : ℕ) (hqX : q ≤ X) :
    progressionWorst q X ≤ 8*(X : ℝ)*(1+Real.log (X+1))/q := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hX : (0 : ℝ) < X := lt_of_lt_of_le hq (by exact_mod_cast hqX)
  have hL : 0 ≤ Real.log (X+1) := Real.log_nonneg (by linarith)
  have htwo : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hqlog : Real.log q ≤ Real.log (X+1) := Real.log_le_log hq (by exact_mod_cast (by omega : q ≤ X+1))
  have ht := totient_ratio_log_bound q 1 (NeZero.ne q) (by decide)
  norm_num at ht
  have hratio : (q : ℝ)/q.totient ≤ 3+2*Real.log (X+1) := by
    have hd : Real.log q/Real.log 2 ≤ 2*Real.log (X+1) := by
      apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
      nlinarith
    linarith
  have hmul : (X : ℝ)/q.totient ≤ (X : ℝ)/q*(3+2*Real.log (X+1)) := by
    have hh := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ (X : ℝ)/q)
    simpa only [div_mul_div_cancel₀ hq.ne'] using hh
  have hdiv : (X/q : ℕ)+1 ≤ (2 : ℝ)*X/q := by
    have hcast : ((X/q : ℕ) : ℝ) ≤ (X : ℝ)/q := Nat.cast_div_le
    have hge : (1 : ℝ) ≤ (X : ℝ)/q := (le_div_iff₀ hq).mpr (by simpa using (show (q : ℝ) ≤ X by exact_mod_cast hqX))
    rw [mul_div_assoc]
    linarith
  calc
    _ ≤ ((X/q : ℕ)+1 : ℝ)*Real.log (X+1)+(X : ℝ)/q.totient := progressionWorst_trivial X
    _ ≤ (2*(X : ℝ)/q)*Real.log (X+1)+(X : ℝ)/q*(3+2*Real.log (X+1)) :=
      add_le_add (mul_le_mul_of_nonneg_right hdiv hL) hmul
    _ ≤ _ := by
      apply (le_div_iff₀ hq).mpr
      field_simp
      nlinarith [mul_nonneg hX.le hL]


end
end MaynardDevelopment
end

/- HigherDivisorMoments -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section

lemma zeta_pow_nonneg (k n : ℕ) : 0 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^k) n := by
  induction k generalizing n with
  | zero => simp only [pow_zero, ArithmeticFunction.one_apply]; split_ifs <;> positivity
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply]
    apply Finset.sum_nonneg
    intro de hde
    apply mul_nonneg (ih _)
    simp only [ArithmeticFunction.natCoe_apply]
    positivity

lemma divisor_pow_le_zeta (k n : ℕ) (hn : n ≠ 0) :
    (n.divisors.card : ℝ)^k ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^(2^k)) n := by
  induction k generalizing n with
  | zero => simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hn]
  | succ k ih =>
    have he : (ArithmeticFunction.zeta : ArithmeticFunction ℝ)^(2^(k+1)) =
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)^(2^k) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)^(2^k) := by
      rw [pow_succ, pow_mul, pow_two]
    rw [he, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (fun d e => ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^(2^k)) d *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^(2^k)) e)]
    calc
      _ = ∑ _d ∈ n.divisors, (n.divisors.card : ℝ)^k := by simp [pow_succ, mul_comm]
      _ ≤ ∑ d ∈ n.divisors, (d.divisors.card : ℝ)^k * ((n/d).divisors.card : ℝ)^k := by
        apply Finset.sum_le_sum
        intro d hd
        rw [← mul_pow]
        apply pow_le_pow_left₀ (by positivity)
        exact_mod_cast (show n.divisors.card ≤ d.divisors.card * (n/d).divisors.card by
          have hh := card_divisors_mul_le d (n/d)
          rwa [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)] at hh)
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro d hd
        have hd0 := (Nat.pos_of_mem_divisors hd).ne'
        have he0 : n/d ≠ 0 := by
          intro he0
          have hh := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
          simp [he0] at hh
          exact hn hh.symm
        exact mul_le_mul (ih d hd0) (ih (n/d) he0)
          (by positivity) (zeta_pow_nonneg _ _)


lemma sum_zeta_pow_div_le (k X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^k) n / n) ≤
      (harmonic X : ℝ)^k := by
  induction k generalizing X with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply]
    by_cases hX : 1 ≤ X
    · simp only [ite_div, zero_div]
      simp [hX]
    · have : X=0 := by omega
      simp [this]
  | succ k ih =>
    simp_rw [pow_succ', div_eq_mul_inv]
    rw [sum_convolution_weighted]
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 X, (d : ℝ)⁻¹ * (harmonic (X/d) : ℝ)^k := by
        apply Finset.sum_le_sum
        intro d hd
        have hd0 : d≠0 := by have hh := (Finset.mem_Icc.mp hd).1; omega
        simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hd0, if_false,
          Nat.cast_one, one_mul, Nat.cast_mul, mul_inv_rev]
        have he (x : ℕ) : ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^k) x *
            ((x : ℝ)⁻¹*(d : ℝ)⁻¹) = (d : ℝ)⁻¹ *
              (((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^k) x * (x : ℝ)⁻¹) := by ring
        simp only [he]
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (by simpa only [div_eq_mul_inv] using ih (X/d)) (by positivity)
      _ ≤ ∑ d ∈ Finset.Icc 1 X, (d : ℝ)⁻¹ * (harmonic X : ℝ)^k := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (harmonic_real_nonneg _) (harmonic_real_mono (Nat.div_le_self X d)) _) (by positivity)
      _ = _ := by rw [← Finset.sum_mul, ← harmonic_real_sum]

lemma sum_divisor_pow_div_le (k X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (n.divisors.card : ℝ)^k / n) ≤ (1+Real.log X)^(2^k) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^(2^k)) n / n := by
      apply Finset.sum_le_sum
      intro n hn
      exact div_le_div_of_nonneg_right (divisor_pow_le_zeta k n (by have hh := (Finset.mem_Icc.mp hn).1; omega)) (by positivity)
    _ ≤ (harmonic X : ℝ)^(2^k) := sum_zeta_pow_div_le _ _
    _ ≤ _ := pow_le_pow_left₀ (harmonic_real_nonneg _) (harmonic_le_one_add_log X) _

end
end MaynardDevelopment
end

/- RoughHarmonic -/
section

open scoped BigOperators Topology
open Filter
namespace MaynardDevelopment
noncomputable section

lemma norm_sum_mul_antitone_le (c : ℕ → ℂ) (f : ℕ → ℝ) (N : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (hf : Antitone f) (hf0 : ∀ n, 0 ≤ f n)
    (hc : ∀ k ≤ N, ‖∑ n ∈ Finset.range k, c n‖ ≤ C) :
    ‖∑ n ∈ Finset.range N, c n * (f n : ℂ)‖ ≤ C * f 0 := by
  have hdiff (n : ℕ) : f (n+1) ≤ f n := hf (Nat.le_succ n)
  rw [sum_mul_abel]
  calc
    _ ≤ ‖(∑ n ∈ Finset.range N, c n)*(f N : ℂ)‖ +
        ‖∑ n ∈ Finset.range N, (∑ j ∈ Finset.range (n+1), c j)*((f (n+1) : ℂ)-f n)‖ := norm_sub_le _ _
    _ ≤ C*f N+∑ n ∈ Finset.range N, C*(f n-f (n+1)) := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 N)]
        exact mul_le_mul_of_nonneg_right (hc N le_rfl) (hf0 N)
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr (hdiff n)), neg_sub]
        exact mul_le_mul_of_nonneg_right (hc (n+1) (by have := Finset.mem_range.mp hn; omega))
          (sub_nonneg.mpr (hdiff n))
    _ = _ := by
      rw [← Finset.mul_sum]
      have hh : (∑ n ∈ Finset.range N, (f n-f (n+1)))=f 0-f N := by
        simpa only [← Finset.sum_neg_distrib, neg_sub] using congrArg Neg.neg (Finset.sum_range_sub f N)
      rw [hh]
      ring

def roughDensity (W : ℕ) : ℝ := (W.totient : ℝ)/W

def roughHarmonic (W X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, if W.Coprime n then (n : ℝ)⁻¹ else 0

lemma roughDensity_pos {W : ℕ} (hW : W≠0) : 0 < roughDensity W := by
  apply div_pos
  · exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW)
  · exact_mod_cast Nat.pos_of_ne_zero hW

lemma roughDensity_le_one (W : ℕ) : roughDensity W ≤ 1 := by
  by_cases hW : W=0
  · simp [roughDensity,hW]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hW : (0 : ℝ)<W)).mpr
    exact_mod_cast Nat.totient_le W

lemma roughHarmonic_nonneg (W X : ℕ) : 0 ≤ roughHarmonic W X := by
  apply Finset.sum_nonneg
  intros
  split_ifs <;> positivity

lemma roughHarmonic_mono (W : ℕ) : Monotone (roughHarmonic W) := by
  intro X Y hXY
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hXY)
  intros
  split_ifs <;> positivity

lemma roughHarmonic_error (W X : ℕ) (hW : W≠0) :
    |roughHarmonic W X-roughDensity W*(harmonic X : ℝ)| ≤ 2*(W : ℝ) := by
  let c (n : ℕ) : ℂ := (if W.Coprime n then 1 else 0) - (roughDensity W : ℂ)
  have hc : ∀ n, ‖c n‖ ≤ 1 := by
    intro n
    have hc0 := (roughDensity_pos hW).le
    have hc1 := roughDensity_le_one W
    dsimp [c]
    split_ifs
    · rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      linarith
    · simpa [abs_of_nonneg hc0] using hc1
  have hp : Function.Periodic c W := by
    intro n
    simp [c, Nat.coprime_add_self_right]
  have hs : (∑ n ∈ Finset.range W, c n)=0 := by
    simp only [c, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hh : (∑ n ∈ Finset.range W, if W.Coprime n then (1 : ℂ) else 0)=(W.totient : ℂ) := by
      simp only [Finset.sum_boole, Nat.totient_eq_card_coprime]
    rw [hh]
    simp only [roughDensity, Complex.ofReal_div, Complex.ofReal_natCast]
    have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW
    field_simp
    ring
  have hsum (N : ℕ) : ‖∑ n ∈ Finset.range N, c (n+1)‖ ≤ 2*(W : ℝ) := by
    have hh := norm_sum_Ico_periodic_zero_le (Nat.pos_of_ne_zero hW) hp hs hc 1 N
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at hh
    simpa only [Nat.add_comm] using hh
  have hf : Antitone (fun n : ℕ => (n+1 : ℝ)⁻¹) := by
    intro n m hnm
    apply inv_anti₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hh := norm_sum_mul_antitone_le (fun n => c (n+1)) (fun n : ℕ => (n+1 : ℝ)⁻¹) X
    (by positivity : 0 ≤ 2*(W : ℝ)) hf (fun n => by positivity) (fun n _ => hsum n)
  have hid : (∑ n ∈ Finset.range X, c (n+1)*Complex.ofReal ((n+1 : ℝ)⁻¹)) =
      Complex.ofReal (roughHarmonic W X-roughDensity W*(harmonic X : ℝ)) := by
    rw [harmonic_real_sum]
    simp only [roughHarmonic, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum,
      Complex.ofReal_inv, Complex.ofReal_natCast, Finset.mul_sum, ← Finset.sum_sub_distrib,
      sum_Icc_one_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [c]
    split_ifs <;> push_cast <;> ring
  rw [hid, Complex.norm_real, Real.norm_eq_abs] at hh
  simpa using hh

lemma roughHarmonic_log_error (W X : ℕ) (hW : W≠0) (hX : X≠0) :
    |roughHarmonic W X-roughDensity W*Real.log X| ≤ 2*(W : ℝ)+1 := by
  have hXr : (0 : ℝ)<X := by exact_mod_cast Nat.pos_of_ne_zero hX
  have hlo : Real.log X ≤ (harmonic X : ℝ) :=
    (Real.log_le_log hXr (show (X : ℝ) ≤ (X+1 : ℕ) by push_cast; linarith)).trans (log_add_one_le_harmonic X)
  have hhi := harmonic_le_one_add_log X
  have herr : |roughDensity W*((harmonic X : ℝ)-Real.log X)| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg (roughDensity_pos hW).le (sub_nonneg.mpr hlo))]
    exact (mul_le_mul (roughDensity_le_one W) (show (harmonic X : ℝ)-Real.log X ≤ 1 by linarith)
      (sub_nonneg.mpr hlo) zero_le_one).trans_eq (by ring)
  calc
    _ = |(roughHarmonic W X-roughDensity W*(harmonic X : ℝ))+
        roughDensity W*((harmonic X : ℝ)-Real.log X)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add (roughHarmonic_error W X hW) herr)

lemma roughHarmonic_power_tendsto (W b : ℕ) (hW : W≠0) :
    Tendsto (fun R : ℕ => roughHarmonic W (R^b)/Real.log R) atTop (𝓝 (roughDensity W*b)) := by
  have hL : Tendsto (fun R : ℕ => Real.log R) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ R : ℕ in atTop,
      |roughHarmonic W (R^b)-roughDensity W*b*Real.log R| ≤ 2*(W : ℝ)+1 := by
    filter_upwards [eventually_ge_atTop 1] with R hR
    have hh := roughHarmonic_log_error W (R^b) hW (pow_ne_zero _ (by omega))
    simpa only [Nat.cast_pow, Real.log_pow, mul_assoc, mul_left_comm, mul_comm] using hh
  have hbound : ∀ᶠ R : ℕ in atTop,
      |roughHarmonic W (R^b)/Real.log R-roughDensity W*b| ≤ (2*(W : ℝ)+1)/Real.log R := by
    filter_upwards [he, hL.eventually (eventually_gt_atTop 0)] with R he hR
    have hid : roughHarmonic W (R^b)/Real.log R-roughDensity W*b =
        (roughHarmonic W (R^b)-roughDensity W*b*Real.log R)/Real.log R := by field_simp
    rw [hid, abs_div, abs_of_pos hR]
    exact div_le_div_of_nonneg_right he hR.le
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun R : ℕ => roughDensity W*b-(2*(W : ℝ)+1)/Real.log R)
    (h := fun R : ℕ => roughDensity W*b+(2*(W : ℝ)+1)/Real.log R)
  · simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hL)
  · simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hL)
  · filter_upwards [hbound] with R hR; linarith [(abs_le.mp hR).1]
  · filter_upwards [hbound] with R hR; linarith [(abs_le.mp hR).2]

end
end MaynardDevelopment
end

/- PrimeHarmonicMoment -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section

lemma nat_div_half_lower {N d : ℕ} (hd : 0<d) (hdN : d≤N) :
    (N : ℝ)/d ≤ 2*(N/d : ℕ) := by
  have hfloor : N < (N/d+1)*d := by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ N hd
  have hquot : 1 ≤ N/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hdN)
  have hfloorR : (N : ℝ)<((N/d : ℕ)+1 : ℝ)*d := by exact_mod_cast hfloor
  have hquotR : (1 : ℝ)≤(N/d : ℕ) := by exact_mod_cast hquot
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  apply (div_le_iff₀ hdR).mpr
  nlinarith

lemma mangoldt_harmonic_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n/(n : ℝ)) ≤ 2*Real.log N := by
  by_cases hN : N=0
  · simp [hN]
  have hNR : (0 : ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hid : (∑ n ∈ Finset.Icc 1 N, Real.log n) =
      ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d*(N/d : ℕ) := by
    have hh := sum_convolution N ArithmeticFunction.vonMangoldt (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
    rw [ArithmeticFunction.vonMangoldt_mul_zeta] at hh
    simp only [ArithmeticFunction.log_apply] at hh
    rw [hh]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Finset.mul_sum]
    have he (e : ℕ) (he : e ∈ Finset.Icc 1 (N/d)) :
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) e=1 := by
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
        (show e≠0 by have hh := (Finset.mem_Icc.mp he).1; omega)]
    simp only [Finset.sum_congr rfl he, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    simp
  have hlog : (∑ n ∈ Finset.Icc 1 N, Real.log n) ≤ (N : ℝ)*Real.log N := by
    calc
      _ ≤ ∑ _n ∈ Finset.Icc 1 N, Real.log N := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' := Finset.mem_Icc.mp hn
        exact Real.log_le_log (by exact_mod_cast hn'.1) (by exact_mod_cast hn'.2)
      _ = _ := by simp
  have hbound : (N : ℝ)*(∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n/(n : ℝ)) ≤
      2*(∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d*(N/d : ℕ)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have hh := mul_le_mul_of_nonneg_left (nat_div_half_lower hn'.1 hn'.2)
      (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    convert hh using 1 <;> ring
  rw [← hid] at hbound
  nlinarith

lemma prime_harmonic_log_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (N : ℕ)
    (hPN : ∀ p ∈ P, p≤N) :
    (∑ p ∈ P, Real.log p/(p : ℝ)) ≤ 2*Real.log N := by
  calc
    _ = ∑ p ∈ P, ArithmeticFunction.vonMangoldt p/(p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [ArithmeticFunction.vonMangoldt_apply_prime (hP p hp)]
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n/(n : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact Finset.mem_Icc.mpr ⟨(hP p hp).one_le,hPN p hp⟩
      · intros; exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    _ ≤ _ := mangoldt_harmonic_le N

end
end MaynardDevelopment
end

/- FiniteEuler -/
section

open scoped BigOperators Topology
open Filter
namespace MaynardDevelopment
noncomputable section

lemma powerset_prod_sum {α : Type*} (P : Finset α) (w : α → ℝ) :
    (∑ s ∈ P.powerset, ∏ p ∈ s, w p) = ∏ p ∈ P, (1+w p) := by
  classical
  simpa [add_comm] using (Finset.prod_add w (fun _ => 1) P).symm

lemma powerset_moment {α : Type*} [DecidableEq α] (P : Finset α) (w l : α → ℝ) :
    (∑ s ∈ P.powerset, (∏ p ∈ s, w p)*(∑ p ∈ s, l p)) =
      ∑ p ∈ P, w p*l p*∏ q ∈ P.erase p, (1+w q) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    rw [Finset.sum_powerset_insert hp]
    have hs : ∀ s ∈ P.powerset, p ∉ s := fun s hs => fun hh => hp ((Finset.mem_powerset.mp hs) hh)
    have hterm : (∑ s ∈ P.powerset, (∏ q ∈ insert p s, w q)*(∑ q ∈ insert p s, l q)) =
        w p*l p*(∑ s ∈ P.powerset, ∏ q ∈ s, w q) +
        w p*(∑ s ∈ P.powerset, (∏ q ∈ s, w q)*(∑ q ∈ s, l q)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs'
      rw [Finset.prod_insert (hs s hs'), Finset.sum_insert (hs s hs')]
      ring
    rw [hterm, powerset_prod_sum, ih, Finset.sum_insert hp, Finset.erase_insert hp]
    have he : (∑ q ∈ P, w q*l q*∏ r ∈ (insert p P).erase q, (1+w r)) =
        (1+w p)*(∑ q ∈ P, w q*l q*∏ r ∈ P.erase q, (1+w r)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hqp : q≠p := by intro he; subst q; contradiction
      rw [Finset.erase_insert_of_ne hqp.symm, Finset.prod_insert (by simp [hp])]
      ring
    rw [he]
    ring

def primeSetProduct (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

def harmonicEuler (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1+(p : ℝ)⁻¹)

lemma primeSetProduct_injOn (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    Set.InjOn primeSetProduct (P.powerset : Set (Finset ℕ)) := by
  intro s hs t ht he
  have hs' := Finset.mem_powerset.mp hs
  have ht' := Finset.mem_powerset.mp ht
  have hh := congrArg Nat.primeFactors he
  dsimp only [primeSetProduct] at hh
  rwa [Nat.primeFactors_prod (fun p hp => hP p (hs' hp)),
    Nat.primeFactors_prod (fun p hp => hP p (ht' hp))] at hh

lemma primeSetProduct_pos (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    0 < primeSetProduct s := Finset.prod_pos (fun p hp => (hs p hp).pos)

lemma primeSetProduct_weight (s : Finset ℕ) :
    (primeSetProduct s : ℝ)⁻¹ = ∏ p ∈ s, (p : ℝ)⁻¹ := by
  simp [primeSetProduct, Finset.prod_inv_distrib]

lemma primeSetProduct_log (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    Real.log (primeSetProduct s) = ∑ p ∈ s, Real.log p := by
  rw [primeSetProduct, Nat.cast_prod, Real.log_prod]
  intro p hp
  exact_mod_cast (hs p hp).ne_zero

lemma powerset_truncated_harmonic_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (W Y : ℕ) (hW : ∀ p ∈ P, W.Coprime p) :
    (∑ s ∈ P.powerset.filter (fun s => primeSetProduct s≤Y), (primeSetProduct s : ℝ)⁻¹) ≤ roughHarmonic W Y := by
  classical
  let S := P.powerset.filter (fun s => primeSetProduct s≤Y)
  have hi : Set.InjOn primeSetProduct (S : Set (Finset ℕ)) :=
    (primeSetProduct_injOn P hP).mono (by intro s hs; exact (Finset.mem_filter.mp hs).1)
  have he : (∑ s ∈ S, (primeSetProduct s : ℝ)⁻¹) =
      ∑ n ∈ S.image primeSetProduct, if W.Coprime n then (n : ℝ)⁻¹ else 0 := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro s hs
    have hs' := Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1
    change _ = if W.Coprime (∏ p ∈ s, p) then _ else _
    rw [if_pos (Nat.Coprime.prod_right (fun p hp => hW p (hs' hp)))]
  change (∑ s ∈ S, (primeSetProduct s : ℝ)⁻¹) ≤ _
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hn
    have hs' := Finset.mem_filter.mp hs
    exact Finset.mem_Icc.mpr ⟨primeSetProduct_pos s (fun p hp => hP p ((Finset.mem_powerset.mp hs'.1) hp)),hs'.2⟩
  · intros; split_ifs <;> positivity

lemma harmonicEuler_moment_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (N : ℕ)
    (hPN : ∀ p ∈ P, p≤N) :
    (∑ s ∈ P.powerset, (primeSetProduct s : ℝ)⁻¹*Real.log (primeSetProduct s)) ≤
      harmonicEuler P*(2*Real.log N) := by
  have hid : (∑ s ∈ P.powerset, (primeSetProduct s : ℝ)⁻¹*Real.log (primeSetProduct s)) =
      ∑ p ∈ P, (p : ℝ)⁻¹*Real.log p*∏ q ∈ P.erase p, (1+(q : ℝ)⁻¹) := by
    rw [← powerset_moment]
    apply Finset.sum_congr rfl
    intro s hs
    rw [primeSetProduct_weight, primeSetProduct_log s (fun p hp => hP p ((Finset.mem_powerset.mp hs) hp))]
  rw [hid]
  calc
    _ ≤ ∑ p ∈ P, (p : ℝ)⁻¹*Real.log p*harmonicEuler P := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (Real.log_natCast_nonneg p))
      unfold harmonicEuler
      rw [← Finset.mul_prod_erase P (fun q : ℕ => 1+(q : ℝ)⁻¹) hp]
      have hh : 0 ≤ ∏ q ∈ P.erase p, (1+(q : ℝ)⁻¹) := by positivity
      have hi : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
      nlinarith
    _ = harmonicEuler P*(∑ p ∈ P, Real.log p/(p : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_harmonic_log_le P hP N hPN) (by unfold harmonicEuler; positivity)

/-- Elementary Mertens upper bound, with all fixed forbidden primes retained in the density. -/
lemma harmonicEuler_le_roughHarmonic (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (W N : ℕ) (hW : ∀ p ∈ P, W.Coprime p) (hN : 1<N) (hPN : ∀ p ∈ P, p≤N) :
    harmonicEuler P ≤ 2*roughHarmonic W (N^4) := by
  classical
  let S := P.powerset.filter (fun s => primeSetProduct s≤N^4)
  let B := P.powerset.filter (fun s => ¬primeSetProduct s≤N^4)
  let w (s : Finset ℕ) : ℝ := (primeSetProduct s : ℝ)⁻¹
  have hlog : 0<Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hall : (∑ s ∈ S, w s)+(∑ s ∈ B, w s)=harmonicEuler P := by
    rw [Finset.sum_filter_add_sum_filter_not]
    simp only [w, primeSetProduct_weight]
    exact powerset_prod_sum P _
  have htail : (4*Real.log N)*(∑ s ∈ B, w s) ≤ harmonicEuler P*(2*Real.log N) := by
    calc
      _ ≤ ∑ s ∈ B, w s*Real.log (primeSetProduct s) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro s hs
        have hs' := Finset.mem_filter.mp hs
        have hn : N^4<primeSetProduct s := by omega
        have hh := Real.log_le_log (show (0 : ℝ)<(N^4 : ℕ) by positivity)
          (show ((N^4 : ℕ) : ℝ) ≤ primeSetProduct s by exact_mod_cast hn.le)
        rw [Nat.cast_pow, Real.log_pow] at hh
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (by dsimp [w]; positivity)
      _ ≤ ∑ s ∈ P.powerset, w s*Real.log (primeSetProduct s) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro s hs hsB
        exact mul_nonneg (by dsimp [w]; positivity) (Real.log_natCast_nonneg _)
      _ ≤ _ := harmonicEuler_moment_le P hP N hPN
  have hlow := powerset_truncated_harmonic_le P hP W (N^4) hW
  change (∑ s ∈ S, w s) ≤ _ at hlow
  nlinarith

lemma harmonicEuler_power_bound (W T : ℕ) (hW : W≠0) (hT : 0<T) :
    ∀ᶠ R : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) →
      (∀ p ∈ P, W.Coprime p) → (∀ p ∈ P, p≤R^T) →
      harmonicEuler P ≤ 16*T*roughDensity W*Real.log R := by
  have hL := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpos : 0 < 4*(T : ℝ)*roughDensity W := by
    have hh := roughDensity_pos hW
    have ht : (0 : ℝ)<T := by exact_mod_cast hT
    positivity
  have hb : ∀ᶠ R : ℕ in atTop, (2*(W : ℝ)+1) ≤ 4*T*roughDensity W*Real.log R :=
    (hL.const_mul_atTop hpos).eventually (eventually_ge_atTop _)
  filter_upwards [hb,eventually_ge_atTop 2] with R hR hR2 P hP hc hPN
  have hRT : 1<R^T := one_lt_pow₀ (by omega : 1<R) (by omega)
  have he := harmonicEuler_le_roughHarmonic P hP W (R^T) hc hRT hPN
  have hh := (abs_le.mp (roughHarmonic_log_error W ((R^T)^4) hW (by positivity))).2
  rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  nlinarith


end
end MaynardDevelopment
end

/- HarmonicMultiples -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section

lemma roughHarmonic_multiples_le (W X d : ℕ) (hd : d≠0) :
    (∑ n ∈ Finset.Icc 1 X, if W.Coprime n ∧ d∣n then (n : ℝ)⁻¹ else 0) ≤ roughHarmonic W X/d := by
  classical
  let S := (Finset.Icc 1 X).filter (fun n => W.Coprime n ∧ d∣n)
  have hi : Set.InjOn (fun n => n/d) (S : Set ℕ) := by
    intro n hn m hm he
    change n ∈ S at hn
    change m ∈ S at hm
    have hn' := Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2.2
    have hm' := Nat.mul_div_cancel' (Finset.mem_filter.mp hm).2.2
    change n/d=m/d at he
    rw [he] at hn'
    omega
  have he : (∑ n ∈ Finset.Icc 1 X, if W.Coprime n ∧ d∣n then (n : ℝ)⁻¹ else 0) =
      (∑ m ∈ S.image (fun n => n/d), if W.Coprime m then (m : ℝ)⁻¹ else 0)/d := by
    rw [Finset.sum_image hi, Finset.sum_div]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have heq : d*(n/d)=n := Nat.mul_div_cancel' hn'.2.2
    have hc : W.Coprime (n/d) := hn'.2.1.of_dvd_right (Nat.div_dvd_of_dvd hn'.2.2)
    rw [if_pos hc]
    have heqr : (d : ℝ)*(n/d : ℕ)=n := by exact_mod_cast heq
    rw [← heqr, mul_inv_rev, div_eq_mul_inv]
  rw [he]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    have hn' := Finset.mem_filter.mp hn
    have hnI := Finset.mem_Icc.mp hn'.1
    have heq : d*(n/d)=n := Nat.mul_div_cancel' hn'.2.2
    have hpos : 0<n/d := by nlinarith
    exact Finset.mem_Icc.mpr ⟨hpos, (Nat.div_le_self n d).trans hnI.2⟩
  · intros; split_ifs <;> positivity

lemma inverse_square_step (n : ℕ) (hn : 0<n) :
    ((n+1 : ℝ)^2)⁻¹ ≤ (n : ℝ)⁻¹-(n+1 : ℝ)⁻¹ := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  field_simp
  nlinarith

lemma sum_inverse_square_tail (B N : ℕ) (hB : 0<B) :
    (∑ n ∈ Finset.Ioc B N, ((n : ℝ)^2)⁻¹) ≤ (B : ℝ)⁻¹ := by
  have hsum : ∀ M : ℕ, (∑ j ∈ Finset.range M, ((B+j+1 : ℝ)^2)⁻¹) ≤
      (B : ℝ)⁻¹-(B+M : ℝ)⁻¹ := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ]
      have hh := inverse_square_step (B+M) (by omega)
      push_cast at hh ⊢
      simp only [← add_assoc]
      linarith
  by_cases hBN : B≤N
  · have he : (∑ n ∈ Finset.Ioc B N, ((n : ℝ)^2)⁻¹) =
        ∑ j ∈ Finset.range (N-B), ((B+j+1 : ℝ)^2)⁻¹ := by
      rw [show Finset.Ioc B N = Finset.Ico (B+1) (N+1) by ext n; simp, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one]
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      ring
    rw [he]
    exact (hsum (N-B)).trans (sub_le_self _ (by positivity))
  · simp [Finset.Ioc_eq_empty_of_le (by omega : N≤B)]

lemma weighted_cover_le {α β : Type*} (s : Finset α) (t : Finset β) (bad : α → Prop)
    (cover : β → α → Prop) [DecidablePred bad] [∀ j, DecidablePred (cover j)]
    (w : α → ℝ) (hw : ∀ a ∈ s, 0 ≤ w a)
    (hc : ∀ a ∈ s, bad a → ∃ j ∈ t, cover j a) :
    (∑ a ∈ s, if bad a then w a else 0) ≤ ∑ j ∈ t, ∑ a ∈ s, if cover j a then w a else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hb : bad a
  · rw [if_pos hb]
    obtain ⟨j,hj,hja⟩ := hc a ha hb
    calc
      _ = if cover j a then w a else 0 := by rw [if_pos hja]
      _ ≤ _ := Finset.single_le_sum (f := fun j => if cover j a then w a else 0)
        (fun j hj => by by_cases hc : cover j a <;> simp [hc, hw a ha]) hj
  · rw [if_neg hb]
    apply Finset.sum_nonneg
    intro j hj
    split_ifs; exact hw a ha; exact le_rfl

lemma roughHarmonic_nonsquarefree_le (W X B : ℕ) (hB : 0<B)
    (hsmall : ∀ p : ℕ, Nat.Prime p → p≤B → p∣W) :
    (∑ n ∈ Finset.Icc 1 X, if W.Coprime n ∧ ¬Squarefree n then (n : ℝ)⁻¹ else 0) ≤
      roughHarmonic W X/B := by
  classical
  have hc : ∀ n ∈ Finset.Icc 1 X, W.Coprime n ∧ ¬Squarefree n →
      ∃ p ∈ Finset.Ioc B X, W.Coprime n ∧ p^2∣n := by
    intro n hn hbad
    have hns := hbad.2
    rw [Nat.squarefree_iff_prime_squarefree] at hns
    push_neg at hns
    obtain ⟨p,hp,hd⟩ := hns
    have hpn : p∣n := dvd_trans (dvd_mul_right p p) hd
    have hn0 : n≠0 := by have hh := (Finset.mem_Icc.mp hn).1; omega
    have hpX : p≤X := (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn).trans (Finset.mem_Icc.mp hn).2
    have hBp : B<p := by
      by_contra hh
      have hpW := hsmall p hp (by omega)
      have hh := Nat.eq_one_of_dvd_coprimes hbad.1 hpW hpn
      exact hp.ne_one hh
    exact ⟨p,Finset.mem_Ioc.mpr ⟨hBp,hpX⟩,hbad.1, by simpa [pow_two] using hd⟩
  refine (weighted_cover_le (Finset.Icc 1 X) (Finset.Ioc B X)
    (fun n => W.Coprime n ∧ ¬Squarefree n) (fun p n => W.Coprime n ∧ p^2∣n)
    (fun n => (n : ℝ)⁻¹) (fun n _ => by positivity) hc).trans ?_
  calc
    _ ≤ ∑ p ∈ Finset.Ioc B X, roughHarmonic W X/(p^2 : ℕ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact roughHarmonic_multiples_le W X (p^2) (pow_ne_zero _ (by have hh := (Finset.mem_Ioc.mp hp).1; omega))
    _ = roughHarmonic W X*(∑ p ∈ Finset.Ioc B X, ((p : ℝ)^2)⁻¹) := by
      simp [div_eq_mul_inv, Finset.mul_sum]
    _ ≤ _ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (sum_inverse_square_tail B X hB) (roughHarmonic_nonneg _ _)

end
end MaynardDevelopment
end

/- SquarefreeHarmonic -/
section

open scoped BigOperators Topology
open Filter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

def sieveInteger (W E n : ℕ) : Prop := W.Coprime n ∧ Squarefree n ∧ (E=1 ∨ ¬E∣n)

def sieveHarmonic (W E X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, if sieveInteger W E n then (n : ℝ)⁻¹ else 0

def sieveHarmonicBin (W E x y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc x y, if sieveInteger W E n then (n : ℝ)⁻¹ else 0

lemma sieveHarmonic_nonneg (W E X : ℕ) : 0 ≤ sieveHarmonic W E X := by
  apply Finset.sum_nonneg
  intros; split_ifs <;> first | exact le_rfl | positivity

lemma sieveHarmonic_le_rough (W E X : ℕ) : sieveHarmonic W E X ≤ roughHarmonic W X := by
  apply Finset.sum_le_sum
  intro n hn
  by_cases hc : W.Coprime n
  · simp only [if_pos hc]
    split_ifs <;> first | exact le_rfl | positivity
  · simp [sieveInteger, hc]

lemma sieveHarmonic_lower (W E X B : ℕ) (hB : 0<B)
    (hsmall : ∀ p : ℕ, Nat.Prime p → p≤B → p∣W) (hE : E=1 ∨ B≤E) :
    roughHarmonic W X-2*roughHarmonic W X/B ≤ sieveHarmonic W E X := by
  have hterm : roughHarmonic W X-sieveHarmonic W E X ≤
      (∑ n ∈ Finset.Icc 1 X, if W.Coprime n ∧ ¬Squarefree n then (n : ℝ)⁻¹ else 0)+
      (∑ n ∈ Finset.Icc 1 X, if W.Coprime n ∧ E≠1 ∧ E∣n then (n : ℝ)⁻¹ else 0) := by
    unfold roughHarmonic sieveHarmonic
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    by_cases hcn : W.Coprime n <;> by_cases hsn : Squarefree n <;>
      by_cases hEn : E∣n <;> by_cases hE1 : E=1 <;>
      simp [sieveInteger, hcn, hsn, hEn, hE1] <;> positivity
  have hsf := roughHarmonic_nonsquarefree_le W X B hB hsmall
  have hex : (∑ n ∈ Finset.Icc 1 X, if W.Coprime n ∧ E≠1 ∧ E∣n then (n : ℝ)⁻¹ else 0) ≤
      roughHarmonic W X/B := by
    rcases hE with rfl | hE
    · simp only [ne_eq, not_true_eq_false, false_and, and_false, if_false, Finset.sum_const_zero]
      exact div_nonneg (roughHarmonic_nonneg _ _) (Nat.cast_nonneg _)
    · have he0 : E≠0 := by omega
      calc
        _ ≤ ∑ n ∈ Finset.Icc 1 X, if W.Coprime n ∧ E∣n then (n : ℝ)⁻¹ else 0 := by
          apply Finset.sum_le_sum
          intro n hn
          split_ifs <;> simp_all <;> positivity
        _ ≤ roughHarmonic W X/E := roughHarmonic_multiples_le W X E he0
        _ ≤ _ := div_le_div_of_nonneg_left (roughHarmonic_nonneg _ _)
          (by exact_mod_cast hB) (by exact_mod_cast hE)
  rw [mul_div_assoc]
  linarith

lemma sieveHarmonicBin_eq_sub (W E x y : ℕ) (hxy : x≤y) :
    sieveHarmonicBin W E x y = sieveHarmonic W E y-sieveHarmonic W E x := by
  have he : Finset.Icc 1 x ∪ Finset.Ioc x y=Finset.Icc 1 y := by
    ext n
    simp
    omega
  have hd : Disjoint (Finset.Icc 1 x) (Finset.Ioc x y) := by
    rw [Finset.disjoint_left]
    intro n hn hm
    have hn' := (Finset.mem_Icc.mp hn).2
    have hm' := (Finset.mem_Ioc.mp hm).1
    omega
  have hh := Finset.sum_union hd (f := fun n => if sieveInteger W E n then (n : ℝ)⁻¹ else 0)
  rw [he] at hh
  dsimp [sieveHarmonicBin,sieveHarmonic]
  linarith

lemma sieveHarmonicBin_le_rough (W E x y : ℕ) (hxy : x≤y) :
    sieveHarmonicBin W E x y ≤ roughHarmonic W y-roughHarmonic W x := by
  have he : Finset.Icc 1 x ∪ Finset.Ioc x y=Finset.Icc 1 y := by
    ext n; simp; omega
  have hd : Disjoint (Finset.Icc 1 x) (Finset.Ioc x y) := by
    rw [Finset.disjoint_left]
    intro n hn hm
    have hn' := (Finset.mem_Icc.mp hn).2
    have hm' := (Finset.mem_Ioc.mp hm).1
    omega
  have hh := Finset.sum_union hd (f := fun n => if W.Coprime n then (n : ℝ)⁻¹ else 0)
  rw [he] at hh
  have hs : sieveHarmonicBin W E x y ≤ ∑ n ∈ Finset.Ioc x y, if W.Coprime n then (n : ℝ)⁻¹ else 0 := by
    apply Finset.sum_le_sum
    intro n hn
    by_cases hc : W.Coprime n
    · simp only [if_pos hc]
      split_ifs <;> first | exact le_rfl | positivity
    · simp [sieveInteger,hc]
  dsimp [roughHarmonic]
  linarith

lemma sieveHarmonicBin_power_bounds (W B a b : ℕ) (hW : W≠0) (hab : a<b) (hB : 8*b≤B)
    (hsmall : ∀ p : ℕ, Nat.Prime p → p≤B → p∣W) :
    ∀ᶠ R : ℕ in atTop, ∀ E : ℕ, (E=1 ∨ B≤E) →
      (roughDensity W*(b-a)/2)*Real.log R ≤ sieveHarmonicBin W E (R^a) (R^b) ∧
      sieveHarmonicBin W E (R^a) (R^b) ≤ (2*roughDensity W*(b-a))*Real.log R := by
  have hb : 0<b := by omega
  have hB0 : 0<B := by omega
  have hc := roughDensity_pos hW
  have hbR : (0 : ℝ)<b := by exact_mod_cast hb
  have hba : (0 : ℝ)<b-a := sub_pos.mpr (by exact_mod_cast hab)
  have hBa : (8 : ℝ)*b≤B := by exact_mod_cast hB
  have hpos : 0<roughDensity W*(b-a)/16 := by positivity
  have hL : Tendsto (fun R : ℕ => Real.log R) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr : ∀ᶠ R : ℕ in atTop, 2*(W : ℝ)+1 ≤ roughDensity W*(b-a)/16*Real.log R :=
    (hL.const_mul_atTop hpos).eventually (eventually_ge_atTop _)
  filter_upwards [herr, eventually_ge_atTop 2] with R hR hR2 E hE
  have hRp : 0<R := by omega
  have hlog : 0<Real.log R := Real.log_pos (by exact_mod_cast hR2)
  have hx := roughHarmonic_log_error W (R^a) hW (pow_ne_zero _ (by omega))
  have hy := roughHarmonic_log_error W (R^b) hW (pow_ne_zero _ (by omega))
  rw [Nat.cast_pow, Real.log_pow] at hx hy
  have hxy : R^a≤R^b := Nat.pow_le_pow_right (by omega) hab.le
  have hlo := sieveHarmonic_lower W E (R^b) B hB0 hsmall hE
  have hupper := sieveHarmonic_le_rough W E (R^a)
  have hbin := sieveHarmonicBin_le_rough W E (R^a) (R^b) hxy
  have hsub := sieveHarmonicBin_eq_sub W E (R^a) (R^b) hxy
  have hxlo := (abs_le.mp hx).1
  have hxhi := (abs_le.mp hx).2
  have hylo := (abs_le.mp hy).1
  have hyhi := (abs_le.mp hy).2
  have hBreal : (0 : ℝ)<B := by exact_mod_cast hB0
  have hloss : 2*roughHarmonic W (R^b)/B ≤ roughDensity W*(b-a)/3*Real.log R := by
    apply (div_le_iff₀ hBreal).mpr
    have hgap : (1 : ℝ) ≤ b-a := by
      have hh : (a : ℝ)+1≤b := by exact_mod_cast (Nat.succ_le_of_lt hab)
      linarith
    have hmul : roughDensity W*(b-a)/3*Real.log R*(8*b) ≤ roughDensity W*(b-a)/3*Real.log R*B :=
      mul_le_mul_of_nonneg_left hBa (by positivity)
    have haR : (0 : ℝ)≤a := Nat.cast_nonneg a
    have hmoment : roughHarmonic W (R^b) ≤ (5/4)*roughDensity W*b*Real.log R := by
      nlinarith [mul_nonneg (show 0 ≤ roughDensity W*Real.log R by positivity) haR]
    have hmargin := mul_nonneg (show 0 ≤ roughDensity W*b*Real.log R by positivity)
      (show 0≤(b : ℝ)-a-1 by linarith)
    nlinarith
  constructor <;> nlinarith

end
end MaynardDevelopment
end

/- DiscreteVariational -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α]

def discreteTensor (d : ℕ) (g t : α → ℝ) (C : ℝ) (x : Fin d → α) : ℝ :=
  if (∑ i, t (x i))≤C then ∏ i, g (x i) else 0

def discreteI (d : ℕ) (w g t : α → ℝ) (C : ℝ) : ℝ :=
  ∑ x : Fin d → α, (∏ i, w (x i))*discreteTensor d g t C x^2

def discreteJ (d : ℕ) (w g t : α → ℝ) (C : ℝ) : ℝ :=
  ∑ x : Fin d → α, (∏ i, w (x i))*(∑ a : α, w a*discreteTensor (d+1) g t C (Fin.cons a x))^2

lemma finite_tensor_sum (d : ℕ) (f : α → ℝ) :
    (∑ x : Fin d → α, ∏ i, f (x i)) = (∑ a, f a)^d := by
  classical
  simpa using (Fintype.prod_sum (fun _ : Fin d => f)).symm

lemma discreteI_upper (d : ℕ) (w g t : α → ℝ) (C : ℝ) (hw : ∀ a, 0≤w a) :
    discreteI d w g t C ≤ (∑ a, w a*g a^2)^d := by
  rw [← finite_tensor_sum]
  apply Finset.sum_le_sum
  intro x hx
  dsimp [discreteTensor]
  split_ifs
  · rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  · simp only [zero_pow (by decide : 2≠0), mul_zero]
    exact Finset.prod_nonneg (fun i _ => mul_nonneg (hw _) (sq_nonneg _))

lemma finite_coordinate_moment (d : ℕ) (w t : α → ℝ) (i : Fin (d+1)) :
    (∑ x : Fin (d+1) → α, (∏ j, w (x j))*t (x i)) =
      (∑ a, w a*t a)*(∑ a, w a)^d := by
  classical
  have hid (x : Fin (d+1) → α) : (∏ j, w (x j))*t (x i) =
      ∏ j : Fin (d+1), if j=i then w (x j)*t (x j) else w (x j) := by
    simp_rw [show ∀ j : Fin (d+1), (if j=i then w (x j)*t (x j) else w (x j))=
      w (x j)*(if j=i then t (x i) else 1) from fun j => by split_ifs with h; subst j; rfl; simp]
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [hid]
  rw [← Fintype.prod_sum (fun j : Fin (d+1) => fun a : α => if j=i then w a*t a else w a)]
  have hsum (j : Fin (d+1)) : (∑ a : α, if j=i then w a*t a else w a) =
      if j=i then (∑ a, w a*t a) else (∑ a, w a) := by split_ifs <;> rfl
  simp_rw [hsum]
  rw [Finset.prod_ite]
  have hfilter : (Finset.univ.filter (fun j : Fin (d+1) => j=i))={i} := by ext j; simp
  rw [hfilter]
  simp [Finset.filter_ne', Finset.card_erase_of_mem]

lemma finite_total_moment (d : ℕ) (w t : α → ℝ) :
    (∑ x : Fin (d+1) → α, (∏ j, w (x j))*(∑ j, t (x j))) =
      (d+1 : ℝ)*(∑ a, w a*t a)*(∑ a, w a)^d := by
  calc
    _ = ∑ x : Fin (d+1) → α, ∑ j, (∏ i, w (x i))*t (x j) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ = ∑ j : Fin (d+1), (∑ a, w a*t a)*(∑ a, w a)^d := by
      rw [Finset.sum_comm]
      simp only [finite_coordinate_moment]
    _ = _ := by simp; ring


lemma finite_tensor_markov (d : ℕ) (w t : α → ℝ) (K : ℝ)
    (hw : ∀ a, 0≤w a) (ht : ∀ a, 0≤t a) (hK : 0<K)
    (hM : 2*(d+1 : ℝ)*(∑ a, w a*t a) ≤ K*(∑ a, w a)) :
    (∑ x : Fin (d+1) → α, if (∑ j, t (x j))≤K then ∏ j, w (x j) else 0) ≥
      (∑ a, w a)^(d+1)/2 := by
  let lo : ℝ := ∑ x : Fin (d+1) → α, if (∑ j, t (x j))≤K then ∏ j, w (x j) else 0
  let hi : ℝ := ∑ x : Fin (d+1) → α, if K<(∑ j, t (x j)) then ∏ j, w (x j) else 0
  have hsplit : lo+hi=(∑ a, w a)^(d+1) := by
    dsimp only [lo,hi]
    rw [← Finset.sum_add_distrib, ← finite_tensor_sum]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : (∑ j, t (x j))≤K <;> simp [h, not_lt.mpr, not_le.mp]
  have htail : K*hi ≤ (d+1 : ℝ)*(∑ a, w a*t a)*(∑ a, w a)^d := by
    dsimp only [hi]
    rw [Finset.mul_sum, ← finite_total_moment]
    apply Finset.sum_le_sum
    intro x hx
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right h.le (Finset.prod_nonneg (fun i _ => hw _))
        |>.trans_eq (by ring)
    · simp only [mul_zero]
      exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw _)) (Finset.sum_nonneg (fun i _ => ht _))
  have hmass := mul_le_mul_of_nonneg_right hM (pow_nonneg (show 0 ≤ ∑ a, w a from Finset.sum_nonneg (fun a _ => hw a)) d)
  rw [pow_succ] at hsplit ⊢
  dsimp only [lo] at hsplit ⊢
  nlinarith

lemma discreteTensor_cons_marginal (d : ℕ) (w g t : α → ℝ) (C T : ℝ)
    (ht : ∀ a, g a≠0 → t a≤T) (x : Fin d → α) (hx : (∑ i, t (x i))≤C-T) :
    (∑ a : α, w a*discreteTensor (d+1) g t C (Fin.cons a x)) =
      (∑ a : α, w a*g a)*(∏ i, g (x i)) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hs : (∑ i : Fin (d+1), t (Fin.cons (α := fun _ => α) a x i))=t a+∑ i, t (x i) := by rw [Fin.sum_univ_succ]; rfl
  have hp : (∏ i : Fin (d+1), g (Fin.cons (α := fun _ => α) a x i))=g a*∏ i, g (x i) := by rw [Fin.prod_univ_succ]; rfl
  by_cases hg : g a=0
  · simp [discreteTensor, hp, hg]
  · have hh : (∑ i : Fin (d+1), t (Fin.cons (α := fun _ => α) a x i))≤C := by rw [hs]; have hh := ht a hg; linarith
    rw [discreteTensor, if_pos hh, hp]
    ring

lemma discreteJ_lower (d : ℕ) (w g t : α → ℝ) (C T : ℝ)
    (hw : ∀ a, 0≤w a) (ht : ∀ a, 0≤t a) (hg : ∀ a, g a≠0 → t a≤T)
    (hCT : 0<C-T)
    (hM : 2*(d+1 : ℝ)*(∑ a, w a*g a^2*t a) ≤ (C-T)*(∑ a, w a*g a^2)) :
    (∑ a, w a*g a)^2*(∑ a, w a*g a^2)^(d+1)/2 ≤ discreteJ (d+1) w g t C := by
  have hmark := finite_tensor_markov d (fun a => w a*g a^2) t (C-T)
    (fun a => mul_nonneg (hw a) (sq_nonneg _)) ht hCT hM
  calc
    _ ≤ (∑ a, w a*g a)^2 *
        (∑ x : Fin (d+1) → α, if (∑ j, t (x j))≤C-T then ∏ j, w (x j)*g (x j)^2 else 0) := by
      have hh := mul_le_mul_of_nonneg_left hmark (sq_nonneg (∑ a, w a*g a))
      convert hh using 1 <;> ring
    _ ≤ discreteJ (d+1) w g t C := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x hx
      split_ifs with h
      · rw [discreteTensor_cons_marginal _ w g t C T hg x h, mul_pow,
          ← Finset.prod_pow, Finset.prod_mul_distrib]
        ring_nf
        exact le_rfl
      · simp only [mul_zero]
        exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw _)) (sq_nonneg _)

end
end MaynardDevelopment
end

/- DyadicSieveTest -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

def dyadicBin (j : ℕ) (t : ℝ) : Prop := (2 : ℝ)^j<t ∧ t≤(2 : ℝ)^(j+1)

def dyadicStep (M : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, if dyadicBin j t then ((2 : ℝ)^j)⁻¹ else 0

lemma dyadicBin_unique {i j : ℕ} {t : ℝ} (hi : dyadicBin i t) (hj : dyadicBin j t) : i=j := by
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have hh : (2 : ℝ)^(i+1)≤2^j := pow_le_pow_right₀ (by norm_num) (by omega)
    dsimp [dyadicBin] at hi hj
    linarith
  · have hh : (2 : ℝ)^(j+1)≤2^i := pow_le_pow_right₀ (by norm_num) (by omega)
    dsimp [dyadicBin] at hi hj
    linarith

lemma dyadicStep_eq_of_bin {M j : ℕ} {t : ℝ} (hj : j<M) (ht : dyadicBin j t) :
    dyadicStep M t=((2 : ℝ)^j)⁻¹ := by
  unfold dyadicStep
  rw [Finset.sum_eq_single j]
  · rw [if_pos ht]
  · intro i hi hij
    rw [if_neg (fun hi => hij (dyadicBin_unique hi ht))]
  · simp [Finset.mem_range.mpr hj]

lemma dyadicStep_nonneg (M : ℕ) (t : ℝ) : 0≤dyadicStep M t := by
  apply Finset.sum_nonneg
  intros; split_ifs <;> positivity

lemma dyadicStep_support {M : ℕ} {t : ℝ} (hg : dyadicStep M t≠0) :
    1<t ∧ t≤(2 : ℝ)^M := by
  have he : ∃ j ∈ Finset.range M, dyadicBin j t := by
    by_contra h
    push_neg at h
    simp +contextual [dyadicStep,h] at hg
  obtain ⟨j,hj,ht⟩ := he
  have hp : (1 : ℝ)≤2^j := one_le_pow₀ (by norm_num)
  have hq : (2 : ℝ)^(j+1)≤2^M := pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hj; omega)
  exact ⟨hp.trans_lt ht.1, ht.2.trans hq⟩

lemma dyadicStep_sq (M : ℕ) (t : ℝ) :
    dyadicStep M t^2=∑ j ∈ Finset.range M, if dyadicBin j t then (((2 : ℝ)^j)⁻¹)^2 else 0 := by
  by_cases he : ∃ j ∈ Finset.range M, dyadicBin j t
  · obtain ⟨j,hj,ht⟩ := he
    rw [dyadicStep_eq_of_bin (Finset.mem_range.mp hj) ht, Finset.sum_eq_single j]
    · rw [if_pos ht]
    · intro i hi hij
      rw [if_neg (fun hi => hij (dyadicBin_unique hi ht))]
    · simp [hj]
  · push_neg at he
    simp +contextual [dyadicStep,he]

lemma sum_dyadic_inv_le (M : ℕ) : (∑ j ∈ Finset.range M, ((2 : ℝ)^j)⁻¹)≤2 := by
  have he : (∑ j ∈ Finset.range M, ((2 : ℝ)^j)⁻¹)=2-2*((2 : ℝ)^M)⁻¹ := by
    induction M with
    | zero => norm_num
    | succ M ih => rw [Finset.sum_range_succ, ih, pow_succ, mul_inv_rev]; ring
  rw [he]
  have hh : 0≤((2 : ℝ)^M)⁻¹ := by positivity
  linarith

variable {α : Type*} [Fintype α]

def dyadicMass (w t : α → ℝ) (j : ℕ) : ℝ := ∑ a, if dyadicBin j (t a) then w a else 0

lemma dyadicStep_first_sum (M : ℕ) (w t : α → ℝ) :
    (∑ a, w a*dyadicStep M (t a))=∑ j ∈ Finset.range M, ((2 : ℝ)^j)⁻¹*dyadicMass w t j := by
  simp only [dyadicStep, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dyadicMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> ring

lemma dyadicStep_second_sum (M : ℕ) (w t : α → ℝ) :
    (∑ a, w a*dyadicStep M (t a)^2)=∑ j ∈ Finset.range M, (((2 : ℝ)^j)⁻¹)^2*dyadicMass w t j := by
  simp only [dyadicStep_sq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dyadicMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> ring

lemma dyadicStep_moment_upper (M : ℕ) (w t : α → ℝ) (hw : ∀ a, 0≤w a) :
    (∑ a, w a*dyadicStep M (t a)^2*t a) ≤
      ∑ j ∈ Finset.range M, (((2 : ℝ)^j)⁻¹)^2*2^(j+1)*dyadicMass w t j := by
  simp only [dyadicStep_sq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j hj
  rw [dyadicMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  split_ifs with h
  · have hh := mul_le_mul_of_nonneg_left h.2 (mul_nonneg (hw a) (sq_nonneg (((2 : ℝ)^j)⁻¹)))
    convert hh using 1 <;> ring
  · simp

lemma dyadicStep_scalar_bounds (M : ℕ) (w t : α → ℝ) (c : ℝ) (hM : 0<M) (hc : 0<c)
    (hw : ∀ a, 0≤w a)
    (hmass : ∀ j<M, c*2^j/2 ≤ dyadicMass w t j ∧ dyadicMass w t j ≤ 2*c*2^j) :
    c*M/2 ≤ (∑ a, w a*dyadicStep M (t a)) ∧
      c/2 ≤ (∑ a, w a*dyadicStep M (t a)^2) ∧
      (∑ a, w a*dyadicStep M (t a)^2) ≤ 4*c ∧
      (∑ a, w a*dyadicStep M (t a)^2*t a) ≤ 4*c*M := by
  have hp (j : ℕ) : (0 : ℝ)<2^j := by positivity
  constructor
  · rw [dyadicStep_first_sum]
    calc
      _ = ∑ _j ∈ Finset.range M, c/2 := by simp; ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hh := mul_le_mul_of_nonneg_left (hmass j (Finset.mem_range.mp hj)).1 (inv_nonneg.mpr (hp j).le)
        have he : ((2 : ℝ)^j)⁻¹*(c*2^j/2)=c/2 := by field_simp
        rwa [he] at hh
  constructor
  · rw [dyadicStep_second_sum]
    calc
      c/2 ≤ (((2 : ℝ)^0)⁻¹)^2*dyadicMass w t 0 := by simpa using (hmass 0 hM).1
      _ ≤ _ := Finset.single_le_sum (f := fun j => (((2 : ℝ)^j)⁻¹)^2*dyadicMass w t j)
        (fun j hj => mul_nonneg (sq_nonneg _) (by
          apply Finset.sum_nonneg
          intro a ha
          split_ifs
          · exact hw a
          · exact le_rfl)) (Finset.mem_range.mpr hM)
  constructor
  · rw [dyadicStep_second_sum]
    calc
      _ ≤ ∑ j ∈ Finset.range M, (((2 : ℝ)^j)⁻¹)^2*(2*c*2^j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hmass j (Finset.mem_range.mp hj)).2 (sq_nonneg _)
      _ = 2*c*(∑ j ∈ Finset.range M, ((2 : ℝ)^j)⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        field_simp
      _ ≤ _ := by have hh := mul_le_mul_of_nonneg_left (sum_dyadic_inv_le M) (by positivity : 0≤2*c); nlinarith
  · refine (dyadicStep_moment_upper M w t hw).trans ?_
    calc
      _ ≤ ∑ j ∈ Finset.range M, (((2 : ℝ)^j)⁻¹)^2*2^(j+1)*(2*c*2^j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hmass j (Finset.mem_range.mp hj)).2 (by positivity)
      _ = _ := by
        have he (j : ℕ) : (((2 : ℝ)^j)⁻¹)^2*2^(j+1)*(2*c*2^j)=4*c := by rw [pow_succ]; field_simp; ring
        simp only [he, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

end
end MaynardDevelopment
end

/- DiscreteSieveRatio -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section

def sieveDimension (M : ℕ) : ℕ := 2^M+2

def sieveCutoff (M : ℕ) : ℕ := 32*sieveDimension M*M+2^M

lemma sieveCutoff_bounds (M : ℕ) (hM : 0<M) :
    0<sieveCutoff M ∧ sieveCutoff M ≤ 33*sieveDimension M*M := by
  have hk : 0<sieveDimension M := by unfold sieveDimension; positivity
  have hT : 2^M≤sieveDimension M := by unfold sieveDimension; omega
  have hMk : sieveDimension M≤sieveDimension M*M := by nlinarith
  dsimp [sieveCutoff]
  constructor
  · positivity
  · nlinarith

lemma discrete_ratio_arithmetic {B C c L G k M : ℝ}
    (hB : 0≤B) (hc : 0<c) (hM : 0<M) (hk : 0<k)
    (hC0 : 0≤C) (hC : C≤33*k*M) (hlarge : 1056*B<M)
    (hL : c*M/2≤L) (hG : G≤4*c) :
    2*B*C*c*G < k*L^2 := by
  have hLpos : 0<L := lt_of_lt_of_le (by positivity) hL
  have hscalar : 8*B*C < k*M^2/4 := by
    have h1 := mul_le_mul_of_nonneg_left hC (show 0≤8*B by positivity)
    have h2 := mul_lt_mul_of_pos_left hlarge (show 0<k*M/4 by positivity)
    nlinarith
  have h1 := mul_lt_mul_of_pos_right hscalar (sq_pos_of_pos hc)
  have h2 := mul_le_mul_of_nonneg_left hG (show 0≤2*B*C*c by positivity)
  have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0≤c*M/2) hL 2) hk.le
  nlinarith

variable {α : Type*} [Fintype α]

/-- An unbounded-ratio sieve test using only finitely many dyadic bins. -/
theorem discrete_sieve_ratio (M : ℕ) (B c : ℝ) (w t : α → ℝ)
    (hM : 0<M) (hB : 0≤B) (hc : 0<c) (hlarge : 1056*B<M)
    (hw : ∀ a, 0≤w a) (ht : ∀ a, 0≤t a)
    (hmass : ∀ j<M, c*2^j/2≤dyadicMass w t j ∧ dyadicMass w t j≤2*c*2^j) :
    B*sieveCutoff M*c*discreteI (sieveDimension M) w (fun a => dyadicStep M (t a)) t (sieveCutoff M) <
      (sieveDimension M : ℝ)*discreteJ (sieveDimension M-1) w (fun a => dyadicStep M (t a)) t (sieveCutoff M) := by
  let g (a : α) : ℝ := dyadicStep M (t a)
  let G : ℝ := ∑ a, w a*g a^2
  let L : ℝ := ∑ a, w a*g a
  let U : ℝ := ∑ a, w a*g a^2*t a
  let d : ℕ := 2^M
  let C : ℝ := sieveCutoff M
  have hk : sieveDimension M=d+2 := rfl
  obtain ⟨hL,hGlo,hGhi,hU⟩ := dyadicStep_scalar_bounds M w t c hM hc hw hmass
  change c*M/2≤L at hL
  change c/2≤G at hGlo
  change G≤4*c at hGhi
  change U≤4*c*M at hU
  have hGp : 0<G := by linarith
  have hMR : (0 : ℝ)<M := by exact_mod_cast hM
  have hkR : (0 : ℝ)<sieveDimension M := by rw [hk]; positivity
  have hC0 : 0<C := by dsimp [C]; exact_mod_cast (sieveCutoff_bounds M hM).1
  have hCup : C≤33*sieveDimension M*M := by dsimp [C]; exact_mod_cast (sieveCutoff_bounds M hM).2
  have hCT : C-(2 : ℝ)^M=32*(sieveDimension M : ℝ)*M := by
    dsimp [C,sieveCutoff]
    push_cast
    ring
  have hCTpos : 0<C-(2 : ℝ)^M := by rw [hCT]; positivity
  have hmoment : 2*(d+1 : ℝ)*U ≤ (C-(2 : ℝ)^M)*G := by
    rw [hCT]
    have hd : (d+1 : ℝ)≤sieveDimension M := by rw [hk]; push_cast; linarith
    have hh1 := mul_le_mul_of_nonneg_left hU (show 0≤2*(d+1 : ℝ) by positivity)
    have hh2 := mul_le_mul_of_nonneg_left hGlo (show 0≤32*(sieveDimension M : ℝ)*M by positivity)
    have hh3 := mul_le_mul_of_nonneg_right hd (show 0≤8*c*M by positivity)
    nlinarith
  have hJ := discreteJ_lower d w g t C ((2 : ℝ)^M) hw ht
    (fun a ha => (dyadicStep_support ha).2) hCTpos hmoment
  change L^2*G^(d+1)/2 ≤ discreteJ (d+1) w g t C at hJ
  have hI := discreteI_upper (d+2) w g t C hw
  change discreteI (d+2) w g t C≤G^(d+2) at hI
  have hstrict := discrete_ratio_arithmetic hB hc hMR hkR hC0.le hCup hlarge hL hGhi
  have hpow : 0<G^(d+1) := pow_pos hGp _
  have hmain : B*C*c*G^(d+2) < (sieveDimension M : ℝ)*(L^2*G^(d+1)/2) := by
    have hh := mul_lt_mul_of_pos_right hstrict hpow
    rw [show d+2=(d+1)+1 by omega, pow_succ]
    nlinarith
  change B*C*c*discreteI (sieveDimension M) w g t C < (sieveDimension M : ℝ)*discreteJ (sieveDimension M-1) w g t C
  rw [hk]
  rw [show (d+2-1 : ℕ)=d+1 by simp [Nat.add_sub_assoc]]
  calc
    _ ≤ B*C*c*G^(d+2) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ < (sieveDimension M : ℝ)*(L^2*G^(d+1)/2) := hmain
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hJ hkR.le
      simpa [hk] using hh


end
end MaynardDevelopment
end

/- PrimeSubsetTest -/
section

open scoped BigOperators Topology
open Filter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

def sievePrimes (W E N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter (fun p => Nat.Prime p ∧ ¬p∣W ∧ p≠E)

lemma mem_sievePrimes {W E N p : ℕ} :
    p∈sievePrimes W E N ↔ p≤N ∧ Nat.Prime p ∧ ¬p∣W ∧ p≠E := by
  simp [sievePrimes, Nat.lt_succ_iff]

lemma primeSetProduct_squarefree (s : Finset ℕ) (hs : ∀ p∈s, Nat.Prime p) :
    Squarefree (primeSetProduct s) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)
  · intro p hp
    exact (hs p hp).squarefree

lemma primeSetProduct_sieveInteger {W E N : ℕ} (hE : E=1 ∨ Nat.Prime E)
    (s : Finset ℕ) (hs : s⊆sievePrimes W E N) : sieveInteger W E (primeSetProduct s) := by
  have hp (p : ℕ) (hp : p∈s) := mem_sievePrimes.mp (hs hp)
  refine ⟨?_,primeSetProduct_squarefree s (fun p h => (hp p h).2.1),?_⟩
  · exact Nat.Coprime.prod_right (fun p h => ((hp p h).2.1.coprime_iff_not_dvd.mpr (hp p h).2.2.1).symm)
  · rcases hE with he | he
    · exact Or.inl he
    · right
      intro hd
      obtain ⟨p,hps,hdp⟩ := (he.prime.dvd_finset_prod_iff (fun p : ℕ => p)).mp hd
      have heq : E=p := (Nat.prime_dvd_prime_iff_eq he (hp p hps).2.1).mp hdp
      exact (hp p hps).2.2.2 heq.symm

lemma sieveInteger_primeFactors_subset {W E N n : ℕ} (hn : sieveInteger W E n) (hnN : n≤N) :
    n.primeFactors⊆sievePrimes W E N := by
  intro p hp
  have hp' := Nat.mem_primeFactors.mp hp
  apply mem_sievePrimes.mpr
  refine ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hp'.2.2) hp'.2.1).trans hnN,hp'.1,?_,?_⟩
  · intro hd
    exact hp'.1.ne_one (Nat.eq_one_of_dvd_coprimes hn.1 hd hp'.2.1)
  · intro he
    rcases hn.2.2 with hE | hE
    · exact hp'.1.ne_one (he.trans hE)
    · exact hE (he ▸ hp'.2.1)

lemma subset_harmonic_bin_eq (W E N x y : ℕ) (hE : E=1 ∨ Nat.Prime E) (hyN : y≤N) :
    (∑ s ∈ (sievePrimes W E N).powerset,
      if x<primeSetProduct s ∧ primeSetProduct s≤y then (primeSetProduct s : ℝ)⁻¹ else 0) =
      sieveHarmonicBin W E x y := by
  classical
  rw [← Finset.sum_filter]
  unfold sieveHarmonicBin
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun s _ => primeSetProduct s)
  · intro s hs
    have hs' := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr hs'.2,
      primeSetProduct_sieveInteger hE s (Finset.mem_powerset.mp hs'.1)⟩
  · intro s hs t ht he
    exact primeSetProduct_injOn (sievePrimes W E N) (fun p hp => (mem_sievePrimes.mp hp).2.1)
      (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp ht).1 he
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    have he : primeSetProduct n.primeFactors=n := Nat.prod_primeFactors_of_squarefree hn'.2.2.1
    refine ⟨n.primeFactors,?_,he⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr (sieveInteger_primeFactors_subset hn'.2 ((Finset.mem_Ioc.mp hn'.1).2.trans hyN)),
      by rw [he]; exact Finset.mem_Ioc.mp hn'.1⟩
  · intros; rfl

abbrev PrimeSubset (P : Finset ℕ) := ↥P.powerset

def subsetWeight {P : Finset ℕ} (s : PrimeSubset P) : ℝ := (primeSetProduct s.val : ℝ)⁻¹

def subsetTime {P : Finset ℕ} (R : ℕ) (s : PrimeSubset P) : ℝ := Real.log (primeSetProduct s.val)/Real.log R

lemma subsetWeight_nonneg {P : Finset ℕ} (s : PrimeSubset P) : 0≤subsetWeight s := by
  unfold subsetWeight; positivity

lemma subsetTime_nonneg {P : Finset ℕ} (R : ℕ) (s : PrimeSubset P) : 0≤subsetTime R s :=
  div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

lemma dyadicBin_log_iff (R n j : ℕ) (hR : 1<R) (hn : 0<n) :
    dyadicBin j (Real.log n/Real.log R) ↔ R^(2^j)<n ∧ n≤R^(2^(j+1)) := by
  have hL : 0<Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hnr : (0 : ℝ)<n := by exact_mod_cast hn
  have hRa : (0 : ℝ)<(R^(2^j) : ℕ) := by positivity
  have hRb : (0 : ℝ)<(R^(2^(j+1)) : ℕ) := by positivity
  rw [dyadicBin, lt_div_iff₀ hL, div_le_iff₀ hL]
  have ha : (2 : ℝ)^j*Real.log R=Real.log (R^(2^j) : ℕ) := by
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow, Nat.cast_ofNat]
  have hb : (2 : ℝ)^(j+1)*Real.log R=Real.log (R^(2^(j+1)) : ℕ) := by
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow, Nat.cast_ofNat]
  rw [ha,hb,Real.log_lt_log_iff hRa hnr,Real.log_le_log_iff hnr hRb]
  exact_mod_cast Iff.rfl

lemma subset_dyadicMass_eq (W E R M j : ℕ) (hR : 1<R) (hE : E=1 ∨ Nat.Prime E) (hj : j<M) :
    dyadicMass (α := PrimeSubset (sievePrimes W E (R^(2^M)))) subsetWeight (subsetTime R) j =
      sieveHarmonicBin W E (R^(2^j)) (R^(2^(j+1))) := by
  unfold dyadicMass subsetWeight subsetTime
  rw [← Finset.sum_subtype (sievePrimes W E (R^(2^M))).powerset (fun s => Iff.rfl)
    (fun s => if dyadicBin j (Real.log (primeSetProduct s)/Real.log R) then (primeSetProduct s : ℝ)⁻¹ else 0)]
  have he : (∑ s ∈ (sievePrimes W E (R^(2^M))).powerset,
      if dyadicBin j (Real.log (primeSetProduct s)/Real.log R) then (primeSetProduct s : ℝ)⁻¹ else 0) =
      (∑ s ∈ (sievePrimes W E (R^(2^M))).powerset,
      if R^(2^j)<primeSetProduct s ∧ primeSetProduct s≤R^(2^(j+1)) then (primeSetProduct s : ℝ)⁻¹ else 0) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [dyadicBin_log_iff R (primeSetProduct s) j hR (primeSetProduct_pos s
      (fun p hp => (mem_sievePrimes.mp ((Finset.mem_powerset.mp hs) hp)).2.1))]
    split_ifs <;> rfl
  rw [he]
  apply subset_harmonic_bin_eq W E _ _ _ hE
  exact Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

lemma subset_dyadicMass_bounds (W B M : ℕ) (hW : W≠0) (hB : 8*2^M≤B)
    (hsmall : ∀ p : ℕ, Nat.Prime p → p≤B → p∣W) :
    ∀ᶠ R : ℕ in atTop, ∀ E : ℕ, (E=1 ∨ Nat.Prime E) → (E=1 ∨ B≤E) →
      ∀ j<M, ((roughDensity W*Real.log R)*2^j/2) ≤
        dyadicMass (α := PrimeSubset (sievePrimes W E (R^(2^M)))) subsetWeight (subsetTime R) j ∧
        dyadicMass (α := PrimeSubset (sievePrimes W E (R^(2^M)))) subsetWeight (subsetTime R) j ≤
          2*(roughDensity W*Real.log R)*2^j := by
  have hall : ∀ᶠ R : ℕ in atTop, ∀ j : Fin M, ∀ E : ℕ, (E=1 ∨ B≤E) →
      (roughDensity W*((2^(j.val+1) : ℕ)-(2^j.val : ℕ))/2)*Real.log R ≤
        sieveHarmonicBin W E (R^(2^j.val)) (R^(2^(j.val+1))) ∧
      sieveHarmonicBin W E (R^(2^j.val)) (R^(2^(j.val+1))) ≤
        (2*roughDensity W*((2^(j.val+1) : ℕ)-(2^j.val : ℕ)))*Real.log R := by
    apply Filter.eventually_all.mpr
    intro j
    apply sieveHarmonicBin_power_bounds W B (2^j.val) (2^(j.val+1)) hW
    · exact Nat.pow_lt_pow_right (by omega) (by omega)
    · exact (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_right (by omega) (by omega))).trans hB
    · exact hsmall
  filter_upwards [hall,eventually_ge_atTop 2] with R hR hR2 E hE hEB j hj
  rw [subset_dyadicMass_eq W E R M j (by omega) hE hj]
  have hh := hR ⟨j,hj⟩ E hEB
  dsimp only at hh
  have he : (((2^(j+1) : ℕ) : ℝ)-(2^j : ℕ))=(2 : ℝ)^j := by
    push_cast
    rw [pow_succ]
    ring
  rw [he] at hh
  constructor <;> nlinarith [hh.1,hh.2]

/-- The prime-subset test achieves any prescribed ratio, before interaction and progression errors. -/
theorem primeSubset_sieve_ratio (W D M : ℕ) (B : ℝ) (hW : W≠0) (hD : 8*2^M≤D)
    (hsmall : ∀ p : ℕ, Nat.Prime p → p≤D → p∣W) (hM : 0<M) (hB : 0≤B) (hlarge : 1056*B<M) :
    ∀ᶠ R : ℕ in atTop, ∀ E : ℕ, (E=1 ∨ Nat.Prime E) → (E=1 ∨ D≤E) →
      let P := sievePrimes W E (R^(2^M))
      let w : PrimeSubset P → ℝ := subsetWeight
      let t : PrimeSubset P → ℝ := subsetTime R
      let g : PrimeSubset P → ℝ := fun s => dyadicStep M (t s)
      B*sieveCutoff M*(roughDensity W*Real.log R)*discreteI (sieveDimension M) w g t (sieveCutoff M) <
        (sieveDimension M : ℝ)*discreteJ (sieveDimension M-1) w g t (sieveCutoff M) := by
  filter_upwards [subset_dyadicMass_bounds W D M hW hD hsmall,eventually_ge_atTop 2] with R hR hR2 E hE hED
  apply discrete_sieve_ratio M B (roughDensity W*Real.log R) subsetWeight (subsetTime R)
    hM hB (mul_pos (roughDensity_pos hW) (Real.log_pos (by exact_mod_cast hR2))) hlarge
    subsetWeight_nonneg (subsetTime_nonneg R) (hR E hE hED)


end
end MaynardDevelopment
end

/- KernelProducts -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma product_perturbation {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hg : ∀ i ∈ s, 0≤g i) :
    |(∏ i ∈ s, f i)-(∏ i ∈ s, g i)| ≤
      (∏ i ∈ s, (g i+ |f i-g i|))-(∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hga := hg a (Finset.mem_insert_self _ _)
    have hgs := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hP : 0≤∏ i ∈ s, g i := Finset.prod_nonneg hgs
    have hQ : 0≤∏ i ∈ s, (g i + |f i-g i|) := Finset.prod_nonneg (fun i hi => add_nonneg (hgs i hi) (abs_nonneg _))
    have hF : |∏ i ∈ s, f i| ≤ ∏ i ∈ s, (g i + |f i-g i|) := by
      rw [Finset.abs_prod]
      apply Finset.prod_le_prod (fun i _ => abs_nonneg _)
      intro i hi
      have hh := abs_add_le (f i-g i) (g i)
      rw [sub_add_cancel, abs_of_nonneg (hgs i hi)] at hh
      linarith
    simp only [Finset.prod_insert ha]
    calc
      _ = |(f a-g a)*(∏ i ∈ s, f i)+g a*((∏ i ∈ s, f i)-(∏ i ∈ s, g i))| := by congr 1; ring
      _ ≤ |(f a-g a)*(∏ i ∈ s, f i)|+ |g a*((∏ i ∈ s, f i)-(∏ i ∈ s, g i))| := abs_add_le _ _
      _ ≤ |f a-g a| *(∏ i ∈ s, (g i + |f i-g i|))+
          g a*((∏ i ∈ s, (g i + |f i-g i|))-(∏ i ∈ s, g i)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hga]
        exact add_le_add (mul_le_mul_of_nonneg_left hF (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (ih hgs) hga)
      _ = _ := by ring

lemma sum_pair_product {ι σ : Type*} [Fintype ι] [Fintype σ] (F : ι → σ → σ → ℝ) :
    (∑ r : ι→σ, ∑ s : ι→σ, ∏ p, F p (r p) (s p)) = ∏ p, ∑ a, ∑ b, F p a b := by
  classical
  have hi (r : ι→σ) : (∑ s : ι→σ, ∏ p, F p (r p) (s p))=∏ p, ∑ b, F p (r p) b := by
    exact (Fintype.prod_sum (fun p b => F p (r p) b)).symm
  simp only [hi]
  exact (Fintype.prod_sum (fun p a => ∑ b, F p a b)).symm

def kernelQuadratic {ι σ : Type*} [Fintype ι] [Fintype σ]
    (K : ι → σ → σ → ℝ) (y : (ι→σ)→ℝ) : ℝ :=
  ∑ r : ι→σ, ∑ s : ι→σ, y r*y s*∏ p, K p (r p) (s p)

lemma kernelQuadratic_error {ι σ : Type*} [Fintype ι] [Fintype σ]
    (K L : ι → σ → σ → ℝ) (y : (ι→σ)→ℝ)
    (hy : ∀ r, |y r|≤1) (hL : ∀ p a b, 0≤L p a b) :
    |kernelQuadratic K y-kernelQuadratic L y| ≤
      (∏ p, ∑ a, ∑ b, (L p a b+ |K p a b-L p a b|))-(∏ p, ∑ a, ∑ b, L p a b) := by
  unfold kernelQuadratic
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r : ι→σ, ∑ s : ι→σ, |y r*y s*((∏ p, K p (r p) (s p))-(∏ p, L p (r p) (s p)))| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro r hr
      have hh := Finset.abs_sum_le_sum_abs
        (fun s => y r*y s*(∏ p, K p (r p) (s p))-y r*y s*(∏ p, L p (r p) (s p))) Finset.univ
      simpa only [mul_sub] using hh
    _ ≤ ∑ r : ι→σ, ∑ s : ι→σ, |(∏ p, K p (r p) (s p))-(∏ p, L p (r p) (s p))| := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      rw [abs_mul,abs_mul]
      have hyy : |y r| *|y s|≤1 := by nlinarith [hy r,hy s,abs_nonneg (y r),abs_nonneg (y s)]
      exact mul_le_of_le_one_left (abs_nonneg _) hyy
    _ ≤ ∑ r : ι→σ, ∑ s : ι→σ, ((∏ p, (L p (r p) (s p)+ |K p (r p) (s p)-L p (r p) (s p)|))-
        (∏ p, L p (r p) (s p))) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      exact product_perturbation Finset.univ _ _ (fun p _ => hL p (r p) (s p))
    _ = _ := by
      simp only [Finset.sum_sub_distrib, sum_pair_product]
      rw [sum_pair_product (fun p a b => L p a b+ |K p a b-L p a b|)]

lemma prod_add_error_bound {ι : Type*} (s : Finset ι) (b e : ι→ℝ)
    (hb : ∀ i ∈ s, 1≤b i) (he : ∀ i ∈ s, 0≤e i) :
    (∏ i ∈ s, (b i+e i))-(∏ i ∈ s, b i) ≤
      (∏ i ∈ s, b i)*((∏ i ∈ s, (1+e i))-1) := by
  have hprod : (∏ i ∈ s, (b i+e i)) ≤ (∏ i ∈ s, b i)*(∏ i ∈ s, (1+e i)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro i hi; linarith [hb i hi,he i hi]
    · intro i hi; nlinarith [hb i hi,he i hi]
  nlinarith

lemma product_one_add_exp_le {ι : Type*} (s : Finset ι) (e : ι→ℝ) (he : ∀ i ∈ s, 0≤e i) :
    (∏ i ∈ s, (1+e i))-1 ≤ (∑ i ∈ s, e i)*Real.exp (∑ i ∈ s, e i) := by
  have hp : (∏ i ∈ s, (1+e i))≤Real.exp (∑ i ∈ s, e i) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro i hi; linarith [he i hi]
    · intro i hi; simpa [add_comm] using Real.add_one_le_exp (e i)
  have hh := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg (∑ i ∈ s, e i))
    (Real.exp_nonneg (∑ i ∈ s, e i))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hh
  nlinarith

/-- A global kernel error controlled just by the sums of its local absolute errors. -/
lemma kernelQuadratic_error_envelope {ι σ : Type*} [Fintype ι] [Fintype σ]
    (K L : ι → σ → σ → ℝ) (y : (ι→σ)→ℝ) (e b : ι→ℝ) (H S : ℝ)
    (hy : ∀ r, |y r|≤1) (hL : ∀ p a b, 0≤L p a b)
    (hb1 : ∀ p, 1≤∑ a, ∑ b, L p a b) (hb : ∀ p, (∑ a, ∑ b, L p a b)≤b p)
    (he : ∀ p, (∑ a, ∑ b, |K p a b-L p a b|)≤e p)
    (hprod : (∏ p, b p)≤H) (hsum : (∑ p, e p)≤S) :
    |kernelQuadratic K y-kernelQuadratic L y| ≤ H*S*Real.exp S := by
  have he0 (p : ι) : 0≤e p := le_trans (by positivity) (he p)
  have hS : 0≤S := (Finset.sum_nonneg (fun p _ => he0 p)).trans hsum
  have hH : 0≤H := (Finset.prod_nonneg (fun p _ => (by linarith [hb1 p,hb p] : 0≤b p))).trans hprod
  have hLp : (∏ p, ∑ a, ∑ b, L p a b)≤H :=
    (Finset.prod_le_prod (fun p _ => by linarith [hb1 p]) (fun p _ => hb p)).trans hprod
  have hbig : (∏ p, ∑ a, ∑ b, (L p a b+ |K p a b-L p a b|)) ≤
      ∏ p, ((∑ a, ∑ b, L p a b)+e p) := by
    apply Finset.prod_le_prod
    · intro p hp; apply Finset.sum_nonneg; intro a ha; apply Finset.sum_nonneg; intro b hb; exact add_nonneg (hL p a b) (abs_nonneg _)
    · intro p hp
      simp only [Finset.sum_add_distrib]
      exact add_le_add le_rfl (he p)
  calc
    _ ≤ (∏ p, ((∑ a, ∑ b, L p a b)+e p))-(∏ p, ∑ a, ∑ b, L p a b) :=
      (kernelQuadratic_error K L y hy hL).trans (sub_le_sub_right hbig _)
    _ ≤ (∏ p, ∑ a, ∑ b, L p a b)*((∏ p, (1+e p))-1) :=
      prod_add_error_bound Finset.univ _ e (fun p _ => hb1 p) (fun p _ => he0 p)
    _ ≤ (∏ p, ∑ a, ∑ b, L p a b)*((∑ p, e p)*Real.exp (∑ p, e p)) :=
      mul_le_mul_of_nonneg_left (product_one_add_exp_le Finset.univ e (fun p _ => he0 p))
        (Finset.prod_nonneg (fun p _ => by linarith [hb1 p]))
    _ ≤ H*(S*Real.exp S) := by
      apply mul_le_mul hLp _ (mul_nonneg (Finset.sum_nonneg (fun p _ => he0 p)) (Real.exp_nonneg _)) hH
      exact mul_le_mul hsum (Real.exp_le_exp.mpr hsum) (Real.exp_nonneg _) hS
    _ = _ := by ring

end
end MaynardDevelopment
end

/- SieveAlgebra -/
section

open scoped BigOperators

namespace MaynardDevelopment

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A centered local sieve factor attached to one residue. -/
def contrast (a x : α) : ℝ :=
  if x = a then -1 else ((Fintype.card α : ℝ) - 1)⁻¹

lemma contrast_eq_indicator (a x : α) :
    contrast a x = ((Fintype.card α : ℝ) - 1)⁻¹ -
      (1 + ((Fintype.card α : ℝ) - 1)⁻¹) * (if x = a then 1 else 0) := by
  unfold contrast
  split_ifs <;> ring

lemma sum_contrast (a : α) (hq : 1 < Fintype.card α) : ∑ x, contrast a x = 0 := by
  simp_rw [contrast_eq_indicator]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hn : (Fintype.card α : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card α := by exact_mod_cast hq
    linarith
  field_simp
  ring

lemma contrast_prod_expansion (a b x : α) :
    contrast a x * contrast b x =
      (((Fintype.card α : ℝ) - 1)⁻¹) ^ 2 -
      ((Fintype.card α : ℝ) - 1)⁻¹ * (1 + ((Fintype.card α : ℝ) - 1)⁻¹) *
        ((if x = a then 1 else 0) + (if x = b then 1 else 0)) +
      (1 + ((Fintype.card α : ℝ) - 1)⁻¹) ^ 2 *
        (if x = a ∧ x = b then 1 else 0) := by
  simp_rw [contrast_eq_indicator]
  have hid : (if x = a ∧ x = b then (1 : ℝ) else 0) =
      (if x = a then (1 : ℝ) else 0) * (if x = b then (1 : ℝ) else 0) := by
    split_ifs <;> simp_all
  rw [hid]
  ring

lemma sum_contrast_mul (a b : α) (hq : 1 < Fintype.card α) :
    (∑ x, contrast a x * contrast b x) =
      if a = b then (Fintype.card α : ℝ) / ((Fintype.card α : ℝ) - 1)
      else -(Fintype.card α : ℝ) / ((Fintype.card α : ℝ) - 1) ^ 2 := by
  simp_rw [contrast_prod_expansion]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hdelta : (∑ x : α, (if x = a ∧ x = b then (1 : ℝ) else 0)) =
      if a = b then 1 else 0 := by
    by_cases hab : a = b
    · subst b; simp
    · have hfalse (x : α) : ¬ (x = a ∧ x = b) := by grind
      simp [hfalse, hab]
  rw [hdelta]
  have hn : (Fintype.card α : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card α := by exact_mod_cast hq
    linarith
  split_ifs <;> field_simp <;> ring

variable {ι : Type*} [DecidableEq ι]

def localFactor (h : ι → α) (r : Option ι) (x : α) : ℝ :=
  r.elim 1 (fun i => contrast (h i) x)

def kernelOne (q : ℝ) (r s : Option ι) : ℝ :=
  match r, s with
  | none, none => 1
  | some i, some j => if i = j then (q - 1)⁻¹ else -(q - 1)⁻¹ ^ 2
  | _, _ => 0

lemma mean_localFactor_mul (h : ι → α) (hi : Function.Injective h)
    (hq : 1 < Fintype.card α) (r s : Option ι) :
    (∑ x, localFactor h r x * localFactor h s x) / (Fintype.card α : ℝ) =
      kernelOne (Fintype.card α : ℝ) r s := by
  have hq0 : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card α ≠ 0)
  have hq1 : (Fintype.card α : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card α := by exact_mod_cast hq
    linarith
  cases r with
  | none =>
    cases s with
    | none => simp [localFactor, kernelOne, hq0]
    | some j => simp [localFactor, kernelOne, sum_contrast _ hq]
  | some i =>
    cases s with
    | none => simp [localFactor, kernelOne, sum_contrast _ hq]
    | some j =>
      simp only [localFactor, Option.elim_some, kernelOne]
      rw [sum_contrast_mul _ _ hq]
      have heq : h i = h j ↔ i = j := hi.eq_iff
      simp only [heq]
      split_ifs <;> field_simp <;> ring

/-- Average over residues other than the forbidden residue. -/
def conditionalMean (f : α → ℝ) (a : α) : ℝ :=
  (∑ x ∈ Finset.univ.erase a, f x) / ((Fintype.card α : ℝ) - 1)

lemma conditionalMean_eq (f : α → ℝ) (a : α) :
    conditionalMean f a = ((∑ x, f x) - f a) / ((Fintype.card α : ℝ) - 1) := by
  unfold conditionalMean
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ a)]

lemma conditionalMean_localFactor_mul (h : ι → α) (hi : Function.Injective h)
    (hq : 1 < Fintype.card α) (m : ι) (r s : Option ι) :
    conditionalMean (fun x => localFactor h r x * localFactor h s x) (h m) =
      ((Fintype.card α : ℝ) * kernelOne (Fintype.card α : ℝ) r s -
        localFactor h r (h m) * localFactor h s (h m)) / ((Fintype.card α : ℝ) - 1) := by
  rw [conditionalMean_eq]
  have hh := mean_localFactor_mul h hi hq r s
  have hq0 : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card α ≠ 0)
  have heq := (div_eq_iff hq0).mp hh
  rw [heq]
  ring

def kernelTwo (q : ℝ) (m : ι) (r s : Option ι) : ℝ :=
  match r, s with
  | none, none => 1
  | none, some i | some i, none => if i = m then (q - 1)⁻¹ else -(q - 1)⁻¹ ^ 2
  | some i, some j =>
    if i = m then
      if j = m then (q - 1)⁻¹ ^ 2 else -(q - 1)⁻¹ ^ 3
    else if j = m then -(q - 1)⁻¹ ^ 3
    else if i = j then (q ^ 2 - q - 1) / (q - 1) ^ 3
    else -(q + 1) / (q - 1) ^ 3

set_option maxHeartbeats 800000 in
lemma conditionalMean_localFactor_mul_table (h : ι → α) (hi : Function.Injective h)
    (hq : 1 < Fintype.card α) (m : ι) (r s : Option ι) :
    conditionalMean (fun x => localFactor h r x * localFactor h s x) (h m) =
      kernelTwo (Fintype.card α : ℝ) m r s := by
  rw [conditionalMean_localFactor_mul h hi hq]
  have hq1 : (Fintype.card α : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card α := by exact_mod_cast hq
    linarith
  have hc (i : ι) : contrast (h i) (h m) =
      if i = m then -1 else ((Fintype.card α : ℝ) - 1)⁻¹ := by
    simp only [contrast, hi.eq_iff]
    by_cases hm : i = m
    · simp [hm]
    · simp [hm, Ne.symm hm]
  cases r <;> cases s <;> simp only [kernelOne, kernelTwo, localFactor,
    Option.elim_none, Option.elim_some, hc]
  all_goals try split_ifs
  all_goals first | (exfalso; solve | subst_vars; contradiction) | (field_simp <;> ring)


end
end MaynardDevelopment
end

/- CenteredKernels -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {α ι : Type*} [Fintype α] [DecidableEq α] [DecidableEq ι]

def centeredResidue (a x : α) : ℝ := (Fintype.card α : ℝ)⁻¹-(if x=a then 1 else 0)

def centeredFactor (h : ι→α) (r : Option ι) (x : α) : ℝ :=
  r.elim 1 (fun i => centeredResidue (h i) x)

def sieveKernelOne (q : ℝ) (r s : Option ι) : ℝ :=
  match r,s with
  | none,none => 1
  | some i,some j => (if i=j then q⁻¹ else 0)-(q⁻¹)^2
  | _,_ => 0

def idealKernelOne (q : ℝ) (r s : Option ι) : ℝ :=
  match r,s with
  | none,none => 1
  | some i,some j => if i=j then q⁻¹ else 0
  | _,_ => 0

def sieveKernelTwo (q : ℝ) (m : ι) (r s : Option ι) : ℝ :=
  match r,s with
  | none,none => 1
  | none,some i | some i,none => if i=m then q⁻¹ else -(q⁻¹*(q-1)⁻¹)
  | some i,some j =>
    if i=m then
      if j=m then (q⁻¹)^2 else -((q⁻¹)^2*(q-1)⁻¹)
    else if j=m then -((q⁻¹)^2*(q-1)⁻¹)
    else if i=j then q⁻¹-(q⁻¹)^2*(q-1)⁻¹ else -(q+1)*(q⁻¹)^2*(q-1)⁻¹

def idealKernelTwo (q : ℝ) (m : ι) (r s : Option ι) : ℝ :=
  match r,s with
  | none,none => 1
  | none,some i | some i,none => if i=m then q⁻¹ else 0
  | some i,some j =>
    if i=m then if j=m then (q⁻¹)^2 else 0
    else if j=m then 0
    else if i=j then q⁻¹ else 0

lemma centeredResidue_eq_contrast (a x : α) (hq : 1 < Fintype.card α) :
    centeredResidue a x = ((Fintype.card α : ℝ)-1)/(Fintype.card α : ℝ)*contrast a x := by
  have hqR : (1 : ℝ) < Fintype.card α := by exact_mod_cast hq
  have hq0 : (Fintype.card α : ℝ)≠0 := by linarith
  have hq1 : (Fintype.card α : ℝ)-1≠0 := by linarith
  unfold centeredResidue contrast
  split_ifs  <;> field_simp  <;> ring

lemma centeredFactor_eq (h : ι→α) (r : Option ι) (x : α) (hq : 1 < Fintype.card α) :
    centeredFactor h r x = r.elim 1 (fun _ => ((Fintype.card α : ℝ)-1)/(Fintype.card α : ℝ))*localFactor h r x := by
  cases r
  · simp [centeredFactor,localFactor]
  · exact centeredResidue_eq_contrast _ _ hq

lemma mean_centeredFactor_mul (h : ι→α) (hi : Function.Injective h) (hq : 1 < Fintype.card α)
    (r s : Option ι) :
    (∑ x, centeredFactor h r x*centeredFactor h s x)/(Fintype.card α : ℝ)=
      sieveKernelOne (Fintype.card α : ℝ) r s := by
  have he (x : α) : centeredFactor h r x*centeredFactor h s x =
      (r.elim 1 (fun _ => ((Fintype.card α : ℝ)-1)/(Fintype.card α : ℝ)))*
      (s.elim 1 (fun _ => ((Fintype.card α : ℝ)-1)/(Fintype.card α : ℝ)))*
      (localFactor h r x*localFactor h s x) := by rw [centeredFactor_eq _ _ _ hq,centeredFactor_eq _ _ _ hq]; ring
  simp_rw [he]
  rw [← Finset.mul_sum, mul_div_assoc, mean_localFactor_mul h hi hq]
  have hqR : (1 : ℝ) < Fintype.card α := by exact_mod_cast hq
  have hq0 : (Fintype.card α : ℝ)≠0 := by linarith
  have hq1 : (Fintype.card α : ℝ)-1≠0 := by linarith
  cases r  <;> cases s  <;> simp only [Option.elim_none,Option.elim_some,kernelOne,sieveKernelOne]
  all_goals try split_ifs
  all_goals field_simp  <;> ring

lemma conditionalMean_centeredFactor_mul (h : ι→α) (hi : Function.Injective h) (hq : 1 < Fintype.card α)
    (m : ι) (r s : Option ι) :
    conditionalMean (fun x => centeredFactor h r x*centeredFactor h s x) (h m) =
      sieveKernelTwo (Fintype.card α : ℝ) m r s := by
  rw [conditionalMean_eq]
  have hm := mean_centeredFactor_mul h hi hq r s
  have hqR : (1 : ℝ) < Fintype.card α := by exact_mod_cast hq
  have hq0 : (Fintype.card α : ℝ)≠0 := by linarith
  have hq1 : (Fintype.card α : ℝ)-1≠0 := by linarith
  have hsum := (div_eq_iff (by linarith : (Fintype.card α : ℝ)≠0)).mp hm
  rw [hsum]
  have hc (i : ι) : centeredResidue (h i) (h m)=(Fintype.card α : ℝ)⁻¹-(if i=m then 1 else 0) := by
    simp only [centeredResidue,hi.eq_iff,eq_comm]
  cases r  <;> cases s  <;> simp only [centeredFactor,Option.elim_none,Option.elim_some,hc,sieveKernelOne,sieveKernelTwo]
  all_goals try split_ifs
  all_goals first | (exfalso; solve | subst_vars; contradiction) | (field_simp  <;> ring)

lemma idealKernelOne_nonneg {q : ℝ} (hq : 0 ≤ q) (r s : Option ι) : 0 ≤ idealKernelOne q r s := by
  cases r  <;> cases s  <;> simp only [idealKernelOne]
  all_goals try split_ifs
  all_goals positivity

lemma idealKernelTwo_nonneg {q : ℝ} (hq : 0 ≤ q) (m : ι) (r s : Option ι) : 0 ≤ idealKernelTwo q m r s := by
  cases r  <;> cases s  <;> simp only [idealKernelTwo]
  all_goals try split_ifs
  all_goals positivity

lemma sieveKernelOne_error (q : ℝ) (r s : Option ι) :
    |sieveKernelOne q r s-idealKernelOne q r s| ≤ (q⁻¹)^2 := by
  cases r  <;> cases s  <;> simp only [sieveKernelOne,idealKernelOne]
  all_goals try split_ifs
  all_goals simp [abs_of_nonneg (sq_nonneg (q⁻¹))]
  all_goals positivity

lemma sieveKernelTwo_error {q : ℝ} (hq : 2 ≤ q) (m : ι) (r s : Option ι) :
    |sieveKernelTwo q m r s-idealKernelTwo q m r s| ≤ 4*(q⁻¹)^2 := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q-1 := by linarith
  have hi : 0 ≤ q⁻¹ := by positivity
  have hj : 0 ≤ (q-1)⁻¹ := by positivity
  have hj1 : (q-1)⁻¹ ≤ 1 := (inv_le_one₀ hq1).mpr (by linarith)
  have hji : (q-1)⁻¹ ≤ 2*q⁻¹ := by
    calc
      _  ≤  (q/2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
      _ = _ := by field_simp
  have hratio : (q+1)*(q-1)⁻¹ ≤ 3 := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hq1).mpr (by linarith)
  have h1 : q⁻¹*(q-1)⁻¹ ≤ 4*(q⁻¹)^2 := by nlinarith [mul_le_mul_of_nonneg_left hji hi]
  have h2 : (q⁻¹)^2*(q-1)⁻¹ ≤ 4*(q⁻¹)^2 := by nlinarith [mul_le_mul_of_nonneg_left hj1 (sq_nonneg (q⁻¹))]
  have h3 : (q+1)*(q⁻¹)^2*(q-1)⁻¹ ≤ 4*(q⁻¹)^2 := by nlinarith [mul_le_mul_of_nonneg_right hratio (sq_nonneg (q⁻¹))]
  cases r  <;> cases s  <;> simp only [sieveKernelTwo,idealKernelTwo]
  all_goals try split_ifs
  all_goals simp only [sub_self,sub_zero,zero_sub,abs_zero,abs_neg,
    sub_sub_cancel_left,abs_of_nonneg (mul_nonneg hi hj),
    abs_of_nonneg (mul_nonneg (sq_nonneg (q⁻¹)) hj)]
  all_goals try (first | exact h1 | exact h2 | positivity)
  all_goals rw [abs_of_nonpos (by
    have hh : 0 ≤ (q+1)*(q⁻¹)^2*(q-1)⁻¹ := by positivity
    simpa only [neg_mul] using neg_nonpos.mpr hh)]
  all_goals nlinarith

end
end MaynardDevelopment
end

/- KernelEnvelope -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma idealKernelOne_sum (q : ℝ) :
    (∑ r : Option ι, ∑ s : Option ι, idealKernelOne q r s)=1+(Fintype.card ι : ℝ)*q⁻¹ := by
  simp [Fintype.sum_option,idealKernelOne]

lemma idealKernelTwo_row (q : ℝ) (m : ι) (r : Option ι) :
    (∑ s : Option ι, idealKernelTwo q m r s)=
      r.elim (1+q⁻¹) (fun i => q⁻¹+(if i=m then (q⁻¹)^2 else 0)) := by
  cases r with
  | none => simp [Fintype.sum_option,idealKernelTwo]
  | some i =>
    rw [Fintype.sum_option]
    by_cases hi : i=m
    · simp [idealKernelTwo,hi]
    · have he (j : ι) : idealKernelTwo q m (some i) (some j)=if j=i then q⁻¹ else 0 := by
        by_cases hj : j=m <;> by_cases hij : j=i <;> simp_all [idealKernelTwo,eq_comm]
      simp only [idealKernelTwo, if_neg hi, he, Option.elim_some]
      have hs : (∑ j : ι, if j=m then 0 else if i=j then q⁻¹ else 0)=q⁻¹ := by
        calc
          _ = ∑ j : ι, if j=i then q⁻¹ else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            simpa only [idealKernelTwo,if_neg hi] using he j
          _ = _ := by simp
      rw [hs]
      ring

lemma idealKernelTwo_sum (q : ℝ) (m : ι) :
    (∑ r : Option ι, ∑ s : Option ι, idealKernelTwo q m r s)=
      1+((Fintype.card ι : ℝ)+1)*q⁻¹+(q⁻¹)^2 := by
  simp_rw [idealKernelTwo_row]
  simp only [Fintype.sum_option,Option.elim_none,Option.elim_some]
  rw [Finset.sum_add_distrib]
  simp
  ring

lemma quadratic_bernoulli (d : ℕ) {x : ℝ} (hx : 0≤x) :
    1+(d+2 : ℝ)*x+x^2 ≤ (1+x)^(d+2) := by
  induction d with
  | zero => norm_num; ring_nf; exact le_rfl
  | succ d ih =>
    have hh := mul_le_mul_of_nonneg_right ih (by linarith : 0≤1+x)
    rw [← pow_succ] at hh
    have hx3 : 0≤x^3 := pow_nonneg hx _
    push_cast
    nlinarith [sq_nonneg x]

lemma idealKernelOne_sum_bounds {q : ℝ} (hq : 0≤q) :
    1≤(∑ r : Option ι, ∑ s : Option ι, idealKernelOne q r s) ∧
      (∑ r : Option ι, ∑ s : Option ι, idealKernelOne q r s)≤(1+q⁻¹)^(Fintype.card ι) := by
  rw [idealKernelOne_sum]
  constructor
  · have hh : 0≤(Fintype.card ι : ℝ)*q⁻¹ := by positivity
    linarith
  · exact one_add_mul_le_pow (by
      have hh : 0≤q⁻¹ := by positivity
      linarith) _

lemma idealKernelTwo_sum_bounds {q : ℝ} (hq : 0≤q) (m : ι) :
    1≤(∑ r : Option ι, ∑ s : Option ι, idealKernelTwo q m r s) ∧
      (∑ r : Option ι, ∑ s : Option ι, idealKernelTwo q m r s)≤(1+q⁻¹)^(Fintype.card ι+1) := by
  rw [idealKernelTwo_sum]
  have hi : 0≤q⁻¹ := by positivity
  constructor
  · have hh : 0≤((Fintype.card ι : ℝ)+1)*q⁻¹ := by positivity
    nlinarith [sq_nonneg (q⁻¹)]
  · have hk : 0<Fintype.card ι := Fintype.card_pos_iff.mpr ⟨m⟩
    obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Fintype.card ι≠0)
    rw [hd]
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, show (1 : ℝ)+1=2 by norm_num, add_assoc, Nat.reduceAdd] using quadratic_bernoulli d hi

lemma local_error_sum_bound {q : ℝ} (hq : 2≤q) (m : ι) :
    (∑ r : Option ι, ∑ s : Option ι, |sieveKernelOne q r s-idealKernelOne q r s|)≤
      4*((Fintype.card ι : ℝ)+1)^2*(q⁻¹)^2 ∧
    (∑ r : Option ι, ∑ s : Option ι, |sieveKernelTwo q m r s-idealKernelTwo q m r s|)≤
      4*((Fintype.card ι : ℝ)+1)^2*(q⁻¹)^2 := by
  have h1 := Finset.sum_le_sum (s := Finset.univ) (fun r : Option ι => fun _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s : Option ι => fun _ => sieveKernelOne_error q r s))
  have h2 := Finset.sum_le_sum (s := Finset.univ) (fun r : Option ι => fun _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s : Option ι => fun _ => sieveKernelTwo_error hq m r s))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at h1 h2
  constructor
  · nlinarith [mul_nonneg (sq_nonneg ((Fintype.card ι : ℝ)+1)) (sq_nonneg (q⁻¹))]
  · nlinarith

lemma sum_inverse_square_large (P : Finset ℕ) (D : ℕ) (hD : 0<D) (hP : ∀ p∈P, D<p) :
    (∑ p∈P, ((p : ℝ)^2)⁻¹)≤(D : ℝ)⁻¹ := by
  calc
    _ ≤ ∑ p∈Finset.Ioc D (P.sup id), ((p : ℝ)^2)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact Finset.mem_Ioc.mpr ⟨hP p hp,Finset.le_sup (f := id) hp⟩
      · intros; positivity
    _ ≤ _ := sum_inverse_square_tail D _ hD

lemma prime_kernel_error {σ : Type*} [Fintype σ] (P : Finset ℕ) (D d : ℕ) (C : ℝ)
    (K L : ↥P → σ → σ → ℝ) (y : (↥P→σ)→ℝ)
    (hD : 0<D) (hP : ∀ p∈P, D<p) (hC : 0≤C)
    (hy : ∀ r, |y r|≤1) (hL : ∀ p a b, 0≤L p a b)
    (hb1 : ∀ p, 1≤∑ a, ∑ b, L p a b)
    (hb : ∀ p, (∑ a, ∑ b, L p a b)≤(1+(p.val : ℝ)⁻¹)^d)
    (he : ∀ p, (∑ a, ∑ b, |K p a b-L p a b|)≤C*((p.val : ℝ)⁻¹)^2) :
    |kernelQuadratic K y-kernelQuadratic L y|≤ harmonicEuler P^d*C*Real.exp C/D := by
  have hDr : (0 : ℝ)<D := by exact_mod_cast hD
  have hD1 : (1 : ℝ)≤D := by exact_mod_cast hD
  have hsum : (∑ p : ↥P, C*((p.val : ℝ)⁻¹)^2)≤C/D := by
    rw [← Finset.mul_sum]
    have hh : (∑ p : ↥P, ((p.val : ℝ)⁻¹)^2)=(∑ p∈P, ((p : ℝ)^2)⁻¹) := by
      simp only [inv_pow, Finset.univ_eq_attach]
      exact Finset.sum_attach P (fun p : ℕ => ((p : ℝ)^2)⁻¹)
    rw [hh, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (sum_inverse_square_large P D hD hP) hC
  have hprod : (∏ p : ↥P, (1+(p.val : ℝ)⁻¹)^d)≤harmonicEuler P^d := by
    simp only [← Finset.prod_pow, harmonicEuler, Finset.univ_eq_attach]
    rw [Finset.prod_attach P (fun p : ℕ => (1+(p : ℝ)⁻¹)^d)]
  have hh := kernelQuadratic_error_envelope K L y (fun p : ↥P => C*((p.val : ℝ)⁻¹)^2)
    (fun p : ↥P => (1+(p.val : ℝ)⁻¹)^d) (harmonicEuler P^d) (C/D) hy hL hb1 hb he hprod hsum
  have hexp : Real.exp (C/D)≤Real.exp C := by
    apply Real.exp_le_exp.mpr
    exact div_le_self hC hD1
  have hH : 0≤harmonicEuler P^d := by unfold harmonicEuler; positivity
  calc
    _ ≤ harmonicEuler P^d*(C/D)*Real.exp (C/D) := hh
    _ ≤ harmonicEuler P^d*(C/D)*Real.exp C := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

end
end MaynardDevelopment
end

/- SieveStates -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [DecidableEq ι]

def encodeState (r : Option ι) : Finset ι := r.elim ∅ (fun i => {i})

def stateOption (s : Finset ι) : Option ι :=
  if h : s.card=1 then some (Classical.choose (Finset.card_eq_one.mp h)) else none

lemma stateOption_empty : stateOption (∅ : Finset ι)=none := by simp [stateOption]

lemma stateOption_singleton (i : ι) : stateOption ({i} : Finset ι)=some i := by
  unfold stateOption
  rw [dif_pos (by simp)]
  congr 1
  have hh := Classical.choose_spec (Finset.card_eq_one.mp (Finset.card_singleton i))
  simpa using hh.symm

lemma encodeState_card (r : Option ι) : (encodeState r).card≤1 := by cases r <;> simp [encodeState]

lemma stateOption_encode (r : Option ι) : stateOption (encodeState r)=r := by
  cases r
  · exact stateOption_empty
  · exact stateOption_singleton _

lemma encodeState_injective : Function.Injective (encodeState : Option ι→Finset ι) := by
  intro r s h
  have hh := congrArg stateOption h
  simpa only [stateOption_encode] using hh

lemma encodeState_stateOption (s : Finset ι) (hs : s.card≤1) : encodeState (stateOption s)=s := by
  by_cases h0 : s.card=0
  · have he : s=∅ := Finset.card_eq_zero.mp h0
    simp [he,stateOption_empty,encodeState]
  · have h1 : s.card=1 := by omega
    obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h1
    rw [stateOption_singleton]
    rfl

def extendStateKernel (K : Option ι→Option ι→ℝ) (s t : Finset ι) : ℝ :=
  if s.card≤1 ∧ t.card≤1 then K (stateOption s) (stateOption t) else 0

def fullIdealOne (q : ℝ) (s t : Finset ι) : ℝ := if s=t then (q⁻¹)^s.card else 0

def fullIdealTwo (q : ℝ) (m : ι) (s t : Finset ι) : ℝ :=
  if s.erase m=t.erase m then (q⁻¹)^(s.card+(if m∈t then 1 else 0)) else 0

lemma fullIdealOne_encode (q : ℝ) (r s : Option ι) :
    fullIdealOne q (encodeState r) (encodeState s)=idealKernelOne q r s := by
  cases r <;> cases s <;> simp [encodeState,fullIdealOne,idealKernelOne]

lemma fullIdealTwo_encode (q : ℝ) (m : ι) (r s : Option ι) :
    fullIdealTwo q m (encodeState r) (encodeState s)=idealKernelTwo q m r s := by
  cases r with
  | none =>
    cases s with
    | none => simp [fullIdealTwo,encodeState,idealKernelTwo]
    | some j =>
      by_cases hj : j=m
      · simp [fullIdealTwo,encodeState,idealKernelTwo,hj]
      · simp [fullIdealTwo,encodeState,idealKernelTwo,hj,Ne.symm hj]
  | some i =>
    cases s with
    | none =>
      by_cases hi : i=m
      · simp [fullIdealTwo,encodeState,idealKernelTwo,hi]
      · simp [fullIdealTwo,encodeState,idealKernelTwo,hi,Ne.symm hi]
    | some j =>
      by_cases hi : i=m <;> by_cases hj : j=m <;> by_cases hij : i=j <;>
        simp_all [fullIdealTwo,encodeState,idealKernelTwo,eq_comm]

lemma fullIdealOne_nonneg {q : ℝ} (hq : 0≤q) (s t : Finset ι) : 0≤fullIdealOne q s t := by
  unfold fullIdealOne
  split_ifs <;> positivity

lemma fullIdealTwo_nonneg {q : ℝ} (hq : 0≤q) (m : ι) (s t : Finset ι) : 0≤fullIdealTwo q m s t := by
  unfold fullIdealTwo
  split_ifs <;> positivity

lemma card_erase_member (s : Finset ι) (m : ι) :
    (s.erase m).card+(if m∈s then 1 else 0)=s.card := by
  by_cases h : m∈s
  · simpa [h] using Finset.card_erase_add_one h
  · simp [h,Finset.erase_eq_of_notMem h]

lemma fullIdealTwo_exponent_ge (m : ι) (s t : Finset ι) (h : s.erase m=t.erase m) :
    s.card+(if m∈t then 1 else 0)≥t.card := by
  have hs := card_erase_member s m
  have ht := card_erase_member t m
  rw [h] at hs
  split_ifs at * <;> omega

lemma fullIdealOne_large {q : ℝ} (hq : 1≤q) (s t : Finset ι) (hbad : ¬(s.card≤1 ∧ t.card≤1)) :
    fullIdealOne q s t≤(q⁻¹)^2 := by
  unfold fullIdealOne
  split_ifs with h
  · subst t
    have hc : 2≤s.card := by omega
    exact pow_le_pow_of_le_one (by positivity) ((inv_le_one₀ (by linarith : 0<q)).mpr hq) hc
  · positivity

lemma fullIdealTwo_large {q : ℝ} (hq : 1≤q) (m : ι) (s t : Finset ι) (hbad : ¬(s.card≤1 ∧ t.card≤1)) :
    fullIdealTwo q m s t≤(q⁻¹)^2 := by
  unfold fullIdealTwo
  by_cases h : s.erase m=t.erase m
  · rw [if_pos h]
    have hc := fullIdealTwo_exponent_ge m s t h
    have hn : 2≤s.card+(if m∈t then 1 else 0) := by omega
    exact pow_le_pow_of_le_one (by positivity) ((inv_le_one₀ (by linarith : 0<q)).mpr hq) hn
  · rw [if_neg h]
    exact sq_nonneg _

lemma extended_kernel_errors {q : ℝ} (hq : 2≤q) (m : ι) (s t : Finset ι) :
    |extendStateKernel (sieveKernelOne q) s t-fullIdealOne q s t|≤4*(q⁻¹)^2 ∧
    |extendStateKernel (sieveKernelTwo q m) s t-fullIdealTwo q m s t|≤4*(q⁻¹)^2 := by
  by_cases hv : s.card≤1 ∧ t.card≤1
  · rw [extendStateKernel,if_pos hv,extendStateKernel,if_pos hv,
      ← encodeState_stateOption s hv.1, ← encodeState_stateOption t hv.2,
      fullIdealOne_encode,fullIdealTwo_encode,stateOption_encode,stateOption_encode]
    constructor
    · have hh := sieveKernelOne_error q (stateOption s) (stateOption t)
      nlinarith [sq_nonneg (q⁻¹)]
    · exact sieveKernelTwo_error hq m _ _
  · simp only [extendStateKernel,if_neg hv,zero_sub,abs_neg,
      abs_of_nonneg (fullIdealOne_nonneg (by linarith : 0≤q) s t),
      abs_of_nonneg (fullIdealTwo_nonneg (by linarith : 0≤q) m s t)]
    constructor
    · have hh := fullIdealOne_large (by linarith : 1≤q) s t hv
      nlinarith [sq_nonneg (q⁻¹)]
    · have hh := fullIdealTwo_large (by linarith : 1≤q) m s t hv
      nlinarith [sq_nonneg (q⁻¹)]

variable [Fintype ι]

lemma all_states_weight_sum (x : ℝ) : (∑ s : Finset ι, x^s.card)=(1+x)^(Fintype.card ι) := by
  have hh := powerset_prod_sum (Finset.univ : Finset ι) (fun _ => x)
  simpa using hh

lemma fullIdealOne_sum (q : ℝ) :
    (∑ s : Finset ι, ∑ t : Finset ι, fullIdealOne q s t)=(1+q⁻¹)^(Fintype.card ι) := by
  simp only [fullIdealOne,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  exact all_states_weight_sum _

lemma erase_eq_iff (s t : Finset ι) (m : ι) :
    s.erase m=t.erase m ↔ t=s.erase m ∨ t=insert m (s.erase m) := by
  constructor
  · intro h
    by_cases ht : m∈t
    · right
      rw [h,Finset.insert_erase ht]
    · left
      simpa [Finset.erase_eq_of_notMem ht] using h.symm
  · rintro (rfl | rfl) <;> simp

lemma fullIdealTwo_row_formula (q : ℝ) (m : ι) (s t : Finset ι) :
    fullIdealTwo q m s t =
      (if t=s.erase m then (q⁻¹)^s.card else 0)+
      (if t=insert m (s.erase m) then (q⁻¹)^(s.card+1) else 0) := by
  by_cases h0 : t=s.erase m
  · subst t
    have hne : s.erase m≠insert m (s.erase m) := by
      intro he
      have hh : m∈s.erase m := he ▸ Finset.mem_insert_self m (s.erase m)
      exact Finset.notMem_erase m s hh
    simp [fullIdealTwo,hne]
  · by_cases h1 : t=insert m (s.erase m)
    · subst t
      simp [fullIdealTwo,h0]
    · have hne : s.erase m≠t.erase m := by
        intro he
        rcases (MaynardDevelopment.erase_eq_iff s t m).mp he with he | he
        · exact h0 he
        · exact h1 he
      simp [fullIdealTwo,hne,h0,h1]

lemma fullIdealTwo_sum (q : ℝ) (m : ι) :
    (∑ s : Finset ι, ∑ t : Finset ι, fullIdealTwo q m s t)=(1+q⁻¹)^(Fintype.card ι+1) := by
  simp only [fullIdealTwo_row_formula,Finset.sum_add_distrib,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [pow_succ, ← Finset.sum_mul,all_states_weight_sum]
  ring

end
end MaynardDevelopment
end

/- MatrixCoordinates -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Finset ℕ}

def matrixCoords (r : ↥P→Finset ι) (i : ι) : PrimeSubset P :=
  ⟨P.filter (fun p => ∃ hp : p∈P, i∈r ⟨p,hp⟩),Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩

def coordsMatrix (x : ι→PrimeSubset P) (p : ↥P) : Finset ι :=
  Finset.univ.filter (fun i => p.val∈(x i).val)

lemma mem_matrixCoords (r : ↥P→Finset ι) (i : ι) (p : ↥P) :
    p.val∈(matrixCoords r i).val ↔ i∈r p := by
  simp [matrixCoords,p.property]

lemma mem_coordsMatrix (x : ι→PrimeSubset P) (p : ↥P) (i : ι) :
    i∈coordsMatrix x p ↔ p.val∈(x i).val := by simp [coordsMatrix]

lemma coordsMatrix_matrixCoords (r : ↥P→Finset ι) : coordsMatrix (matrixCoords r)=r := by
  funext p
  ext i
  rw [mem_coordsMatrix,mem_matrixCoords]

lemma matrixCoords_coordsMatrix (x : ι→PrimeSubset P) : matrixCoords (coordsMatrix x)=x := by
  funext i
  apply Subtype.ext
  ext p
  by_cases hp : p∈P
  · exact (mem_matrixCoords (coordsMatrix x) i ⟨p,hp⟩).trans (mem_coordsMatrix x ⟨p,hp⟩ i)
  · have hx : p∉(x i).val := fun hh => hp ((Finset.mem_powerset.mp (x i).property) hh)
    simp [matrixCoords,hp,hx]

def primeColorMatrixEquiv : (↥P→Finset ι) ≃ (ι→PrimeSubset P) where
  toFun := matrixCoords
  invFun := coordsMatrix
  left_inv := coordsMatrix_matrixCoords
  right_inv := matrixCoords_coordsMatrix

lemma subsetWeight_matrixCoords (r : ↥P→Finset ι) (i : ι) :
    subsetWeight (matrixCoords r i)=∏ p : ↥P, if i∈r p then (p.val : ℝ)⁻¹ else 1 := by
  rw [subsetWeight,primeSetProduct_weight]
  have he : (∏ p : ↥P, if i∈r p then (p.val : ℝ)⁻¹ else 1)=
      ∏ p∈P, if ∃ hp : p∈P, i∈r ⟨p,hp⟩ then (p : ℝ)⁻¹ else 1 := by
    rw [Finset.prod_subtype P (fun p => Iff.rfl)
      (fun p => if ∃ hp : p∈P, i∈r ⟨p,hp⟩ then (p : ℝ)⁻¹ else 1)]
    apply Finset.prod_congr rfl
    intro p hp
    simp
  rw [he, ← Finset.prod_filter]
  rfl

lemma matrix_weight_identity (r : ↥P→Finset ι) :
    (∏ p : ↥P, ((p.val : ℝ)⁻¹)^(r p).card)=∏ i, subsetWeight (matrixCoords r i) := by
  simp only [subsetWeight_matrixCoords]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← Finset.prod_filter]
  have he : Finset.univ.filter (fun i => i∈r p)=r p := by ext i; simp
  rw [he,Finset.prod_const]

lemma fullIdealOne_product (r s : ↥P→Finset ι) :
    (∏ p : ↥P, fullIdealOne (p.val : ℝ) (r p) (s p))=
      if r=s then ∏ i, subsetWeight (matrixCoords r i) else 0 := by
  by_cases hrs : r=s
  · subst s
    simp only [fullIdealOne,if_true]
    exact matrix_weight_identity r
  · rw [if_neg hrs]
    obtain ⟨p,hp⟩ : ∃ p, r p≠s p := by by_contra! h; exact hrs (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ p) (by simp [fullIdealOne,hp])

set_option maxHeartbeats 2000000 in
lemma kernelQuadratic_fullIdealOne (y : (ι→PrimeSubset P)→ℝ) :
    kernelQuadratic (fun p : ↥P => fullIdealOne (p.val : ℝ)) (fun r => y (matrixCoords r))=
      ∑ x : ι→PrimeSubset P, (∏ i, subsetWeight (x i))*y x^2 := by
  unfold kernelQuadratic
  simp only [fullIdealOne_product,mul_ite,mul_zero]
  have hh := Fintype.sum_equiv (primeColorMatrixEquiv (P := P) (ι := ι))
    (fun r => ∑ s, if r=s then y (matrixCoords r)*y (matrixCoords s)*(∏ i, subsetWeight (matrixCoords r i)) else 0)
    (fun x : ι→PrimeSubset P => (∏ i, subsetWeight (x i))*y x^2) (by
      intro r
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, primeColorMatrixEquiv, Equiv.coe_fn_mk]
      ring)
  convert hh using 1
  apply Finset.sum_congr (by ext r; simp)
  intro r hr
  simp


end
end MaynardDevelopment
end

/- IdealMarginal -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {P : Finset ℕ} {d : ℕ}

lemma matrixCoords_coordinate_eq_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r s : ↥P→Finset ι) (i : ι) :
    matrixCoords r i=matrixCoords s i ↔ ∀ p : ↥P, (i∈r p ↔ i∈s p) := by
  constructor
  · intro h p
    rw [← mem_matrixCoords r i p,← mem_matrixCoords s i p,h]
  · intro h
    apply Subtype.ext
    ext p
    by_cases hp : p∈P
    · exact (mem_matrixCoords r i ⟨p,hp⟩).trans ((h ⟨p,hp⟩).trans (mem_matrixCoords s i ⟨p,hp⟩).symm)
    · simp [matrixCoords,hp]

lemma matrixErase_zero_iff (r s : ↥P→Finset (Fin (d+1))) :
    (∀ p : ↥P, (r p).erase 0=(s p).erase 0) ↔ Fin.tail (matrixCoords r)=Fin.tail (matrixCoords s) := by
  constructor
  · intro h
    funext i
    apply (matrixCoords_coordinate_eq_iff r s i.succ).mpr
    intro p
    have hh := Finset.ext_iff.mp (h p) i.succ
    simpa using hh
  · intro h p
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · have hi : matrixCoords r j.succ=matrixCoords s j.succ := congrFun h j
      have hh := (matrixCoords_coordinate_eq_iff r s j.succ).mp hi p
      simpa using hh

lemma fullIdealTwo_product_zero (r s : ↥P→Finset (Fin (d+1))) :
    (∏ p : ↥P, fullIdealTwo (p.val : ℝ) 0 (r p) (s p))=
      if Fin.tail (matrixCoords r)=Fin.tail (matrixCoords s) then
        (∏ i, subsetWeight (matrixCoords r i))*subsetWeight (matrixCoords s 0) else 0 := by
  by_cases htail : Fin.tail (matrixCoords r)=Fin.tail (matrixCoords s)
  · rw [if_pos htail]
    have he := (matrixErase_zero_iff r s).mpr htail
    have hp (p : ↥P) : fullIdealTwo (p.val : ℝ) 0 (r p) (s p)=
        ((p.val : ℝ)⁻¹)^(r p).card*(if 0∈s p then (p.val : ℝ)⁻¹ else 1) := by
      rw [fullIdealTwo,if_pos (he p),pow_add]
      split_ifs <;> simp
    simp only [hp,Finset.prod_mul_distrib,matrix_weight_identity,← subsetWeight_matrixCoords]
  · rw [if_neg htail]
    have hn : ∃ p : ↥P, (r p).erase 0≠(s p).erase 0 := by
      by_contra! h
      exact htail ((matrixErase_zero_iff r s).mp h)
    obtain ⟨p,hp⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ p) (by simp [fullIdealTwo,hp])

lemma sum_matrixCoords {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq ↥P]
    (f : (ι→PrimeSubset P)→ℝ) : (∑ r : ↥P→Finset ι, f (matrixCoords r))=∑ x, f x := by
  apply Finset.sum_bij (fun r _ => matrixCoords r)
  · intros; exact Finset.mem_univ _
  · intro r hr s hs h
    have hh := congrArg coordsMatrix h
    simpa only [coordsMatrix_matrixCoords] using hh
  · intro x hx
    exact ⟨coordsMatrix x,Finset.mem_univ _,matrixCoords_coordsMatrix x⟩
  · intros; rfl

lemma sum_fin_cons {α : Type*} [Fintype α] (d : ℕ) (f : (Fin (d+1)→α)→ℝ) :
    (∑ x, f x)=∑ z : Fin d→α, ∑ a : α, f (Fin.cons a z) := by
  classical
  have hh := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (d+1) => α))
    (fun x : α×(Fin d→α) => f (Fin.cons x.1 x.2)) f (fun x => rfl)
  rw [Fintype.sum_prod_type,Finset.sum_comm] at hh
  exact hh.symm

lemma marginal_diagonal_sum {α : Type*} [Fintype α] (d : ℕ) (w : α→ℝ) (y : (Fin (d+1)→α)→ℝ) :
    (∑ x : Fin (d+1)→α, ∑ z : Fin (d+1)→α,
      y x*y z*(if Fin.tail x=Fin.tail z then (∏ i, w (x i))*w (z 0) else 0)) =
      ∑ z : Fin d→α, (∏ i, w (z i))*(∑ a, w a*y (Fin.cons a z))^2 := by
  classical
  rw [sum_fin_cons]
  simp_rw [sum_fin_cons]
  have he (x z : Fin d→α) (a b : α) :
      y (Fin.cons a x)*y (Fin.cons b z)*
        (if Fin.tail (Fin.cons (α := fun _ => α) a x)=Fin.tail (Fin.cons (α := fun _ => α) b z) then
          (∏ i, w (Fin.cons (α := fun _ => α) a x i))*w (Fin.cons (α := fun _ => α) b z 0) else 0) =
      if x=z then (∏ i, w (x i))*(w a*y (Fin.cons a x))*(w b*y (Fin.cons b x)) else 0 := by
    simp only [Fin.tail_cons,Fin.cons_zero,Fin.prod_univ_succ,Fin.cons_succ]
    by_cases h : x=z
    · subst z; simp only [if_true]; ring
    · simp [h]
  simp only [he]
  apply Finset.sum_congr rfl
  intro x hx
  have hs (a : α) : (∑ z : Fin d→α, ∑ b : α,
      if x=z then (∏ i, w (x i))*(w a*y (Fin.cons a x))*(w b*y (Fin.cons b x)) else 0) =
      (∏ i, w (x i))*(w a*y (Fin.cons a x))*(∑ b : α, w b*y (Fin.cons b x)) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
    rw [← Finset.mul_sum]
  simp only [hs]
  rw [← Finset.sum_mul,← Finset.mul_sum]
  ring

set_option maxHeartbeats 2000000 in
lemma kernelQuadratic_fullIdealTwo (y : (Fin (d+1)→PrimeSubset P)→ℝ) :
    kernelQuadratic (fun p : ↥P => fullIdealTwo (p.val : ℝ) 0) (fun r => y (matrixCoords r)) =
      ∑ z : Fin d→PrimeSubset P, (∏ i, subsetWeight (z i))*(∑ a, subsetWeight a*y (Fin.cons a z))^2 := by
  letI : DecidableEq ↥P := fun a b => Classical.propDecidable (a=b)
  unfold kernelQuadratic
  simp only [fullIdealTwo_product_zero]
  have hs (r : ↥P→Finset (Fin (d+1))) :
      (∑ s : ↥P→Finset (Fin (d+1)), y (matrixCoords r)*y (matrixCoords s)*
        (if Fin.tail (matrixCoords r)=Fin.tail (matrixCoords s) then
          (∏ i, subsetWeight (matrixCoords r i))*subsetWeight (matrixCoords s 0) else 0)) =
      ∑ z : Fin (d+1)→PrimeSubset P, y (matrixCoords r)*y z*
        (if Fin.tail (matrixCoords r)=Fin.tail z then
          (∏ i, subsetWeight (matrixCoords r i))*subsetWeight (z 0) else 0) := by
    exact sum_matrixCoords (ι := Fin (d+1)) (P := P)
      (fun z => y (matrixCoords r)*y z*(if Fin.tail (matrixCoords r)=Fin.tail z then
        (∏ i, subsetWeight (matrixCoords r i))*subsetWeight (z 0) else 0))
  simp only [hs]
  rw [sum_matrixCoords (fun x => ∑ z : Fin (d+1)→PrimeSubset P, y x*y z*
    (if Fin.tail x=Fin.tail z then (∏ i, subsetWeight (x i))*subsetWeight (z 0) else 0))]
  convert marginal_diagonal_sum d subsetWeight y using 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs <;> rfl

end
end MaynardDevelopment
end

/- FullKernelBounds -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullKernelOne (q : ℝ) (s t : Finset ι) : ℝ := extendStateKernel (sieveKernelOne q) s t

def fullKernelTwo (q : ℝ) (m : ι) (s t : Finset ι) : ℝ := extendStateKernel (sieveKernelTwo q m) s t

def kernelErrorConstant (k : ℕ) : ℝ := 4*(2^k : ℝ)^2

lemma fullKernel_error_sums {q : ℝ} (hq : 2≤q) (m : ι) :
    (∑ s : Finset ι, ∑ t : Finset ι, |fullKernelOne q s t-fullIdealOne q s t|)≤kernelErrorConstant (Fintype.card ι)*(q⁻¹)^2 ∧
    (∑ s : Finset ι, ∑ t : Finset ι, |fullKernelTwo q m s t-fullIdealTwo q m s t|)≤kernelErrorConstant (Fintype.card ι)*(q⁻¹)^2 := by
  have h1 := Finset.sum_le_sum (s := Finset.univ) (fun s : Finset ι => fun _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun t : Finset ι => fun _ => (extended_kernel_errors hq m s t).1))
  have h2 := Finset.sum_le_sum (s := Finset.univ) (fun s : Finset ι => fun _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun t : Finset ι => fun _ => (extended_kernel_errors hq m s t).2))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_finset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] at h1 h2
  constructor <;> dsimp [fullKernelOne,fullKernelTwo,kernelErrorConstant] <;> nlinarith

lemma fullKernelOne_global_error (P : Finset ℕ) (D : ℕ) (m : ι) (hD : 0<D)
    (hP : ∀ p∈P, D<p) (y : (↥P→Finset ι)→ℝ) (hy : ∀ r, |y r|≤1) :
    |kernelQuadratic (fun p : ↥P => fullKernelOne (p.val : ℝ)) y-
      kernelQuadratic (fun p : ↥P => fullIdealOne (p.val : ℝ)) y| ≤
      harmonicEuler P^(Fintype.card ι)*kernelErrorConstant (Fintype.card ι)*
        Real.exp (kernelErrorConstant (Fintype.card ι))/D := by
  apply prime_kernel_error P D (Fintype.card ι) (kernelErrorConstant (Fintype.card ι)) _ _ y hD hP
    (by unfold kernelErrorConstant; positivity) hy
  · intro p a b; exact fullIdealOne_nonneg (Nat.cast_nonneg _) _ _
  · intro p
    rw [fullIdealOne_sum]
    apply one_le_pow₀
    have hh : (0 : ℝ)≤(p.val : ℝ)⁻¹ := by positivity
    linarith
  · intro p; rw [fullIdealOne_sum]
  · intro p
    exact (fullKernel_error_sums (by exact_mod_cast (show 2≤p.val by have hh := hP p.val p.property; omega)) m).1

lemma fullKernelTwo_global_error (P : Finset ℕ) (D : ℕ) (m : ι) (hD : 0<D)
    (hP : ∀ p∈P, D<p) (y : (↥P→Finset ι)→ℝ) (hy : ∀ r, |y r|≤1) :
    |kernelQuadratic (fun p : ↥P => fullKernelTwo (p.val : ℝ) m) y-
      kernelQuadratic (fun p : ↥P => fullIdealTwo (p.val : ℝ) m) y| ≤
      harmonicEuler P^(Fintype.card ι+1)*kernelErrorConstant (Fintype.card ι)*
        Real.exp (kernelErrorConstant (Fintype.card ι))/D := by
  apply prime_kernel_error P D (Fintype.card ι+1) (kernelErrorConstant (Fintype.card ι)) _ _ y hD hP
    (by unfold kernelErrorConstant; positivity) hy
  · intro p a b; exact fullIdealTwo_nonneg (Nat.cast_nonneg _) _ _ _
  · intro p
    rw [fullIdealTwo_sum]
    apply one_le_pow₀
    have hh : (0 : ℝ)≤(p.val : ℝ)⁻¹ := by positivity
    linarith
  · intro p; rw [fullIdealTwo_sum]
  · intro p
    exact (fullKernel_error_sums (by exact_mod_cast (show 2≤p.val by have hh := hP p.val p.property; omega)) m).2

end
end MaynardDevelopment
end

/- TestFunctionBounds -/
section

open scoped BigOperators Topology
open Filter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma dyadicStep_le_one (M : ℕ) (t : ℝ) : dyadicStep M t≤1 := by
  by_cases he : ∃ j∈Finset.range M, dyadicBin j t
  · obtain ⟨j,hj,ht⟩ := he
    rw [dyadicStep_eq_of_bin (Finset.mem_range.mp hj) ht]
    exact (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num))
  · push_neg at he
    have hz : dyadicStep M t=0 := by simp +contextual [dyadicStep,he]
    rw [hz]
    norm_num

lemma discreteTensor_unit_bound {α : Type*} (d : ℕ) (g t : α→ℝ) (C : ℝ)
    (hg : ∀ a, 0≤g a ∧ g a≤1) (x : Fin d→α) :
    0≤discreteTensor d g t C x ∧ |discreteTensor d g t C x|≤1 := by
  unfold discreteTensor
  split_ifs
  · have h0 : 0≤∏ i, g (x i) := Finset.prod_nonneg (fun i _ => (hg _).1)
    refine ⟨h0,?_⟩
    rw [abs_of_nonneg h0]
    exact Finset.prod_le_one (fun i _ => (hg _).1) (fun i _ => (hg _).2)
  · norm_num

lemma discreteI_lower {α : Type*} [Fintype α] (d : ℕ) (w g t : α→ℝ) (C : ℝ)
    (hw : ∀ a, 0≤w a) (ht : ∀ a, 0≤t a) (hC : 0<C)
    (hM : 2*(d+1 : ℝ)*(∑ a, w a*g a^2*t a)≤C*(∑ a, w a*g a^2)) :
    (∑ a, w a*g a^2)^(d+1)/2≤discreteI (d+1) w g t C := by
  have hh := finite_tensor_markov d (fun a => w a*g a^2) t C
    (fun a => mul_nonneg (hw a) (sq_nonneg _)) ht hC hM
  refine hh.trans_eq ?_
  apply Finset.sum_congr rfl
  intro x hx
  dsimp [discreteTensor]
  split_ifs
  · rw [← Finset.prod_pow,Finset.prod_mul_distrib]
  · simp

lemma sieve_discreteI_lower {α : Type*} [Fintype α] (M : ℕ) (w t : α→ℝ) (c : ℝ)
    (hM : 0<M) (hc : 0<c) (hw : ∀ a, 0≤w a) (ht : ∀ a, 0≤t a)
    (hmass : ∀ j<M, c*2^j/2≤dyadicMass w t j ∧ dyadicMass w t j≤2*c*2^j) :
    c^(sieveDimension M)/(2 : ℝ)^(sieveDimension M+1) ≤
      discreteI (sieveDimension M) w (fun a => dyadicStep M (t a)) t (sieveCutoff M) := by
  let k := sieveDimension M
  let g (a : α) := dyadicStep M (t a)
  let G : ℝ := ∑ a, w a*g a^2
  let U : ℝ := ∑ a, w a*g a^2*t a
  obtain ⟨hL,hGlo,hGhi,hU⟩ := dyadicStep_scalar_bounds M w t c hM hc hw hmass
  change c/2≤G at hGlo
  change U≤4*c*M at hU
  have hk : 0<k := by dsimp [k,sieveDimension]; positivity
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  have hMR : (0 : ℝ)<M := by exact_mod_cast hM
  have hC : (0 : ℝ)<sieveCutoff M := by exact_mod_cast (sieveCutoff_bounds M hM).1
  have hKG : 2*(k : ℝ)*U≤(sieveCutoff M : ℝ)*G := by
    have hh1 := mul_le_mul_of_nonneg_left hU (show 0≤2*(k : ℝ) by positivity)
    have hh2 := mul_le_mul_of_nonneg_left hGlo hC.le
    have hbase : (32 : ℝ)*k*M≤sieveCutoff M := by
      dsimp [sieveCutoff,k]
      push_cast
      have hh : (0 : ℝ)≤2^M := by positivity
      linarith
    have hh3 := mul_le_mul_of_nonneg_right hbase (show 0≤c/2 by positivity)
    nlinarith
  have hki : k-1+1=k := Nat.sub_add_cancel hk
  have hlow := discreteI_lower (k-1) w g t (sieveCutoff M) hw ht hC (by
    have hkiR : ((k-1 : ℕ) : ℝ)+1=k := by exact_mod_cast hki
    change 2*(((k-1 : ℕ) : ℝ)+1)*U≤_
    rw [hkiR]
    exact hKG)
  rw [hki] at hlow
  calc
    _ = (c/2)^k/2 := by dsimp [k]; rw [div_pow,pow_succ]; ring
    _ ≤ G^k/2 := div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hGlo _) (by norm_num)
    _ ≤ _ := hlow

lemma robust_kernel_ratio {A B C c k I J Q₁ Q₂ : ℝ}
    (hA : 0≤A) (hB : 2*A+2≤B) (hC : 0<C) (hc : 0<c) (hk : 0≤k) (hkC : k≤C)
    (hI : 0<I) (hmain : B*C*c*I<k*J) (h₁ : |Q₁-I|≤I) (h₂ : |Q₂-J|≤c*I) :
    A*C*c*Q₁<k*Q₂ := by
  have hu := (abs_le.mp h₁).2
  have hl := (abs_le.mp h₂).1
  have hq := mul_le_mul_of_nonneg_left hl hk
  have hkb := mul_le_mul_of_nonneg_right hkC (show 0≤c*I by positivity)
  have hbb := mul_le_mul_of_nonneg_right hB (show 0≤C*c*I by positivity)
  have hqu := mul_le_mul_of_nonneg_left hu (show 0≤A*C*c by positivity)
  have hp : 0<C*c*I := by positivity
  nlinarith

end
end MaynardDevelopment
end

/- QuadraticSieveTest -/
section

open scoped BigOperators Topology
open Filter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

instance sieveDimension_neZero (M : ℕ) : NeZero (sieveDimension M) :=
  ⟨by unfold sieveDimension; positivity⟩

def sieveTest (P : Finset ℕ) (M R : ℕ) (r : ↥P→Finset (Fin (sieveDimension M))) : ℝ :=
  discreteTensor (sieveDimension M) (fun s => dyadicStep M (subsetTime R s)) (subsetTime R)
    (sieveCutoff M) (matrixCoords r)

def sieveQuadraticI (P : Finset ℕ) (M R : ℕ) : ℝ :=
  kernelQuadratic (fun p : ↥P => fullKernelOne (p.val : ℝ)) (sieveTest P M R)

def sieveQuadraticJ (P : Finset ℕ) (M R : ℕ) (i : Fin (sieveDimension M)) : ℝ :=
  kernelQuadratic (fun p : ↥P => fullKernelTwo (p.val : ℝ) i) (sieveTest P M R)

lemma sieveTest_bound (P : Finset ℕ) (M R : ℕ) (r : ↥P→Finset (Fin (sieveDimension M))) :
    0≤sieveTest P M R r ∧ |sieveTest P M R r|≤1 :=
  discreteTensor_unit_bound _ _ _ _ (fun s => ⟨dyadicStep_nonneg _ _,dyadicStep_le_one _ _⟩) _

lemma sieveQuadraticI_error (P : Finset ℕ) (D M R : ℕ) (hD : 0<D) (hP : ∀ p∈P, D<p) :
    |sieveQuadraticI P M R-
      discreteI (sieveDimension M) subsetWeight (fun s : PrimeSubset P => dyadicStep M (subsetTime R s))
        (subsetTime R) (sieveCutoff M)| ≤
      harmonicEuler P^(sieveDimension M)*kernelErrorConstant (sieveDimension M)*
        Real.exp (kernelErrorConstant (sieveDimension M))/D := by
  have hh := fullKernelOne_global_error P D (0 : Fin (sieveDimension M)) hD hP (sieveTest P M R)
    (fun r => (sieveTest_bound P M R r).2)
  have he : kernelQuadratic (fun p : ↥P => fullIdealOne (p.val : ℝ)) (sieveTest P M R)=
      discreteI (sieveDimension M) subsetWeight (fun s : PrimeSubset P => dyadicStep M (subsetTime R s))
        (subsetTime R) (sieveCutoff M) := by
    exact kernelQuadratic_fullIdealOne _
  rw [he] at hh
  simpa [sieveQuadraticI] using hh

lemma sieveQuadraticJ_error (P : Finset ℕ) (D M R : ℕ) (hD : 0<D) (hP : ∀ p∈P, D<p) :
    |sieveQuadraticJ P M R 0-
      discreteJ (sieveDimension M-1) subsetWeight (fun s : PrimeSubset P => dyadicStep M (subsetTime R s))
        (subsetTime R) (sieveCutoff M)| ≤
      harmonicEuler P^(sieveDimension M+1)*kernelErrorConstant (sieveDimension M)*
        Real.exp (kernelErrorConstant (sieveDimension M))/D := by
  have hh := fullKernelTwo_global_error P D (0 : Fin (sieveDimension M)) hD hP (sieveTest P M R)
    (fun r => (sieveTest_bound P M R r).2)
  have he : kernelQuadratic (fun p : ↥P => fullIdealTwo (p.val : ℝ) (0 : Fin (sieveDimension M))) (sieveTest P M R)=
      discreteJ (sieveDimension M-1) subsetWeight (fun s : PrimeSubset P => dyadicStep M (subsetTime R s))
        (subsetTime R) (sieveCutoff M) := by
    exact kernelQuadratic_fullIdealTwo (d := 2^M+1) _
  rw [he] at hh
  simpa [sieveQuadraticJ] using hh

def sieveErrorThreshold (M : ℕ) : ℝ :=
  (16*(2 : ℝ)^M)^(sieveDimension M+1)*
    (kernelErrorConstant (sieveDimension M)*Real.exp (kernelErrorConstant (sieveDimension M)))*
    (2 : ℝ)^(sieveDimension M+1)

lemma relative_euler_error {H a c K D : ℝ} (k : ℕ)
    (hH : 0≤H) (hHac : H≤a*c) (ha : 1≤a) (hc : 0<c) (hK : 0≤K) (hD : 0<D)
    (hlarge : a^(k+1)*K*2^(k+1)≤D) :
    H^k*K/D≤c^k/2^(k+1) ∧ H^(k+1)*K/D≤c^(k+1)/2^(k+1) := by
  have hb (j : ℕ) (hj : j≤k+1) : H^j*K/D≤c^j/2^(k+1) := by
    have hpow := pow_le_pow_left₀ hH hHac j
    rw [mul_pow] at hpow
    have hap := pow_le_pow_right₀ ha hj
    have h1 := mul_le_mul_of_nonneg_right hpow (show 0≤K*2^(k+1) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hap (show 0≤c^j*K*2^(k+1) by positivity)
    have h3 := mul_le_mul_of_nonneg_right hlarge (pow_nonneg hc.le j)
    apply (div_le_div_iff₀ hD (by positivity)).mpr
    nlinarith
  exact ⟨hb k (by omega),hb (k+1) le_rfl⟩

/-- After pre-sieving by sufficiently many fixed primes, the actual finite residue model
has an arbitrarily large prime-detecting ratio. -/
theorem sieve_quadratic_ratio (W D M : ℕ) (A B : ℝ) (hW : W≠0) (hM : 0<M)
    (hA : 0≤A) (hB : 2*A+2≤B) (hlarge : 1056*B<M)
    (hD : 8*2^M≤D) (herror : sieveErrorThreshold M≤D)
    (hsmall : ∀ p : ℕ, Nat.Prime p → p≤D → p∣W) :
    ∀ᶠ R : ℕ in atTop, ∀ E : ℕ, (E=1 ∨ Nat.Prime E) → (E=1 ∨ D≤E) →
      let P := sievePrimes W E (R^(2^M))
      A*sieveCutoff M*(roughDensity W*Real.log R)*sieveQuadraticI P M R <
        (sieveDimension M : ℝ)*sieveQuadraticJ P M R 0 := by
  have hB0 : 0≤B := by linarith
  have hD0 : 0<D := by
    have hh : 0<(2 : ℕ)^M := by positivity
    omega
  filter_upwards [primeSubset_sieve_ratio W D M B hW hD hsmall hM hB0 hlarge,
    subset_dyadicMass_bounds W D M hW hD hsmall,
    harmonicEuler_power_bound W (2^M) hW (by positivity),eventually_ge_atTop 2]
    with R hratio hmass hEuler hR2 E hE hED
  let P := sievePrimes W E (R^(2^M))
  let c : ℝ := roughDensity W*Real.log R
  let g (s : PrimeSubset P) := dyadicStep M (subsetTime R s)
  let I : ℝ := discreteI (sieveDimension M) subsetWeight g (subsetTime R) (sieveCutoff M)
  let J : ℝ := discreteJ (sieveDimension M-1) subsetWeight g (subsetTime R) (sieveCutoff M)
  have hc : 0<c := mul_pos (roughDensity_pos hW) (Real.log_pos (by exact_mod_cast hR2))
  have hm := hmass E hE hED
  have hIlow : c^(sieveDimension M)/2^(sieveDimension M+1)≤I :=
    sieve_discreteI_lower M subsetWeight (subsetTime R) c hM hc subsetWeight_nonneg (subsetTime_nonneg R) hm
  have hIp : 0<I := lt_of_lt_of_le (by positivity) hIlow
  have hPs (p : ℕ) (hp : p∈P) := mem_sievePrimes.mp hp
  have hPD : ∀ p∈P, D<p := by
    intro p hp
    have hh := hPs p hp
    by_contra h
    exact hh.2.2.1 (hsmall p hh.2.1 (by omega))
  have heuler : harmonicEuler P≤(16*(2 : ℝ)^M)*c := by
    have hh := hEuler P (fun p hp => (hPs p hp).2.1)
      (fun p hp => ((hPs p hp).2.1.coprime_iff_not_dvd.mpr (hPs p hp).2.2.1).symm)
      (fun p hp => (hPs p hp).1)
    convert hh using 1 <;> dsimp [c] <;> push_cast <;> ring
  have her := relative_euler_error (sieveDimension M) (H := harmonicEuler P)
    (a := 16*(2 : ℝ)^M) (c := c)
    (K := kernelErrorConstant (sieveDimension M)*Real.exp (kernelErrorConstant (sieveDimension M)))
    (D := (D : ℝ)) (by unfold harmonicEuler; positivity) heuler
    (by have hh : (1 : ℝ)≤2^M := one_le_pow₀ (by norm_num); linarith)
    hc (by unfold kernelErrorConstant; positivity) (by exact_mod_cast hD0) herror
  have h1 := sieveQuadraticI_error P D M R hD0 hPD
  have h2 := sieveQuadraticJ_error P D M R hD0 hPD
  change |sieveQuadraticI P M R-I|≤_ at h1
  change |sieveQuadraticJ P M R 0-J|≤_ at h2
  have h1' : |sieveQuadraticI P M R-I|≤I := by
    refine h1.trans ((le_of_eq ?_).trans (her.1.trans hIlow))
    ring
  have h2' : |sieveQuadraticJ P M R 0-J|≤c*I := by
    refine h2.trans ((le_of_eq ?_).trans (her.2.trans ?_))
    · ring
    · have hh := mul_le_mul_of_nonneg_left hIlow hc.le
      rw [pow_succ]
      convert hh using 1 <;> ring
  have hC : (0 : ℝ)<sieveCutoff M := by exact_mod_cast (sieveCutoff_bounds M hM).1
  have hkC : (sieveDimension M : ℝ)≤sieveCutoff M := by
    have hh : sieveDimension M≤sieveDimension M*M := by nlinarith
    have hn : sieveDimension M≤sieveCutoff M := by
      dsimp [sieveCutoff]
      exact hh.trans ((Nat.mul_le_mul_right M (Nat.le_mul_of_pos_left _ (by decide : 0<32))).trans
        (Nat.le_add_right _ _))
    exact_mod_cast hn
  exact robust_kernel_ratio hA hB hC hc (Nat.cast_nonneg _) hkC hIp (hratio E hE hED) h1' h2'

end
end MaynardDevelopment
end

/- SieveSymmetry -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [DecidableEq ι]

lemma encodeState_map (e : ι≃ι) (r : Option ι) :
    (encodeState r).map e.toEmbedding=encodeState (r.map e) := by
  cases r <;> simp [encodeState]

lemma stateOption_map (e : ι≃ι) (s : Finset ι) (hs : s.card≤1) :
    stateOption (s.map e.toEmbedding)=(stateOption s).map e := by
  rw [← encodeState_stateOption s hs,encodeState_map,stateOption_encode,stateOption_encode]

lemma sieveKernelTwo_map (q : ℝ) (e : ι≃ι) (m : ι) (r s : Option ι) :
    sieveKernelTwo q (e m) (r.map e) (s.map e)=sieveKernelTwo q m r s := by
  cases r <;> cases s <;> simp [sieveKernelTwo,e.injective.eq_iff]

lemma fullKernelTwo_map (q : ℝ) (e : ι≃ι) (m : ι) (s t : Finset ι) :
    fullKernelTwo q (e m) (s.map e.toEmbedding) (t.map e.toEmbedding)=fullKernelTwo q m s t := by
  unfold fullKernelTwo extendStateKernel
  simp only [Finset.card_map]
  by_cases h : s.card≤1 ∧ t.card≤1
  · rw [if_pos h,if_pos h,stateOption_map e s h.1,stateOption_map e t h.2,sieveKernelTwo_map]
  · rw [if_neg h,if_neg h]

variable [Fintype ι] {P : Finset ℕ}

lemma matrixCoords_map (e : ι≃ι) (r : ↥P→Finset ι) :
    matrixCoords (fun p => (r p).map e.toEmbedding)=fun i => matrixCoords r (e.symm i) := by
  funext i
  apply Subtype.ext
  ext p
  by_cases hp : p∈P
  · rw [show p= (⟨p,hp⟩ : ↥P).val from rfl,mem_matrixCoords,mem_matrixCoords,Finset.mem_map_equiv]
  · simp [matrixCoords,hp]

lemma discreteTensor_reindex {α : Type*} (k : ℕ) (e : Fin k≃Fin k) (g t : α→ℝ) (C : ℝ) (x : Fin k→α) :
    discreteTensor k g t C (fun i => x (e i))=discreteTensor k g t C x := by
  unfold discreteTensor
  rw [e.sum_comp (fun i => t (x i)),e.prod_comp (fun i => g (x i))]

lemma sieveTest_map (P : Finset ℕ) (M R : ℕ) (e : Fin (sieveDimension M)≃Fin (sieveDimension M))
    (r : ↥P→Finset (Fin (sieveDimension M))) :
    sieveTest P M R (fun p => (r p).map e.toEmbedding)=sieveTest P M R r := by
  unfold sieveTest
  rw [matrixCoords_map]
  exact discreteTensor_reindex _ _ _ _ _ _

lemma matrix_map_bijective (P : Finset ℕ) (e : ι≃ι) :
    Function.Bijective (fun r : ↥P→Finset ι => fun p => (r p).map e.toEmbedding) := by
  constructor
  · intro r s h
    funext p
    exact Finset.map_injective e.toEmbedding (congrFun h p)
  · intro r
    refine ⟨fun p => (r p).map e.symm.toEmbedding,?_⟩
    funext p
    ext i
    simp

lemma sieveQuadraticJ_map (P : Finset ℕ) (M R : ℕ)
    (e : Fin (sieveDimension M)≃Fin (sieveDimension M)) (m : Fin (sieveDimension M)) :
    sieveQuadraticJ P M R (e m)=sieveQuadraticJ P M R m := by
  letI : DecidableEq ↥P := fun a b => Classical.propDecidable (a=b)
  unfold sieveQuadraticJ kernelQuadratic
  let f (r : ↥P→Finset (Fin (sieveDimension M))) := fun p => (r p).map e.symm.toEmbedding
  have hf := matrix_map_bijective P e.symm
  apply Finset.sum_bij (fun r _ => f r)
  · intros; exact Finset.mem_univ _
  · intro r hr s hs h
    exact hf.1 h
  · intro r hr
    obtain ⟨s,hs⟩ := hf.2 r
    exact ⟨s,Finset.mem_univ _,hs⟩
  · intro r hr
    apply Finset.sum_bij (fun s _ => f s)
    · intros; exact Finset.mem_univ _
    · intro s hs t ht h
      exact hf.1 h
    · intro s hs
      obtain ⟨t,ht⟩ := hf.2 s
      exact ⟨t,Finset.mem_univ _,ht⟩
    · intro s hs
      dsimp only [f]
      rw [sieveTest_map,sieveTest_map]
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      have hh := fullKernelTwo_map (p.val : ℝ) e.symm (e m) (r p) (s p)
      simpa using hh.symm

lemma sieveQuadraticJ_eq_zero (P : Finset ℕ) (M R : ℕ) (m : Fin (sieveDimension M)) :
    sieveQuadraticJ P M R m=sieveQuadraticJ P M R 0 := by
  have hh := sieveQuadraticJ_map P M R (Equiv.swap 0 m) 0
  simpa using hh

lemma sum_sieveQuadraticJ (P : Finset ℕ) (M R : ℕ) :
    (∑ m : Fin (sieveDimension M), sieveQuadraticJ P M R m)=
      (sieveDimension M : ℝ)*sieveQuadraticJ P M R 0 := by
  simp only [sieveQuadraticJ_eq_zero,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

end
end MaynardDevelopment
end

/- LocalCoefficients -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stateCoefficient (q : ℝ) (r d : Finset ι) : ℝ :=
  if r.card ≤ 1 then
    (if d=∅ then (q⁻¹)^r.card else 0)-(if r≠∅ ∧ d=r then 1 else 0)
  else 0

lemma stateCoefficient_empty (q : ℝ) (d : Finset ι) :
    stateCoefficient q ∅ d=if d=∅ then 1 else 0 := by simp [stateCoefficient]

lemma stateCoefficient_singleton (q : ℝ) (i : ι) (d : Finset ι) :
    stateCoefficient q {i} d=(if d=∅ then q⁻¹ else 0)-(if d={i} then 1 else 0) := by
  simp [stateCoefficient]

lemma stateCoefficient_support {q : ℝ} {r d : Finset ι} (h : stateCoefficient q r d≠0) :
    r.card ≤ 1 ∧ d⊆r := by
  have hr : r.card ≤ 1 := by by_contra hh; simp [stateCoefficient,hh] at h
  refine ⟨hr,?_⟩
  by_cases hd : d=∅
  · simp [hd]
  · have hdr : d=r := by by_contra hh; simp [stateCoefficient,hr,hd,hh] at h
    rw [hdr]

lemma stateCoefficient_abs_le {q : ℝ} (hq : 0 ≤ q) (r d : Finset ι) :
    |stateCoefficient q r d| ≤ if d=∅ then (q⁻¹)^r.card else if r=d then 1 else 0 := by
  by_cases hr : r.card ≤ 1
  · by_cases hd : d=∅
    · subst d
      have hz : ¬(r≠∅ ∧ ∅=r) := by tauto
      simp [stateCoefficient,hr,hz,abs_of_nonneg hq]
    · by_cases he : r=d
      · subst r
        simp [stateCoefficient,hr,hd]
      · simp [stateCoefficient,hr,hd,he,Ne.symm he]
  · simp only [stateCoefficient,if_neg hr,abs_zero]
    split_ifs <;> positivity

lemma stateCoefficient_abs_sum {q : ℝ} (hq : 0 ≤ q) (d : Finset ι) :
    (∑ r : Finset ι, |stateCoefficient q r d|) ≤ (1+q⁻¹)^(Fintype.card ι) := by
  calc
    _  ≤  ∑ r : Finset ι, if d=∅ then (q⁻¹)^r.card else if r=d then 1 else 0 :=
      Finset.sum_le_sum (fun r _ => stateCoefficient_abs_le hq r d)
    _  ≤  _ := by
      by_cases hd : d=∅
      · simp only [if_pos hd]
        rw [all_states_weight_sum]
      · simp only [if_neg hd,Finset.sum_ite_eq',Finset.mem_univ,if_true]
        apply one_le_pow₀
        have hh : 0 ≤ q⁻¹ := by positivity
        linarith

variable {α : Type*} [Fintype α] [DecidableEq α]

def stateFactor (h : ι→α) (r : Finset ι) (x : α) : ℝ :=
  if r.card ≤ 1 then centeredFactor h (stateOption r) x else 0

def stateIndicator (h : ι→α) (d : Finset ι) (x : α) : ℝ :=
  ∏ i∈d, if x=h i then 1 else 0

lemma stateFactor_encode (h : ι→α) (r : Option ι) (x : α) :
    stateFactor h (encodeState r) x=centeredFactor h r x := by
  rw [stateFactor,if_pos (encodeState_card r),stateOption_encode]

lemma stateIndicator_empty (h : ι→α) (x : α) : stateIndicator h ∅ x=1 := by simp [stateIndicator]
lemma stateIndicator_singleton (h : ι→α) (i : ι) (x : α) :
    stateIndicator h {i} x=if x=h i then 1 else 0 := by simp [stateIndicator]

lemma stateIndicator_nonneg (h : ι→α) (d : Finset ι) (x : α) : 0 ≤ stateIndicator h d x := by
  apply Finset.prod_nonneg
  intros; split_ifs <;> norm_num

lemma stateIndicator_le_one (h : ι→α) (d : Finset ι) (x : α) : stateIndicator h d x ≤ 1 := by
  apply Finset.prod_le_one
  · intros; split_ifs <;> norm_num
  · intros; split_ifs <;> norm_num

lemma stateFactor_expansion (h : ι→α) (r : Finset ι) (x : α) :
    stateFactor h r x=∑ d : Finset ι, stateCoefficient (Fintype.card α : ℝ) r d*stateIndicator h d x := by
  by_cases hr : r.card ≤ 1
  · by_cases h0 : r.card=0
    · have he : r=∅ := Finset.card_eq_zero.mp h0
      subst r
      simp [stateFactor,stateOption_empty,centeredFactor,stateCoefficient_empty,mul_ite,stateIndicator_empty]
    · have h1 : r.card=1 := by omega
      obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h1
      simp only [stateCoefficient_singleton,sub_mul,ite_mul,zero_mul,one_mul,Finset.sum_sub_distrib,
        Finset.sum_ite_eq',Finset.mem_univ,if_true,stateIndicator_empty,stateIndicator_singleton,mul_one]
      simp [stateFactor,stateOption_singleton,centeredFactor,centeredResidue]
  · simp [stateFactor,stateCoefficient,hr]

lemma mean_stateFactor_mul (h : ι→α) (hi : Function.Injective h) (hq : 1<Fintype.card α)
    (r s : Finset ι) :
    (∑ x, stateFactor h r x*stateFactor h s x)/(Fintype.card α : ℝ)=fullKernelOne (Fintype.card α : ℝ) r s := by
  by_cases hr : r.card ≤ 1 <;> by_cases hs : s.card ≤ 1
  · simp only [stateFactor,if_pos hr,if_pos hs,fullKernelOne,extendStateKernel,if_pos (And.intro hr hs)]
    exact mean_centeredFactor_mul h hi hq _ _
  all_goals simp [stateFactor,hr,hs,fullKernelOne,extendStateKernel]

lemma conditionalMean_stateFactor_mul (h : ι→α) (hi : Function.Injective h) (hq : 1<Fintype.card α)
    (m : ι) (r s : Finset ι) :
    conditionalMean (fun x => stateFactor h r x*stateFactor h s x) (h m)=fullKernelTwo (Fintype.card α : ℝ) m r s := by
  by_cases hr : r.card ≤ 1 <;> by_cases hs : s.card ≤ 1
  · simp only [stateFactor,if_pos hr,if_pos hs,fullKernelTwo,extendStateKernel,if_pos (And.intro hr hs)]
    exact conditionalMean_centeredFactor_mul h hi hq _ _ _
  all_goals simp [stateFactor,hr,hs,fullKernelTwo,extendStateKernel,conditionalMean]

end
end MaynardDevelopment
end

/- MatrixCoefficients -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Finset ℕ}

def matrixCoefficient (y : (↥P→Finset ι)→ℝ) (d : ↥P→Finset ι) : ℝ :=
  ∑ r : ↥P→Finset ι, y r*∏ p : ↥P, stateCoefficient (p.val : ℝ) (r p) (d p)

set_option maxHeartbeats 2000000 in
lemma matrixCoefficient_bound (y : (↥P→Finset ι)→ℝ) (hy : ∀ r, |y r|≤1) (d : ↥P→Finset ι) :
    |matrixCoefficient y d|≤harmonicEuler P^(Fintype.card ι) := by
  unfold matrixCoefficient
  calc
    _ ≤ ∑ r : ↥P→Finset ι, |y r*∏ p : ↥P, stateCoefficient (p.val : ℝ) (r p) (d p)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : ↥P→Finset ι, ∏ p : ↥P, |stateCoefficient (p.val : ℝ) (r p) (d p)| := by
      apply Finset.sum_le_sum
      intro r hr
      rw [abs_mul,Finset.abs_prod]
      exact mul_le_of_le_one_left (Finset.prod_nonneg (fun p _ => abs_nonneg _)) (hy r)
    _ = ∏ p : ↥P, ∑ r : Finset ι, |stateCoefficient (p.val : ℝ) r (d p)| :=
      (Fintype.prod_sum (fun p : ↥P => fun r : Finset ι => |stateCoefficient (p.val : ℝ) r (d p)|)).symm
    _ ≤ ∏ p : ↥P, (1+(p.val : ℝ)⁻¹)^(Fintype.card ι) := by
      apply Finset.prod_le_prod
      · intro p hp; positivity
      · intro p hp; exact stateCoefficient_abs_sum (Nat.cast_nonneg _) _
    _ = _ := by
      rw [Finset.prod_pow]
      congr 1
      simp only [harmonicEuler,Finset.univ_eq_attach]
      exact Finset.prod_attach P (fun p : ℕ => 1+(p : ℝ)⁻¹)

lemma matrixCoefficient_support (y : (↥P→Finset ι)→ℝ) (d : ↥P→Finset ι)
    (h : matrixCoefficient y d≠0) :
    ∃ r : ↥P→Finset ι, y r≠0 ∧ ∀ p : ↥P, (r p).card≤1 ∧ d p⊆r p := by
  classical
  have he : ∃ r : ↥P→Finset ι, y r*(∏ p : ↥P, stateCoefficient (p.val : ℝ) (r p) (d p))≠0 := by
    by_contra! hh
    exact h (Finset.sum_eq_zero (fun r hr => hh r))
  obtain ⟨r,hr⟩ := he
  refine ⟨r,(mul_ne_zero_iff.mp hr).1,?_⟩
  intro p
  have hp : stateCoefficient (p.val : ℝ) (r p) (d p)≠0 :=
    (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hr).2) p (Finset.mem_univ p)
  exact stateCoefficient_support hp

lemma matrixCoefficient_expansion (y : (↥P→Finset ι)→ℝ) (f : ↥P→Finset ι→ℝ) :
    (∑ d : ↥P→Finset ι, matrixCoefficient y d*(∏ p : ↥P, f p (d p))) =
      ∑ r : ↥P→Finset ι, y r*(∏ p : ↥P, ∑ d : Finset ι, stateCoefficient (p.val : ℝ) (r p) d*f p d) := by
  unfold matrixCoefficient
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp_rw [mul_assoc, ← Finset.prod_mul_distrib]
  rw [← Finset.mul_sum]
  congr 1
  convert (Fintype.prod_sum (fun p : ↥P => fun d : Finset ι => stateCoefficient (p.val : ℝ) (r p) d*f p d)).symm using 1

end
end MaynardDevelopment
end

/- ProductGram -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {π σ : Type*} [Fintype π] [DecidableEq π] [Fintype σ]
variable {α : π→Type*} [∀ p, Fintype (α p)]

def productPolynomial (f : ∀ p, σ→α p→ℝ) (y : (π→σ)→ℝ) (x : ∀ p, α p) : ℝ :=
  ∑ r : π→σ, y r*∏ p, f p (r p) (x p)

lemma productPolynomial_sq (μ : ∀ p, α p→ℝ) (f : ∀ p, σ→α p→ℝ)
    (y : (π→σ)→ℝ) (x : ∀ p, α p) :
    (∏ p, μ p (x p))*productPolynomial f y x^2 =
      ∑ r : π→σ, ∑ s : π→σ, y r*y s*(∏ p, μ p (x p)*f p (r p) (x p)*f p (s p) (x p)) := by
  unfold productPolynomial
  rw [pow_two,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro r hr
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro s hs
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  ring

lemma productPolynomial_gram (μ : ∀ p, α p→ℝ) (f : ∀ p, σ→α p→ℝ) (y : (π→σ)→ℝ) :
    (∑ x : ∀ p, α p, (∏ p, μ p (x p))*productPolynomial f y x^2)=
      kernelQuadratic (fun p r s => ∑ x : α p, μ p x*f p r x*f p s x) y := by
  simp only [productPolynomial_sq,kernelQuadratic]
  rw [Finset.sum_comm]
  apply Finset.sum_congr (by ext; simp)
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr (by ext; simp)
  intro s hs
  rw [← Finset.mul_sum]
  congr 1
  exact (Fintype.prod_sum (fun p : π => fun x : α p => μ p x*f p (r p) x*f p (s p) x)).symm

end
end MaynardDevelopment
end

/- IndicatorKernels -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

lemma stateIndicator_eq_ite (h : ι→α) (s : Finset ι) (x : α) :
    stateIndicator h s x=if ∀ i∈s, x=h i then 1 else 0 := by
  by_cases hh : ∀ i∈s, x=h i
  · rw [if_pos hh]
    apply Finset.prod_eq_one
    intro i hi
    rw [if_pos (hh i hi)]
  · rw [if_neg hh]
    push_neg at hh
    obtain ⟨i,hi,hx⟩ := hh
    exact Finset.prod_eq_zero hi (if_neg hx)

lemma stateIndicator_union (h : ι→α) (s t : Finset ι) (x : α) :
    stateIndicator h s x*stateIndicator h t x=stateIndicator h (s∪t) x := by
  simp only [stateIndicator_eq_ite]
  have hh : (∀ i∈s∪t, x=h i) ↔ (∀ i∈s, x=h i) ∧ (∀ i∈t, x=h i) := by simp [Finset.mem_union,or_imp,forall_and]
  split_ifs <;> norm_num <;> tauto

lemma stateIndicator_zero_of_large (h : ι→α) (hi : Function.Injective h) (s : Finset ι)
    (hs : ¬s.card≤1) (x : α) : stateIndicator h s x=0 := by
  rw [stateIndicator_eq_ite,if_neg]
  intro hh
  apply hs
  apply Finset.card_le_one.mpr
  intro i hi' j hj'
  apply hi
  exact (hh i hi').symm.trans (hh j hj')

def indicatorKernelOne (q : ℝ) (r s : Finset ι) : ℝ :=
  if (r∪s).card≤1 then (q⁻¹)^(r∪s).card else 0

def indicatorKernelTwo (q : ℝ) (m : ι) (r s : Finset ι) : ℝ :=
  if (r∪s).card≤1 ∧ m∉r∪s then ((q-1)⁻¹)^(r∪s).card else 0

lemma mean_stateIndicator (h : ι→α) (hi : Function.Injective h) (hq : 0<Fintype.card α)
    (s : Finset ι) :
    (∑ x, stateIndicator h s x)/(Fintype.card α : ℝ)=
      if s.card≤1 then ((Fintype.card α : ℝ)⁻¹)^s.card else 0 := by
  by_cases hs : s.card≤1
  · rw [if_pos hs]
    by_cases h0 : s.card=0
    · have he : s=∅ := Finset.card_eq_zero.mp h0
      simp [he,stateIndicator_empty,(show (Fintype.card α : ℝ)≠0 by exact_mod_cast hq.ne')]
    · have h1 : s.card=1 := by omega
      obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h1
      simp [stateIndicator_singleton]
  · rw [if_neg hs]
    simp [stateIndicator_zero_of_large h hi s hs]

lemma mean_stateIndicator_mul (h : ι→α) (hi : Function.Injective h) (hq : 0<Fintype.card α)
    (r s : Finset ι) :
    (∑ x, stateIndicator h r x*stateIndicator h s x)/(Fintype.card α : ℝ)=
      indicatorKernelOne (Fintype.card α : ℝ) r s := by
  simp only [stateIndicator_union]
  exact mean_stateIndicator h hi hq _

lemma conditionalMean_stateIndicator (h : ι→α) (hi : Function.Injective h) (hq : 1<Fintype.card α)
    (m : ι) (s : Finset ι) :
    conditionalMean (stateIndicator h s) (h m)=
      if s.card≤1 ∧ m∉s then (((Fintype.card α : ℝ)-1)⁻¹)^s.card else 0 := by
  by_cases hs : s.card≤1
  · by_cases h0 : s.card=0
    · have he : s=∅ := Finset.card_eq_zero.mp h0
      rw [he,conditionalMean_eq]
      have hq1 : (Fintype.card α : ℝ)-1≠0 := by exact_mod_cast (by omega : (Fintype.card α : ℤ)-1≠0)
      simp [stateIndicator_empty,hq1]
    · have h1 : s.card=1 := by omega
      obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h1
      rw [conditionalMean_eq]
      simp only [stateIndicator_singleton,Finset.sum_ite_eq',Finset.mem_univ,if_true,
        Finset.card_singleton,le_refl,Finset.mem_singleton,and_true,true_and,hi.eq_iff]
      by_cases hm : m=i <;> simp [hm]
  · simp [hs,conditionalMean,stateIndicator_zero_of_large h hi s hs]

lemma conditionalMean_stateIndicator_mul (h : ι→α) (hi : Function.Injective h) (hq : 1<Fintype.card α)
    (m : ι) (r s : Finset ι) :
    conditionalMean (fun x => stateIndicator h r x*stateIndicator h s x) (h m)=
      indicatorKernelTwo (Fintype.card α : ℝ) m r s := by
  simp only [stateIndicator_union]
  exact conditionalMean_stateIndicator h hi hq _ _

end
end MaynardDevelopment
end

/- CoefficientGrams -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Finset ℕ}
variable {α : ↥P→Type*} [∀ p, Fintype (α p)] [∀ p, DecidableEq (α p)]

lemma coefficient_polynomial_eq (h : ∀ p, ι→α p) (hc : ∀ p, Fintype.card (α p)=p.val)
    (y : (↥P→Finset ι)→ℝ) (x : ∀ p, α p) :
    productPolynomial (fun p => stateIndicator (h p)) (matrixCoefficient y) x=
      productPolynomial (fun p => stateFactor (h p)) y x := by
  unfold productPolynomial
  rw [matrixCoefficient_expansion y (fun p d => stateIndicator (h p) d (x p))]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [← hc p]
  exact (stateFactor_expansion (h p) (r p) (x p)).symm

lemma scalar_uniform_average {β : Type*} [Fintype β] (q : ℝ) (f g : β→ℝ) :
    (∑ x, q⁻¹*f x*g x)=(∑ x, f x*g x)/q := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intros
  ring

lemma scalar_avoid_average {β : Type*} [Fintype β] [DecidableEq β] (a : β) (f g : β→ℝ) :
    (∑ x, (if x=a then 0 else ((Fintype.card β : ℝ)-1)⁻¹)*f x*g x)=
      conditionalMean (fun x => f x*g x) a := by
  have he (x : β) : (if x=a then 0 else ((Fintype.card β : ℝ)-1)⁻¹)*f x*g x =
      if x≠a then (f x*g x)/((Fintype.card β : ℝ)-1) else 0 := by
    by_cases hx : x=a <;> simp [hx] <;> ring
  simp only [he,← Finset.sum_filter]
  rw [Finset.filter_ne',← Finset.sum_div]
  rfl

lemma coefficient_gram_one (h : ∀ p, ι→α p) (hi : ∀ p, Function.Injective (h p))
    (hc : ∀ p, Fintype.card (α p)=p.val) (hq : ∀ p : ↥P, 1<p.val) (y : (↥P→Finset ι)→ℝ) :
    kernelQuadratic (fun p : ↥P => fullKernelOne (p.val : ℝ)) y=
      kernelQuadratic (fun p : ↥P => indicatorKernelOne (p.val : ℝ)) (matrixCoefficient y) := by
  let μ (p : ↥P) (_x : α p) : ℝ := (p.val : ℝ)⁻¹
  have hk : (fun p r s => ∑ x : α p, μ p x*stateFactor (h p) r x*stateFactor (h p) s x)=
      (fun p : ↥P => fullKernelOne (p.val : ℝ)) := by
    funext p r s
    rw [scalar_uniform_average,← hc p]
    exact mean_stateFactor_mul (h p) (hi p) (by rw [hc]; exact hq p) r s
  have hl : (fun p r s => ∑ x : α p, μ p x*stateIndicator (h p) r x*stateIndicator (h p) s x)=
      (fun p : ↥P => indicatorKernelOne (p.val : ℝ)) := by
    funext p r s
    rw [scalar_uniform_average,← hc p]
    exact mean_stateIndicator_mul (h p) (hi p) (by rw [hc]; have hh := hq p; omega) r s
  have hfirst := productPolynomial_gram μ (fun p => stateFactor (h p)) y
  have hlast := productPolynomial_gram μ (fun p => stateIndicator (h p)) (matrixCoefficient y)
  rw [hk] at hfirst
  rw [hl] at hlast
  rw [← hfirst,← hlast]
  apply Finset.sum_congr rfl
  intro x hx
  rw [coefficient_polynomial_eq h hc y x]

lemma coefficient_gram_two (h : ∀ p, ι→α p) (hi : ∀ p, Function.Injective (h p))
    (hc : ∀ p, Fintype.card (α p)=p.val) (hq : ∀ p : ↥P, 1<p.val) (y : (↥P→Finset ι)→ℝ) (m : ι) :
    kernelQuadratic (fun p : ↥P => fullKernelTwo (p.val : ℝ) m) y=
      kernelQuadratic (fun p : ↥P => indicatorKernelTwo (p.val : ℝ) m) (matrixCoefficient y) := by
  let μ (p : ↥P) (x : α p) : ℝ := if x=h p m then 0 else ((Fintype.card (α p) : ℝ)-1)⁻¹
  have hk : (fun p r s => ∑ x : α p, μ p x*stateFactor (h p) r x*stateFactor (h p) s x)=
      (fun p : ↥P => fullKernelTwo (p.val : ℝ) m) := by
    funext p r s
    rw [scalar_avoid_average,← hc p]
    exact conditionalMean_stateFactor_mul (h p) (hi p) (by rw [hc]; exact hq p) m r s
  have hl : (fun p r s => ∑ x : α p, μ p x*stateIndicator (h p) r x*stateIndicator (h p) s x)=
      (fun p : ↥P => indicatorKernelTwo (p.val : ℝ) m) := by
    funext p r s
    rw [scalar_avoid_average,← hc p]
    exact conditionalMean_stateIndicator_mul (h p) (hi p) (by rw [hc]; exact hq p) m r s
  have hfirst := productPolynomial_gram μ (fun p => stateFactor (h p)) y
  have hlast := productPolynomial_gram μ (fun p => stateIndicator (h p)) (matrixCoefficient y)
  rw [hk] at hfirst
  rw [hl] at hlast
  rw [← hfirst,← hlast]
  apply Finset.sum_congr rfl
  intro x hx
  rw [coefficient_polynomial_eq h hc y x]

end
end MaynardDevelopment
end

/- MatrixProducts -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Finset ℕ}

def matrixProduct (r : ↥P→Finset ι) : ℕ := ∏ p : ↥P, p.val^(r p).card

lemma matrixProduct_pos (hP : ∀ p∈P, 0 < p) (r : ↥P→Finset ι) : 0 < matrixProduct r := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (hP p.val p.property) _

lemma matrixProduct_mono (hP : ∀ p∈P, 1 ≤ p) (r s : ↥P→Finset ι) (hrs : ∀ p, r p⊆s p) :
    matrixProduct r ≤ matrixProduct s := by
  apply Finset.prod_le_prod'
  intro p hp
  exact Nat.pow_le_pow_right (hP p.val p.property) (Finset.card_le_card (hrs p))

lemma primeSetProduct_matrixCoords (r : ↥P→Finset ι) (i : ι) :
    primeSetProduct (matrixCoords r i).val=∏ p : ↥P, if i∈r p then p.val else 1 := by
  unfold primeSetProduct matrixCoords
  rw [Finset.prod_filter]
  rw [Finset.prod_subtype P (fun p => Iff.rfl)
    (fun p => if ∃ hp : p∈P, i∈r ⟨p,hp⟩ then p else 1)]
  apply Finset.prod_congr rfl
  intro p hp
  simp

lemma matrixProduct_eq_coords (r : ↥P→Finset ι) :
    matrixProduct r=∏ i, primeSetProduct (matrixCoords r i).val := by
  simp only [primeSetProduct_matrixCoords]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← Finset.prod_filter]
  have he : Finset.univ.filter (fun i => i∈r p)=r p := by ext i; simp
  rw [he,Finset.prod_const]

lemma matrixProducts_injective (hP : ∀ p∈P, Nat.Prime p) :
    Function.Injective (fun r : ↥P→Finset ι => fun i => primeSetProduct (matrixCoords r i).val) := by
  intro r s h
  have he : matrixCoords r=matrixCoords s := by
    funext i
    apply Subtype.ext
    exact primeSetProduct_injOn P hP (matrixCoords r i).property (matrixCoords s i).property (congrFun h i)
  have hh := congrArg coordsMatrix he
  simpa only [coordsMatrix_matrixCoords] using hh

lemma matrixCoords_product_dvd (r : ↥P→Finset ι) (i : ι) :
    primeSetProduct (matrixCoords r i).val∣matrixProduct r := by
  rw [matrixProduct_eq_coords]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

lemma matrix_time_sum (hP : ∀ p∈P, Nat.Prime p) (R : ℕ) (r : ↥P→Finset ι) :
    (∑ i, subsetTime R (matrixCoords r i))=Real.log (matrixProduct r)/Real.log R := by
  simp only [subsetTime, ← Finset.sum_div]
  congr 1
  rw [matrixProduct_eq_coords,Nat.cast_prod,Real.log_prod]
  intro i hi
  have hh := primeSetProduct_pos (matrixCoords r i).val
    (fun p hp => hP p ((Finset.mem_powerset.mp (matrixCoords r i).property) hp))
  exact_mod_cast hh.ne'

end
end MaynardDevelopment
end

/- SieveSupport -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

def sieveLambda (P : Finset ℕ) (M R : ℕ) : (↥P→Finset (Fin (sieveDimension M)))→ℝ :=
  matrixCoefficient (sieveTest P M R)

lemma sieveLambda_bound (P : Finset ℕ) (M R : ℕ) (d : ↥P→Finset (Fin (sieveDimension M))) :
    |sieveLambda P M R d| ≤ harmonicEuler P^(sieveDimension M) := by
  simpa only [Fintype.card_fin] using matrixCoefficient_bound (sieveTest P M R)
    (fun r => (sieveTest_bound P M R r).2) d

lemma sieveTest_product_support (P : Finset ℕ) (M R : ℕ) (hP : ∀ p∈P, Nat.Prime p) (hR : 1<R)
    (r : ↥P→Finset (Fin (sieveDimension M))) (hr : sieveTest P M R r≠0) :
    matrixProduct r ≤ R^(sieveCutoff M) := by
  have hcut : (∑ i, subsetTime R (matrixCoords r i)) ≤ sieveCutoff M := by
    by_contra h
    simp [sieveTest,discreteTensor,h] at hr
  rw [matrix_time_sum hP] at hcut
  have hlog : 0<Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hpos := matrixProduct_pos (fun p hp => (hP p hp).pos) r
  have hRpow : 0<R^(sieveCutoff M) := pow_pos (by omega) _
  have hh := (div_le_iff₀ hlog).mp hcut
  have he : Real.log (R^(sieveCutoff M) : ℕ)=(sieveCutoff M : ℝ)*Real.log R := by rw [Nat.cast_pow,Real.log_pow]
  rw [← he] at hh
  exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast hpos) (by exact_mod_cast hRpow)).mp hh

lemma sieveLambda_product_support (P : Finset ℕ) (M R : ℕ) (hP : ∀ p∈P, Nat.Prime p) (hR : 1<R)
    (d : ↥P→Finset (Fin (sieveDimension M))) (hd : sieveLambda P M R d≠0) :
    matrixProduct d ≤ R^(sieveCutoff M) := by
  obtain ⟨r,hr,hs⟩ := matrixCoefficient_support (sieveTest P M R) d hd
  exact (matrixProduct_mono (fun p hp => (hP p hp).one_le) d r (fun p => (hs p).2)).trans
    (sieveTest_product_support P M R hP hR r hr)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Finset ℕ}

def matrixModulus (r s : ↥P→Finset ι) : ℕ :=
  ∏ p : ↥P, if (r p).Nonempty ∨ (s p).Nonempty then p.val else 1

lemma matrixModulus_pos (hP : ∀ p∈P, 0<p) (r s : ↥P→Finset ι) : 0 < matrixModulus r s := by
  apply Finset.prod_pos
  intro p hp
  split_ifs
  · exact hP p.val p.property
  · exact zero_lt_one

lemma matrixModulus_le_product (hP : ∀ p∈P, 1≤p) (r s : ↥P→Finset ι) :
    matrixModulus r s ≤ matrixProduct r*matrixProduct s := by
  unfold matrixModulus matrixProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro p hp
  rw [← pow_add]
  split_ifs with h
  · have hc : (r p).card+(s p).card≠0 := by
      rcases h with h | h
      · have hh := Finset.card_pos.mpr h; omega
      · have hh := Finset.card_pos.mpr h; omega
    exact Nat.le_self_pow hc p.val
  · exact Nat.one_le_pow _ _ (hP p.val p.property)

lemma coords_product_dvd_matrixModulus_left (r s : ↥P→Finset ι) (i : ι) :
    primeSetProduct (matrixCoords r i).val ∣ matrixModulus r s := by
  rw [primeSetProduct_matrixCoords]
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  by_cases hi : i∈r p
  · rw [if_pos hi,if_pos (Or.inl ⟨i,hi⟩)]
  · rw [if_neg hi]
    exact one_dvd _

lemma matrixModulus_comm (r s : ↥P→Finset ι) : matrixModulus r s=matrixModulus s r := by
  unfold matrixModulus
  simp only [or_comm]

lemma coords_product_dvd_matrixModulus_right (r s : ↥P→Finset ι) (i : ι) :
    primeSetProduct (matrixCoords s i).val ∣ matrixModulus r s := by
  rw [matrixModulus_comm]
  exact coords_product_dvd_matrixModulus_left s r i

lemma matrixProduct_card_bound (hP : ∀ p∈P, Nat.Prime p) (S : Finset (↥P→Finset ι)) (Y : ℕ)
    (hS : ∀ r∈S, matrixProduct r≤Y) :
    S.card ≤ ∑ n∈Finset.Icc 1 Y, n.divisors.card^(Fintype.card ι) := by
  classical
  let T : Finset (Σ n : ℕ, ι→ℕ) := (Finset.Icc 1 Y).sigma (fun n => Fintype.piFinset (fun _ : ι => n.divisors))
  let f (r : ↥P→Finset ι) : Σ n : ℕ, ι→ℕ := ⟨matrixProduct r,fun i => primeSetProduct (matrixCoords r i).val⟩
  have hcard : S.card≤T.card := by
    apply Finset.card_le_card_of_injOn f
    · intro r hr
      change f r∈T
      apply Finset.mem_sigma.mpr
      have hp := matrixProduct_pos (fun p hp => (hP p hp).pos) r
      refine ⟨Finset.mem_Icc.mpr ⟨hp,hS r hr⟩,Fintype.mem_piFinset.mpr ?_⟩
      intro i
      exact Nat.mem_divisors.mpr ⟨matrixCoords_product_dvd r i,hp.ne'⟩
    · intro r hr s hs he
      apply matrixProducts_injective hP
      exact congrArg (fun z : Σ n : ℕ, ι→ℕ => z.2) he
  have he : T.card=∑ n∈Finset.Icc 1 Y, n.divisors.card^(Fintype.card ι) := by
    simp [T,Finset.card_sigma,Fintype.card_piFinset]
  exact hcard.trans_eq he

lemma sum_divisor_pow_le (k Y : ℕ) :
    (∑ n∈Finset.Icc 1 Y, (n.divisors.card : ℝ)^k) ≤ (Y : ℝ)*(1+Real.log Y)^(2^k-1) := by
  have hk : 2^k-1+1=2^k := Nat.sub_add_cancel (Nat.one_le_pow k 2 (by decide))
  calc
    _ ≤ ∑ n∈Finset.Icc 1 Y, ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^(2^k)) n := by
      apply Finset.sum_le_sum
      intro n hn
      exact divisor_pow_le_zeta k n (by have hh := (Finset.mem_Icc.mp hn).1; omega)
    _ ≤ (Y : ℝ)*(harmonic Y : ℝ)^(2^k-1) := by simpa only [hk] using sum_zeta_pow_le (2^k-1) Y
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (harmonic_real_nonneg _) (harmonic_le_one_add_log Y) _) (Nat.cast_nonneg _)

lemma matrixProduct_card_log_bound (hP : ∀ p∈P, Nat.Prime p) (S : Finset (↥P→Finset ι)) (Y : ℕ)
    (hS : ∀ r∈S, matrixProduct r≤Y) :
    (S.card : ℝ) ≤ (Y : ℝ)*(1+Real.log Y)^(2^(Fintype.card ι)-1) := by
  have hh : (S.card : ℝ) ≤ ∑ n∈Finset.Icc 1 Y, (n.divisors.card : ℝ)^(Fintype.card ι) := by
    exact_mod_cast matrixProduct_card_bound hP S Y hS
  exact hh.trans (sum_divisor_pow_le _ _)

end
end MaynardDevelopment
end

/- IndicatorProducts -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma totient_prod_coprime {β : Type*} [DecidableEq β] (s : Finset β) (f : β→ℕ)
    (hf : ∀ a∈s, ∀ b∈s, a≠b → (f a).Coprime (f b)) :
    (∏ a∈s, f a).totient=∏ a∈s, (f a).totient := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Nat.totient_mul]
    · rw [ih (by intro b hb c hc hbc; exact hf b (by simp [hb]) c (by simp [hc]) hbc)]
    · apply Nat.Coprime.prod_right
      intro b hb
      exact hf a (by simp) b (by simp [hb]) (by intro h; subst b; contradiction)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Finset ℕ}

def matrixCompatible (r s : ↥P→Finset ι) : Prop := ∀ p, (r p∪s p).card≤1
def matrixAvoids (m : ι) (r s : ↥P→Finset ι) : Prop := ∀ p, m∉r p∪s p

def matrixLocalModulus (r s : ↥P→Finset ι) (p : ↥P) : ℕ :=
  if (r p).Nonempty ∨ (s p).Nonempty then p.val else 1

lemma matrixLocalModulus_coprime (hP : ∀ p∈P, Nat.Prime p) (r s : ↥P→Finset ι)
    (p q : ↥P) (hpq : p≠q) : (matrixLocalModulus r s p).Coprime (matrixLocalModulus r s q) := by
  unfold matrixLocalModulus
  split_ifs
  · exact (Nat.coprime_primes (hP _ p.property) (hP _ q.property)).mpr (by intro h; exact hpq (Subtype.ext h))
  · exact Nat.coprime_one_right _
  · exact Nat.coprime_one_left _
  · exact Nat.coprime_one_left _

lemma matrixModulus_totient (hP : ∀ p∈P, Nat.Prime p) (r s : ↥P→Finset ι) :
    (matrixModulus r s).totient=∏ p : ↥P, if (r p).Nonempty ∨ (s p).Nonempty then p.val-1 else 1 := by
  change (∏ p : ↥P, matrixLocalModulus r s p).totient=_
  rw [totient_prod_coprime _ _ (by intro a ha b hb hab; exact matrixLocalModulus_coprime hP r s a b hab)]
  apply Finset.prod_congr rfl
  intro p hp
  unfold matrixLocalModulus
  split_ifs <;> simp [Nat.totient_prime (hP _ p.property)]

lemma pow_card_small {β : Type*} [DecidableEq β] (t : Finset β) (ht : t.card≤1) (x : ℝ) :
    x^t.card=if t.Nonempty then x else 1 := by
  by_cases h : t.Nonempty
  · have hh : t.card=1 := by have := Finset.card_pos.mpr h; omega
    simp [h,hh]
  · have hh : t.card=0 := by simpa using h
    simp [hh,h]

lemma prod_indicatorKernelOne (r s : ↥P→Finset ι) :
    (∏ p : ↥P, indicatorKernelOne (p.val : ℝ) (r p) (s p))=
      if matrixCompatible r s then (matrixModulus r s : ℝ)⁻¹ else 0 := by
  by_cases h : matrixCompatible r s
  · rw [if_pos h]
    unfold matrixModulus
    rw [Nat.cast_prod,← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [indicatorKernelOne,if_pos (h p),pow_card_small _ (h p)]
    simp only [Finset.union_nonempty]
    split_ifs <;> simp
  · rw [if_neg h]
    obtain ⟨p,hp⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ p) (by simp [indicatorKernelOne,hp])

lemma prod_indicatorKernelTwo (hP : ∀ p∈P, Nat.Prime p) (m : ι) (r s : ↥P→Finset ι) :
    (∏ p : ↥P, indicatorKernelTwo (p.val : ℝ) m (r p) (s p))=
      if matrixCompatible r s ∧ matrixAvoids m r s then ((matrixModulus r s).totient : ℝ)⁻¹ else 0 := by
  by_cases h : matrixCompatible r s ∧ matrixAvoids m r s
  · rw [if_pos h,matrixModulus_totient hP,Nat.cast_prod,← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [indicatorKernelTwo,if_pos ⟨h.1 p,h.2 p⟩,pow_card_small _ (h.1 p)]
    simp only [Finset.union_nonempty]
    split_ifs <;> simp [Nat.cast_sub (hP _ p.property).one_le]
  · rw [if_neg h]
    have hn : ¬∀ p, (r p∪s p).card≤1 ∧ m∉r p∪s p := by
      simpa only [forall_and,matrixCompatible,matrixAvoids] using h
    obtain ⟨p,hp⟩ := not_forall.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ p) (by rw [indicatorKernelTwo,if_neg hp])

end
end MaynardDevelopment
end

/- MatrixCRT -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma modEq_finset_prod_iff {β : Type*} [DecidableEq β] (s : Finset β) (f : β→ℕ)
    (hf : ∀ a∈s, ∀ b∈s, a≠b → (f a).Coprime (f b)) (a b : ℕ) :
    Nat.ModEq (∏ i∈s, f i) a b ↔ ∀ i∈s, Nat.ModEq (f i) a b := by
  induction s using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,← Nat.modEq_and_modEq_iff_modEq_mul]
    · rw [ih (by intro j hj k hk hjk; exact hf j (by simp [hj]) k (by simp [hk]) hjk)]
      simp
    · apply Nat.Coprime.prod_right
      intro j hj
      exact hf i (by simp) j (by simp [hj]) (by intro h; subst j; contradiction)

lemma exists_residue_product {β : Type*} [DecidableEq β] (s : Finset β) (f a : β→ℕ)
    (h0 : ∀ i∈s, f i≠0) (hf : ∀ i∈s, ∀ j∈s, i≠j → (f i).Coprime (f j)) :
    ∃ b : ℕ, ∀ n : ℕ, (∀ i∈s, Nat.ModEq (f i) n (a i)) ↔ Nat.ModEq (∏ i∈s, f i) n b := by
  obtain ⟨b,hb⟩ := Nat.chineseRemainderOfFinset a f s h0 hf
  refine ⟨b,fun n => ?_⟩
  rw [modEq_finset_prod_iff s f hf]
  constructor
  · intro hn i hi; exact (hn i hi).trans (hb i hi).symm
  · intro hn i hi; exact (hn i hi).trans (hb i hi)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Finset ℕ}

def matrixCondition (h : ∀ p : ↥P, ι→ZMod p.val) (r : ↥P→Finset ι) (n : ℕ) : Prop :=
  ∀ p, ∀ i∈r p, (n : ZMod p.val)=h p i

lemma matrixCondition_union (h : ∀ p : ↥P, ι→ZMod p.val) (r s : ↥P→Finset ι) (n : ℕ) :
    matrixCondition h r n ∧ matrixCondition h s n ↔ matrixCondition h (fun p => r p∪s p) n := by
  simp only [matrixCondition,Finset.mem_union,or_imp,forall_and]

lemma matrixCondition_compatible (h : ∀ p : ↥P, ι→ZMod p.val)
    (hi : ∀ p, Function.Injective (h p)) (r s : ↥P→Finset ι) (n : ℕ)
    (hn : matrixCondition h r n ∧ matrixCondition h s n) : matrixCompatible r s := by
  have hh := (matrixCondition_union h r s n).mp hn
  intro p
  apply Finset.card_le_one.mpr
  intro i hi' j hj
  exact hi p ((hh p i hi').symm.trans (hh p j hj))

lemma matrixCondition_residue (hP : ∀ p∈P, Nat.Prime p)
    (h : ∀ p : ↥P, ι→ZMod p.val) (r s : ↥P→Finset ι) (hc : matrixCompatible r s) :
    ∃ b : ℕ, ∀ n, matrixCondition h r n ∧ matrixCondition h s n ↔ Nat.ModEq (matrixModulus r s) n b := by
  letI (p : ↥P) : NeZero p.val := ⟨(hP _ p.property).ne_zero⟩
  let a (p : ↥P) : ℕ := if he : (r p∪s p).Nonempty then (h p (Classical.choose he)).val else 0
  have hloc (p : ↥P) (n : ℕ) :
      (∀ i∈r p∪s p, (n : ZMod p.val)=h p i) ↔ Nat.ModEq (matrixLocalModulus r s p) n (a p) := by
    by_cases he : (r p∪s p).Nonempty
    · have he' : (r p).Nonempty ∨ (s p).Nonempty := Finset.union_nonempty.mp he
      simp only [matrixLocalModulus,if_pos he',a,dif_pos he]
      rw [← ZMod.natCast_eq_natCast_iff,ZMod.natCast_zmod_val]
      constructor
      · intro hn; exact hn _ (Classical.choose_spec he)
      · intro hn i hi
        have hh := Finset.card_le_one.mp (hc p) i hi _ (Classical.choose_spec he)
        simpa only [hh] using hn
    · have he' : ¬((r p).Nonempty ∨ (s p).Nonempty) := by simpa only [Finset.union_nonempty] using he
      have hz : r p∪s p=∅ := Finset.not_nonempty_iff_eq_empty.mp he
      simp [hz,matrixLocalModulus,he',Nat.modEq_one]
  obtain ⟨b,hb⟩ := exists_residue_product Finset.univ (matrixLocalModulus r s) a
    (by intro p hp; unfold matrixLocalModulus; split_ifs; exact (hP _ p.property).ne_zero; decide)
    (by intro p hp q hq hpq; exact matrixLocalModulus_coprime hP r s p q hpq)
  refine ⟨b,fun n => ?_⟩
  rw [matrixCondition_union]
  change (∀ p, ∀ i∈r p∪s p, (n : ZMod p.val)=h p i) ↔ _
  simp only [hloc]
  simpa only [Finset.mem_univ,forall_true_left] using hb n

lemma matrixModulus_coprime (hP : ∀ p∈P, Nat.Prime p) (W : ℕ)
    (hW : ∀ p∈P, W.Coprime p) (r s : ↥P→Finset ι) : W.Coprime (matrixModulus r s) := by
  apply Nat.Coprime.prod_right
  intro p hp
  split_ifs
  · exact hW _ p.property
  · exact Nat.coprime_one_right _

lemma matrixCondition_progression (hP : ∀ p∈P, Nat.Prime p) (W a : ℕ)
    (hW : ∀ p∈P, W.Coprime p) (h : ∀ p : ↥P, ι→ZMod p.val)
    (r s : ↥P→Finset ι) (hc : matrixCompatible r s) :
    ∃ b : ℕ, ∀ n, (Nat.ModEq W n a ∧ matrixCondition h r n ∧ matrixCondition h s n) ↔
      Nat.ModEq (W*matrixModulus r s) n b := by
  obtain ⟨c,hc'⟩ := matrixCondition_residue hP h r s hc
  have hco := matrixModulus_coprime hP W hW r s
  obtain ⟨b,hb⟩ := Nat.chineseRemainder hco a c
  refine ⟨b,fun n => ?_⟩
  rw [hc' n,← Nat.modEq_and_modEq_iff_modEq_mul hco]
  constructor
  · rintro ⟨h1,h2⟩; exact ⟨h1.trans hb.1.symm,h2.trans hb.2.symm⟩
  · rintro ⟨h1,h2⟩; exact ⟨h1.trans hb.1,h2.trans hb.2⟩

end
end MaynardDevelopment
end

/- ResidueCounting -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma card_residue_interval_lower {q : ℕ} [NeZero q] (a : ZMod q) (X : ℕ) :
    X/q ≤ ((Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q)=a)).card := by
  let b : ℕ := if a.val=0 then q else a.val
  have hb0 : 0<b := by dsimp [b]; split_ifs with h; exact NeZero.pos q; omega
  have hbq : b≤q := by dsimp [b]; split_ifs; exact le_rfl; exact (ZMod.val_lt a).le
  have hba : (b : ZMod q)=a := by
    dsimp [b]
    split_ifs with h
    · have ha : a=0 := (ZMod.val_eq_zero a).mp h
      simp [ha]
    · exact ZMod.natCast_zmod_val a
  have hh : (Finset.range (X/q)).card≤((Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q)=a)).card := by
    apply Finset.card_le_card_of_injOn (fun j => q*j+b)
    · intro j hj
      change q*j+b∈(Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q)=a)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega,?_⟩,?_⟩
      · have hj' : j+1≤X/q := Finset.mem_range.mp hj
        calc
          q*j+b ≤ q*(j+1) := by nlinarith
          _ ≤ q*(X/q) := Nat.mul_le_mul_left _ hj'
          _ ≤ X := Nat.mul_div_le _ _
      · simp [Nat.cast_add,Nat.cast_mul,hba]
    · intro j hj k hk he
      have hq := NeZero.pos q
      change q*j+b=q*k+b at he
      nlinarith
  simpa using hh

lemma card_residue_interval_error {q : ℕ} [NeZero q] (a : ZMod q) (X : ℕ) :
    |(((Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q)=a)).card : ℝ)-(X : ℝ)/q|≤1 := by
  have hlow : (X/q : ℕ)≤((Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q)=a)).card := card_residue_interval_lower a X
  have hupp := card_residue_interval a X
  have hq : (0 : ℝ)<q := by exact_mod_cast NeZero.pos q
  have hdiv : ((X/q : ℕ) : ℝ)≤(X : ℝ)/q := by
    apply (le_div_iff₀ hq).mpr
    exact_mod_cast Nat.div_mul_le_self X q
  have hdiv' : (X : ℝ)/q<(X/q : ℕ)+1 := by
    apply (div_lt_iff₀ hq).mpr
    exact_mod_cast (show X < (X/q+1)*q by simpa [mul_comm] using Nat.lt_mul_div_succ X (NeZero.pos q))
  have hl : ((X/q : ℕ) : ℝ)≤((Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q)=a)).card := by exact_mod_cast hlow
  have hu : (((Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q)=a)).card : ℝ)≤(X/q : ℕ)+1 := by exact_mod_cast hupp
  rw [abs_le]
  constructor <;> linarith

lemma count_modEq_error (q b X : ℕ) (hq : q≠0) :
    |(∑ n∈Finset.Icc 1 X, if Nat.ModEq q n b then (1 : ℝ) else 0)-(X : ℝ)/q|≤1 := by
  letI : NeZero q := ⟨hq⟩
  have he : (∑ n∈Finset.Icc 1 X, if Nat.ModEq q n b then (1 : ℝ) else 0)=
      (((Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q)=(b : ZMod q))).card : ℝ) := by
    simp [← ZMod.natCast_eq_natCast_iff,← Finset.sum_filter]
  rw [he]
  exact card_residue_interval_error (b : ZMod q) X

end
end MaynardDevelopment
end

/- WeightedDistribution -/
section

open scoped BigOperators Topology
open Filter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma weighted_cauchy {α : Type*} (s : Finset α) (w e : α → ℝ)
    (he : ∀ i ∈ s, 0 ≤ e i) :
    (∑ i ∈ s, w i*e i)^2 ≤ (∑ i ∈ s, e i)*(∑ i ∈ s, (w i)^2*e i) := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (e i))
    (fun i => w i*Real.sqrt (e i))
  have h1 : (∑ i ∈ s, Real.sqrt (e i)*(w i*Real.sqrt (e i))) = ∑ i ∈ s, w i*e i := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = w i*(Real.sqrt (e i))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (he i hi)]
  have h2 : (∑ i ∈ s, (Real.sqrt (e i))^2)=∑ i ∈ s, e i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (he i hi)
  have h3 : (∑ i ∈ s, (w i*Real.sqrt (e i))^2)=∑ i ∈ s, (w i)^2*e i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (he i hi)]
  rwa [h1,h2,h3] at hh

def weightedProgressionError (R k D X : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 D, (q.divisors.card : ℝ)^k *
    if GoodModulus R q then progressionWorst q X else 0

lemma weightedProgressionError_nonneg (R k D X : ℕ) : 0 ≤ weightedProgressionError R k D X := by
  apply Finset.sum_nonneg
  intro q hq
  apply mul_nonneg (by positivity)
  split_ifs
  · exact progressionWorst_nonneg _ _
  · exact le_rfl

lemma weightedProgressionError_cauchy (R k D X : ℕ) (hDX : D ≤ X) :
    weightedProgressionError R k D X ^2 ≤
      (∑ q ∈ Finset.Icc 1 D, if GoodModulus R q then progressionWorst q X else 0)*
        (8*(X : ℝ)*(1+Real.log (X+1))*(1+Real.log D)^(2^(2*k))) := by
  let e (q : ℕ) : ℝ := if GoodModulus R q then progressionWorst q X else 0
  have he (q : ℕ) : 0 ≤ e q := by
    dsimp [e]; split_ifs
    · exact progressionWorst_nonneg _ _
    · exact le_rfl
  refine (weighted_cauchy (Finset.Icc 1 D) (fun q => (q.divisors.card : ℝ)^k) e (fun q _ => he q)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun q _ => he q))
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 D, (q.divisors.card : ℝ)^(2*k) *
        (8*(X : ℝ)*(1+Real.log (X+1))/q) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' := Finset.mem_Icc.mp hq
      haveI : NeZero q := ⟨by omega⟩
      rw [← pow_mul, Nat.mul_comm k 2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        e q ≤ progressionWorst q X := by dsimp [e]; split_ifs; rfl; exact progressionWorst_nonneg _ _
        _ ≤ _ := progressionWorst_harmonic X (hq'.2.trans hDX)
    _ = 8*(X : ℝ)*(1+Real.log (X+1))*
        ∑ q ∈ Finset.Icc 1 D, (q.divisors.card : ℝ)^(2*k)/q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_divisor_pow_div_le _ _)
      (by have hL := Real.log_nonneg (show (1 : ℝ) ≤ X+1 by have h : (0 : ℝ) ≤ X := Nat.cast_nonneg X; linarith); positivity)

/-- Divisor-weighted distribution with an arbitrarily large logarithmic saving.
The exceptional prime is chosen using the stronger unweighted exponent. -/
theorem weightedProgressionError_log_saving (k A : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ D : ℕ, (D+1)^22 ≤ X →
      weightedProgressionError (conductorCutoff (2*A+2^(2*k)+1) X) k D X ≤
        (480000000*2^(2^(2*k)) + 1 : ℝ)*(X : ℝ)/(Real.log X)^A := by
  have hL : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [progressionWorst_log_saving (2*A+2^(2*k)+1),hL] with X hX hL D hD
  have hDX := (modulus_power_bounds hD).1
  have hLp : 1+Real.log (X+1 : ℝ) ≤ 3*Real.log X := by
    have hh := log_nat_add_one_le_twice hL
    linarith
  have hLD : 1+Real.log D ≤ 2*Real.log X := by
    by_cases hD0 : D=0
    · simp [hD0]; linarith
    · have hh := Real.log_le_log (show (0 : ℝ)<D by exact_mod_cast Nat.pos_of_ne_zero hD0)
        (show (D : ℝ)≤X by exact_mod_cast hDX)
      linarith
  have hLn : 0 ≤ 1+Real.log D := by have hh := Real.log_natCast_nonneg D; linarith
  have hXn : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hLpos : 0 < Real.log X := by linarith
  let E := weightedProgressionError (conductorCutoff (2*A+2^(2*k)+1) X) k D X
  have hE := weightedProgressionError_cauchy (conductorCutoff (2*A+2^(2*k)+1) X) k D X hDX
  have hM : 8*(X : ℝ)*(1+Real.log (X+1))*(1+Real.log D)^(2^(2*k)) ≤
      24*2^(2^(2*k))*(X : ℝ)*(Real.log X)^(2^(2*k)+1) := by
    calc
      _ ≤ 8*(X : ℝ)*(3*Real.log X)*(2*Real.log X)^(2^(2*k)) := by gcongr
      _ = _ := by rw [mul_pow, pow_succ]; ring
  have hEsq : E^2 ≤ (480000000*2^(2^(2*k)) : ℝ)*((X : ℝ)/(Real.log X)^A)^2 := by
    calc
      E^2 ≤ (20000000*(X : ℝ)/(Real.log X)^(2*A+2^(2*k)+1))*
          (24*2^(2^(2*k))*(X : ℝ)*(Real.log X)^(2^(2*k)+1)) := by
        refine hE.trans (mul_le_mul (hX D hD) hM ?_ (by positivity))
        have hLp0 : 0 ≤ Real.log (X+1 : ℝ) := Real.log_nonneg (by linarith)
        positivity
      _ = _ := by
        rw [show 2*A+2^(2*k)+1=2*A+(2^(2*k)+1) by omega, pow_add, pow_mul]
        field_simp
        <;> ring
  have hc : (0 : ℝ) ≤ 480000000*2^(2^(2*k)) := by positivity
  have hz : 0 ≤ (X : ℝ)/(Real.log X)^A := by positivity
  have hn := weightedProgressionError_nonneg (conductorCutoff (2*A+2^(2*k)+1) X) k D X
  change 0 ≤ E at hn
  change E ≤ _
  rw [mul_div_assoc]
  apply (sq_le_sq₀ hn (mul_nonneg (by linarith) hz)).mp
  calc
    E^2 ≤ (480000000*2^(2^(2*k)) : ℝ)*((X : ℝ)/(Real.log X)^A)^2 := hEsq
    _ ≤ ((480000000*2^(2^(2*k)) : ℝ)+1)^2*((X : ℝ)/(Real.log X)^A)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith [sq_nonneg (480000000*2^(2^(2*k)) : ℝ)]
    _ = _ := by ring


end
end MaynardDevelopment
end

/- CoefficientGrouping -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Finset ℕ}

lemma matrix_pair_grouping (hP : ∀ p∈P, Nat.Prime p) (S : Finset (↥P→Finset ι))
    (Y : ℕ) (hS : ∀ r∈S, matrixProduct r≤Y) (F : ℕ→ℝ) (hF : ∀ n, 0≤F n) :
    (∑ r∈S, ∑ s∈S, F (matrixModulus r s)) ≤
      ∑ q∈Finset.Icc 1 (Y^2), (q.divisors.card : ℝ)^(2*Fintype.card ι)*F q := by
  classical
  let T : Finset (Σ q : ℕ, (ι→ℕ)×(ι→ℕ)) :=
    (Finset.Icc 1 (Y^2)).sigma (fun q =>
      (Fintype.piFinset (fun _ : ι => q.divisors)) ×ˢ (Fintype.piFinset (fun _ : ι => q.divisors)))
  let f (rs : (↥P→Finset ι)×(↥P→Finset ι)) : Σ q : ℕ, (ι→ℕ)×(ι→ℕ) :=
    ⟨matrixModulus rs.1 rs.2, (fun i => primeSetProduct (matrixCoords rs.1 i).val,
      fun i => primeSetProduct (matrixCoords rs.2 i).val)⟩
  have hf : Set.InjOn f (↑(S×ˢS : Finset ((↥P→Finset ι)×(↥P→Finset ι))) : Set ((↥P→Finset ι)×(↥P→Finset ι))) := by
    intro rs hrs uv huv he
    have hh := congrArg (fun z : Σ q : ℕ, (ι→ℕ)×(ι→ℕ) => z.2) he
    have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    exact Prod.ext (matrixProducts_injective hP h1) (matrixProducts_injective hP h2)
  have hsub : (S×ˢS).image f⊆T := by
    intro z hz
    obtain ⟨⟨r,s⟩,hrs,rfl⟩ := Finset.mem_image.mp hz
    have hrs' := Finset.mem_product.mp hrs
    have hq0 := matrixModulus_pos (fun p hp => (hP p hp).pos) r s
    have hqY : matrixModulus r s≤Y^2 := by
      refine (matrixModulus_le_product (fun p hp => (hP p hp).one_le) r s).trans ?_
      simpa [pow_two] using Nat.mul_le_mul (hS r hrs'.1) (hS s hrs'.2)
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hq0,hqY⟩,Finset.mem_product.mpr ⟨?_,?_⟩⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact Nat.mem_divisors.mpr ⟨coords_product_dvd_matrixModulus_left r s i,hq0.ne'⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact Nat.mem_divisors.mpr ⟨coords_product_dvd_matrixModulus_right r s i,hq0.ne'⟩
  calc
    _ = ∑ rs∈S×ˢS, F (matrixModulus rs.1 rs.2) := (Finset.sum_product S S _).symm
    _ = ∑ z∈(S×ˢS).image f, F z.1 := by rw [Finset.sum_image hf]
    _ ≤ ∑ z∈T, F z.1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hF _)
    _ = _ := by
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [Finset.sum_const, Finset.card_product,Fintype.card_piFinset,Finset.prod_const,
        Finset.card_univ,nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow,pow_mul]
      ring

lemma divisor_card_mono_dvd {a b : ℕ} (hb : b≠0) (hab : a∣b) : a.divisors.card≤b.divisors.card := by
  apply Finset.card_le_card
  intro d hd
  exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hd).trans hab,hb⟩

lemma weighted_multiples_sum_le (W Y k : ℕ) (hW : 0<W) (F : ℕ→ℝ) (hF : ∀ n, 0≤F n) :
    (∑ q∈Finset.Icc 1 Y, (q.divisors.card : ℝ)^k*F (W*q)) ≤
      ∑ q∈Finset.Icc 1 (W*Y), (q.divisors.card : ℝ)^k*F q := by
  classical
  have hi : Set.InjOn (fun q => W*q) (Finset.Icc 1 Y : Set ℕ) := by
    intro a ha b hb he
    exact Nat.eq_of_mul_eq_mul_left hW he
  have hsub : (Finset.Icc 1 Y).image (fun q => W*q)⊆Finset.Icc 1 (W*Y) := by
    intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    have ha' := Finset.mem_Icc.mp ha
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hW ha'.1,Nat.mul_le_mul_left _ ha'.2⟩
  calc
    _ ≤ ∑ q∈Finset.Icc 1 Y, ((W*q).divisors.card : ℝ)^k*F (W*q) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_right _ (hF _)
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast divisor_card_mono_dvd
        (Nat.mul_pos hW (Finset.mem_Icc.mp hq).1).ne' (dvd_mul_left q W)
    _ = ∑ q∈(Finset.Icc 1 Y).image (fun q => W*q), (q.divisors.card : ℝ)^k*F q :=
      (Finset.sum_image (f := fun q : ℕ => (q.divisors.card : ℝ)^k*F q) hi).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => mul_nonneg (by positivity) (hF q))

lemma coefficient_pair_error_bound (hP : ∀ p∈P, Nat.Prime p) (S : Finset (↥P→Finset ι))
    (Y W : ℕ) (hW : 0<W) (hS : ∀ r∈S, matrixProduct r≤Y) (lam : (↥P→Finset ι)→ℝ) (L : ℝ)
    (hL : 0≤L) (hlam : ∀ r∈S, |lam r|≤L) (F : ℕ→ℝ) (hF : ∀ n, 0≤F n) :
    (∑ r∈S, ∑ s∈S, |lam r*lam s| *F (W*matrixModulus r s)) ≤
      L^2*(∑ q∈Finset.Icc 1 (W*Y^2), (q.divisors.card : ℝ)^(2*Fintype.card ι)*F q) := by
  calc
    _ ≤ ∑ r∈S, ∑ s∈S, L^2*F (W*matrixModulus r s) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      apply mul_le_mul_of_nonneg_right _ (hF _)
      rw [abs_mul,pow_two]
      exact mul_le_mul (hlam r hr) (hlam s hs) (abs_nonneg _) hL
    _ = L^2*(∑ r∈S, ∑ s∈S, F (W*matrixModulus r s)) := by simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((matrix_pair_grouping hP S Y hS (fun q => F (W*q)) (fun q => hF _)).trans
        (weighted_multiples_sum_le W (Y^2) (2*Fintype.card ι) hW F hF)) (sq_nonneg _)

end
end MaynardDevelopment
end

/- SieveAveraging -/
section

open scoped BigOperators
set_option maxHeartbeats 2000000
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma finite_quadratic_average {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (lam : α→ℝ) (f : α→β→ℝ) (w : β→ℝ) :
    (∑ n∈T, w n*(∑ r∈S, lam r*f r n)^2)=
      ∑ r∈S, ∑ s∈S, lam r*lam s*(∑ n∈T, w n*f r n*f s n) := by
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intros
  ring

lemma finite_quadratic_error {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (lam : α→ℝ) (f : α→β→ℝ) (w : β→ℝ)
    (main err : α→α→ℝ)
    (he : ∀ r∈S, ∀ s∈S, |(∑ n∈T, w n*f r n*f s n)-main r s|≤err r s) :
    |(∑ n∈T, w n*(∑ r∈S, lam r*f r n)^2)-∑ r∈S, ∑ s∈S, lam r*lam s*main r s|≤
      ∑ r∈S, ∑ s∈S, |lam r*lam s| *err r s := by
  rw [finite_quadratic_average,← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib,← mul_sub]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro r hr
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro s hs
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (he r hr s hs) (abs_nonneg _)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Finset ℕ}

def matrixIndicator (h : ∀ p : ↥P, ι→ZMod p.val) (r : ↥P→Finset ι) (n : ℕ) : ℝ :=
  if matrixCondition h r n then 1 else 0

def integerSieveWeight (h : ∀ p : ↥P, ι→ZMod p.val) (lam : (↥P→Finset ι)→ℝ) (n : ℕ) : ℝ :=
  (∑ r, lam r*matrixIndicator h r n)^2

lemma matrixIndicator_pair (h : ∀ p : ↥P, ι→ZMod p.val) (r s : ↥P→Finset ι) (n : ℕ) :
    matrixIndicator h r n*matrixIndicator h s n=
      if matrixCondition h r n ∧ matrixCondition h s n then 1 else 0 := by
  unfold matrixIndicator
  split_ifs <;> norm_num <;> tauto

lemma matrix_count_error (hP : ∀ p∈P, Nat.Prime p) (W a X : ℕ) (hW0 : W≠0)
    (hW : ∀ p∈P, W.Coprime p) (h : ∀ p : ↥P, ι→ZMod p.val)
    (hi : ∀ p, Function.Injective (h p)) (r s : ↥P→Finset ι) :
    |(∑ n∈Finset.Icc 1 X, (if Nat.ModEq W n a then (1 : ℝ) else 0)*matrixIndicator h r n*matrixIndicator h s n)-
      (X : ℝ)/W*(∏ p : ↥P, indicatorKernelOne (p.val : ℝ) (r p) (s p))|≤1 := by
  rw [prod_indicatorKernelOne]
  have he (n : ℕ) : (if Nat.ModEq W n a then (1 : ℝ) else 0)*matrixIndicator h r n*matrixIndicator h s n=
      if Nat.ModEq W n a ∧ matrixCondition h r n ∧ matrixCondition h s n then 1 else 0 := by
    rw [mul_assoc,matrixIndicator_pair]
    split_ifs <;> norm_num <;> tauto
  simp only [he]
  by_cases hc : matrixCompatible r s
  · obtain ⟨b,hb⟩ := matrixCondition_progression hP W a hW h r s hc
    simp only [hb,if_pos hc]
    have hq := matrixModulus_pos (fun p hp => (hP p hp).pos) r s
    have hh := count_modEq_error (W*matrixModulus r s) b X (Nat.mul_ne_zero hW0 hq.ne')
    simpa only [Nat.cast_mul,div_mul_eq_div_mul_one_div,one_div] using hh
  · rw [if_neg hc,mul_zero,sub_zero]
    have hz : ∀ n, ¬(Nat.ModEq W n a ∧ matrixCondition h r n ∧ matrixCondition h s n) := by
      intro n hn
      exact hc (matrixCondition_compatible h hi r s n hn.2)
    simp [hz]

lemma integerSieve_uniform_error (hP : ∀ p∈P, Nat.Prime p) (W a X : ℕ) (hW0 : W≠0)
    (hW : ∀ p∈P, W.Coprime p) (h : ∀ p : ↥P, ι→ZMod p.val)
    (hi : ∀ p, Function.Injective (h p)) (lam : (↥P→Finset ι)→ℝ) :
    |(∑ n∈Finset.Icc 1 X, (if Nat.ModEq W n a then (1 : ℝ) else 0)*integerSieveWeight h lam n)-
      (X : ℝ)/W*kernelQuadratic (fun p : ↥P => indicatorKernelOne (p.val : ℝ)) lam|≤(∑ r, |lam r|)^2 := by
  have hh := finite_quadratic_error Finset.univ (Finset.Icc 1 X) lam (matrixIndicator h)
    (fun n => if Nat.ModEq W n a then (1 : ℝ) else 0)
    (fun r s => (X : ℝ)/W*(∏ p : ↥P, indicatorKernelOne (p.val : ℝ) (r p) (s p)))
    (fun _ _ => 1) (fun r hr s hs => matrix_count_error hP W a X hW0 hW h hi r s)
  have he : (∑ r, ∑ s, lam r*lam s*((X : ℝ)/W*(∏ p : ↥P, indicatorKernelOne (p.val : ℝ) (r p) (s p))))=
      (X : ℝ)/W*kernelQuadratic (fun p : ↥P => indicatorKernelOne (p.val : ℝ)) lam := by
    unfold kernelQuadratic
    simp only [Finset.mul_sum]
    apply Finset.sum_congr (by ext; simp)
    intro r hr
    apply Finset.sum_congr (by ext; simp)
    intros
    ring
  rw [he] at hh
  simpa only [integerSieveWeight,mul_one,abs_mul,pow_two,Finset.sum_mul,Finset.mul_sum,mul_comm] using hh

end
end MaynardDevelopment
end

/- ShiftedProgressions -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma interval_shift_error (f : ℕ→ℝ) (X h : ℕ) (C : ℝ)
    (hf : ∀ n∈Finset.Icc 1 (X+h), |f n|≤C) :
    |(∑ n∈Finset.Icc 1 X, f (n+h))-(∑ n∈Finset.Icc 1 X, f n)|≤2*h*C := by
  have he : (∑ n∈Finset.Icc 1 X, f (n+h))=∑ n∈Finset.Ico (h+1) (X+h+1), f n := by
    rw [← Finset.Ico_add_one_right_eq_Icc,Finset.sum_Ico_add']
    simp only [add_comm 1 h,add_right_comm X 1 h]
  have h1 := Finset.sum_Ico_consecutive f (m := 1) (n := h+1) (k := X+h+1) (by omega) (by omega)
  have h2 := Finset.sum_Ico_consecutive f (m := 1) (n := X+1) (k := X+h+1) (by omega) (by omega)
  have hb (a b : ℕ) (hab : 1≤a) (hb : b≤X+h+1) :
      |∑ n∈Finset.Ico a b, f n|≤(b-a : ℕ)*C := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ n∈Finset.Ico a b, C := by
        apply Finset.sum_le_sum
        intro n hn
        exact hf n (Finset.mem_Icc.mpr (by have hh := Finset.mem_Ico.mp hn; omega))
      _ = _ := by simp
  have hb1 := hb 1 (h+1) (by omega) (by omega)
  have hb2 := hb (X+1) (X+h+1) (by omega) le_rfl
  have hdiff : (∑ n∈Finset.Icc 1 X, f (n+h))-(∑ n∈Finset.Icc 1 X, f n)=
      (∑ n∈Finset.Ico (X+1) (X+h+1), f n)-(∑ n∈Finset.Ico 1 (h+1), f n) := by
    rw [he,← Finset.Ico_add_one_right_eq_Icc]
    linarith
  rw [hdiff]
  have hh := abs_sub (∑ n∈Finset.Ico (X+1) (X+h+1), f n) (∑ n∈Finset.Ico 1 (h+1), f n)
  simp only [Nat.add_sub_cancel,Nat.add_sub_add_right,Nat.add_sub_cancel_left] at hb1 hb2
  linarith

lemma vonMangoldt_interval_bound (n Y : ℕ) (hn : n∈Finset.Icc 1 Y) :
    |ArithmeticFunction.vonMangoldt n|≤Real.log (Y+1 : ℝ) := by
  rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log ?_ ?_)
  · exact_mod_cast (Finset.mem_Icc.mp hn).1
  · have hh : (n : ℝ)≤Y := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    linarith

lemma shifted_progression_error (q b X h : ℕ) (hq : q≠0) (hb : (b+h).Coprime q) :
    |(∑ n∈Finset.Icc 1 X, if Nat.ModEq q n b then ArithmeticFunction.vonMangoldt (n+h) else 0)-
      (X : ℝ)/q.totient|≤progressionWorst q X+2*h*Real.log (X+h+1 : ℝ) := by
  letI : NeZero q := ⟨hq⟩
  let f (n : ℕ) : ℝ := if Nat.ModEq q n (b+h) then ArithmeticFunction.vonMangoldt n else 0
  have he (n : ℕ) : f (n+h)=if Nat.ModEq q n b then ArithmeticFunction.vonMangoldt (n+h) else 0 := by
    have hh : Nat.ModEq q (n+h) (b+h) ↔ Nat.ModEq q n b :=
      ⟨fun h' => Nat.ModEq.add_right_cancel (Nat.ModEq.refl h) h',fun h' => h'.add_right h⟩
    simp only [f,hh]
  have hshift := interval_shift_error f X h (Real.log (X+h+1 : ℝ)) (by
    intro n hn
    dsimp [f]
    split_ifs
    · simpa only [Nat.cast_add] using vonMangoldt_interval_bound n (X+h) hn
    · rw [abs_zero]; exact Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X,Nat.cast_nonneg (α := ℝ) h]))
  have hsum : (∑ n∈Finset.Icc 1 X, f n)=progressionSum ((b+h : ℕ) : ZMod q) X := by
    unfold progressionSum ArithmeticFunction.vonMangoldt.residueClass
    simp [f,Set.indicator_apply,← ZMod.natCast_eq_natCast_iff]
  simp only [he,hsum] at hshift
  have hmain := progressionError_le_worst ((ZMod.isUnit_iff_coprime (b+h) q).mpr hb) X
  unfold progressionError at hmain
  have hh := abs_sub_le (∑ n∈Finset.Icc 1 X, if Nat.ModEq q n b then ArithmeticFunction.vonMangoldt (n+h) else 0)
    (progressionSum ((b+h : ℕ) : ZMod q) X) ((X : ℝ)/q.totient)
  linarith

end
end MaynardDevelopment
end

/- PrimePowerErrors -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma sum_le_support_card_real {α : Type*} [DecidableEq α] (s S : Finset α) (f : α→ℝ)
    (C : ℝ) (hC : 0≤C) (hf : ∀ a∈s, f a≤C) (hs : ∀ a∈s, f a≠0 → a∈S) :
    (∑ a∈s, f a)≤(S.card : ℝ)*C := by
  calc
    _ ≤ ∑ a∈s, if a∈S then C else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : a∈S
      · rw [if_pos h]; exact hf a ha
      · rw [if_neg h]
        have hh : f a=0 := by by_contra hh; exact h (hs a ha hh)
        rw [hh]
    _ = ((s.filter (fun a => a∈S)).card : ℝ)*C := by rw [← Finset.sum_filter]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card (show s.filter (fun a => a∈S)⊆S from fun a ha => (Finset.mem_filter.mp ha).2)) hC

lemma shifted_primePower_sum_bound (X h Z : ℕ) (pred : ℕ→Prop) [DecidablePred pred]
    (hs : ∀ n∈Finset.Icc 1 X, pred n → ∀ p k : ℕ, Nat.Prime p → 0<k → p^k=n+h → p≤Z) :
    (∑ n∈Finset.Icc 1 X, if pred n then ArithmeticFunction.vonMangoldt (n+h) else 0)≤
      (Z+1 : ℝ)*(Nat.log 2 (X+h)+1 : ℝ)*Real.log (X+h+1 : ℝ) := by
  let S := (Finset.range (Z+1) ×ˢ Finset.range (Nat.log 2 (X+h)+1)).image (fun pk : ℕ×ℕ => pk.1^pk.2-h)
  have hC : 0≤Real.log (X+h+1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X,Nat.cast_nonneg (α := ℝ) h])
  have hh := sum_le_support_card_real (Finset.Icc 1 X) S
    (fun n => if pred n then ArithmeticFunction.vonMangoldt (n+h) else 0) _ hC (by
      intro n hn
      dsimp only
      split_ifs
      · refine (le_abs_self _).trans ?_
        simpa only [Nat.cast_add] using vonMangoldt_interval_bound (n+h) (X+h)
          (Finset.mem_Icc.mpr (by have h' := Finset.mem_Icc.mp hn; omega))
      · exact hC) (by
      intro n hn hne
      have hpred : pred n := by by_contra hp; simp [hp] at hne
      dsimp only at hne
      rw [if_pos hpred] at hne
      obtain ⟨p,k,hp,hk,hpn⟩ := (isPrimePow_nat_iff (n+h)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne)
      have hpZ := hs n hn hpred p k hp hk hpn
      have hkX : k≤Nat.log 2 (X+h) := Nat.le_log_of_pow_le (by norm_num)
        ((Nat.pow_le_pow_left hp.two_le k).trans (hpn ▸ Nat.add_le_add_right (Finset.mem_Icc.mp hn).2 h))
      apply Finset.mem_image.mpr
      refine ⟨(p,k),?_,?_⟩
      · simp only [Finset.mem_product,Finset.mem_range]; exact ⟨by omega,by omega⟩
      · dsimp; omega)
  have hc : S.card≤(Z+1)*(Nat.log 2 (X+h)+1) := Finset.card_image_le.trans (by simp)
  have hc' : (S.card : ℝ)≤(Z+1 : ℝ)*(Nat.log 2 (X+h)+1 : ℝ) := by exact_mod_cast hc
  exact hh.trans (mul_le_mul_of_nonneg_right hc' hC)

lemma modEq_coprime_iff {q a b : ℕ} (hab : Nat.ModEq q a b) : a.Coprime q ↔ b.Coprime q := by
  rw [Nat.coprime_iff_gcd_eq_one,Nat.coprime_iff_gcd_eq_one,Nat.gcd_comm a q,Nat.gcd_comm b q,
    Nat.gcd_rec q a,Nat.gcd_rec q b]
  change (a%q).gcd q=1 ↔ (b%q).gcd q=1
  rw [hab]

lemma shifted_nonunit_sum_bound (q b X h : ℕ) (hq : q≠0) (hb : ¬(b+h).Coprime q) :
    (∑ n∈Finset.Icc 1 X, if Nat.ModEq q n b then ArithmeticFunction.vonMangoldt (n+h) else 0)≤
      (q+1 : ℝ)*(Nat.log 2 (X+h)+1 : ℝ)*Real.log (X+h+1 : ℝ) := by
  apply shifted_primePower_sum_bound
  intro n hn hnb p k hp hk hpn
  have hnc : ¬(n+h).Coprime q := fun hh => hb ((modEq_coprime_iff (hnb.add_right h)).mp hh)
  have hpd : p∣q := by
    by_contra hh
    apply hnc
    rw [← hpn]
    exact (hp.coprime_iff_not_dvd.mpr hh).pow_left k
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hpd

lemma shifted_nonprime_sum_bound (X h : ℕ) :
    (∑ n∈Finset.Icc 1 X, if ¬Nat.Prime (n+h) then ArithmeticFunction.vonMangoldt (n+h) else 0)≤
      (Nat.sqrt (X+h)+1 : ℝ)*(Nat.log 2 (X+h)+1 : ℝ)*Real.log (X+h+1 : ℝ) := by
  apply shifted_primePower_sum_bound
  intro n hn hnp p k hp hk hpn
  have hk2 : 2≤k := by
    have hk1 : k≠1 := by intro hh; subst k; simp only [pow_one] at hpn; exact hnp (hpn ▸ hp)
    omega
  apply Nat.le_sqrt'.mpr
  exact (Nat.pow_le_pow_right hp.pos hk2).trans (hpn ▸ Nat.add_le_add_right (Finset.mem_Icc.mp hn).2 h)

end
end MaynardDevelopment
end

/- MatrixUnits -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Finset ℕ}

def shiftedResidues (h : ι→ℕ) (p : ↥P) (i : ι) : ZMod p.val := -(h i : ZMod p.val)

lemma shiftedResidues_condition (h : ι→ℕ) (r : ↥P→Finset ι) (n : ℕ) :
    matrixCondition (shiftedResidues h) r n ↔ ∀ p, ∀ i∈r p, p.val∣n+h i := by
  unfold matrixCondition shiftedResidues
  apply forall_congr'
  intro p
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [← Nat.modEq_zero_iff_dvd,← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_add,Nat.cast_zero,eq_neg_iff_add_eq_zero]

lemma matrixModulus_shift_coprime_iff (hP : ∀ p∈P, Nat.Prime p) (h : ι→ℕ)
    (hi : ∀ p : ↥P, Function.Injective (shiftedResidues h p)) (r s : ↥P→Finset ι) (b : ℕ)
    (hb : matrixCondition (shiftedResidues h) r b ∧ matrixCondition (shiftedResidues h) s b) (m : ι) :
    (b+h m).Coprime (matrixModulus r s) ↔ matrixAvoids m r s := by
  have hcond := (matrixCondition_union (shiftedResidues h) r s b).mp hb
  have hd := (shiftedResidues_condition h (fun p => r p∪s p) b).mp hcond
  rw [matrixModulus,Nat.coprime_prod_right_iff]
  simp only [Finset.mem_univ,forall_true_left]
  constructor
  · intro hc p hm
    have hp := hc p
    rw [if_pos (Finset.union_nonempty.mp ⟨m,hm⟩)] at hp
    exact ((hP _ p.property).coprime_iff_not_dvd.mp hp.symm) (hd p m hm)
  · intro ha p
    by_cases he : (r p).Nonempty ∨ (s p).Nonempty
    · rw [if_pos he,Nat.coprime_comm,(hP _ p.property).coprime_iff_not_dvd]
      intro hdiv
      obtain ⟨i,him⟩ := Finset.union_nonempty.mpr he
      have hbm : (b : ZMod p.val)=shiftedResidues h p m := by
        rw [shiftedResidues,eq_neg_iff_add_eq_zero,← Nat.cast_add]
        exact_mod_cast ((ZMod.natCast_eq_natCast_iff (b+h m) 0 p.val).mpr (Nat.modEq_zero_iff_dvd.mpr hdiv))
      have him' : i=m := hi p ((hcond p i him).symm.trans hbm)
      exact ha p (him' ▸ him)
    · rw [if_neg he]
      exact Nat.coprime_one_right _

lemma matrix_progression_unit_iff (hP : ∀ p∈P, Nat.Prime p) (W a : ℕ) (h : ι→ℕ)
    (hi : ∀ p : ↥P, Function.Injective (shiftedResidues h p)) (r s : ↥P→Finset ι) (b : ℕ)
    (hb : ∀ n, (Nat.ModEq W n a ∧ matrixCondition (shiftedResidues h) r n ∧ matrixCondition (shiftedResidues h) s n) ↔
      Nat.ModEq (W*matrixModulus r s) n b)
    (m : ι) (hm : W.Coprime (a+h m)) :
    (b+h m).Coprime (W*matrixModulus r s) ↔ matrixAvoids m r s := by
  have hbb := (hb b).mpr (Nat.ModEq.refl b)
  have hW : (b+h m).Coprime W := (modEq_coprime_iff (hbb.1.add_right (h m))).mpr hm.symm
  rw [Nat.coprime_mul_iff_right,and_iff_right hW]
  exact matrixModulus_shift_coprime_iff hP h hi r s b hbb.2 m

end
end MaynardDevelopment
end

/- CoefficientNorms -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma sum_restrict_support {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (lam f : α→ℝ)
    (hs : ∀ r, lam r≠0 → r∈S) : (∑ r, lam r*f r)=∑ r∈S, lam r*f r := by
  apply (Finset.sum_subset (Finset.subset_univ S) ?_).symm
  intro r hr hnot
  have hz : lam r=0 := by by_contra hh; exact hnot (hs r hh)
  simp [hz]

lemma coefficient_l1_bound {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (lam : α→ℝ) (L : ℝ) (hs : ∀ r, lam r≠0 → r∈S) (hL : ∀ r∈S, |lam r|≤L) :
    (∑ r, |lam r|)≤(S.card : ℝ)*L := by
  have he : (∑ r, |lam r|)=∑ r∈S, |lam r| := by
    simpa using sum_restrict_support S (fun r => |lam r|) (fun _ => 1) (by simpa using hs)
  rw [he]
  calc
    _ ≤ ∑ r∈S, L := Finset.sum_le_sum hL
    _ = _ := by simp

lemma pair_sum_restrict {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (lam : α→ℝ)
    (f : α→α→ℝ) (hs : ∀ r, lam r≠0 → r∈S) :
    (∑ r, ∑ s, lam r*lam s*f r s)=∑ r∈S, ∑ s∈S, lam r*lam s*f r s := by
  simp_rw [mul_assoc,← Finset.mul_sum]
  rw [sum_restrict_support S lam _ hs]
  apply Finset.sum_congr rfl
  intro r hr
  rw [sum_restrict_support S lam _ hs]

lemma kernelQuadratic_restrict {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β]
    (K : ι→β→β→ℝ) (lam : (ι→β)→ℝ) (S : Finset (ι→β)) (hs : ∀ r, lam r≠0 → r∈S) :
    kernelQuadratic K lam=∑ r∈S, ∑ s∈S, lam r*lam s*∏ p, K p (r p) (s p) := by
  unfold kernelQuadratic
  convert pair_sum_restrict S lam (fun r s => ∏ p, K p (r p) (s p)) hs using 1
  apply Finset.sum_congr (by ext; simp)
  intro r hr
  apply Finset.sum_congr (by ext; simp)
  intros
  rfl

lemma integerSieveWeight_restrict {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Finset ℕ}
    (h : ∀ p : ↥P, ι→ZMod p.val) (lam : (↥P→Finset ι)→ℝ) (S : Finset (↥P→Finset ι))
    (hs : ∀ r, lam r≠0 → r∈S) (n : ℕ) :
    integerSieveWeight h lam n=(∑ r∈S, lam r*matrixIndicator h r n)^2 := by
  unfold integerSieveWeight
  rw [sum_restrict_support S lam _ hs]

lemma integerSieveWeight_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Finset ℕ}
    (h : ∀ p : ↥P, ι→ZMod p.val) (lam : (↥P→Finset ι)→ℝ) (n : ℕ) :
    0≤ integerSieveWeight h lam n ∧ integerSieveWeight h lam n≤(∑ r, |lam r|)^2 := by
  refine ⟨sq_nonneg _,?_⟩
  apply sq_le_sq'
  · have hh : |∑ r, lam r*matrixIndicator h r n|≤∑ r, |lam r| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro r hr
      unfold matrixIndicator
      split_ifs <;> simp
    exact (abs_le.mp hh).1
  · have hh : (∑ r, lam r*matrixIndicator h r n)≤∑ r, |lam r| := by
      apply Finset.sum_le_sum
      intro r hr
      unfold matrixIndicator
      split_ifs
      · simpa using le_abs_self (lam r)
      · simp
    exact hh

end
end MaynardDevelopment
end

/- SievePrimeAveraging -/
section

open scoped BigOperators
set_option maxHeartbeats 2000000
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

def elementarySieveError (D X h : ℕ) : ℝ :=
  (D+1 : ℝ)*(Nat.log 2 (X+h)+1 : ℝ)*Real.log (X+h+1 : ℝ)+2*h*Real.log (X+h+1 : ℝ)

lemma elementarySieveError_nonneg (D X h : ℕ) : 0≤elementarySieveError D X h := by
  have hh : 0≤Real.log (X+h+1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X,Nat.cast_nonneg (α := ℝ) h])
  unfold elementarySieveError
  positivity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Finset ℕ}

lemma matrix_prime_error (hP : ∀ p∈P, Nat.Prime p) (W a X D : ℕ) (hW0 : W≠0)
    (hW : ∀ p∈P, W.Coprime p) (h : ι→ℕ)
    (hi : ∀ p : ↥P, Function.Injective (shiftedResidues h p))
    (r s : ↥P→Finset ι) (hqD : W*matrixModulus r s≤D) (m : ι) (hm : W.Coprime (a+h m)) :
    |(∑ n∈Finset.Icc 1 X, (if Nat.ModEq W n a then ArithmeticFunction.vonMangoldt (n+h m) else 0)*
        matrixIndicator (shiftedResidues h) r n*matrixIndicator (shiftedResidues h) s n)-
      (X : ℝ)/W.totient*(∏ p : ↥P, indicatorKernelTwo (p.val : ℝ) m (r p) (s p))|≤
      progressionWorst (W*matrixModulus r s) X+elementarySieveError D X (h m) := by
  have hlog : 0≤Real.log (X+h m+1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X,Nat.cast_nonneg (α := ℝ) (h m)])
  have hn0 := elementarySieveError_nonneg D X (h m)
  have hw0 := progressionWorst_nonneg (W*matrixModulus r s) X
  have he (n : ℕ) : (if Nat.ModEq W n a then ArithmeticFunction.vonMangoldt (n+h m) else 0)*
      matrixIndicator (shiftedResidues h) r n*matrixIndicator (shiftedResidues h) s n=
      if Nat.ModEq W n a ∧ matrixCondition (shiftedResidues h) r n ∧ matrixCondition (shiftedResidues h) s n
      then ArithmeticFunction.vonMangoldt (n+h m) else 0 := by
    rw [mul_assoc,matrixIndicator_pair]
    split_ifs <;> simp_all
  simp only [he]
  rw [prod_indicatorKernelTwo hP]
  by_cases hc : matrixCompatible r s
  · obtain ⟨b,hb⟩ := matrixCondition_progression hP W a hW (shiftedResidues h) r s hc
    simp only [hb]
    have hq0 : W*matrixModulus r s≠0 := Nat.mul_ne_zero hW0 (matrixModulus_pos (fun p hp => (hP _ hp).pos) r s).ne'
    have hunit := matrix_progression_unit_iff hP W a h hi r s b hb m hm
    by_cases ha : matrixAvoids m r s
    · rw [if_pos ⟨hc,ha⟩]
      have hh := shifted_progression_error (W*matrixModulus r s) b X (h m) hq0 (hunit.mpr ha)
      have ht := Nat.totient_mul (matrixModulus_coprime hP W hW r s)
      rw [ht,Nat.cast_mul,div_mul_eq_div_mul_one_div,one_div] at hh
      refine hh.trans (add_le_add_right ?_ _)
      unfold elementarySieveError
      have hh' : 0≤(D+1 : ℝ)*(Nat.log 2 (X+h m)+1 : ℝ)*Real.log (X+h m+1 : ℝ) := by positivity
      linarith
    · rw [if_neg (by tauto),mul_zero,sub_zero]
      have hsum : 0≤∑ n∈Finset.Icc 1 X, if Nat.ModEq (W*matrixModulus r s) n b then ArithmeticFunction.vonMangoldt (n+h m) else 0 := by
        apply Finset.sum_nonneg
        intro n hn
        split_ifs
        · exact ArithmeticFunction.vonMangoldt_nonneg
        · exact le_rfl
      rw [abs_of_nonneg hsum]
      refine (shifted_nonunit_sum_bound _ b X (h m) hq0 (fun hh => ha (hunit.mp hh))).trans ?_
      have hqd : (W*matrixModulus r s : ℕ)≤D := hqD
      have hqd' : ((W*matrixModulus r s : ℕ) : ℝ)≤D := by exact_mod_cast hqd
      unfold elementarySieveError
      have hmul := mul_le_mul_of_nonneg_right (add_le_add_right hqd' 1)
        (show 0≤(Nat.log 2 (X+h m)+1 : ℝ)*Real.log (X+h m+1 : ℝ) by positivity)
      have ht : 0≤2*(h m : ℝ)*Real.log (X+h m+1 : ℝ) := by positivity
      nlinarith
  · rw [if_neg (by tauto),mul_zero,sub_zero]
    have hz : ∀ n, ¬(Nat.ModEq W n a ∧ matrixCondition (shiftedResidues h) r n ∧ matrixCondition (shiftedResidues h) s n) := by
      intro n hn
      exact hc (matrixCondition_compatible (shiftedResidues h) hi r s n hn.2)
    simp only [if_neg (hz _),Finset.sum_const_zero,abs_zero]
    positivity

lemma integerSieve_prime_error (hP : ∀ p∈P, Nat.Prime p) (W a X D Q : ℕ) (hW0 : W≠0)
    (hW : ∀ p∈P, W.Coprime p) (h : ι→ℕ)
    (hi : ∀ p : ↥P, Function.Injective (shiftedResidues h p)) (m : ι) (hm : W.Coprime (a+h m))
    (lam : (↥P→Finset ι)→ℝ) (S : Finset (↥P→Finset ι)) (hs : ∀ r, lam r≠0 → r∈S)
    (hD : ∀ r∈S, ∀ s∈S, W*matrixModulus r s≤D)
    (hgood : ∀ r∈S, ∀ s∈S, GoodModulus Q (W*matrixModulus r s)) :
    |(∑ n∈Finset.Icc 1 X, (if Nat.ModEq W n a then ArithmeticFunction.vonMangoldt (n+h m) else 0)*integerSieveWeight (shiftedResidues h) lam n)-
      (X : ℝ)/W.totient*kernelQuadratic (fun p : ↥P => indicatorKernelTwo (p.val : ℝ) m) lam|≤
      (∑ r∈S, ∑ s∈S, |lam r*lam s| * (if GoodModulus Q (W*matrixModulus r s) then progressionWorst (W*matrixModulus r s) X else 0))+
        (∑ r∈S, |lam r|)^2*elementarySieveError D X (h m) := by
  have hh := finite_quadratic_error S (Finset.Icc 1 X) lam (matrixIndicator (shiftedResidues h))
    (fun n => if Nat.ModEq W n a then ArithmeticFunction.vonMangoldt (n+h m) else 0)
    (fun r s => (X : ℝ)/W.totient*(∏ p : ↥P, indicatorKernelTwo (p.val : ℝ) m (r p) (s p)))
    (fun r s => (if GoodModulus Q (W*matrixModulus r s) then progressionWorst (W*matrixModulus r s) X else 0)+elementarySieveError D X (h m))
    (by intro r hr s hs'; dsimp only; rw [if_pos (hgood r hr s hs')]; exact matrix_prime_error hP W a X D hW0 hW h hi r s (hD r hr s hs') m hm)
  simp_rw [← integerSieveWeight_restrict (shiftedResidues h) lam S hs] at hh
  rw [kernelQuadratic_restrict _ lam S hs]
  have he : (∑ r∈S, ∑ s∈S, lam r*lam s*((X : ℝ)/W.totient*(∏ p : ↥P, indicatorKernelTwo (p.val : ℝ) m (r p) (s p))))=
      (X : ℝ)/W.totient*(∑ r∈S, ∑ s∈S, lam r*lam s*∏ p : ↥P, indicatorKernelTwo (p.val : ℝ) m (r p) (s p)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intros
    ring
  rw [he] at hh
  convert hh using 1
  simp only [mul_add,Finset.sum_add_distrib]
  congr 1
  simp only [abs_mul,pow_two,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intros
  ring

end
end MaynardDevelopment
end

/- SieveMargin -/
section

open scoped BigOperators Topology
open Filter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma robust_kernel_margin {A B C c k I J Q₁ Q₂ : ℝ}
    (hA : 0≤A) (hB : 2*A+2≤B) (hC : 1≤C) (hc : 0<c) (hk : 0≤k) (hkC : k≤C)
    (hI : 0<I) (hmain : B*C*c*I<k*J) (h₁ : |Q₁-I|≤I) (h₂ : |Q₂-J|≤c*I) :
    A*C*c*Q₁+c*I<k*Q₂ := by
  have hu := (abs_le.mp h₁).2
  have hl := (abs_le.mp h₂).1
  have hq := mul_le_mul_of_nonneg_left hl hk
  have hkb := mul_le_mul_of_nonneg_right hkC (show 0≤c*I by positivity)
  have hbb := mul_le_mul_of_nonneg_right hB (show 0≤C*c*I by positivity)
  have hqu := mul_le_mul_of_nonneg_left hu (show 0≤A*C*c by positivity)
  have hp := mul_le_mul_of_nonneg_right hC (show 0≤c*I by positivity)
  nlinarith

theorem sieve_quadratic_margin (W D M : ℕ) (A B : ℝ) (hW : W≠0) (hM : 0<M)
    (hA : 0≤A) (hB : 2*A+2≤B) (hlarge : 1056*B<M)
    (hD : 8*2^M≤D) (herror : sieveErrorThreshold M≤D)
    (hsmall : ∀ p : ℕ, Nat.Prime p → p≤D → p∣W) :
    ∀ᶠ R : ℕ in atTop, ∀ E : ℕ, (E=1 ∨ Nat.Prime E) → (E=1 ∨ D≤E) →
      let P := sievePrimes W E (R^(2^M))
      A*sieveCutoff M*(roughDensity W*Real.log R)*sieveQuadraticI P M R +
        (roughDensity W*Real.log R)^(sieveDimension M+1)/2^(sieveDimension M+1) <
        (sieveDimension M : ℝ)*sieveQuadraticJ P M R 0 := by
  have hB0 : 0≤B := by linarith
  have hD0 : 0<D := by
    have hh : 0<(2 : ℕ)^M := by positivity
    omega
  filter_upwards [primeSubset_sieve_ratio W D M B hW hD hsmall hM hB0 hlarge,
    subset_dyadicMass_bounds W D M hW hD hsmall,
    harmonicEuler_power_bound W (2^M) hW (by positivity),eventually_ge_atTop 2]
    with R hratio hmass hEuler hR2 E hE hED
  let P := sievePrimes W E (R^(2^M))
  let c : ℝ := roughDensity W*Real.log R
  let g (s : PrimeSubset P) := dyadicStep M (subsetTime R s)
  let I : ℝ := discreteI (sieveDimension M) subsetWeight g (subsetTime R) (sieveCutoff M)
  let J : ℝ := discreteJ (sieveDimension M-1) subsetWeight g (subsetTime R) (sieveCutoff M)
  have hc : 0<c := mul_pos (roughDensity_pos hW) (Real.log_pos (by exact_mod_cast hR2))
  have hm := hmass E hE hED
  have hIlow : c^(sieveDimension M)/2^(sieveDimension M+1)≤I :=
    sieve_discreteI_lower M subsetWeight (subsetTime R) c hM hc subsetWeight_nonneg (subsetTime_nonneg R) hm
  have hIp : 0<I := lt_of_lt_of_le (by positivity) hIlow
  have hPs (p : ℕ) (hp : p∈P) := mem_sievePrimes.mp hp
  have hPD : ∀ p∈P, D<p := by
    intro p hp
    have hh := hPs p hp
    by_contra h
    exact hh.2.2.1 (hsmall p hh.2.1 (by omega))
  have heuler : harmonicEuler P≤(16*(2 : ℝ)^M)*c := by
    have hh := hEuler P (fun p hp => (hPs p hp).2.1)
      (fun p hp => ((hPs p hp).2.1.coprime_iff_not_dvd.mpr (hPs p hp).2.2.1).symm)
      (fun p hp => (hPs p hp).1)
    convert hh using 1 <;> dsimp [c] <;> push_cast <;> ring
  have her := relative_euler_error (sieveDimension M) (H := harmonicEuler P)
    (a := 16*(2 : ℝ)^M) (c := c)
    (K := kernelErrorConstant (sieveDimension M)*Real.exp (kernelErrorConstant (sieveDimension M)))
    (D := (D : ℝ)) (by unfold harmonicEuler; positivity) heuler
    (by have hh : (1 : ℝ)≤2^M := one_le_pow₀ (by norm_num); linarith)
    hc (by unfold kernelErrorConstant; positivity) (by exact_mod_cast hD0) herror
  have h1 := sieveQuadraticI_error P D M R hD0 hPD
  have h2 := sieveQuadraticJ_error P D M R hD0 hPD
  change |sieveQuadraticI P M R-I|≤_ at h1
  change |sieveQuadraticJ P M R 0-J|≤_ at h2
  have h1' : |sieveQuadraticI P M R-I|≤I := by
    refine h1.trans ((le_of_eq ?_).trans (her.1.trans hIlow))
    ring
  have h2' : |sieveQuadraticJ P M R 0-J|≤c*I := by
    refine h2.trans ((le_of_eq ?_).trans (her.2.trans ?_))
    · ring
    · have hh := mul_le_mul_of_nonneg_left hIlow hc.le
      rw [pow_succ]
      convert hh using 1 <;> ring
  have hC : (0 : ℝ)<sieveCutoff M := by exact_mod_cast (sieveCutoff_bounds M hM).1
  have hkC : (sieveDimension M : ℝ)≤sieveCutoff M := by
    have hh : sieveDimension M≤sieveDimension M*M := by nlinarith
    have hn : sieveDimension M≤sieveCutoff M := by
      dsimp [sieveCutoff]
      exact hh.trans ((Nat.mul_le_mul_right M (Nat.le_mul_of_pos_left _ (by decide : 0<32))).trans
        (Nat.le_add_right _ _))
    exact_mod_cast hn
  have hC1 : (1 : ℝ)≤sieveCutoff M := by exact_mod_cast (sieveCutoff_bounds M hM).1
  have hmargin := robust_kernel_margin hA hB hC1 hc (Nat.cast_nonneg _) hkC hIp (hratio E hE hED) h1' h2'
  have hlo := mul_le_mul_of_nonneg_left hIlow hc.le
  have he : c*(c^(sieveDimension M)/2^(sieveDimension M+1))=c^(sieveDimension M+1)/2^(sieveDimension M+1) := by rw [pow_succ]; ring
  rw [he] at hlo
  exact lt_of_le_of_lt (add_le_add_right hlo _) hmargin

end
end MaynardDevelopment
end

/- SieveFiniteEstimates -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

def sieveSupportSet (P : Finset ℕ) (M R : ℕ) : Finset (↥P→Finset (Fin (sieveDimension M))) :=
  Finset.univ.filter (fun r => matrixProduct r≤R^(sieveCutoff M))

def sieveL1Envelope (P : Finset ℕ) (M R : ℕ) : ℝ :=
  (R : ℝ)^(sieveCutoff M)*(1+Real.log (R^(sieveCutoff M) : ℕ))^(2^(sieveDimension M)-1)*harmonicEuler P^(sieveDimension M)

lemma sieveL1Envelope_nonneg (P : Finset ℕ) (M R : ℕ) : 0≤sieveL1Envelope P M R := by
  have hh := Real.log_natCast_nonneg (R^(sieveCutoff M))
  have hH : 0≤harmonicEuler P := by unfold harmonicEuler; positivity
  unfold sieveL1Envelope
  positivity

lemma sieveLambda_l1_bound (P : Finset ℕ) (M R : ℕ) (hP : ∀ p∈P, Nat.Prime p) (hR : 1<R) :
    (∑ r, |sieveLambda P M R r|)≤sieveL1Envelope P M R := by
  have hs : ∀ r, sieveLambda P M R r≠0 → r∈sieveSupportSet P M R := by
    intro r hr
    simp only [sieveSupportSet,Finset.mem_filter,Finset.mem_univ,true_and]
    exact sieveLambda_product_support P M R hP hR r hr
  have hh := coefficient_l1_bound (sieveSupportSet P M R) (sieveLambda P M R) (harmonicEuler P^(sieveDimension M)) hs
    (fun r hr => sieveLambda_bound P M R r)
  have hc := matrixProduct_card_log_bound hP (sieveSupportSet P M R) (R^(sieveCutoff M))
    (by intro r hr; exact (Finset.mem_filter.mp hr).2)
  simp only [Fintype.card_fin,Nat.cast_pow] at hc
  refine hh.trans ?_
  simpa only [sieveL1Envelope,Nat.cast_pow] using mul_le_mul_of_nonneg_right hc (show 0≤harmonicEuler P^(sieveDimension M) by unfold harmonicEuler; positivity)

lemma sieveQuadraticI_coefficients (P : Finset ℕ) (M R : ℕ) (hP : ∀ p∈P, Nat.Prime p)
    (h : Fin (sieveDimension M)→ℕ) (hi : ∀ p : ↥P, Function.Injective (shiftedResidues h p)) :
    sieveQuadraticI P M R=kernelQuadratic (fun p : ↥P => indicatorKernelOne (p.val : ℝ)) (sieveLambda P M R) := by
  letI (p : ↥P) : NeZero p.val := ⟨(hP _ p.property).ne_zero⟩
  exact coefficient_gram_one (shiftedResidues h) hi (fun p => ZMod.card p.val) (fun p => (hP _ p.property).one_lt) _

lemma sieveQuadraticJ_coefficients (P : Finset ℕ) (M R : ℕ) (hP : ∀ p∈P, Nat.Prime p)
    (h : Fin (sieveDimension M)→ℕ) (hi : ∀ p : ↥P, Function.Injective (shiftedResidues h p)) (m : Fin (sieveDimension M)) :
    sieveQuadraticJ P M R m=kernelQuadratic (fun p : ↥P => indicatorKernelTwo (p.val : ℝ) m) (sieveLambda P M R) := by
  letI (p : ↥P) : NeZero p.val := ⟨(hP _ p.property).ne_zero⟩
  exact coefficient_gram_two (shiftedResidues h) hi (fun p => ZMod.card p.val) (fun p => (hP _ p.property).one_lt) _ m

lemma sieve_uniform_finite_error (P : Finset ℕ) (M R W a X : ℕ) (hP : ∀ p∈P, Nat.Prime p)
    (hR : 1<R) (hW0 : W≠0) (hW : ∀ p∈P, W.Coprime p)
    (h : Fin (sieveDimension M)→ℕ) (hi : ∀ p : ↥P, Function.Injective (shiftedResidues h p)) :
    |(∑ n∈Finset.Icc 1 X, (if Nat.ModEq W n a then (1 : ℝ) else 0)*integerSieveWeight (shiftedResidues h) (sieveLambda P M R) n)-
      (X : ℝ)/W*sieveQuadraticI P M R|≤sieveL1Envelope P M R^2 := by
  rw [sieveQuadraticI_coefficients P M R hP h hi]
  exact (integerSieve_uniform_error hP W a X hW0 hW (shiftedResidues h) hi _).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (sieveLambda_l1_bound P M R hP hR) 2)

lemma sieve_prime_finite_error (P : Finset ℕ) (M R W a X Q : ℕ) (hP : ∀ p∈P, Nat.Prime p)
    (hR : 1<R) (hW0 : W≠0) (hW : ∀ p∈P, W.Coprime p)
    (h : Fin (sieveDimension M)→ℕ) (hi : ∀ p : ↥P, Function.Injective (shiftedResidues h p))
    (m : Fin (sieveDimension M)) (hm : W.Coprime (a+h m))
    (hgood : ∀ r s : ↥P→Finset (Fin (sieveDimension M)), GoodModulus Q (W*matrixModulus r s)) :
    |(∑ n∈Finset.Icc 1 X, (if Nat.ModEq W n a then ArithmeticFunction.vonMangoldt (n+h m) else 0)*integerSieveWeight (shiftedResidues h) (sieveLambda P M R) n)-
      (X : ℝ)/W.totient*sieveQuadraticJ P M R m|≤
      harmonicEuler P^(2*sieveDimension M)*weightedProgressionError Q (2*sieveDimension M) (W*(R^(sieveCutoff M))^2) X+
      sieveL1Envelope P M R^2*elementarySieveError (W*(R^(sieveCutoff M))^2) X (h m) := by
  let S := sieveSupportSet P M R
  have hs : ∀ r, sieveLambda P M R r≠0 → r∈S := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ r,sieveLambda_product_support P M R hP hR r hr⟩
  have hS : ∀ r∈S, matrixProduct r≤R^(sieveCutoff M) := by intro r hr; exact (Finset.mem_filter.mp hr).2
  have hD : ∀ r∈S, ∀ s∈S, W*matrixModulus r s≤W*(R^(sieveCutoff M))^2 := by
    intro r hr s hs'
    apply Nat.mul_le_mul_left
    exact (matrixModulus_le_product (fun p hp => (hP p hp).one_le) r s).trans (by
      rw [pow_two]; exact Nat.mul_le_mul (hS r hr) (hS s hs'))
  rw [sieveQuadraticJ_coefficients P M R hP h hi m]
  have hh := integerSieve_prime_error hP W a X (W*(R^(sieveCutoff M))^2) Q hW0 hW h hi m hm
    (sieveLambda P M R) S hs hD (fun r hr s hs' => hgood r s)
  refine hh.trans (add_le_add ?_ ?_)
  · have hf (q : ℕ) : 0 ≤ if GoodModulus Q q then progressionWorst q X else 0 := by split_ifs; exact progressionWorst_nonneg _ _; exact le_rfl
    have hgroup := coefficient_pair_error_bound hP S (R^(sieveCutoff M)) W (Nat.pos_of_ne_zero hW0) hS
      (sieveLambda P M R) (harmonicEuler P^(sieveDimension M)) (by unfold harmonicEuler; positivity)
      (fun r hr => sieveLambda_bound P M R r) _ hf
    simpa only [Fintype.card_fin,← pow_mul,mul_comm (sieveDimension M) 2,weightedProgressionError] using hgroup
  · apply mul_le_mul_of_nonneg_right _ (elementarySieveError_nonneg _ _ _)
    apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun r _ _ => abs_nonneg _)).trans ?_
    exact sieveLambda_l1_bound P M R hP hR

end
end MaynardDevelopment
end

/- SieveGrowth -/
section

open scoped BigOperators Topology
open Filter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma eventually_log_monomial_le_nat (K : ℝ) (e : ℕ) (hK : 0≤K) :
    ∀ᶠ R : ℕ in atTop, K*(1+Real.log R)^e≤R := by
  have hh := (Real.isLittleO_pow_log_id_atTop (n := e)).bound (show (0 : ℝ)<1/(K*2^e+1) by positivity)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hh,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1] with R hR hlog
  simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg R) _),
    id_eq,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) R)] at hR
  dsimp only [Function.comp_def] at hlog
  have hpow : (1+Real.log R)^e≤(2*Real.log R)^e := pow_le_pow_left₀ (by linarith) (by linarith) _
  rw [mul_pow] at hpow
  have hlarge := (le_div_iff₀ (show (0 : ℝ)<K*2^e+1 by positivity)).mp
    (show (Real.log R)^e≤(R : ℝ)/(K*2^e+1) by simpa [div_eq_mul_inv,mul_comm] using hR)
  have hm := mul_le_mul_of_nonneg_left hpow hK
  nlinarith [pow_nonneg (Real.log_natCast_nonneg R) e]

lemma eventually_power_log_monomial_le (K : ℝ) (a b e : ℕ) (hK : 0≤K) (hab : a<b) :
    ∀ᶠ R : ℕ in atTop, K*(R : ℝ)^a*(1+Real.log R)^e≤(R : ℝ)^b := by
  filter_upwards [eventually_log_monomial_le_nat K e hK,eventually_ge_atTop 1] with R hR hR1
  have hh := mul_le_mul_of_nonneg_left hR (pow_nonneg (Nat.cast_nonneg R) a)
  calc
    _ ≤ (R : ℝ)^a*R := by nlinarith
    _ = (R : ℝ)^(a+1) := (pow_succ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast hR1) hab

lemma log_nat_power_shift_bound (d h : ℕ) (hd : 0<d) :
    ∀ᶠ R : ℕ in atTop, Real.log (R^d+h+1 : ℕ)≤(d+1 : ℝ)*Real.log R := by
  filter_upwards [eventually_ge_atTop (h+1),eventually_ge_atTop 2] with R hRh hR2
  have hRpow : R≤R^d := Nat.le_self_pow (by omega) _
  have hle : R^d+h+1≤R^(d+1) := by
    rw [pow_succ]
    have hp : 1≤R^d := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hl := Real.log_le_log (show (0 : ℝ)<(R^d+h+1 : ℕ) by positivity) (show ((R^d+h+1 : ℕ) : ℝ)≤(R^(d+1) : ℕ) by exact_mod_cast hle)
  simpa only [Nat.cast_pow,Real.log_pow,Nat.cast_add,Nat.cast_one] using hl

lemma modulus_power_eventually (W C : ℕ) (hC : 0<C) :
    ∀ᶠ R : ℕ in atTop, (W*(R^C)^2+1)^22≤R^(100*C) := by
  filter_upwards [eventually_ge_atTop (W+1),eventually_ge_atTop 2] with R hRW hR
  have hRC : R≤R^C := Nat.le_self_pow (by omega) _
  have hp : 1≤(R^C)^2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by omega))
  have hm : W*(R^C)^2+1≤R^(3*C) := by
    have he : R^(3*C)=(R^C)^2*R^C := by rw [show 3*C=C*2+C by omega,pow_add,pow_mul]
    rw [he]
    nlinarith
  calc
    _ ≤ (R^(3*C))^22 := Nat.pow_le_pow_left hm _
    _ = R^(66*C) := by rw [← pow_mul]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

lemma nat_power_tendsto (d : ℕ) (hd : 0<d) : Tendsto (fun R : ℕ => R^d) atTop atTop := by
  apply tendsto_atTop_mono (f := fun R : ℕ => R) (fun R => Nat.le_self_pow (by omega) R) tendsto_id

lemma sqrt_power_shift_bound (C h : ℕ) (hC : 0<C) :
    ∀ᶠ R : ℕ in atTop, (Nat.sqrt (R^(100*C)+h)+1 : ℝ)≤3*(R : ℝ)^(50*C) := by
  filter_upwards [eventually_ge_atTop (h+1),eventually_ge_atTop 2] with R hRh hR2
  have hRpow : R≤R^(100*C) := Nat.le_self_pow (by omega) _
  have hp : 1≤R^(50*C) := Nat.one_le_pow _ _ (by omega)
  have he : R^(100*C)=(R^(50*C))^2 := by rw [← pow_mul]; congr 1; omega
  have hs := Nat.sqrt_le (R^(100*C)+h)
  have hbound : Nat.sqrt (R^(100*C)+h)+1≤3*R^(50*C) := by
    rw [he] at hs hRpow ⊢
    nlinarith
  exact_mod_cast hbound

end
end MaynardDevelopment
end

/- SieveErrorGrowth -/
section

open scoped BigOperators Topology
open Filter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma sieveL1Envelope_eventually_power (M : ℕ) (K : ℝ) (hK : 0≤K) (hC : 1≤sieveCutoff M) :
    ∀ᶠ R : ℕ in atTop, ∀ P : Finset ℕ, harmonicEuler P≤K*(1+Real.log R) →
      sieveL1Envelope P M R≤(R : ℝ)^(2*sieveCutoff M) := by
  let C := sieveCutoff M
  let k := sieveDimension M
  let e := 2^k-1
  have hconst : 0≤((C : ℝ)+1)^e*K^k := by positivity
  filter_upwards [eventually_power_log_monomial_le (((C : ℝ)+1)^e*K^k) C (2*C) (e+k) hconst (by omega)] with R hR P hP
  have hH : 0≤harmonicEuler P := by unfold harmonicEuler; positivity
  have hL : 0≤1+Real.log R := by linarith [Real.log_natCast_nonneg R]
  have hlog : 1+Real.log (R^C : ℕ)≤((C : ℝ)+1)*(1+Real.log R) := by
    rw [Nat.cast_pow,Real.log_pow]
    nlinarith [Real.log_natCast_nonneg R,Nat.cast_nonneg (α := ℝ) C]
  have he : sieveL1Envelope P M R≤((C : ℝ)+1)^e*K^k*(R : ℝ)^C*(1+Real.log R)^(e+k) := by
    unfold sieveL1Envelope
    change (R : ℝ)^C*(1+Real.log (R^C : ℕ))^e*harmonicEuler P^k≤_
    calc
      _ ≤ (R : ℝ)^C*(((C : ℝ)+1)*(1+Real.log R))^e*(K*(1+Real.log R))^k := by
        gcongr
      _ = _ := by rw [mul_pow,mul_pow,pow_add]; ring
  exact he.trans hR

lemma elementarySieveError_eventually_power (W C h : ℕ) (hC : 0<C) :
    ∀ᶠ R : ℕ in atTop, elementarySieveError (W*(R^C)^2) (R^(100*C)) h≤(R : ℝ)^(3*C) := by
  let d := 100*C
  let A : ℝ := d+1
  let B : ℝ := 2*A+1
  let K : ℝ := (W+1 : ℝ)*B*A+2*h*A
  have hA : 0≤A := by dsimp [A]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hK : 0≤K := by dsimp [K]; positivity
  filter_upwards [log_nat_power_shift_bound d h (by dsimp [d]; omega),
    eventually_power_log_monomial_le K (2*C) (3*C) 2 hK (by omega),eventually_ge_atTop 1]
    with R hlog hR hR1
  let L : ℝ := 1+Real.log R
  have hL : 1≤L := by dsimp [L]; linarith [Real.log_natCast_nonneg R]
  have hRN : (1 : ℝ)≤R := by exact_mod_cast hR1
  have hpow : (1 : ℝ)≤R^(2*C) := one_le_pow₀ hRN
  have hl : 0≤Real.log (R^d+h+1 : ℕ) := Real.log_natCast_nonneg _
  have hlog' : Real.log (R^d+h+1 : ℕ)≤A*L := hlog.trans (mul_le_mul_of_nonneg_left (by dsimp [L]; linarith) hA)
  have hn : (Nat.log 2 (R^d+h)+1 : ℝ)≤B*L := by
    have hh := natural_log_two_bound (R^d+h)
    have hh' : Real.log ((R^d+h : ℕ)+1 : ℝ)=Real.log (R^d+h+1 : ℕ) := by push_cast; rfl
    rw [hh'] at hh
    dsimp [B]
    nlinarith
  have hD : (W*(R^C)^2+1 : ℝ)≤(W+1 : ℝ)*(R : ℝ)^(2*C) := by
    have he : ((R : ℝ)^C)^2=(R : ℝ)^(2*C) := by rw [← pow_mul]; congr 1; omega
    rw [he]
    nlinarith
  have helem : elementarySieveError (W*(R^C)^2) (R^d) h≤K*(R : ℝ)^(2*C)*L^2 := by
    have hlogR : Real.log ((R^d : ℕ)+h+1 : ℝ)=Real.log (R^d+h+1 : ℕ) := by push_cast; rfl
    unfold elementarySieveError
    rw [hlogR]
    have hD' : ((W*(R^C)^2 : ℕ)+1 : ℝ)≤(W+1 : ℝ)*(R : ℝ)^(2*C) := by simpa only [Nat.cast_mul,Nat.cast_pow] using hD
    calc
      _ ≤ ((W+1 : ℝ)*(R : ℝ)^(2*C))*(B*L)*(A*L)+2*h*(A*L) := by gcongr
      _ ≤ K*(R : ℝ)^(2*C)*L^2 := by
        have hx : L≤(R : ℝ)^(2*C)*L^2 := by nlinarith [sq_nonneg (L-1)]
        have hh := mul_le_mul_of_nonneg_left hx (show 0≤2*(h : ℝ)*A by positivity)
        dsimp [K]
        nlinarith
  exact helem.trans hR

lemma nonprimeError_eventually_power (C h : ℕ) (hC : 0<C) :
    ∀ᶠ R : ℕ in atTop,
      (Nat.sqrt (R^(100*C)+h)+1 : ℝ)*(Nat.log 2 (R^(100*C)+h)+1 : ℝ)*Real.log (R^(100*C)+h+1 : ℝ)≤(R : ℝ)^(51*C) := by
  let d := 100*C
  let A : ℝ := d+1
  let B : ℝ := 2*A+1
  have hA : 0≤A := by dsimp [A]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  filter_upwards [log_nat_power_shift_bound d h (by dsimp [d]; omega),sqrt_power_shift_bound C h hC,
    eventually_power_log_monomial_le (3*B*A) (50*C) (51*C) 2 (by positivity) (by omega)] with R hlog hs hR
  let L : ℝ := 1+Real.log R
  have hL : 1≤L := by dsimp [L]; linarith [Real.log_natCast_nonneg R]
  have hlog' : Real.log (R^d+h+1 : ℕ)≤A*L := hlog.trans (mul_le_mul_of_nonneg_left (by dsimp [L]; linarith) hA)
  have hn : (Nat.log 2 (R^d+h)+1 : ℝ)≤B*L := by
    have hh := natural_log_two_bound (R^d+h)
    have hh' : Real.log ((R^d+h : ℕ)+1 : ℝ)=Real.log (R^d+h+1 : ℕ) := by push_cast; rfl
    rw [hh'] at hh
    dsimp [B]
    nlinarith
  have hlogR : Real.log ((R^d : ℕ)+h+1 : ℝ)=Real.log (R^d+h+1 : ℕ) := by push_cast; rfl
  rw [show 100*C=d from rfl]
  simp only [Nat.cast_pow] at hlogR
  rw [hlogR]
  calc
    _ ≤ (3*(R : ℝ)^(50*C))*(B*L)*(A*L) := by gcongr
    _ = (3*B*A)*(R : ℝ)^(50*C)*L^2 := by ring
    _ ≤ _ := hR

end
end MaynardDevelopment
end

/- SieveDistributionGrowth -/
section

open scoped BigOperators Topology
open Filter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

def sieveDistributionExponent (k : ℕ) : ℕ := 2*(2*k+1)+2^(4*k)+1

def sieveDistributionLevel (k X : ℕ) : ℕ := conductorCutoff (sieveDistributionExponent k) X

lemma weightedSieveError_eventually (W C k : ℕ) (K : ℝ) (hC : 0<C) (hK : 0≤K) :
    ∀ᶠ R : ℕ in atTop, ∀ H : ℝ, 0≤H → H≤K*Real.log R →
      H^(2*k)*weightedProgressionError (sieveDistributionLevel k (R^(100*C))) (2*k) (W*(R^C)^2) (R^(100*C))≤(R : ℝ)^(100*C) := by
  let A := 2*k+1
  let B : ℝ := 480000000*2^(2^(2*(2*k)))+1
  have hB : 0≤B := by dsimp [B]; positivity
  have hconst : 0≤K^(2*k)*B := by positivity
  have hdist := (nat_power_tendsto (100*C) (by omega)).eventually (weightedProgressionError_log_saving (2*k) A)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (max 1 (K^(2*k)*B))
  filter_upwards [hdist,modulus_power_eventually W C hC,hlog] with R hdist hmod hlog H hH hHK
  dsimp only [Function.comp_def] at hlog
  have hL : 1≤Real.log R := le_trans (le_max_left _ _) hlog
  have hL0 : 0<Real.log R := by linarith
  have hKB : K^(2*k)*B≤Real.log R := le_trans (le_max_right _ _) hlog
  have hbound := hdist (W*(R^C)^2) hmod
  have hcut : 2*A+2^(2*(2*k))+1=sieveDistributionExponent k := by dsimp [A,sieveDistributionExponent]; rw [show 2*(2*k)=4*k by omega]
  rw [hcut] at hbound
  change weightedProgressionError (sieveDistributionLevel k (R^(100*C))) (2*k) (W*(R^C)^2) (R^(100*C))≤B*(R^(100*C) : ℕ)/(Real.log (R^(100*C) : ℕ))^A at hbound
  have hlogX : Real.log (R^(100*C) : ℕ)=(100*C : ℕ)*Real.log R := by rw [Nat.cast_pow,Real.log_pow]
  have hlogle : Real.log R≤Real.log (R^(100*C) : ℕ) := by
    rw [hlogX]
    have hh : (1 : ℝ)≤(100*C : ℕ) := by exact_mod_cast (show 1≤100*C by omega)
    nlinarith
  have hden : (Real.log R)^A≤(Real.log (R^(100*C) : ℕ))^A := pow_le_pow_left₀ hL0.le hlogle _
  have he : B*(R^(100*C) : ℕ)/(Real.log (R^(100*C) : ℕ))^A≤B*(R : ℝ)^(100*C)/(Real.log R)^A := by
    simp only [Nat.cast_pow] at hden ⊢
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hL0 _) hden
  have hp := mul_le_mul (pow_le_pow_left₀ hH hHK _) (hbound.trans he)
    (weightedProgressionError_nonneg _ _ _ _) (by positivity : 0≤(K*Real.log R)^(2*k))
  refine hp.trans ?_
  have heq : (K*Real.log R)^(2*k)*(B*(R : ℝ)^(100*C)/(Real.log R)^A)=
      (K^(2*k)*B/Real.log R)*(R : ℝ)^(100*C) := by
    dsimp [A]
    rw [mul_pow,pow_succ]
    field_simp
  rw [heq]
  exact mul_le_of_le_one_left (pow_nonneg (Nat.cast_nonneg R) _) ((div_le_one hL0).mpr hKB)

lemma shiftLog_eventually_power (C h : ℕ) (hC : 0<C) :
    ∀ᶠ R : ℕ in atTop, Real.log (R^(100*C)+h+1 : ℝ)≤(R : ℝ)^C := by
  filter_upwards [log_nat_power_shift_bound (100*C) h (by omega),
    eventually_power_log_monomial_le (100*C+1 : ℕ) 0 C 1 (by positivity) hC] with R hlog hpow
  simp only [pow_zero,one_mul,mul_one,pow_one] at hpow
  have hlog' : Real.log (R^(100*C)+h+1 : ℝ)≤(100*C+1 : ℕ)*(1+Real.log R) := by
    have hh := hlog.trans (mul_le_mul_of_nonneg_left (show Real.log R≤1+Real.log R by linarith) (show (0 : ℝ)≤(100*C : ℕ)+1 by positivity))
    simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat] using hh
  exact hlog'.trans hpow

end
end MaynardDevelopment
end

/- SievePresieving -/
section

open scoped BigOperators Topology
open Filter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma extend_presieving_progression {ι : Type*} [Fintype ι] (h : ι→ℕ)
    (hadm : ∀ p : ℕ, Nat.Prime p → ∃ a : ℕ, ∀ i, ¬p∣a+h i)
    (W₀ a₀ D : ℕ) (hW₀ : W₀≠0) (ha₀ : ∀ i, W₀.Coprime (a₀+h i)) :
    ∃ W a : ℕ, W≠0 ∧ W₀∣W ∧ Nat.ModEq W₀ a a₀ ∧ (∀ i, W.Coprime (a+h i)) ∧
      (∀ p : ℕ, Nat.Prime p → p≤D → p∣W) := by
  let P := sievePrimes W₀ 1 D
  have hP (p : ℕ) (hp : p∈P) := mem_sievePrimes.mp hp
  let residues (p : ℕ) : ℕ := if hp : Nat.Prime p then Classical.choose (hadm p hp) else 0
  have hr (p : ℕ) (hp : Nat.Prime p) (i : ι) : ¬p∣residues p+h i := by
    dsimp [residues]
    rw [dif_pos hp]
    exact Classical.choose_spec (hadm p hp) i
  let Q := ∏ p∈P, p
  have hQ0 : Q≠0 := (Finset.prod_pos (fun p hp => (hP p hp).2.1.pos)).ne'
  have hco : W₀.Coprime Q := Nat.Coprime.prod_right (fun p hp => ((hP p hp).2.1.coprime_iff_not_dvd.mpr (hP p hp).2.2.1).symm)
  obtain ⟨b,hb⟩ := Nat.chineseRemainderOfFinset residues id P
    (fun p hp => (hP p hp).2.1.ne_zero)
    (fun p hp q hq hpq => (Nat.coprime_primes (hP p hp).2.1 (hP q hq).2.1).mpr hpq)
  obtain ⟨a,ha⟩ := Nat.chineseRemainder hco a₀ b
  refine ⟨W₀*Q,a,Nat.mul_ne_zero hW₀ hQ0,dvd_mul_right _ _,ha.1,?_,?_⟩
  · intro i
    apply Nat.Coprime.mul_left
    · exact ((modEq_coprime_iff (ha.1.add_right (h i))).mpr (ha₀ i).symm).symm
    · apply Nat.Coprime.prod_left
      intro p hp
      apply (hP p hp).2.1.coprime_iff_not_dvd.mpr
      intro hd
      have hpa : Nat.ModEq p a (residues p) := (ha.2.of_dvd (Finset.dvd_prod_of_mem id hp)).trans (hb p hp)
      have hz : Nat.ModEq p (residues p+h i) 0 := (hpa.add_right (h i)).symm.trans (Nat.modEq_zero_iff_dvd.mpr hd)
      exact hr p (hP p hp).2.1 i (Nat.modEq_zero_iff_dvd.mp hz)
  · intro p hp hpD
    by_cases hpd : p∣W₀
    · exact dvd_mul_of_dvd_left hpd Q
    · have hpP : p∈P := mem_sievePrimes.mpr ⟨hpD,hp,hpd,hp.ne_one⟩
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id hpP) W₀

lemma sievePrimes_shift_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι→ℕ) (hi : Function.Injective h) (W E N D : ℕ)
    (hD : ∀ i, h i≤D) (hsmall : ∀ p, Nat.Prime p → p≤D → p∣W) :
    ∀ p : ↥(sievePrimes W E N), Function.Injective (shiftedResidues h p) := by
  intro p i j hij
  have hp := mem_sievePrimes.mp p.property
  have hDp : D<p.val := by by_contra hh; exact hp.2.2.1 (hsmall _ hp.2.1 (by omega))
  apply hi
  apply Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff (h i) (h j) p.val).mp (neg_injective hij))
  · exact (hD i).trans_lt hDp
  · exact (hD j).trans_lt hDp

lemma sievePrimes_good_modulus {ι : Type*} [Fintype ι] [DecidableEq ι] (W N Q : ℕ)
    (hW : W≠0) (hE : exceptionPrime Q=1 ∨ W<exceptionPrime Q)
    (r s : ↥(sievePrimes W (exceptionPrime Q) N)→Finset ι) :
    GoodModulus Q (W*matrixModulus r s) := by
  rcases hE with he | he
  · exact Or.inl he
  · rcases exceptionPrime_eq_one_or_prime Q with h1 | hp
    · exact Or.inl h1
    · right
      intro hd
      rcases hp.dvd_mul.mp hd with hdW | hdM
      · exact (not_le_of_gt he) (Nat.le_of_dvd (Nat.pos_of_ne_zero hW) hdW)
      · obtain ⟨p,hp',hdiv⟩ := (hp.prime.dvd_finset_prod_iff (fun p => if (r p).Nonempty ∨ (s p).Nonempty then p.val else 1)).mp hdM
        by_cases hn : (r p).Nonempty ∨ (s p).Nonempty
        · rw [if_pos hn] at hdiv
          have hpp := mem_sievePrimes.mp p.property
          exact hpp.2.2.2 ((Nat.prime_dvd_prime_iff_eq hp hpp.2.1).mp hdiv).symm
        · rw [if_neg hn] at hdiv
          exact hp.not_dvd_one hdiv

end
end MaynardDevelopment
end

/- WeightedPrimeDetection -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def shiftedPrimeCount (h : ι→ℕ) (n : ℕ) : ℕ := (Finset.univ.filter (fun i => Nat.Prime (n+h i))).card

lemma shiftedPrimeCount_le (h : ι→ℕ) (n : ℕ) : shiftedPrimeCount h n ≤ Fintype.card ι := Finset.card_filter_le _ _

lemma vonMangoldt_sum_primeCount_bound (h : ι→ℕ) (n H X : ℕ) (hn : n∈Finset.Icc 1 X) (hH : ∀ i, h i ≤ H) :
    (∑ i, ArithmeticFunction.vonMangoldt (n+h i)) ≤ 
      Real.log (X+H+1 : ℝ)*shiftedPrimeCount h n+
        ∑ i, if ¬Nat.Prime (n+h i) then ArithmeticFunction.vonMangoldt (n+h i) else 0 := by
  have he : Real.log (X+H+1 : ℝ)*shiftedPrimeCount h n=
      ∑ i, if Nat.Prime (n+h i) then Real.log (X+H+1 : ℝ) else 0 := by
    simp [shiftedPrimeCount,Finset.sum_ite,mul_comm]
  rw [he,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hp : Nat.Prime (n+h i)
  · simp only [hp,not_true_eq_false,if_true,if_false,add_zero]
    refine (le_abs_self _).trans ?_
    simpa only [Nat.cast_add] using vonMangoldt_interval_bound (n+h i) (X+H)
      (Finset.mem_Icc.mpr (by have hh := Finset.mem_Icc.mp hn; have hh' := hH i; omega))
  · simp [hp]

lemma weighted_nonprime_sum_bound (h X : ℕ) (w : ℕ→ℝ) (V : ℝ) (hw : ∀ n∈Finset.Icc 1 X, w n ≤ V)
    (hV : 0 ≤ V) :
    (∑ n∈Finset.Icc 1 X, w n*(if ¬Nat.Prime (n+h) then ArithmeticFunction.vonMangoldt (n+h) else 0)) ≤ 
      V*((Nat.sqrt (X+h)+1 : ℝ)*(Nat.log 2 (X+h)+1 : ℝ)*Real.log (X+h+1 : ℝ)) := by
  calc
    _  ≤  ∑ n∈Finset.Icc 1 X, V*(if ¬Nat.Prime (n+h) then ArithmeticFunction.vonMangoldt (n+h) else 0) := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_right (hw n hn)
      split_ifs  <;> first | exact ArithmeticFunction.vonMangoldt_nonneg | exact le_rfl
    _ = V*(∑ n∈Finset.Icc 1 X, if ¬Nat.Prime (n+h) then ArithmeticFunction.vonMangoldt (n+h) else 0) := by rw [Finset.mul_sum]
    _  ≤  _ := mul_le_mul_of_nonneg_left (shifted_nonprime_sum_bound X h) hV

lemma weighted_prime_detection_bound (h : ι→ℕ) (H X N m : ℕ) (hH : ∀ i, h i ≤ H)
    (w : ℕ→ℝ) (V : ℝ) (hV : 0 ≤ V) (hw : ∀ n∈Finset.Icc 1 X, 0 ≤ w n ∧ w n ≤ V)
    (hc : ∀ n∈Finset.Icc 1 X, N  ≤  n → w n ≠ 0 → shiftedPrimeCount h n ≤ m)
    (hbad : ∀ i, (∑ n∈Finset.Icc 1 X, w n*(if ¬Nat.Prime (n+h i) then ArithmeticFunction.vonMangoldt (n+h i) else 0)) ≤ X) :
    (∑ i, ∑ n∈Finset.Icc 1 X, w n*ArithmeticFunction.vonMangoldt (n+h i)) ≤ 
      (m : ℝ)*Real.log (X+H+1 : ℝ)*(∑ n∈Finset.Icc 1 X, w n)+
      (Fintype.card ι : ℝ)*X+(N : ℝ)*(Fintype.card ι : ℝ)*Real.log (X+H+1 : ℝ)*V := by
  let L := Real.log (X+H+1 : ℝ)
  let k : ℝ := Fintype.card ι
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X,Nat.cast_nonneg (α := ℝ) H])
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hpoint (n : ℕ) (hn : n∈Finset.Icc 1 X) :
      w n*(∑ i, ArithmeticFunction.vonMangoldt (n+h i)) ≤ 
        (m : ℝ)*L*w n+(∑ i, w n*(if ¬Nat.Prime (n+h i) then ArithmeticFunction.vonMangoldt (n+h i) else 0))+
        (if n < N then k*L*V else 0) := by
    have hwn := (hw n hn).1
    have hh := mul_le_mul_of_nonneg_left (vonMangoldt_sum_primeCount_bound h n H X hn hH) (hw n hn).1
    have hcount : w n*L*(shiftedPrimeCount h n : ℝ) ≤ (m : ℝ)*L*w n+(if n < N then k*L*V else 0) := by
      by_cases hnN : n < N
      · rw [if_pos hnN]
        have hcnt : (shiftedPrimeCount h n : ℝ) ≤ k := by dsimp [k]; exact_mod_cast shiftedPrimeCount_le h n
        have h1 := mul_le_mul_of_nonneg_left hcnt (show 0 ≤ w n*L by positivity)
        have h2 := mul_le_mul_of_nonneg_left (hw n hn).2 (show 0 ≤ k*L by positivity)
        have h3 : 0 ≤ (m : ℝ)*L*w n := by positivity
        nlinarith
      · rw [if_neg hnN,add_zero]
        by_cases hw0 : w n=0
        · simp [hw0]
        · have hcnt : (shiftedPrimeCount h n : ℝ) ≤ m := by exact_mod_cast hc n hn (by omega) hw0
          have hh := mul_le_mul_of_nonneg_left hcnt (show 0 ≤ w n*L by positivity)
          nlinarith
    rw [mul_add] at hh
    simp only [Finset.mul_sum] at hh ⊢
    dsimp only [L] at hcount ⊢
    nlinarith
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib] at hsum
  have htotal : (∑ n∈Finset.Icc 1 X, w n*(∑ i, ArithmeticFunction.vonMangoldt (n+h i)))=
      ∑ i, ∑ n∈Finset.Icc 1 X, w n*ArithmeticFunction.vonMangoldt (n+h i) := by
    simp only [Finset.mul_sum]; rw [Finset.sum_comm]
  have hbad' : (∑ n∈Finset.Icc 1 X, ∑ i, w n*(if ¬Nat.Prime (n+h i) then ArithmeticFunction.vonMangoldt (n+h i) else 0)) ≤ k*X := by
    rw [Finset.sum_comm]
    calc
      _  ≤  ∑ i : ι, (X : ℝ) := Finset.sum_le_sum (fun i hi => hbad i)
      _ = _ := by simp [k]
  have hsmall : (∑ n∈Finset.Icc 1 X, if n < N then k*L*V else 0) ≤ (N : ℝ)*k*L*V := by
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    have hcard : ((Finset.Icc 1 X).filter (fun n => n < N)).card ≤ N := by
      calc
        _  ≤  (Finset.range N).card := Finset.card_le_card (by intro n hn; exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2)
        _ = _ := Finset.card_range N
    have hh := mul_le_mul_of_nonneg_right (show (((Finset.Icc 1 X).filter (fun n => n < N)).card : ℝ) ≤ N by exact_mod_cast hcard)
      (show 0 ≤ k*L*V by positivity)
    nlinarith
  rw [htotal,← Finset.mul_sum] at hsum
  change _ ≤ (m : ℝ)*L*(∑ n∈Finset.Icc 1 X, w n)+k*X+(N : ℝ)*k*L*V
  linarith

end
end MaynardDevelopment
end

/- SieveActualWeights -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

def actualSieveWeight (P : Finset ℕ) (M R W a : ℕ) (h : Fin (sieveDimension M)→ℕ) (n : ℕ) : ℝ :=
  if Nat.ModEq W n a then integerSieveWeight (shiftedResidues h) (sieveLambda P M R) n else 0

def actualSieveSum (P : Finset ℕ) (M R W a X : ℕ) (h : Fin (sieveDimension M)→ℕ) : ℝ :=
  ∑ n∈Finset.Icc 1 X, actualSieveWeight P M R W a h n

def actualPrimeSum (P : Finset ℕ) (M R W a X : ℕ) (h : Fin (sieveDimension M)→ℕ) (i : Fin (sieveDimension M)) : ℝ :=
  ∑ n∈Finset.Icc 1 X, actualSieveWeight P M R W a h n*ArithmeticFunction.vonMangoldt (n+h i)

lemma actualSieveWeight_nonneg (P : Finset ℕ) (M R W a : ℕ) (h : Fin (sieveDimension M)→ℕ) (n : ℕ) :
    0≤actualSieveWeight P M R W a h n := by
  unfold actualSieveWeight
  split_ifs
  · exact (integerSieveWeight_bound _ _ _).1
  · exact le_rfl

lemma actualSieveWeight_bound (P : Finset ℕ) (M R W a : ℕ) (h : Fin (sieveDimension M)→ℕ)
    (hP : ∀ p∈P, Nat.Prime p) (hR : 1<R) (n : ℕ) :
    actualSieveWeight P M R W a h n≤sieveL1Envelope P M R^2 := by
  unfold actualSieveWeight
  split_ifs
  · exact (integerSieveWeight_bound _ _ _).2.trans (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (sieveLambda_l1_bound P M R hP hR) 2)
  · exact sq_nonneg _

lemma actualSieveSum_nonneg (P : Finset ℕ) (M R W a X : ℕ) (h : Fin (sieveDimension M)→ℕ) :
    0≤actualSieveSum P M R W a X h := Finset.sum_nonneg (fun n hn => actualSieveWeight_nonneg P M R W a h n)

lemma actualSieveSum_error (P : Finset ℕ) (M R W a X : ℕ) (hP : ∀ p∈P, Nat.Prime p)
    (hR : 1<R) (hW0 : W≠0) (hW : ∀ p∈P, W.Coprime p)
    (h : Fin (sieveDimension M)→ℕ) (hi : ∀ p : ↥P, Function.Injective (shiftedResidues h p)) :
    |actualSieveSum P M R W a X h-(X : ℝ)/W*sieveQuadraticI P M R|≤sieveL1Envelope P M R^2 := by
  simpa only [actualSieveSum,actualSieveWeight,ite_mul,one_mul,zero_mul] using sieve_uniform_finite_error P M R W a X hP hR hW0 hW h hi

lemma actualPrimeSum_error (P : Finset ℕ) (M R W a X Q : ℕ) (hP : ∀ p∈P, Nat.Prime p)
    (hR : 1<R) (hW0 : W≠0) (hW : ∀ p∈P, W.Coprime p)
    (h : Fin (sieveDimension M)→ℕ) (hi : ∀ p : ↥P, Function.Injective (shiftedResidues h p))
    (m : Fin (sieveDimension M)) (hm : W.Coprime (a+h m))
    (hgood : ∀ r s : ↥P→Finset (Fin (sieveDimension M)), GoodModulus Q (W*matrixModulus r s)) :
    |actualPrimeSum P M R W a X h m-(X : ℝ)/W.totient*sieveQuadraticJ P M R m|≤
      harmonicEuler P^(2*sieveDimension M)*weightedProgressionError Q (2*sieveDimension M) (W*(R^(sieveCutoff M))^2) X+
      sieveL1Envelope P M R^2*elementarySieveError (W*(R^(sieveCutoff M))^2) X (h m) := by
  simpa only [actualPrimeSum,actualSieveWeight,ite_mul,mul_ite,zero_mul,mul_zero,mul_comm] using sieve_prime_finite_error P M R W a X Q hP hR hW0 hW h hi m hm hgood

end
end MaynardDevelopment
end

/- SieveFinalAlgebra -/
section

open scoped BigOperators Topology
open Filter
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma sieve_margin_eventually_large (W M : ℕ) (Z : ℝ) (hW : W≠0) (hZ : 0≤Z) :
    ∀ᶠ R : ℕ in atTop, Z < (roughDensity W*Real.log R)^(sieveDimension M+1)/2^(sieveDimension M+1)/(W.totient : ℝ) := by
  have ht := Filter.Tendsto.const_mul_atTop (roughDensity_pos hW)
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have htphi : (0 : ℝ)<W.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW)
  filter_upwards [ht.eventually_ge_atTop (max 1 (Z*(W.totient : ℝ)*2^(sieveDimension M+1)+1))] with R hR
  dsimp only [Function.comp_def] at hR
  have h1 : 1≤roughDensity W*Real.log R := (le_max_left _ _).trans hR
  have h2 : Z*(W.totient : ℝ)*2^(sieveDimension M+1)<roughDensity W*Real.log R := by
    have hh := (le_max_right _ _).trans hR
    linarith
  have hpow : roughDensity W*Real.log R≤(roughDensity W*Real.log R)^(sieveDimension M+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ h1 (show 1≤sieveDimension M+1 by omega)
  apply (lt_div_iff₀ htphi).mpr
  apply (lt_div_iff₀ (by positivity)).mpr
  exact h2.trans_le hpow

lemma sieve_main_transfer {S₁ S₂ main₁ main₂ B V k X : ℝ}
    (hB : 0≤B) (hX : 0<X) (hk : 0≤k)
    (hmain : B*main₁+(4*k+4)*X< main₂)
    (h₁ : |S₁-main₁|≤V) (h₂ : |S₂-main₂|≤2*k*X) (hV : B*V≤X) :
    B*S₁+(k+1)*X<S₂ := by
  have h1 := mul_le_mul_of_nonneg_left (abs_le.mp h₁).2 hB
  have h2 := (abs_le.mp h₂).1
  nlinarith

lemma sum_prime_error {k : ℕ} (f g : Fin k→ℝ) (X : ℝ) (hh : ∀ i, |f i-g i|≤2*X) :
    |(∑ i, f i)-(∑ i, g i)|≤2*k*X := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ i : Fin k, 2*X := Finset.sum_le_sum (fun i hi => hh i)
    _ = _ := by simp; ring

end
end MaynardDevelopment
end

/- PresievedPrimeTuples -/
section

open scoped BigOperators Topology
open Filter
set_option maxHeartbeats 4000000
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

lemma presieved_many_primes (m M W a D N : ℕ) (hM : 0<M) (hW0 : W≠0)
    (hlarge : 1056*(400*(m+1 : ℝ)+2)<M)
    (hD : 8*2^M≤D) (herror : sieveErrorThreshold M≤D)
    (hsmall : ∀ p, Nat.Prime p → p≤D → p∣W)
    (h : Fin (sieveDimension M)→ℕ) (hi : Function.Injective h)
    (hH : ∀ i, h i≤D) (ha : ∀ i, W.Coprime (a+h i)) :
    ∃ n : ℕ, N≤n ∧ Nat.ModEq W n a ∧ m≤shiftedPrimeCount h n := by
  by_contra hnone
  push_neg at hnone
  let k := sieveDimension M
  let C := sieveCutoff M
  let d := 100*C
  let H := Finset.univ.sup h
  let K : ℝ := 16*(2 : ℝ)^M*roughDensity W
  let A : ℝ := 200*(m+1)
  have hC : 0<C := (sieveCutoff_bounds M hM).1
  have hC1 : 1≤C := hC
  have hCR : (1 : ℝ)≤C := by exact_mod_cast hC1
  have hK : 0≤K := by dsimp [K]; exact mul_nonneg (by positivity) (roughDensity_pos hW0).le
  have hA : 0≤A := by dsimp [A]; positivity
  have hd : 0<d := by dsimp [d]; omega
  have hHw (i : Fin k) : h i≤H := Finset.le_sup (Finset.mem_univ i)
  have htX := nat_power_tendsto d hd
  have htQ : Tendsto (fun R : ℕ => sieveDistributionLevel k (R^d)) atTop atTop :=
    (conductorCutoff_tendsto_atTop (sieveDistributionExponent k)).comp htX
  have hexc := htQ.eventually (exceptionPrime_eventually_large (max W D))
  have helem : ∀ᶠ R : ℕ in atTop, ∀ i : Fin k,
      elementarySieveError (W*(R^C)^2) (R^d) (h i)≤(R : ℝ)^(3*C) :=
    eventually_all.mpr (fun i => elementarySieveError_eventually_power W C (h i) hC)
  have hnp : ∀ᶠ R : ℕ in atTop, ∀ i : Fin k,
      (Nat.sqrt (R^d+h i)+1 : ℝ)*(Nat.log 2 (R^d+h i)+1 : ℝ)*Real.log (R^d+h i+1 : ℝ)≤(R : ℝ)^(51*C) :=
    eventually_all.mpr (fun i => nonprimeError_eventually_power C (h i) hC)
  have hratio := sieve_quadratic_margin W D M A (400*(m+1 : ℝ)+2) hW0 hM hA
    (by dsimp [A]; ring_nf; rfl) hlarge hD herror hsmall
  have hBV := eventually_power_log_monomial_le (A*C) (4*C) d 1 (by positivity) (by dsimp [d]; omega)
  have hsmallV := eventually_power_log_monomial_le ((N : ℝ)*k*(d+1 : ℕ)) (4*C) d 1 (by positivity) (by dsimp [d]; omega)
  have hev : ∀ᶠ R : ℕ in atTop, False := by
    filter_upwards [hexc,helem,hnp,hratio,hBV,hsmallV,
      harmonicEuler_power_bound W (2^M) hW0 (by positivity),
      sieveL1Envelope_eventually_power M K hK hC1,
      weightedSieveError_eventually W C k K hC hK,
      log_nat_power_shift_bound d H hd,
      sieve_margin_eventually_large W M (4*k+4 : ℝ) hW0 (by positivity),eventually_ge_atTop 2]
      with R hexc helem hnp hratio hBV hsmallV hEuler hEnv hDist hlog hmargin hR2
    let X := R^d
    let Q := sieveDistributionLevel k X
    let E := exceptionPrime Q
    let P := sievePrimes W E (R^(2^M))
    let V : ℝ := (R : ℝ)^(4*C)
    let B : ℝ := A*C*Real.log R
    let L : ℝ := Real.log (X+H+1 : ℝ)
    let S₁ := actualSieveSum P M R W a X h
    let S₂ := ∑ i, actualPrimeSum P M R W a X h i
    let main₁ := (X : ℝ)/W*sieveQuadraticI P M R
    let main₂ := (X : ℝ)/W.totient*((k : ℝ)*sieveQuadraticJ P M R 0)
    have hR : 1<R := by omega
    have hRN : (1 : ℝ)≤R := by exact_mod_cast (show 1≤R by omega)
    have hlogR : 0<Real.log R := Real.log_pos (by exact_mod_cast hR)
    have hL0 : 0≤L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X,Nat.cast_nonneg (α := ℝ) H])
    have hX0 : (0 : ℝ)<X := by dsimp [X]; positivity
    have hphi : (0 : ℝ)<W.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW0)
    have hWpos : (0 : ℝ)<W := by exact_mod_cast Nat.pos_of_ne_zero hW0
    have hB0 : 0≤B := by dsimp [B]; positivity
    have hV0 : 0≤V := by dsimp [V]; positivity
    have hPp (p : ℕ) (hp : p∈P) := mem_sievePrimes.mp hp
    have hP : ∀ p∈P, Nat.Prime p := fun p hp => (hPp p hp).2.1
    have hWP : ∀ p∈P, W.Coprime p := fun p hp => ((hPp p hp).2.1.coprime_iff_not_dvd.mpr (hPp p hp).2.2.1).symm
    have hpi : ∀ p : ↥P, Function.Injective (shiftedResidues h p) := sievePrimes_shift_injective h hi W E (R^(2^M)) D hH hsmall
    have hEprime : E=1 ∨ Nat.Prime E := exceptionPrime_eq_one_or_prime Q
    have hED : E=1 ∨ D≤E := hexc.imp id (fun hh => by have hle := le_max_right W D; dsimp [E,Q,X]; omega)
    have hEW : E=1 ∨ W<E := hexc.imp id (fun hh => (le_max_left W D).trans_lt hh)
    have hgood (r s : ↥P→Finset (Fin k)) : GoodModulus Q (W*matrixModulus r s) := sievePrimes_good_modulus W (R^(2^M)) Q hW0 hEW r s
    have hHE : harmonicEuler P≤K*Real.log R := by
      have hh := hEuler P hP hWP (fun p hp => (hPp p hp).1)
      convert hh using 1 <;> dsimp [K] <;> push_cast <;> ring
    have hHE' : harmonicEuler P≤K*(1+Real.log R) := hHE.trans (mul_le_mul_of_nonneg_left (by linarith) hK)
    have henv : sieveL1Envelope P M R≤(R : ℝ)^(2*C) := hEnv P hHE'
    have henvsq : sieveL1Envelope P M R^2≤V := by
      have hh := pow_le_pow_left₀ (sieveL1Envelope_nonneg P M R) henv 2
      dsimp [V]
      convert hh using 1 <;> rw [← pow_mul]; congr 1; omega
    have hVE (i : Fin k) : V*elementarySieveError (W*(R^C)^2) X (h i)≤X := by
      calc
        _ ≤ V*(R : ℝ)^(3*C) := mul_le_mul_of_nonneg_left (helem i) hV0
        _ = (R : ℝ)^(7*C) := by dsimp [V]; rw [← pow_add]; congr 1; omega
        _ ≤ (R : ℝ)^d := pow_le_pow_right₀ hRN (by dsimp [d]; omega)
        _ = (X : ℝ) := by simp [X]
    have hVnp (i : Fin k) : V*((Nat.sqrt (X+h i)+1 : ℝ)*(Nat.log 2 (X+h i)+1 : ℝ)*Real.log (X+h i+1 : ℝ))≤X := by
      calc
        _ ≤ V*(R : ℝ)^(51*C) := mul_le_mul_of_nonneg_left (by simpa only [X,Nat.cast_pow] using hnp i) hV0
        _ = (R : ℝ)^(55*C) := by dsimp [V]; rw [← pow_add]; congr 1; omega
        _ ≤ (R : ℝ)^d := pow_le_pow_right₀ hRN (by dsimp [d]; omega)
        _ = (X : ℝ) := by simp [X]
    have h1 : |S₁-main₁|≤V := (actualSieveSum_error P M R W a X hP hR hW0 hWP h hpi).trans henvsq
    have h2i (i : Fin k) : |actualPrimeSum P M R W a X h i-(X : ℝ)/W.totient*sieveQuadraticJ P M R i|≤2*X := by
      have hh := actualPrimeSum_error P M R W a X Q hP hR hW0 hWP h hpi i (ha i) hgood
      have hdist := hDist (harmonicEuler P) (by unfold harmonicEuler; positivity) hHE
      have herr : sieveL1Envelope P M R^2*elementarySieveError (W*(R^C)^2) X (h i)≤X :=
        (mul_le_mul_of_nonneg_right henvsq (elementarySieveError_nonneg _ _ _)).trans (hVE i)
      have hx : (R : ℝ)^(100*C)=(X : ℝ) := by simp [X,d]
      rw [hx] at hdist
      exact hh.trans (by linarith)
    have h2 : |S₂-main₂|≤2*k*X := by
      have hh := sum_prime_error _ _ (X : ℝ) h2i
      rw [← Finset.mul_sum,sum_sieveQuadraticJ] at hh
      exact hh
    have hBV' : B*V≤X := by
      have hh : B*V≤A*C*(R : ℝ)^(4*C)*(1+Real.log R)^1 := by dsimp [B,V]; nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) R) (4*C)]
      exact hh.trans (by simpa [X] using hBV)
    have hlog' : L≤(d+1 : ℕ)*Real.log R := by
      dsimp [L,X]
      simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hlog
    have hmL : (m : ℝ)*L≤B := by
      have hh := mul_le_mul_of_nonneg_left hlog' (Nat.cast_nonneg m)
      have hcoef : (m : ℝ)*(d+1 : ℕ)≤A*C := by
        dsimp [d,A]
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      have hh' := mul_le_mul_of_nonneg_right hcoef hlogR.le
      dsimp [B]
      nlinarith
    have hNV : (N : ℝ)*k*L*V≤X := by
      have hh : (N : ℝ)*k*L*V≤((N : ℝ)*k*(d+1 : ℕ))*(R : ℝ)^(4*C)*(1+Real.log R)^1 := by
        have hl : L≤(d+1 : ℕ)*(1+Real.log R) := hlog'.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
        have hm := mul_le_mul_of_nonneg_left hl (show 0≤(N : ℝ)*k*V by positivity)
        dsimp [V] at hm
        nlinarith
      exact hh.trans (by simpa [X] using hsmallV)
    have hrat := hratio E hEprime hED
    have hmain : B*main₁+(4*(k : ℝ)+4)*X < main₂ := by
      have hh := mul_lt_mul_of_pos_left hrat (div_pos hX0 hphi)
      have hmar := mul_lt_mul_of_pos_left hmargin hX0
      have hid : (X : ℝ)/W.totient*(A*(sieveCutoff M)*(roughDensity W*Real.log R)*sieveQuadraticI P M R)=B*main₁ := by
        dsimp [B,main₁,C,roughDensity]
        field_simp
      have hmid : (X : ℝ)/W.totient*((roughDensity W*Real.log R)^(k+1)/2^(k+1))=
          (X : ℝ)*((roughDensity W*Real.log R)^(k+1)/2^(k+1)/(W.totient : ℝ)) := by ring
      change (X : ℝ)/W.totient*(A*(sieveCutoff M)*(roughDensity W*Real.log R)*sieveQuadraticI P M R+
        (roughDensity W*Real.log R)^(k+1)/2^(k+1)) < main₂ at hh
      rw [mul_add,hid,hmid] at hh
      nlinarith
    have hpositive := sieve_main_transfer hB0 hX0 (Nat.cast_nonneg k) hmain h1 h2 hBV'
    have hw (n : ℕ) (_hn : n∈Finset.Icc 1 X) : 0≤actualSieveWeight P M R W a h n ∧ actualSieveWeight P M R W a h n≤V :=
      ⟨actualSieveWeight_nonneg P M R W a h n,(actualSieveWeight_bound P M R W a h hP hR n).trans henvsq⟩
    have hbad (i : Fin k) : (∑ n∈Finset.Icc 1 X, actualSieveWeight P M R W a h n*(if ¬Nat.Prime (n+h i) then ArithmeticFunction.vonMangoldt (n+h i) else 0))≤X :=
      (weighted_nonprime_sum_bound (h i) X _ V (fun n hn => (hw n hn).2) hV0).trans (hVnp i)
    have hcnt (n : ℕ) (hn : n∈Finset.Icc 1 X) (hnN : N≤n) (hwn : actualSieveWeight P M R W a h n≠0) : shiftedPrimeCount h n≤ m := by
      have hnW : Nat.ModEq W n a := by by_contra hh; simp [actualSieveWeight,hh] at hwn
      have hh := hnone n hnN hnW
      omega
    have hupper := weighted_prime_detection_bound h H X N m hHw (actualSieveWeight P M R W a h) V hV0 hw hcnt hbad
    simp only [Fintype.card_fin] at hupper
    change S₂≤(m : ℝ)*L*S₁+(k : ℝ)*X+(N : ℝ)*k*L*V at hupper
    have hS₁ : 0≤S₁ := actualSieveSum_nonneg P M R W a X h
    have hmLS := mul_le_mul_of_nonneg_right hmL hS₁
    nlinarith
  exact (hev.exists).elim (fun _ h => h)

end
end MaynardDevelopment
end

/- MaynardPrimeTuples -/
section

open scoped BigOperators
namespace MaynardDevelopment
noncomputable section
attribute [local instance] Classical.propDecidable

/-- An elementary positive-level Maynard sieve consequence, with arbitrary fixed
progression and arbitrarily large translates. -/
theorem maynard_prime_tuples :
    ∀ m : ℕ, ∃ k : ℕ, ∀ h : Fin k→ℕ,
      StrictMono h → (∀ p : ℕ, Nat.Prime p → ∃ a : ℕ, ∀ i, ¬p∣a+h i) →
      ∀ W a : ℕ, 0<W → (∀ i, W.Coprime (a+h i)) →
      ∀ N : ℕ, ∃ n : ℕ, N≤n ∧ m≤(Finset.univ.filter (fun i => Nat.Prime (W*n+a+h i))).card := by
  intro m
  let M := 1056*(400*(m+1)+2)+1
  have hM : 0<M := by dsimp [M]; omega
  have hlarge : 1056*(400*(m+1 : ℝ)+2)<M := by
    exact_mod_cast (show 1056*(400*(m+1)+2)<M by dsimp [M]; omega)
  refine ⟨sieveDimension M,?_⟩
  intro h hmono hadm W₀ a₀ hW₀ ha₀ N
  let D := max (8*2^M) (max ⌈sieveErrorThreshold M⌉₊ (Finset.univ.sup h))
  have hD : 8*2^M≤D := le_max_left _ _
  have herror : sieveErrorThreshold M≤D := by
    have hh : ⌈sieveErrorThreshold M⌉₊≤D := (le_max_left _ _).trans (le_max_right _ _)
    exact (Nat.le_ceil _).trans (by exact_mod_cast hh)
  have hH (i : Fin (sieveDimension M)) : h i≤D :=
    (Finset.le_sup (Finset.mem_univ i)).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨W,a,hW,hdiv,ha,hcop,hsmall⟩ := extend_presieving_progression h hadm W₀ a₀ D hW₀.ne' ha₀
  obtain ⟨b,hbN,hbmod,hbmany⟩ := presieved_many_primes m M W a D (W₀*N+a₀) hM hW hlarge hD herror hsmall h hmono.injective hH hcop
  have hba : Nat.ModEq W₀ b a₀ := (hbmod.of_dvd hdiv).trans ha
  have hab : a₀≤b := by omega
  have hbd : W₀∣b-a₀ := (Nat.modEq_iff_dvd' hab).mp hba.symm
  let n := (b-a₀)/W₀
  have he : W₀*n+a₀=b := by
    dsimp [n]
    rw [Nat.mul_div_cancel' hbd]
    omega
  have hnN : N≤n := by
    have hh : W₀*N≤W₀*n := by omega
    exact Nat.le_of_mul_le_mul_left hh hW₀
  refine ⟨n,hnN,?_⟩
  simpa only [he,shiftedPrimeCount] using hbmany

end
end MaynardDevelopment
end


open Nat BigOperators Int

/--
A092243: Score at stage $n$ in "tug of war" between prime gap increases vs. prime gap decreases:
start with score = 0 at $n = 1$ and at stage $k > 1$, increase (resp. decrease) the score by 1
if the $k$-th prime gap is greater (resp. less) than the previous prime gap.
-/
noncomputable def A092243 (n : ℕ) : ℤ :=
  -- P_i is the $i$-th prime, 0-indexed: P 0 = 2, P 1 = 3, ...
  -- Note: Nat.nth Nat.Prime i gives the i-th prime, where i=0 is the 0-th prime, 2.
  let P (i : ℕ) : ℕ := Nat.nth Nat.Prime i

  -- $G_k$ is the $k$-th prime gap (OEIS 1-indexed), $G_k = P_k - P_{k-1}$, for $k \ge 1$.
  -- Here we use the 0-indexed primes P_i, so the k-th gap involves the prime P[k] and P[k-1].
  let G_gap (k : ℕ) : ℕ := P k - P (k - 1)

  if n = 0 then 0 -- Defining for n=0 as 0, though OEIS starts at 1
  else if n = 1 then 0
  else

  -- The score is the cumulative sum of the changes $\Delta(k) = \operatorname{sign}(G_k - G_{k-1})$ for $k=2$ to $n$.
  -- The sum starts at k=2 because the first gap G_1 is compared to G_2. The comparison is between G_k and G_{k-1}.
  -- Since the first gap is G_1, the first comparison is at k=2 (G_2 vs G_1).
  (Finset.Icc 2 n).sum fun k : ℕ =>
    let Gk   : ℕ := G_gap k
    -- Since $k \ge 2$, $k-1 \ge 1$, so G_gap (k-1) is safely computed.
    let Gkm1 : ℕ := G_gap (k - 1)

    -- Calculate $\operatorname{sign}(G_k - G_{k-1})$ using integer subtraction and sign function.
    ((Gk : ℤ) - (Gkm1 : ℤ)) |>.sign

/-
We remove the specific proofs for a_one etc., as they failed compilation and are not the object of the final submission.
The definition of A092243 is now corrected for proper syntax of the n-th prime.
-/

/--
Conjectures regarding the long-term behavior of A092243 (the score $s$).

Questions from OEIS A092243, including the primary conjectures:
1. Is s > 0 for some n > 250000?
2. Is s bounded from below?
3. Is s bounded from above?
4. Is s > 0 for infinitely many values of n?
5. Is s < 0 for infinitely many values of n?
-/
structure OEIS_A092243_Conjectures where
  /-- Is the score ever positive after n = 250,000? -/
  positive_after_large_n : ∃ n : ℕ, n > 250000 ∧ A092243 n > 0
  /-- Is the score bounded from below? -/
  bounded_below : ∃ B : ℤ, ∀ n : ℕ, B ≤ A092243 n
  /-- Is the score bounded from above? -/
  bounded_above : ∃ B : ℤ, ∀ n : ℕ, A092243 n ≤ B
  /-- Is the score positive infinitely often? -/
  infinitely_positive : Set.Infinite {n : ℕ | A092243 n > 0}
  /-- Is the score negative infinitely often? -/
  infinitely_negative : Set.Infinite {n : ℕ | A092243 n < 0}

private noncomputable def gap (k : ℕ) : ℕ := Nat.nth Nat.Prime k - Nat.nth Nat.Prime (k - 1)

private noncomputable def delta (k : ℕ) : ℤ := ((gap k : ℤ) - gap (k - 1)).sign

private lemma score_sum (n : ℕ) : A092243 n = ∑ k ∈ Finset.Icc 2 n, delta k := by
  unfold A092243 delta gap
  split_ifs with h₀ h₁
  · subst n; simp
  · subst n; simp
  · rfl

private lemma score_step (n : ℕ) (hn : 1 ≤ n) :
    A092243 (n + 1) = A092243 n + delta (n + 1) := by
  rw [score_sum, score_sum]
  exact Finset.sum_Icc_succ_top (a := 2) (b := n) (by omega) delta

private lemma delta_eq_one {k : ℕ} (hk : gap (k - 1) < gap k) : delta k = 1 := by
  unfold delta
  apply Int.sign_eq_one_iff_pos.mpr
  exact sub_pos.mpr (by exact_mod_cast hk)

private lemma score_run (n m : ℕ) (hn : 1 ≤ n)
    (h : ∀ j < m, gap (n + j) < gap (n + j + 1)) :
    A092243 (n + m) = A092243 n + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ih' := ih (fun j hj => h j (by omega))
    rw [show n + (m + 1) = (n + m) + 1 by omega, score_step _ (by omega), ih']
    have hd : delta (n + m + 1) = 1 := delta_eq_one (by simpa using h m (by omega))
    rw [hd]
    push_cast
    ring

private lemma not_conjecture_of_increasing_runs
    (runs : ∀ m : ℕ, ∃ n : ℕ, 1 ≤ n ∧
      ∀ j < m, gap (n + j) < gap (n + j + 1)) :
    ¬ OEIS_A092243_Conjectures := by
  intro h
  obtain ⟨L, hL⟩ := h.bounded_below
  obtain ⟨U, hU⟩ := h.bounded_above
  obtain ⟨n, hn, hrun⟩ := runs ((U - L).toNat + 1)
  have heq := score_run n ((U - L).toNat + 1) hn hrun
  have h₁ := hL n
  have h₂ := hU (n + ((U - L).toNat + 1))
  omega


/-- The usual admissibility condition for a tuple of natural-number shifts. -/
private def TupleAdmissible {k : ℕ} (h : Fin k → ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a : ℕ, ∀ i, ¬ p ∣ a + h i

/-- A consecutive-prime-tuple input, expressed using the prime enumeration.
This is an assumption below, not an asserted theorem. -/
private def ConsecutivePrimeTuples : Prop :=
  ∀ m : ℕ, ∃ k : ℕ, ∀ h : Fin k → ℕ,
    StrictMono h → TupleAdmissible h →
    ∃ a n : ℕ, ∀ i : Fin m, ∃ j : Fin k,
      Nat.nth Nat.Prime (n + i.val) = a + h j

private def geometric (k j : ℕ) : ℕ := k.factorial * 3 ^ j

private lemma geometric_pos (k j : ℕ) : 0 < geometric k j := by
  unfold geometric
  positivity

private lemma geometric_mono (k : ℕ) : StrictMono (geometric k) := by
  intro a b hab
  unfold geometric
  exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by omega) hab) (Nat.factorial_pos k)

private lemma geometric_gaps (k i j l : ℕ) (hjl : j < l) :
    geometric k j - geometric k i < geometric k l - geometric k j := by
  have hp := geometric_pos k j
  have hpow : 3 ^ (j + 1) ≤ 3 ^ l := Nat.pow_le_pow_right (by omega) (by omega)
  have hmul := Nat.mul_le_mul_left k.factorial hpow
  have hlarge : 3 * geometric k j ≤ geometric k l := by
    unfold geometric
    rw [pow_succ] at hmul
    nlinarith
  omega

private lemma geometric_admissible (k : ℕ) :
    TupleAdmissible (fun i : Fin k => geometric k i.val) := by
  intro p hp
  by_cases hpk : p ≤ k
  · refine ⟨1, ?_⟩
    intro i hdiv
    have hd : p ∣ geometric k i.val :=
      dvd_mul_of_dvd_left (Nat.dvd_factorial hp.pos hpk) _
    have hone : p ∣ 1 := (Nat.dvd_add_iff_left hd).mpr hdiv
    exact hp.ne_one (Nat.dvd_one.mp hone)
  · classical
    haveI : NeZero p := ⟨hp.ne_zero⟩
    let bad : Finset (ZMod p) := Finset.univ.image (fun i : Fin k => -(geometric k i.val : ZMod p))
    have hcard : bad.card < (Finset.univ : Finset (ZMod p)).card := by
      have hle : bad.card ≤ k := by
        simpa [bad] using
          (Finset.card_image_le (s := (Finset.univ : Finset (Fin k)))
            (f := fun i : Fin k => -(geometric k i.val : ZMod p)))
      simpa using lt_of_le_of_lt hle (by omega : k < p)
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    refine ⟨a.val, ?_⟩
    intro i hi
    have hz : ((a.val + geometric k i.val : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hi
    rw [Nat.cast_add, ZMod.natCast_zmod_val] at hz
    have heq := add_eq_zero_iff_eq_neg.mp hz
    apply ha
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩

private lemma increasing_runs_of_consecutive_tuples
    (ht : ConsecutivePrimeTuples) :
    ∀ m : ℕ, ∃ n : ℕ, 1 ≤ n ∧
      ∀ j < m, gap (n + j) < gap (n + j + 1) := by
  intro m
  obtain ⟨k, hk⟩ := ht (m + 2)
  have hmono : StrictMono (fun i : Fin k => geometric k i.val) :=
    (geometric_mono k).comp (fun _ _ h => h)
  obtain ⟨a, n, htuple⟩ := hk _ hmono (geometric_admissible k)
  refine ⟨n + 1, by omega, ?_⟩
  intro j hj
  obtain ⟨i₀, h₀⟩ := htuple ⟨j, by omega⟩
  obtain ⟨i₁, h₁⟩ := htuple ⟨j + 1, by omega⟩
  obtain ⟨i₂, h₂⟩ := htuple ⟨j + 2, by omega⟩
  have hprime : Nat.nth Nat.Prime (n + (j + 1)) < Nat.nth Nat.Prime (n + (j + 2)) :=
    Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)
  rw [h₁, h₂] at hprime
  have hi : i₁.val < i₂.val := (geometric_mono k).lt_iff_lt.mp (by omega)
  have hg := geometric_gaps k i₀.val i₁.val i₂.val hi
  unfold gap
  rw [show n + 1 + j = n + (j + 1) by omega,
    show n + (j + 1) - 1 = n + j by omega,
    show n + (j + 1) + 1 = n + (j + 2) by omega,
    show n + (j + 2) - 1 = n + (j + 1) by omega]
  rw [h₀, h₁, h₂]
  simpa only [Nat.add_sub_add_left] using hg

private theorem disproof_of_consecutive_prime_tuples (ht : ConsecutivePrimeTuples) :
    ¬ OEIS_A092243_Conjectures :=
  not_conjecture_of_increasing_runs (increasing_runs_of_consecutive_tuples ht)


/-- An arithmetic-progression form of the prime-tuple conclusion of Maynard's sieve.
This proposition is used as a hypothesis, not asserted without proof. -/
private def MaynardPrimeTuples : Prop :=
  ∀ m : ℕ, ∃ k : ℕ, ∀ h : Fin k → ℕ,
    StrictMono h → TupleAdmissible h →
    ∀ W a : ℕ, 0 < W → (∀ i, W.Coprime (a + h i)) →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      m ≤ (Finset.univ.filter (fun i => Nat.Prime (W * n + a + h i))).card

private lemma covering_progression {k : ℕ} (h : Fin k → ℕ) :
    ∃ W a N : ℕ, 0 < W ∧ (∀ i, W.Coprime (a + h i)) ∧
      ∀ n ≥ N, ∀ t ≤ Finset.univ.sup h,
        (∀ i, t ≠ h i) → ¬ Nat.Prime (W * n + a + t) := by
  classical
  let H := Finset.univ.sup h
  let F := (Finset.range (H + 1)).filter (fun t => ∀ i, t ≠ h i)
  let q : ℕ → ℕ := fun t => Nat.nth Nat.Prime (H + t + 1)
  have hqprime (t : ℕ) : (q t).Prime :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _
  have hqlarge (t : ℕ) : H + t < q t := by
    have hh : H + t + 1 ≤ q t := Nat.le_nth (fun hf =>
      False.elim (Nat.infinite_setOf_prime hf))
    omega
  have hpair : (F : Set ℕ).Pairwise (Function.onFun Nat.Coprime q) := by
    intro s hs t ht hst
    apply (hqprime s).coprime_iff_not_dvd.mpr
    intro hd
    obtain hone | heq := (hqprime t).eq_one_or_self_of_dvd (q s) hd
    · exact (hqprime s).ne_one hone
    · have hind := Nat.nth_injective Nat.infinite_setOf_prime heq
      exact hst (by omega)
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfFinset (fun t => q t - t) q F
    (fun t _ => (hqprime t).ne_zero) hpair
  have ha_div (t : ℕ) (ht : t ∈ F) : q t ∣ a + t := by
    apply Nat.modEq_zero_iff_dvd.mp
    have hc := (ha t ht).add_right t
    rw [Nat.sub_add_cancel (by have := hqlarge t; omega)] at hc
    exact hc.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl (q t)))
  let W := ∏ t ∈ F, q t
  have hW : 0 < W := Finset.prod_pos (fun t _ => (hqprime t).pos)
  have hcop (i : Fin k) : W.Coprime (a + h i) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro t ht
    apply (hqprime t).coprime_iff_not_dvd.mpr
    intro hd
    have heq : h i ≡ t [MOD q t] :=
      Nat.ModEq.add_left_cancel' a
        ((Nat.modEq_zero_iff_dvd.mpr hd).trans
          (Nat.modEq_zero_iff_dvd.mpr (ha_div t ht)).symm)
    have hh : h i ≤ H := Finset.le_sup (Finset.mem_univ i)
    have htF := Finset.mem_filter.mp ht
    have htH : t ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp htF.1)
    have hit : h i = t := heq.eq_of_lt_of_lt (by have := hqlarge t; omega)
      (by have := hqlarge t; omega)
    exact htF.2 i hit.symm
  refine ⟨W, a, F.sup q + 1, hW, hcop, ?_⟩
  intro n hn t ht htne hprime
  have htF : t ∈ F := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), htne⟩
  have hqW : q t ∣ W := Finset.dvd_prod_of_mem q htF
  have hdiv : q t ∣ W * n + a + t := by
    have h₁ := dvd_mul_of_dvd_left hqW n
    have h₂ := ha_div t htF
    simpa [Nat.add_assoc] using dvd_add h₁ h₂
  have hqbound : q t ≤ F.sup q := Finset.le_sup htF
  have hbig : q t < W * n + a + t := by
    have : n ≤ W * n := by nlinarith
    omega
  obtain hone | heq := hprime.eq_one_or_self_of_dvd (q t) hdiv
  · exact (hqprime t).ne_one hone
  · omega

private lemma prime_count_of_tuple {k : ℕ} (h : Fin k → ℕ)
    (hi : Function.Injective h) (b : ℕ) :
    (Finset.univ.filter (fun i => Nat.Prime (b + h i))).card ≤
      Nat.count (fun t => Nat.Prime (b + t)) (Finset.univ.sup h + 1) := by
  classical
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_le_card_of_injOn h
  · intro i hi'
    have hp : Nat.Prime (b + h i) := by simpa using hi'
    change h i ∈ (Finset.range (Finset.univ.sup h + 1)).filter (fun t => Nat.Prime (b + t))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hp⟩
    have hh : h i ≤ Finset.univ.sup h := Finset.le_sup (Finset.mem_univ i)
    omega
  · exact hi.injOn

private lemma consecutive_tuples_of_maynard
    (hm : MaynardPrimeTuples) : ConsecutivePrimeTuples := by
  intro m
  obtain ⟨k, hk⟩ := hm m
  refine ⟨k, ?_⟩
  intro h hmono hadm
  obtain ⟨W, a, N, hW, hcop, hcover⟩ := covering_progression h
  obtain ⟨n, hn, hmany⟩ := hk h hmono hadm W a hW hcop N
  let b := W * n + a
  let H := Finset.univ.sup h
  have hcnt : m ≤ Nat.count (fun t => Nat.Prime (b + t)) (H + 1) :=
    hmany.trans (prime_count_of_tuple h hmono.injective b)
  refine ⟨b, Nat.count Nat.Prime b, ?_⟩
  intro i
  let p := Nat.nth Nat.Prime (Nat.count Nat.Prime b + i.val)
  have hpb : b ≤ p := by
    apply (Nat.le_nth_count (p := Nat.Prime) Nat.infinite_setOf_prime b).trans
    exact Nat.nth_monotone (p := Nat.Prime) Nat.infinite_setOf_prime (Nat.le_add_right _ _)
  have hpH : p < b + (H + 1) := by
    have hsum := Nat.count_add Nat.Prime b (H + 1)
    apply Nat.nth_lt_of_lt_count (p := Nat.Prime)
    change Nat.count Nat.Prime b + i.val < Nat.count Nat.Prime (b + (H + 1))
    have := i.isLt
    omega
  have hp : p.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _
  have hex : ∃ j : Fin k, p - b = h j := by
    by_contra hnot
    push_neg at hnot
    have hc := hcover n hn (p - b) (by omega) hnot
    apply hc
    change Nat.Prime (b + (p - b))
    simpa [Nat.add_sub_of_le hpb] using hp
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, ?_⟩
  change p = b + h j
  omega

private theorem disproof_of_maynard (hm : MaynardPrimeTuples) :
    ¬ OEIS_A092243_Conjectures :=
  disproof_of_consecutive_prime_tuples (consecutive_tuples_of_maynard hm)


theorem oeis_92243_conjecture : OEIS_A092243_Conjectures := by sorry

theorem oeis_92243_conjecture.disproof : ¬ (type_of% @oeis_92243_conjecture) := by
  exact disproof_of_maynard MaynardDevelopment.maynard_prime_tuples

#print axioms oeis_92243_conjecture.disproof
