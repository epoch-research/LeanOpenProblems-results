import FormalConjecturesUtil

/-!
An affine-independence ingredient considered for Erdős Problem 714.
This file does not assert that the associated graph construction is free.
-/

open Polynomial

namespace Erdos714CubicEmbedding

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E]

/-- An element of a cubic extension annihilated by a nonzero quadratic is in the base field. -/
theorem quadratic_root_in_base (hdegree : Module.finrank F E = 3)
    {p : F[X]} (hp : p ≠ 0) (hdeg : p.natDegree ≤ 2)
    {x : E} (hx : aeval x p = 0) : ∃ a : F, algebraMap F E a = x := by
  have hi : IsIntegral F x := IsIntegral.of_finite F x
  have hdvd := minpoly.dvd F x hx
  have hle : (minpoly F x).natDegree ≤ 2 :=
    (natDegree_le_of_dvd hdvd hp).trans hdeg
  have hdiv := minpoly.degree_dvd hi
  rw [hdegree] at hdiv
  have hone : (minpoly F x).natDegree = 1 := by
    have hpos := minpoly.natDegree_pos hi
    have hchoices := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdiv
    omega
  exact minpoly.natDegree_eq_one_iff.mp hone

/-- A quadratic relation outside the base field must have zero coefficients. -/
theorem quadratic_coefficients_zero (hdegree : Module.finrank F E = 3)
    {x : E} (hx : ¬ ∃ a : F, algebraMap F E a = x) (a b c : F)
    (he : algebraMap F E a * x ^ 2 + algebraMap F E b * x + algebraMap F E c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  let p : F[X] := C a * X ^ 2 + C b * X + C c
  have hzero : p = 0 := by
    by_contra hp
    apply hx
    apply quadratic_root_in_base hdegree hp
    · dsimp [p]
      compute_degree!
    · simpa [p] using he
  have h₂ := congrArg (fun p : F[X] => p.coeff 2) hzero
  have h₁ := congrArg (fun p : F[X] => p.coeff 1) hzero
  have h₀ := congrArg (fun p : F[X] => p.coeff 0) hzero
  simpa [p] using And.intro h₂ (And.intro h₁ h₀)


/-- The first two moment relations force collinearity in a cubic extension. -/
theorem square_dependence_collinear (hdegree : Module.finrank F E = 3)
    (h_two : (2 : F) ≠ 0) {u v w : E}
    (hu : u ≠ 0) (hw0 : w ≠ 0) (hwu : w ≠ u) (hwv : w ≠ v)
    (a b : F)
    (hw : w = algebraMap F E a * u + algebraMap F E b * v)
    (hsq : w ^ 2 = algebraMap F E a * u ^ 2 + algebraMap F E b * v ^ 2) :
    ∃ t : F, v = algebraMap F E t * u := by
  by_contra hn
  have hnot : ¬ ∃ t : F, algebraMap F E t = v / u := by
    rintro ⟨t, ht⟩
    apply hn
    refine ⟨t, ?_⟩
    rw [ht, div_mul_cancel₀ _ hu]
  have he : algebraMap F E (b * (b - 1)) * (v / u) ^ 2 +
      algebraMap F E (2 * a * b) * (v / u) + algebraMap F E (a * (a - 1)) = 0 := by
    rw [hw] at hsq
    simp only [map_mul, map_sub, map_ofNat, map_one]
    field_simp
    linear_combination hsq
  obtain ⟨hb, hab, ha⟩ := quadratic_coefficients_zero hdegree hnot
    (b * (b - 1)) (2 * a * b) (a * (a - 1)) he
  have hab' : a = 0 ∨ b = 0 := by
    rcases mul_eq_zero.mp hab with h | h
    · exact Or.inl ((mul_eq_zero.mp h).resolve_left h_two)
    · exact Or.inr h
  have ha' : a = 0 ∨ a = 1 := by simpa only [sub_eq_zero] using mul_eq_zero.mp ha
  have hb' : b = 0 ∨ b = 1 := by simpa only [sub_eq_zero] using mul_eq_zero.mp hb
  rcases hab' with rfl | rfl
  · rcases hb' with rfl | rfl
    · exact hw0 (by simpa using hw)
    · exact hwv (by simpa using hw)
  · rcases ha' with rfl | rfl
    · exact hw0 (by simpa using hw)
    · exact hwu (by simpa using hw)

/-- The product of three conjugates; its scalar-line restrictions are cubic. -/
def cubicNorm (σ τ : E →ₐ[F] E) (x : E) : E := x * σ x * τ x

lemma cubicNorm_ne_zero (σ τ : E →ₐ[F] E) {x : E} (hx : x ≠ 0) :
    cubicNorm σ τ x ≠ 0 :=
  mul_ne_zero (mul_ne_zero hx (map_ne_zero σ |>.mpr hx)) (map_ne_zero τ |>.mpr hx)

lemma cubicNorm_line (σ τ : E →ₐ[F] E) (x u : E) (t : F) :
    cubicNorm σ τ (x + algebraMap F E t * u) =
      cubicNorm σ τ x +
      (u * σ x * τ x + x * σ u * τ x + x * σ x * τ u) * algebraMap F E t +
      (u * σ u * τ x + u * σ x * τ u + x * σ u * τ u) * (algebraMap F E t)^2 +
      cubicNorm σ τ u * (algebraMap F E t)^3 := by
  simp only [cubicNorm, map_add, map_mul, AlgHom.commutes]
  ring

/-- The four moment equations have only the trivial solution on distinct points. -/
theorem four_moments (hdegree : Module.finrank F E = 3) (h_two : (2 : F) ≠ 0)
    (σ τ : E →ₐ[F] E) (x : Fin 4 → E) (hx : Function.Injective x)
    (c : Fin 4 → F)
    (h₀ : ∑ i, algebraMap F E (c i) = 0)
    (h₁ : ∑ i, algebraMap F E (c i) * x i = 0)
    (h₂ : ∑ i, algebraMap F E (c i) * (x i)^2 = 0)
    (h₃ : ∑ i, algebraMap F E (c i) * cubicNorm σ τ (x i) = 0) :
    ∀ i, c i = 0 := by
  let f := algebraMap F E
  have hf : Function.Injective f := (algebraMap F E).injective
  simp only [Fin.sum_univ_four] at h₀ h₁ h₂ h₃
  change f (c 0) + f (c 1) + f (c 2) + f (c 3) = 0 at h₀
  change f (c 0) * x 0 + f (c 1) * x 1 + f (c 2) * x 2 + f (c 3) * x 3 = 0 at h₁
  change f (c 0) * (x 0)^2 + f (c 1) * (x 1)^2 +
    f (c 2) * (x 2)^2 + f (c 3) * (x 3)^2 = 0 at h₂
  have hn (i j : Fin 4) (h : i ≠ j) : x i - x j ≠ 0 := sub_ne_zero.mpr (hx.ne h)
  by_cases hc₃ : c 3 = 0
  · have hf₃ : f (c 3) = 0 := by simp [hc₃, f]
    rw [hf₃] at h₀ h₁ h₂
    have hp₂ : f (c 2) * (x 2 - x 0) * (x 2 - x 1) = 0 := by
      linear_combination h₂ - (x 0 + x 1) * h₁ + (x 0 * x 1) * h₀
    have hf₂ : f (c 2) = 0 := by
      rcases mul_eq_zero.mp hp₂ with h | h
      · exact (mul_eq_zero.mp h).resolve_right (hn 2 0 (by decide))
      · exact False.elim (hn 2 1 (by decide) h)
    rw [hf₂] at h₀ h₁
    have hp₁ : f (c 1) * (x 1 - x 0) = 0 := by
      linear_combination h₁ - x 0 * h₀
    have hf₁ := (mul_eq_zero.mp hp₁).resolve_right (hn 1 0 (by decide))
    have hf₀ : f (c 0) = 0 := by simpa [hf₁] using h₀
    intro i
    apply hf
    fin_cases i <;> simpa [f] using (by assumption : f (c _) = 0)
  · exfalso
    have hf₃ : f (c 3) ≠ 0 := by simpa [f] using hc₃
    let u := x 1 - x 0
    let v := x 2 - x 0
    let w := x 3 - x 0
    have hu : u ≠ 0 := hn 1 0 (by decide)
    have hw0 : w ≠ 0 := hn 3 0 (by decide)
    have hwu : w ≠ u := by
      intro h
      exact hx.ne (by decide : (3 : Fin 4) ≠ 1) (sub_left_injective h)
    have hwv : w ≠ v := by
      intro h
      exact hx.ne (by decide : (3 : Fin 4) ≠ 2) (sub_left_injective h)
    have hl₀ : f (c 1) * u + f (c 2) * v + f (c 3) * w = 0 := by
      dsimp [u, v, w]
      linear_combination h₁ - x 0 * h₀
    have hq₀ : f (c 1) * u^2 + f (c 2) * v^2 + f (c 3) * w^2 = 0 := by
      dsimp [u, v, w]
      linear_combination h₂ - (2 * x 0) * h₁ + (x 0)^2 * h₀
    let a := -c 1 / c 3
    let b := -c 2 / c 3
    have hw : w = f a * u + f b * v := by
      dsimp [a, b, f]
      simp only [map_div₀, map_neg]
      field_simp [show algebraMap F E (c 3) ≠ 0 from hf₃]
      linear_combination hl₀
    have hsq : w^2 = f a * u^2 + f b * v^2 := by
      dsimp [a, b, f]
      simp only [map_div₀, map_neg]
      field_simp [show algebraMap F E (c 3) ≠ 0 from hf₃]
      linear_combination hq₀
    obtain ⟨t, hv⟩ := square_dependence_collinear hdegree h_two hu hw0 hwu hwv a b hw hsq
    let s := a + b * t
    have hws : w = f s * u := by
      rw [hw, hv]
      simp only [s, map_add, map_mul]
      ring
    have hl : f (c 1) + f (c 2) * f t + f (c 3) * f s = 0 := by
      have hp : (f (c 1) + f (c 2) * f t + f (c 3) * f s) * u = 0 := by
        rw [hv, hws] at hl₀
        linear_combination hl₀
      exact (mul_eq_zero.mp hp).resolve_right hu
    have hq : f (c 1) + f (c 2) * (f t)^2 + f (c 3) * (f s)^2 = 0 := by
      have hp : (f (c 1) + f (c 2) * (f t)^2 + f (c 3) * (f s)^2) * u^2 = 0 := by
        rw [hv, hws] at hq₀
        linear_combination hq₀
      exact (mul_eq_zero.mp hp).resolve_right (pow_ne_zero 2 hu)
    let B := u * σ (x 0) * τ (x 0) + x 0 * σ u * τ (x 0) + x 0 * σ (x 0) * τ u
    let C := u * σ u * τ (x 0) + u * σ (x 0) * τ u + x 0 * σ u * τ u
    have hline (z : F) : cubicNorm σ τ (x 0 + f z * u) =
        cubicNorm σ τ (x 0) + B * f z + C * (f z)^2 + cubicNorm σ τ u * (f z)^3 :=
      cubicNorm_line σ τ (x 0) u z
    have hx₁ : x 1 = x 0 + f 1 * u := by simp [u, f]
    have hx₂ : x 2 = x 0 + f t * u := by rw [← hv]; dsimp [v]; ring
    have hx₃ : x 3 = x 0 + f s * u := by rw [← hws]; dsimp [w]; ring
    have hn₁ := hline 1
    have hn₂ := hline t
    have hn₃ := hline s
    rw [← hx₁] at hn₁
    rw [← hx₂] at hn₂
    rw [← hx₃] at hn₃
    simp only [map_one, one_pow, mul_one] at hn₁
    rw [hn₁, hn₂, hn₃] at h₃
    have hcub : f (c 1) + f (c 2) * (f t)^3 + f (c 3) * (f s)^3 = 0 := by
      have hp : (f (c 1) + f (c 2) * (f t)^3 + f (c 3) * (f s)^3) *
          cubicNorm σ τ u = 0 := by
        linear_combination h₃ - cubicNorm σ τ (x 0) * h₀ - B * hl - C * hq
      exact (mul_eq_zero.mp hp).resolve_right (cubicNorm_ne_zero σ τ hu)
    have hp : f (c 3) * f s * (f s - 1) * (f s - f t) = 0 := by
      linear_combination hcub - (1 + f t) * hq + f t * hl
    have hs₀ : f s ≠ 0 := by intro h; apply hw0; simpa [h] using hws
    have hs₁ : f s - 1 ≠ 0 := by
      intro h
      apply hwu
      simpa [sub_eq_zero.mp h] using hws
    have hst : f s - f t ≠ 0 := by
      intro h
      apply hwv
      rw [hws, sub_eq_zero.mp h, ← hv]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hf₃ hs₀) hs₁) hst) hp

/-- Any four distinct images under the square-and-conjugate-norm map are affine independent. -/
theorem affineIndependent_four (hdegree : Module.finrank F E = 3)
    (h_two : (2 : F) ≠ 0) (σ τ : E →ₐ[F] E)
    (x : Fin 4 → E) (hx : Function.Injective x) :
    AffineIndependent F (fun i => (x i, (x i)^2, cubicNorm σ τ (x i))) := by
  rw [affineIndependent_iff_of_fintype]
  intro c hc hp
  rw [Finset.univ.weightedVSub_eq_linear_combination hc] at hp
  apply four_moments hdegree h_two σ τ x hx c
  · simpa only [map_sum, map_zero] using congrArg (algebraMap F E) hc
  · simpa [Fin.sum_univ_four, Algebra.smul_def] using congrArg Prod.fst hp
  · simpa [Fin.sum_univ_four, Algebra.smul_def] using
      congrArg (fun z : E × E × E => z.2.1) hp
  · simpa [Fin.sum_univ_four, Algebra.smul_def] using
      congrArg (fun z : E × E × E => z.2.2) hp

/-- The same conclusion with a base-field-valued norm, once its conjugate formula is supplied. -/
theorem affineIndependent_norm_four (hdegree : Module.finrank F E = 3)
    (h_two : (2 : F) ≠ 0) (σ τ : E →ₐ[F] E)
    (N : E → F) (hN : ∀ z, algebraMap F E (N z) = cubicNorm σ τ z)
    (x : Fin 4 → E) (hx : Function.Injective x) :
    AffineIndependent F (fun i => (x i, (x i)^2, N (x i))) := by
  rw [affineIndependent_iff_of_fintype]
  intro c hc hp
  rw [Finset.univ.weightedVSub_eq_linear_combination hc] at hp
  apply four_moments hdegree h_two σ τ x hx c
  · simpa only [map_sum, map_zero] using congrArg (algebraMap F E) hc
  · simpa [Fin.sum_univ_four, Algebra.smul_def] using congrArg Prod.fst hp
  · simpa [Fin.sum_univ_four, Algebra.smul_def] using
      congrArg (fun z : E × E × F => z.2.1) hp
  · have hn : ∑ i, c i * N (x i) = 0 := by
      simpa [Fin.sum_univ_four] using congrArg (fun z : E × E × F => z.2.2) hp
    simpa only [map_sum, map_mul, hN, map_zero] using congrArg (algebraMap F E) hn

end Erdos714CubicEmbedding

#print axioms Erdos714CubicEmbedding.four_moments
#print axioms Erdos714CubicEmbedding.affineIndependent_four
#print axioms Erdos714CubicEmbedding.affineIndependent_norm_four
