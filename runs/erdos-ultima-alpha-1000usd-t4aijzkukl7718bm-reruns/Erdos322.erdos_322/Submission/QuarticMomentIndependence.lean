import FormalConjecturesUtil

/-!
The first, second, and fourth power sums in four variables are algebraically
independent. This rules out a universal polynomial equality among the three
moments, but is not an estimate for their attained integer values.
-/

namespace Erdos322Research.QuarticMomentIndependence

noncomputable section
open MvPolynomial

private abbrev P3 := MvPolynomial (Fin 3) ℚ
private abbrev P4 := MvPolynomial (Fin 4) ℚ
private abbrev e (k : ℕ) : P4 := esymm (Fin 4) ℚ k
private abbrev p (k : ℕ) : P4 := psum (Fin 4) ℚ k

private theorem second_formula : p 2 = (e 1)^2 - 2*e 2 := by
  have h := psum_eq_mul_esymm_sub_sum (Fin 4) ℚ 2 (by decide)
  have hs : (Finset.antidiagonal 2).filter (fun a => a.1 ∈ Set.Ioo 0 2) = {(1,1)} := by decide
  rw [hs] at h
  simp only [Finset.sum_singleton] at h
  norm_num only [pow_succ, pow_zero, one_mul, mul_one, neg_mul, neg_neg, sub_neg_eq_add,
    psum_one, ← esymm_one] at h
  linear_combination h

private theorem third_formula : p 3 = (e 1)^3 - 3*e 1*e 2 + 3*e 3 := by
  have h := psum_eq_mul_esymm_sub_sum (Fin 4) ℚ 3 (by decide)
  have hs : (Finset.antidiagonal 3).filter (fun a => a.1 ∈ Set.Ioo 0 3) =
      {(1,2),(2,1)} := by decide
  rw [hs] at h
  norm_num [psum_one, ← esymm_one, ← second_formula] at h
  have h2 := second_formula
  linear_combination h + e 1*h2

private theorem fourth_formula :
    p 4 = (e 1)^4 - 4*(e 1)^2*e 2 + 2*(e 2)^2 + 4*e 1*e 3 - 4*e 4 := by
  have h := psum_eq_mul_esymm_sub_sum (Fin 4) ℚ 4 (by decide)
  have hs : (Finset.antidiagonal 4).filter (fun a => a.1 ∈ Set.Ioo 0 4) =
      {(1,3),(2,2),(3,1)} := by decide
  rw [hs] at h
  norm_num [psum_one, ← esymm_one] at h
  have h2 := second_formula
  have h3 := third_formula
  linear_combination h + e 1*h3 - e 2*h2

private def elementaryMap : P4 →ₐ[ℚ] P4 :=
  aeval (fun i : Fin 4 => e (i.val+1))

private theorem elementaryMap_injective : Function.Injective elementaryMap := by
  intro a b hab
  apply esymmAlgHom_injective ℚ (σ := Fin 4) (n := 4) (by simp)
  apply Subtype.ext
  simpa only [esymmAlgHom_apply] using hab

private def formalPower : P3 →ₐ[ℚ] P4 :=
  aeval ![X 0, X 0^2-2*X 1,
    X 0^4-4*X 0^2*X 1+2*X 1^2+4*X 0*X 2-4*X 3]

private def halfSecond : P3 := C (1/2)*(X 0^2-X 1)
private def lastCoefficient : P3 :=
  X 0^4-4*X 0^2*halfSecond+2*halfSecond^2-X 2

private def formalSection : P4 →ₐ[ℚ] P3 :=
  aeval ![X 0, halfSecond, 0, C (1/4)*lastCoefficient]

private theorem formal_left_inverse : formalSection.comp formalPower = AlgHom.id ℚ P3 := by
  have hhalf : (2 : P3)*C (1/2) = 1 := by
    calc
      (2 : P3)*C (1/2) = C (2*(1/2) : ℚ) := by rw [map_mul, map_ofNat]
      _ = 1 := by norm_num
  have hquarter : (4 : P3)*C (1/4) = 1 := by
    calc
      (4 : P3)*C (1/4) = C (4*(1/4) : ℚ) := by rw [map_mul, map_ofNat]
      _ = 1 := by norm_num
  simp only [one_div] at hhalf hquarter
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [formalSection, formalPower]
  · simp [formalSection, formalPower, halfSecond, map_ofNat]
    linear_combination -(X 0^2-X 1 : P3)*hhalf
  · simp [formalSection, formalPower, map_ofNat]
    dsimp [lastCoefficient]
    linear_combination -(X 0^4-4*X 0^2*halfSecond+2*halfSecond^2-X 2 : P3)*hquarter

private theorem formalPower_injective : Function.Injective formalPower := by
  have h : Function.LeftInverse formalSection formalPower := by
    intro p
    exact DFunLike.congr_fun formal_left_inverse p
  exact h.injective

/-- Substitution of the three actual power sums. -/
def powerMap : P3 →ₐ[ℚ] P4 := aeval ![p 1, p 2, p 4]

private theorem factorization : powerMap = elementaryMap.comp formalPower := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [powerMap, elementaryMap, formalPower, p, e, esymm_one]
  · simpa [powerMap, elementaryMap, formalPower, map_ofNat] using second_formula
  · simpa [powerMap, elementaryMap, formalPower, map_ofNat] using fourth_formula

/-- No nonzero rational polynomial vanishes identically upon substituting the
first, second, and fourth power sums in four independent variables. -/
theorem powerMap_injective : Function.Injective powerMap := by
  rw [factorization]
  exact elementaryMap_injective.comp formalPower_injective

/-- The corresponding algebraic-independence statement. -/
theorem power_sums_algebraically_independent :
    AlgebraicIndependent ℚ ![psum (Fin 4) ℚ 1, psum (Fin 4) ℚ 2, psum (Fin 4) ℚ 4] := by
  exact algebraicIndependent_iff_injective_aeval.mpr powerMap_injective

private theorem eval_powerMap (x : Fin 4 → ℚ) (P : P3) :
    eval x (powerMap P) = eval ![∑ i, x i, ∑ i, x i^2, ∑ i, x i^4] P := by
  change (aeval x) (powerMap P) = _
  rw [powerMap, aeval_eq_bind₁, aeval_bind₁]
  have he : (fun i : Fin 3 => aeval x (![p 1, p 2, p 4] i)) =
      ![∑ i, x i, ∑ i, x i^2, ∑ i, x i^4] := by
    funext i
    fin_cases i <;> simp [p, psum]
  exact congrArg (fun f : Fin 3 → ℚ => aeval f P) he

/-- Even when only nonnegative integer quadruples are tested, there is no
nonzero rational polynomial identity common to their three moment values. -/
theorem no_universal_nat_relation (P : P3)
    (h : ∀ a : Fin 4 → ℕ,
      eval ![∑ i, (a i : ℚ), ∑ i, (a i : ℚ)^2, ∑ i, (a i : ℚ)^4] P = 0) :
    P = 0 := by
  apply powerMap_injective
  rw [map_zero]
  let S : Fin 4 → Set ℚ := fun _ => Set.range (fun n : ℕ => (n : ℚ))
  have hS (i : Fin 4) : (S i).Infinite :=
    Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ))
  apply MvPolynomial.funext_set S hS
  intro x hx
  have hex (i : Fin 4) : ∃ a : ℕ, (a : ℚ) = x i := hx i (Set.mem_univ i)
  choose a ha using hex
  have he : x = fun i => (a i : ℚ) := funext (fun i => (ha i).symm)
  rw [eval_powerMap, he, map_zero]
  exact h a

/-- A nonzero polynomial fails at some natural moment triple. -/
theorem exists_nat_moment_ne_zero (P : P3) (hP : P ≠ 0) :
    ∃ a : Fin 4 → ℕ,
      eval ![∑ i, (a i : ℚ), ∑ i, (a i : ℚ)^2, ∑ i, (a i : ℚ)^4] P ≠ 0 := by
  by_contra h
  push_neg at h
  exact hP (no_universal_nat_relation P h)

end
end Erdos322Research.QuarticMomentIndependence
