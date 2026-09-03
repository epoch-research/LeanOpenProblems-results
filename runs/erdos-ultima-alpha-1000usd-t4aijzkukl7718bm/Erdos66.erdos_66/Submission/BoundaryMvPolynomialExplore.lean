import Submission.LogBoundaryPolynomialExplore

/-! The polynomial nonvanishing necessary condition, stated using Mathlib's
actual bivariate polynomials and the original radial argument r. -/
namespace Erdos66BoundaryMvPolynomial
open Filter AdditiveCombinatorics Erdos66Generating Erdos66LogBoundaryPolynomial
open scoped Classical Topology
set_option maxHeartbeats 1800000

noncomputable def degreePair (d : Fin 2 →₀ ℕ) : ℕ×ℕ := (d 0,d 1)
noncomputable def exponentPair (p : ℕ×ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![p.1,p.2]

lemma exponentPair_degreePair (d : Fin 2 →₀ ℕ) : exponentPair (degreePair d)=d := by
  ext i
  fin_cases i <;> simp [exponentPair,degreePair]

lemma degreePair_injective : Function.Injective degreePair := by
  intro d e h
  rw [←exponentPair_degreePair d,←exponentPair_degreePair e,h]

lemma monomial_product (d : Fin 2 →₀ ℕ) (x y : ℝ) :
    (∏ i∈d.support, (![x,y] i)^d i)=x^(degreePair d).1*y^(degreePair d).2 := by
  calc
    _ = d.prod (fun i k ↦ (![x,y] i)^k) := rfl
    _ = ∏ i : Fin 2, (![x,y] i)^d i := Finsupp.prod_fintype _ _ (by simp)
    _ = _ := by rw [Fin.prod_univ_two]; simp [degreePair]

lemma polynomial_eval_pair (P : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    (MvPolynomial.eval ![x,y]) P=
      ∑ p∈P.support.image degreePair, MvPolynomial.coeff (exponentPair p) P*(x^p.1*y^p.2) := by
  rw [Finset.sum_image (fun d hd e he h ↦ degreePair_injective h),MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro d hd
  rw [exponentPair_degreePair,monomial_product]

/-- Every nonzero bivariate polynomial is eventually nonzero at the
boundary distance and generating function of a hypothetical witness. -/
theorem witness_boundary_eval_ne_zero {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (P : MvPolynomial (Fin 2) ℝ) (hP : P≠0) :
    ∀ᶠ r in 𝓝[<] 1, (MvPolynomial.eval ![1-r,series (indicator A) r]) P≠0 := by
  have hS := (MvPolynomial.support_nonempty.mpr hP).image degreePair
  have ha : ∀ p∈P.support.image degreePair, MvPolynomial.coeff (exponentPair p) P≠0 := by
    intro p hp
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hp
    rw [exponentPair_degreePair]
    exact MvPolynomial.mem_support_iff.mp hd
  have hh := witness_polynomial_eventually_ne_zero hc h (P.support.image degreePair) hS
    (fun p ↦ MvPolynomial.coeff (exponentPair p) P) ha
  simpa only [polynomial_eval_pair] using hh

noncomputable def boundaryShift : MvPolynomial (Fin 2) ℝ →+* MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![1-MvPolynomial.X 0,MvPolynomial.X 1]

lemma boundaryShift_involutive : Function.Involutive boundaryShift := by
  have he : boundaryShift.comp boundaryShift=RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [boundaryShift]
    · intro i
      fin_cases i <;> simp [boundaryShift]
  intro P
  exact DFunLike.congr_fun he P

lemma eval_boundaryShift (P : MvPolynomial (Fin 2) ℝ) (r y : ℝ) :
    (MvPolynomial.eval ![1-r,y]) (boundaryShift P)=(MvPolynomial.eval ![r,y]) P := by
  have he : (MvPolynomial.eval ![1-r,y]).comp boundaryShift=MvPolynomial.eval ![r,y] := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [boundaryShift]
    · intro i
      fin_cases i <;> simp [boundaryShift]
  exact DFunLike.congr_fun he P

/-- The variable r and the generating function satisfy no fixed nonzero
polynomial relation near r=1. This does not assert that Boolean series
must be algebraic; they need not be. -/
theorem witness_eval_ne_zero {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (P : MvPolynomial (Fin 2) ℝ) (hP : P≠0) :
    ∀ᶠ r in 𝓝[<] 1, (MvPolynomial.eval ![r,series (indicator A) r]) P≠0 := by
  have hQ : boundaryShift P≠0 := by
    intro he
    apply hP
    calc
      P = boundaryShift (boundaryShift P) := (boundaryShift_involutive P).symm
      _ = 0 := by rw [he,map_zero]
  simpa only [eval_boundaryShift] using witness_boundary_eval_ne_zero hc h (boundaryShift P) hQ

end Erdos66BoundaryMvPolynomial
