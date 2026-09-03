import Submission.QuarticSquareLinearRigidity

/-! A parity extension of square-target linear rigidity to even quadratic
curves. This only constrains such parametrizations; it is not a point-count
bound for the conjecture. -/
namespace Erdos322Research.QuarticSquareEvenCurve
noncomputable section
open Polynomial Finset
set_option Elab.async false
set_option maxHeartbeats 0

private lemma coeff_comp_neg (g : ℚ[X]) (n : ℕ) :
    (g.comp (-X)).coeff n=(-1 : ℚ)^n*g.coeff n := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp,coeff_add,hp,hq,mul_add]
  | monomial m a =>
    have hp : (-1 : ℚ[X])^m=C ((-1 : ℚ)^m) := by simp
    rw [monomial_comp,neg_pow,hp,← mul_assoc,← C_mul,
      coeff_C_mul_X_pow,coeff_monomial]
    by_cases h : n=m
    · subst n; simp [mul_comm]
    · simp [h,Ne.symm h]

/-- An even polynomial with a polynomial square root and nonzero constant
coefficient has an even square root. -/
theorem square_root_even (f g : ℚ[X]) (h : expand ℚ 2 f=g^2)
    (h0 : g.coeff 0 ≠ 0) : expand ℚ 2 (contract 2 g)=g := by
  have he : (expand ℚ 2 f).comp (-X)=expand ℚ 2 f := by
    rw [expand_eq_comp_X_pow,comp_assoc]
    congr 1
    simp
  have hs : (g.comp (-X))^2=g^2 := by rw [← pow_comp,← h,he]
  have hg : g.comp (-X)=g := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hg | hg
    · exact hg
    · have hh := congrArg (fun p : ℚ[X] ↦ p.coeff 0) hg
      simp [coeff_comp_neg] at hh
      exact False.elim (h0 (by linarith))
  have hz (n : ℕ) (hn : ¬2 ∣ n) : g.coeff n=0 := by
    have he := congrArg (fun p : ℚ[X] ↦ p.coeff n) hg
    dsimp only at he
    rw [coeff_comp_neg] at he
    have ho : Odd n := Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hn)
    rw [ho.neg_one_pow] at he
    linarith
  ext n
  rw [coeff_expand (by decide : 0<2)]
  split_ifs with hn
  · rw [coeff_contract (by decide : 2 ≠ 0),Nat.div_mul_cancel hn]
  · exact (hz n hn).symm

/-- Squareness descends through substitution by `X^2` when the square root
has a nonzero constant coefficient. -/
theorem square_of_square_expansion (f g : ℚ[X]) (h : expand ℚ 2 f=g^2)
    (h0 : g.coeff 0 ≠ 0) : f=(contract 2 g)^2 := by
  apply expand_injective (by decide : 0<2)
  rw [map_pow,square_root_even f g h h0]
  exact h

private lemma fourth_sum_pos (a : Fin 4 → ℚ) (h : ∃ i, a i ≠ 0) :
    0<∑ i, a i^4 := by
  obtain ⟨i,hi⟩ := h
  apply sum_pos' (fun j _ ↦ by positivity)
  exact ⟨i,mem_univ i,pow_pos (sq_pos_of_ne_zero hi) 2 |>.trans_eq (by ring)⟩

/-- The two coefficient vectors of an even quadratic polynomial curve with
square fourth-power norm must be proportional. Squareness at the second
endpoint is explicit, as it is in applications to homogeneous quadratic maps. -/
theorem even_quadratic_minors_zero (a b : Fin 4 → ℚ) (g : ℚ[X])
    (hb : IsSquare (∑ i, b i^4))
    (h : (∑ i, (C (a i)+C (b i)*X^2)^4)=g^2) (i j : Fin 4) :
    a i*b j=a j*b i := by
  by_cases ha : ∃ i, a i ≠ 0
  · let f : ℚ[X] := ∑ i, (C (a i)+C (b i)*X)^4
    have hexpand : expand ℚ 2 f=g^2 := by
      simpa [f,map_sum,map_pow,map_add,map_mul] using h
    have hconst := congrArg (fun p : ℚ[X] ↦ p.eval 0) h
    simp only [eval_finset_sum,eval_pow,eval_add,eval_C,eval_mul,eval_X,
      zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at hconst
    have hg0 : g.coeff 0 ≠ 0 := by
      intro hz
      have he : g.eval 0=0 := by simpa only [coeff_zero_eq_eval_zero] using hz
      rw [he,zero_pow (by decide : 2 ≠ 0)] at hconst
      exact (ne_of_gt (fourth_sum_pos a ha)) hconst
    have hs := square_of_square_expansion f g hexpand hg0
    have haf (t : ℚ) : IsSquare (∑ l, (a l+t*b l)^4) := by
      have he := congrArg (fun p : ℚ[X] ↦ p.eval t) hs
      simp only [f,eval_finset_sum,eval_pow,eval_add,eval_C,eval_mul,eval_X] at he
      apply (isSquare_iff_exists_sq _).mpr
      refine ⟨(contract 2 g).eval t,?_⟩
      simpa [mul_comm] using he
    apply QuarticSquareLinearRigidity.pointwise_square_minors_zero a b ?_ i j
    intro x y
    by_cases hx : x=0
    · subst x
      simpa only [zero_mul,zero_add,mul_pow,← mul_sum] using
        (show IsSquare (y^4) from ⟨y^2,by ring⟩).mul hb
    · obtain ⟨r,hr⟩ := (haf (y/x)).exists_sq
      apply (isSquare_iff_exists_sq _).mpr
      refine ⟨x^2*r,?_⟩
      calc
        (∑ l, (x*a l+y*b l)^4) = x^4*∑ l, (a l+(y/x)*b l)^4 := by
          rw [mul_sum]
          apply sum_congr rfl
          intro l _
          field_simp
        _ = (x^2*r)^2 := by rw [hr]; ring
  · push_neg at ha
    simp [ha]


/-- For homogeneous quadratic outputs, a common polar-orthogonal direction
has output proportional to the base output whenever a polynomial square root
exists along the line. -/
theorem quadratic_polar_minors_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    (Q : Fin 4 → QuadraticForm ℚ V) (x u : V) (g : ℚ[X])
    (horth : ∀ i, QuadraticMap.polar (Q i) x u=0)
    (hu : IsSquare (∑ i, (Q i u)^4))
    (hroot : ∀ t : ℚ, (∑ i, (Q i (x+t • u))^4)=(g.eval t)^2)
    (i j : Fin 4) : Q i x*Q j u=Q j x*Q i u := by
  apply even_quadratic_minors_zero (fun i ↦ Q i x) (fun i ↦ Q i u) g hu ?_ i j
  apply Polynomial.funext
  intro t
  simp only [eval_finset_sum,eval_pow,eval_add,eval_C,eval_mul,eval_X]
  convert hroot t using 1
  apply sum_congr rfl
  intro l _
  congr 1
  rw [QuadraticMap.map_add (Q l) x (t • u),QuadraticMap.map_smul,
    QuadraticMap.polar_smul_right,horth l]
  simp only [smul_eq_mul]
  ring

/-- This applies to any polynomial square target, with no degree restriction
on its given square root and no special choice of the source norm. -/
theorem polynomial_square_polar_minors_zero {σ : Type*}
    (Q : Fin 4 → QuadraticForm ℚ (σ → ℚ)) (G : MvPolynomial σ ℚ)
    (h : ∀ v : σ → ℚ, (∑ i, (Q i v)^4)=(MvPolynomial.eval v G)^2)
    (x u : σ → ℚ) (horth : ∀ i, QuadraticMap.polar (Q i) x u=0)
    (i j : Fin 4) : Q i x*Q j u=Q j x*Q i u := by
  let g : ℚ[X] := MvPolynomial.eval₂ Polynomial.C (fun k ↦ C (x k)+X*C (u k)) G
  have hg (t : ℚ) : g.eval t=MvPolynomial.eval (x+t • u) G := by
    change (Polynomial.evalRingHom t) (MvPolynomial.eval₂ _ _ G)=_
    rw [MvPolynomial.eval₂_comp_left]
    have hc : (Polynomial.evalRingHom t).comp Polynomial.C=RingHom.id ℚ := by
      ext a
      simp
    rw [hc,MvPolynomial.eval₂_id]
    have hv : (⇑(Polynomial.evalRingHom t) ∘ fun k ↦ C (x k)+X*C (u k))=x+t • u := by
      funext k
      simp [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [hv]
  apply quadratic_polar_minors_zero Q x u g horth ?_ ?_ i j
  · exact (isSquare_iff_exists_sq _).mpr ⟨MvPolynomial.eval u G,h u⟩
  · intro t
    rw [hg]
    exact h (x+t • u)

/-- Consequently the whole source plane spanned by a base vector and a common
polar-orthogonal direction maps into one rational output line. This is a
structural restriction, not a bound on the number of source planes. -/
theorem polynomial_square_polar_plane_radial {σ : Type*}
    (Q : Fin 4 → QuadraticForm ℚ (σ → ℚ)) (G : MvPolynomial σ ℚ)
    (h : ∀ v : σ → ℚ, (∑ i, (Q i v)^4)=(MvPolynomial.eval v G)^2)
    (x u : σ → ℚ) (horth : ∀ i, QuadraticMap.polar (Q i) x u=0)
    (j : Fin 4) (hj : Q j x ≠ 0) (s t : ℚ) (i : Fin 4) :
    Q i (s • x+t • u)=(s^2+(Q j u/Q j x)*t^2)*Q i x := by
  have hu : Q i u=(Q j u/Q j x)*Q i x := by
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hj).mpr
    linear_combination polynomial_square_polar_minors_zero Q G h x u horth j i
  rw [QuadraticMap.map_add (Q i) (s • x) (t • u),QuadraticMap.map_smul,QuadraticMap.map_smul,
    QuadraticMap.polar_smul_left,QuadraticMap.polar_smul_right,horth i]
  simp only [smul_eq_mul]
  rw [hu]
  ring

end
end Erdos322Research.QuarticSquareEvenCurve
