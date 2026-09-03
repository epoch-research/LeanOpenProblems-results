import FormalConjecturesUtil

/-! Rational fourth-power representations specialize even at an apparent
pole of a rational formula. No representation-count growth is asserted. -/
namespace Erdos322Research.QuarticRationalSpecialization

open Polynomial

/-- Cancel the common powers of `X` before evaluating a rational norm identity
at zero. Positivity ensures that no coordinate has a surviving pole. -/
theorem polynomial_specialization {ι : Type*} [Fintype ι]
    (P : ι → Polynomial ℚ) (D H : Polynomial ℚ) (hD : D ≠ 0)
    (h : ∑ i, P i^4 = D^4*H) : ∃ b : ι → ℚ, ∑ i, b i^4 = H.eval 0 := by
  classical
  have aux : ∀ n : ℕ, ∀ D : Polynomial ℚ, D.natDegree=n → D ≠ 0 →
      ∀ P : ι → Polynomial ℚ, (∑ i, P i^4 = D^4*H) →
      ∃ b : ι → ℚ, ∑ i, b i^4 = H.eval 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro D hn hD P h
      by_cases hz : D.eval 0 = 0
      · have hs : ∑ i, (P i).eval 0 ^ 4 = 0 := by
          have hh := congrArg (evalRingHom (0 : ℚ)) h
          simpa only [map_sum, map_pow, map_mul, coe_evalRingHom, hz, zero_pow (by decide : 4 ≠ 0), zero_mul] using hh
        have hp (i : ι) : (P i).eval 0 = 0 := by
          have hh := Finset.single_le_sum (f := fun j ↦ (P j).eval 0 ^ 4)
            (fun _ _ ↦ by positivity) (Finset.mem_univ i)
          rw [hs] at hh
          exact eq_zero_of_pow_eq_zero (le_antisymm hh (by positivity))
        have hdiv : (X : Polynomial ℚ) ∣ D := X_dvd_iff.mpr ((coeff_zero_eq_eval_zero D).trans hz)
        obtain ⟨E,hE⟩ := hdiv
        have hE0 : E ≠ 0 := by intro he; apply hD; simp [hE,he]
        have hQ : ∀ i, ∃ Q : Polynomial ℚ, P i = X*Q := fun i ↦
          X_dvd_iff.mpr ((coeff_zero_eq_eval_zero (P i)).trans (hp i))
        choose Q hQ using hQ
        have hnew : ∑ i, Q i^4 = E^4*H := by
          apply mul_left_cancel₀ (pow_ne_zero 4 (X_ne_zero : (X : Polynomial ℚ) ≠ 0))
          calc
            X^4*(∑ i, Q i^4) = ∑ i, (X*Q i)^4 := by simp only [mul_pow, Finset.mul_sum]
            _ = D^4*H := by simpa only [← hQ] using h
            _ = X^4*(E^4*H) := by rw [hE]; ring
        have hlt : E.natDegree < n := by
          rw [← hn, hE, natDegree_X_mul hE0]
          omega
        exact ih E.natDegree hlt E rfl hE0 Q hnew
      · refine ⟨fun i ↦ (P i).eval 0 / D.eval 0,?_⟩
        have hh := congrArg (evalRingHom (0 : ℚ)) h
        simp only [map_sum, map_pow, map_mul, coe_evalRingHom] at hh
        simp only [div_pow, ← Finset.sum_div, hh]
        field_simp
  exact aux D.natDegree D rfl hD P h


private noncomputable def lineSub {σ : Type*} (a b : σ → ℚ) :
    MvPolynomial σ ℚ →+* Polynomial ℚ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i ↦ Polynomial.C (a i) + Polynomial.X*Polynomial.C (b i-a i))

private theorem lineSub_eval {σ : Type*} (a b : σ → ℚ) (t : ℚ) (P : MvPolynomial σ ℚ) :
    (lineSub a b P).eval t = MvPolynomial.eval (fun i ↦ a i+t*(b i-a i)) P := by
  have he : (Polynomial.evalRingHom t).comp (lineSub a b) =
      MvPolynomial.eval (fun i ↦ a i+t*(b i-a i)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lineSub]
    · intro i
      simp [lineSub]
  exact congrArg (fun f : MvPolynomial σ ℚ →+* ℚ ↦ f P) he

/-- A polynomial identity representing `H` by rational fourth powers produces
rational representations at EVERY rational input, even where `D` vanishes. -/
theorem multivariate_specialization {ι σ : Type*} [Fintype ι]
    (P : ι → MvPolynomial σ ℚ) (D H : MvPolynomial σ ℚ) (hD : D ≠ 0)
    (h : ∑ i, P i^4 = D^4*H) (a : σ → ℚ) :
    ∃ b : ι → ℚ, ∑ i, b i^4 = MvPolynomial.eval a H := by
  classical
  obtain ⟨z,hz⟩ : ∃ z : σ → ℚ, MvPolynomial.eval z D ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hD
    apply MvPolynomial.funext
    intro z
    simpa only [map_zero] using hn z
  have hL : lineSub a z D ≠ 0 := by
    intro he
    apply hz
    have hh := congrArg (Polynomial.eval 1) he
    simpa only [lineSub_eval, one_mul, add_sub_cancel, Polynomial.eval_zero] using hh
  have hid : ∑ i, (lineSub a z (P i))^4 = (lineSub a z D)^4*(lineSub a z H) := by
    simpa only [map_sum,map_pow,map_mul] using congrArg (lineSub a z) h
  obtain ⟨b,hb⟩ := polynomial_specialization (fun i ↦ lineSub a z (P i))
    (lineSub a z D) (lineSub a z H) hL hid
  refine ⟨b,?_⟩
  simpa only [lineSub_eval, zero_mul, add_zero] using hb

end Erdos322Research.QuarticRationalSpecialization
