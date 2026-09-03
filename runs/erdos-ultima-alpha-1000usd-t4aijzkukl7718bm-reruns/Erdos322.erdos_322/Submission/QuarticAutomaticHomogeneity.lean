import FormalConjecturesUtil
/-! Automatic homogeneity for polynomial fourth-power norm transfers. -/
namespace Erdos322Research.QuarticAutomaticHomogeneity
open Polynomial
private lemma constant_coordinates {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (P : Fin 4 → Polynomial R) (a : R)
    (h : ∑ i, P i^4 = C a) : ∀ i, P i = C ((P i).coeff 0) := by
  classical
  intro i
  apply Polynomial.eq_C_of_natDegree_eq_zero
  by_contra hn
  let D := Finset.univ.sup (fun j ↦ (P j).natDegree)
  have hDi : (P i).natDegree ≤ D := Finset.le_sup (f := fun j ↦ (P j).natDegree)
    (Finset.mem_univ i)
  have hDpos : 0 < D := by omega
  have hD (j : Fin 4) : (P j).natDegree ≤ D :=
    Finset.le_sup (f := fun j ↦ (P j).natDegree) (Finset.mem_univ j)
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨i⟩) (fun j ↦ (P j).natDegree)
  change D = (P j).natDegree at hj
  have hp : P j ≠ 0 := by
    intro hz
    simp [hz] at hj
    omega
  have hc : (P j).coeff D ≠ 0 := by
    rw [hj, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp
  have he : (∑ j, P j^4).coeff (4*D) = ∑ j, (P j).coeff D^4 := by
    simp only [finset_sum_coeff]
    exact Finset.sum_congr rfl (fun j _ ↦ coeff_pow_of_natDegree_le (hD j))
  have hs : (∑ j, (P j).coeff D^4) = 0 := by
    rw [← he, h]
    simpa using (Polynomial.coeff_eq_zero_of_natDegree_lt (show (C a).natDegree < 4*D by simpa using (show 0 < 4*D by omega)))
  have hpos : 0 < (P j).coeff D^4 := by positivity
  have hle := Finset.single_le_sum (f := fun j ↦ (P j).coeff D^4)
    (fun _ _ ↦ by positivity) (Finset.mem_univ j)
  rw [hs] at hle
  linarith


theorem monomial_fourth_sum (P : Fin 4 → Polynomial ℚ) (a : ℚ) (n : ℕ)
    (h : ∑ i, P i^4=Polynomial.C a*Polynomial.X^(4*n)) :
    ∃ b : Fin 4 → ℚ, ∀ i, P i=Polynomial.C (b i)*Polynomial.X^n := by
  induction n generalizing P with
  | zero =>
    have hh : ∑ i, P i^4=Polynomial.C a := by simpa using h
    refine ⟨fun i ↦ (P i).coeff 0,?_⟩
    intro i
    simpa using constant_coordinates P a hh i
  | succ n ih =>
    have hs : ∑ i, (P i).eval 0^4=0 := by
      have hh := congrArg (Polynomial.evalRingHom (0 : ℚ)) h
      simpa using hh
    have hp (i : Fin 4) : (P i).eval 0=0 := by
      have hh := Finset.single_le_sum (f := fun j ↦ (P j).eval 0^4)
        (fun _ _ ↦ by positivity) (Finset.mem_univ i)
      rw [hs] at hh
      exact eq_zero_of_pow_eq_zero (le_antisymm hh (by positivity))
    have hdiv : ∀ i, ∃ Q : Polynomial ℚ, P i=Polynomial.X*Q := fun i ↦
      Polynomial.X_dvd_iff.mpr ((Polynomial.coeff_zero_eq_eval_zero (P i)).trans (hp i))
    choose Q hQ using hdiv
    have hh : ∑ i, Q i^4=Polynomial.C a*Polynomial.X^(4*n) := by
      apply mul_left_cancel₀ (pow_ne_zero 4 (Polynomial.X_ne_zero : (Polynomial.X : Polynomial ℚ) ≠ 0))
      calc
        Polynomial.X^4*(∑ i, Q i^4)=∑ i, (Polynomial.X*Q i)^4 := by
          simp only [mul_pow,Finset.mul_sum]
        _ = Polynomial.C a*Polynomial.X^(4*(n+1)) := by simpa only [← hQ] using h
        _ = Polynomial.X^4*(Polynomial.C a*Polynomial.X^(4*n)) := by
          rw [show 4*(n+1)=4*n+4 by omega,pow_add]
          ring
    obtain ⟨b,hb⟩ := ih Q hh
    refine ⟨b,?_⟩
    intro i
    rw [hQ i,hb i,pow_succ]
    ring

open MvPolynomial
set_option maxHeartbeats 0
set_option Elab.async false

private noncomputable def lineEval {σ : Type*} (x : σ → ℚ) : MvPolynomial σ ℚ →+* Polynomial ℚ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun j ↦ Polynomial.C (x j)*Polynomial.X)

private lemma lineEval_monomial {σ : Type*} (x : σ → ℚ) (d : σ →₀ ℕ) (a : ℚ) :
    lineEval x (monomial d a)=Polynomial.C (MvPolynomial.eval x (monomial d a))*Polynomial.X^d.degree := by
  classical
  simp only [lineEval,MvPolynomial.eval₂Hom_monomial,MvPolynomial.eval_monomial,
    Finsupp.prod,mul_pow,Finset.prod_mul_distrib,← map_pow,← map_prod,
    Finset.prod_pow_eq_pow_sum,Finsupp.degree_apply]
  simp only [map_mul]
  ring

private lemma lineEval_coeff {σ : Type*} (P : MvPolynomial σ ℚ) (x : σ → ℚ) (n : ℕ) :
    (lineEval x P).coeff n=MvPolynomial.eval x (homogeneousComponent n P) := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [homogeneousComponent_apply]
  simp only [map_sum,Polynomial.finset_sum_coeff,lineEval_monomial,
    Polynomial.coeff_C_mul_X_pow,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hn : n=d.degree
  · simp [hn]
  · simp [hn,Ne.symm hn]

private lemma eval_lineEval {σ : Type*} (P : MvPolynomial σ ℚ) (x : σ → ℚ) (t : ℚ) :
    (lineEval x P).eval t=MvPolynomial.eval (fun j ↦ x j*t) P := by
  change ((Polynomial.evalRingHom t).comp (lineEval x)) P = _
  have hh : (Polynomial.evalRingHom t).comp (lineEval x)=MvPolynomial.eval (fun j ↦ x j*t) := by
    ext <;> simp [lineEval]
  rw [hh]

/-- Homogeneity is automatic; it need not be assumed separately in a
polynomial transfer of an even-power norm. -/
theorem transfer_is_homogeneous {σ : Type*} [Fintype σ]
    (P : Fin 4 → MvPolynomial σ ℚ) (C : ℚ) (e : ℕ)
    (h : ∑ i, P i^4=MvPolynomial.C C*(∑ j : σ, MvPolynomial.X j^4)^e) :
    ∀ i, (P i).IsHomogeneous e := by
  classical
  intro i
  have heval (x : σ → ℚ) :
      MvPolynomial.eval x (homogeneousComponent e (P i))=MvPolynomial.eval x (P i) := by
    have hn : lineEval x (∑ j : σ, MvPolynomial.X j^4)=
        Polynomial.C (∑ j, x j^4)*Polynomial.X^4 := by
      simp only [lineEval,map_sum,map_pow,MvPolynomial.eval₂Hom_X',mul_pow]
      rw [← Finset.sum_mul]
    have hh : ∑ i, (lineEval x (P i))^4=
        Polynomial.C (C*(∑ j, x j^4)^e)*Polynomial.X^(4*e) := by
      have he := congrArg (lineEval x) h
      rw [map_sum,map_mul] at he
      simp only [map_pow] at he
      rw [hn] at he
      have hc : lineEval x (MvPolynomial.C C)=Polynomial.C C := by simp [lineEval]
      rw [hc] at he
      rw [he,mul_pow,← map_pow,← pow_mul,← mul_assoc,← map_mul]
    obtain ⟨b,hb⟩ := monomial_fourth_sum (fun i ↦ lineEval x (P i)) _ e hh
    rw [← lineEval_coeff,hb i]
    simp only [Polynomial.coeff_C_mul_X_pow,ite_true]
    have he := congrArg (Polynomial.evalRingHom (1 : ℚ)) (hb i)
    simpa [eval_lineEval] using he.symm
  have hp : homogeneousComponent e (P i)=P i := MvPolynomial.funext heval
  rw [← hp]
  exact homogeneousComponent_isHomogeneous _ _

end Erdos322Research.QuarticAutomaticHomogeneity
