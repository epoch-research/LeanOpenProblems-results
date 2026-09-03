import Submission.HigherUniformityPerturbation

/-! A uniform separation bound for distinct normalized polynomial phases.
The degree, but not the size of the finite abelian group, controls the gap. -/
namespace Erdos3HigherPolynomialSeparation
open Finset Erdos3HigherUniformityDefect Erdos3HigherUniformityPerturbation
  Erdos3HigherPhaseDifferences Erdos3HigherLocalPolynomialProgressions
  Erdos3HigherPhaseRepresentation Erdos3LinearFormsUniformity Erdos3FiniteUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2000000
variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def phaseMean (q : G → Additive Circle) : ℂ := 𝔼 x : G, phase (q x)

noncomputable def polynomialGap (n : ℕ) : ℝ := (1/4)^n

lemma polynomialGap_pos (n : ℕ) : 0 < polynomialGap n := pow_pos (by norm_num) _
lemma polynomialGap_le_one (n : ℕ) : polynomialGap n ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)
lemma polynomialGap_succ (n : ℕ) : polynomialGap (n+1) = polynomialGap n/4 := by
  unfold polynomialGap
  rw [pow_succ]
  ring

lemma global_polynomial_derivative (n : ℕ) (q : G → Additive Circle)
    (hq : IsLocallyPolynomial Set.univ (n+1) q) (a : G) :
    IsLocallyPolynomial Set.univ n (fwdDiff a q) := by
  intro x h _
  have hh := hq x (Fin.cons a h) (fun _ ↦ Set.mem_univ _)
  simpa only [cubeDifference,Fin.cons_zero,Fin.cons_succ] using hh

lemma global_polynomial_zero_constant (q : G → Additive Circle)
    (hq : IsLocallyPolynomial Set.univ 0 q) : ∀ x, q x = q 0 := by
  intro x
  have hh := hq 0 (fun _ ↦ x) (fun _ ↦ Set.mem_univ _)
  simpa only [cubeDifference,fwdDiff,zero_add,sub_eq_zero] using hh

lemma phaseMean_norm_le (q : G → Additive Circle) : ‖phaseMean q‖ ≤ 1 :=
  (RCLike.norm_expect_le (K := ℂ)).trans
    (expect_le univ_nonempty (fun x _ ↦ (phase_norm (q x)).le))

lemma phaseMean_derivative_re (q : G → Additive Circle) :
    (𝔼 h : G, (phaseMean (fwdDiff h q)).re) = ‖phaseMean q‖^2 := by
  unfold phaseMean
  simp_rw [expect_re]
  have he (h x : G) : phase (fwdDiff h q x) = derivative (fun x ↦ phase (q x)) h x :=
    congr_fun (phase_fwdDiff q h) x
  simp_rw [he]
  exact derivative_re_mean _

/-- A constant derivative of a phase with nonzero mean must be trivial. -/
lemma constant_derivative_zero (q : G → Additive Circle) (hmean : phaseMean q ≠ 0)
    (h : G) (hc : ∀ x, fwdDiff h q x = fwdDiff h q 0) :
    ∀ x, fwdDiff h q x = 0 := by
  let z := fwdDiff h q 0
  have hshift (x : G) : q (x+h) = z+q x := sub_eq_iff_eq_add.mp (hc x)
  have hμ : phaseMean q = phase z*phaseMean q := by
    calc
      _ = 𝔼 x : G, phase (q (x+h)) :=
        (Fintype.expect_equiv (Equiv.addRight h) _ _ (fun _ ↦ rfl)).symm
      _ = 𝔼 x : G, phase z*phase (q x) := by simp only [hshift,phase_add]
      _ = _ := (mul_expect ..).symm
  have hz : phase z = 1 := by
    have he : phase z*phaseMean q = 1*phaseMean q := by simpa only [one_mul] using hμ.symm
    exact mul_right_cancel₀ hmean he
  have hz0 := (phase_eq_one_iff z).mp hz
  intro x
  exact (hc x).trans hz0

/-- A nonconstant polynomial phase has a uniform gap below maximal mean.
The constant 4^-n is intentionally conservative and independent of |G|. -/
theorem polynomial_mean_gap (n : ℕ) (q : G → Additive Circle)
    (hq : IsLocallyPolynomial Set.univ n q) (hnon : ¬ ∀ x, q x = q 0) :
    ‖phaseMean q‖^2 ≤ 1-polynomialGap n := by
  induction n generalizing q with
  | zero => exact (hnon (global_polynomial_zero_constant q hq)).elim
  | succ n ih =>
    rw [polynomialGap_succ]
    by_cases hmean : phaseMean q = 0
    · rw [hmean,norm_zero,zero_pow (by decide : 2 ≠ 0)]
      have hg := polynomialGap_le_one n
      linarith only [hg]
    push_neg at hnon
    obtain ⟨a,ha⟩ := hnon
    let m : G → ℝ := fun h ↦ (phaseMean (fwdDiff h q)).re
    have hm1 (h : G) : m h ≤ 1 :=
      (Complex.re_le_norm _).trans (phaseMean_norm_le _)
    have hsmall (h : G) (hh : ¬ ∀ x, fwdDiff h q x = fwdDiff h q 0) :
        m h ≤ 1-polynomialGap n/2 := by
      have hgap := ih (fwdDiff h q) (global_polynomial_derivative n q hq h) hh
      have hre := Complex.re_le_norm (phaseMean (fwdDiff h q))
      have hsq := sq_nonneg (‖phaseMean (fwdDiff h q)‖-1)
      dsimp only [m]
      nlinarith only [hgap,hre,hsq]
    have hpair (h : G) : m h+m (h+a) ≤ 2-polynomialGap n/2 := by
      by_cases hh : ∀ x, fwdDiff h q x = fwdDiff h q 0
      · have hh0 := constant_derivative_zero q hmean h hh
        have hha : ¬ ∀ x, fwdDiff (h+a) q x = fwdDiff (h+a) q 0 := by
          intro he
          have he0 := constant_derivative_zero q hmean (h+a) he
          have h1 := hh0 a
          have h2 := he0 0
          simp only [fwdDiff,zero_add] at h1 h2
          apply ha
          rw [add_comm a h] at h1
          exact (sub_eq_zero.mp h1).symm.trans (sub_eq_zero.mp h2)
        linarith only [hm1 h,hsmall (h+a) hha]
      · linarith only [hsmall h hh,hm1 (h+a)]
    have hbound := expect_le univ_nonempty (fun h _ ↦ hpair h)
    have hshift : (𝔼 h : G, m (h+a)) = 𝔼 h : G, m h :=
      Fintype.expect_equiv (Equiv.addRight a) _ _ (fun _ ↦ rfl)
    rw [expect_add_distrib,hshift] at hbound
    have hm : (𝔼 h : G, m h) = ‖phaseMean q‖^2 := phaseMean_derivative_re q
    rw [hm] at hbound
    linarith only [hbound]

lemma cubeDifference_sub (k : ℕ) (q p : G → Additive Circle)
    (h : Fin k → G) (x : G) :
    cubeDifference k (fun y ↦ q y-p y) h x =
      cubeDifference k q h x-cubeDifference k p h x := by
  induction k generalizing q p with
  | zero => rfl
  | succ k ih =>
    have he : fwdDiff (h 0) (fun y ↦ q y-p y) =
        fun y ↦ fwdDiff (h 0) q y-fwdDiff (h 0) p y := by
      funext y
      simp only [fwdDiff]
      abel
    rw [cubeDifference,he,ih]
    rfl

lemma global_polynomial_sub (n : ℕ) (q p : G → Additive Circle)
    (hq : IsLocallyPolynomial Set.univ n q)
    (hp : IsLocallyPolynomial Set.univ n p) :
    IsLocallyPolynomial Set.univ n (fun x ↦ q x-p x) := by
  intro x h hR
  rw [cubeDifference_sub,hq x h hR,hp x h hR,sub_self]

lemma phase_distance_square_mean (q p : G → Additive Circle) :
    (𝔼 x : G, ‖phase (q x)-phase (p x)‖^2) =
      2*(1-(phaseMean (fun x ↦ q x-p x)).re) := by
  have he (x : G) : ‖phase (q x)-phase (p x)‖^2 =
      2*(1-(phase (q x-p x)).re) := by
    rw [phase_sub_norm,Complex.norm_sub_one_sq_eq_of_norm_eq_one (phase_norm _)]
  simp_rw [he]
  rw [← mul_expect,expect_sub_distrib,Fintype.expect_const]
  unfold phaseMean
  rw [expect_re]

/-- Distinct polynomial phases, modulo constants, have a fixed L2 separation. -/
theorem polynomial_distance_square_gap (n : ℕ) (q p : G → Additive Circle)
    (hq : IsLocallyPolynomial Set.univ n q)
    (hp : IsLocallyPolynomial Set.univ n p)
    (hne : ¬ ∀ x, q x-p x = q 0-p 0) :
    polynomialGap n ≤ 𝔼 x : G, ‖phase (q x)-phase (p x)‖^2 := by
  have hh := polynomial_mean_gap n (fun x ↦ q x-p x) (global_polynomial_sub n q p hq hp) hne
  have hre := Complex.re_le_norm (phaseMean (fun x ↦ q x-p x))
  have hsq := sq_nonneg (‖phaseMean (fun x ↦ q x-p x)‖-1)
  rw [phase_distance_square_mean]
  nlinarith only [hh,hre,hsq]

lemma phase_distance_square_le (q p : G → Additive Circle) :
    (𝔼 x : G, ‖phase (q x)-phase (p x)‖^2) ≤
      2*meanDistance (fun x ↦ phase (q x)) (fun x ↦ phase (p x)) := by
  unfold meanDistance
  rw [mul_expect]
  apply expect_le_expect
  intro x _
  have hb : ‖phase (q x)-phase (p x)‖ ≤ 2 :=
    (norm_sub_le _ _).trans_eq (by rw [phase_norm,phase_norm]; norm_num)
  have hn := norm_nonneg (phase (q x)-phase (p x))
  nlinarith only [hb,hn]

/-- Close polynomial phases differ by a constant, with a degree-only radius. -/
theorem close_polynomials_constant_difference (n : ℕ) (q p : G → Additive Circle)
    (hq : IsLocallyPolynomial Set.univ n q)
    (hp : IsLocallyPolynomial Set.univ n p)
    (hclose : meanDistance (fun x ↦ phase (q x)) (fun x ↦ phase (p x)) < polynomialGap n/2) :
    ∀ x, q x-p x = q 0-p 0 := by
  by_contra hne
  have hl := polynomial_distance_square_gap n q p hq hp hne
  have hu := phase_distance_square_le q p
  linarith only [hl,hu,hclose]

/-- In particular, normalized polynomial phases in this radius are identical. -/
theorem close_normalized_polynomials_eq (n : ℕ) (q p : G → Additive Circle)
    (hq : IsLocallyPolynomial Set.univ n q)
    (hp : IsLocallyPolynomial Set.univ n p) (h0 : q 0 = p 0)
    (hclose : meanDistance (fun x ↦ phase (q x)) (fun x ↦ phase (p x)) < polynomialGap n/2) :
    q = p := by
  funext x
  have hh := close_polynomials_constant_difference n q p hq hp hclose x
  rw [h0,sub_self] at hh
  exact sub_eq_zero.mp hh

#print axioms polynomial_mean_gap
#print axioms polynomial_distance_square_gap
#print axioms close_normalized_polynomials_eq
end Erdos3HigherPolynomialSeparation
