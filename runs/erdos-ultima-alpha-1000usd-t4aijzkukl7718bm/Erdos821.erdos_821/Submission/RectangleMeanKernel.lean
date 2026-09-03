import Submission.DoubleCofactorKloosterman

/-!
# A finite mean bound for the rectangle error

A fourth-power Holder estimate sums the reciprocal Kloosterman bound without
losing an extra power of the modulus cutoff. Only the analytic coefficient
is estimated in the first part; the last theorem applies it to prime moduli.
-/
open Finset ArithmeticFunction
open scoped Classical BigOperators
namespace Erdos821.Kloosterman
open Erdos821.AnalyticSieve

noncomputable def modulusBound (q : ℕ) : ℝ := Real.sqrt (Real.sqrt (3*(q : ℝ)^3))

lemma modulusBound_nonneg (q : ℕ) : 0 ≤ modulusBound q := Real.sqrt_nonneg _

lemma modulusBound_fourth (q : ℕ) : modulusBound q ^ 4 = 3*(q : ℝ)^3 := by
  rw [show (4 : ℕ)=2*2 from rfl, pow_mul, modulusBound,
    Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]

lemma modulusBound_mono {q Q : ℕ} (h : q ≤ Q) : modulusBound q ≤ modulusBound Q := by
  unfold modulusBound
  gcongr

lemma harmonic_cast_mono {a b : ℕ} (hab : a ≤ b) : (harmonic a : ℝ) ≤ harmonic b := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hab) (by intros; positivity)

lemma sum_fourth_le_card_cube {I : Type*} (s : Finset I) (a : I → ℝ) :
    (∑ i ∈ s, a i)^4 ≤ (s.card : ℝ)^3 * ∑ i ∈ s, a i^4 := by
  have h1 : (∑ i ∈ s, a i)^2 ≤ (s.card : ℝ)*∑ i ∈ s, a i^2 := by
    simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] using
      sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) a
  have h2 : (∑ i ∈ s, a i^2)^2 ≤ (s.card : ℝ)*∑ i ∈ s, a i^4 := by
    calc
      _ ≤ (s.card : ℝ)*∑ i ∈ s, (a i^2)^2 := by
        simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] using
          sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => a i^2)
      _ = _ := by
        congr 1
        apply sum_congr rfl
        intro i _
        ring
  calc
    _ = ((∑ i ∈ s, a i)^2)^2 := by ring
    _ ≤ ((s.card : ℝ)*∑ i ∈ s, a i^2)^2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (s.card : ℝ)^2*(∑ i ∈ s, a i^2)^2 := mul_pow _ _ _
    _ ≤ (s.card : ℝ)^2*((s.card : ℝ)*∑ i ∈ s, a i^4) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring

lemma sum_modulusBound_div_fourth (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, modulusBound q/(q : ℝ))^4 ≤
      3*(Q : ℝ)^3*(harmonic Q : ℝ) := by
  have hh := sum_fourth_le_card_cube (Icc 1 Q) (fun q => modulusBound q/(q : ℝ))
  have he (q : ℕ) (hq : q ∈ Icc 1 Q) : (modulusBound q/(q : ℝ))^4=3/(q : ℝ) := by
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by have := (mem_Icc.mp hq).1; omega)
    rw [div_pow, modulusBound_fourth]
    field_simp
  rw [Nat.card_Icc] at hh
  simp only [Nat.add_sub_cancel, sum_congr rfl he] at hh
  have hs : (∑ q ∈ Icc 1 Q, 3/(q : ℝ))=3*(harmonic Q : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      div_eq_mul_inv, mul_sum]
  rw [hs] at hh
  nlinarith only [hh]

lemma sum_modulusBound_div_le (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, modulusBound q/(q : ℝ)) ≤
      modulusBound Q*(1+(harmonic Q : ℝ)) := by
  have hH := harmonic_natCast_nonneg Q
  have hH4 : (harmonic Q : ℝ) ≤ (1+(harmonic Q : ℝ))^4 := by
    have h1 : 1 ≤ 1+(harmonic Q : ℝ) := by linarith
    have h2 : (1+(harmonic Q : ℝ))^2 ≤ (1+(harmonic Q : ℝ))^4 := by
      nlinarith [sq_nonneg (harmonic Q : ℝ), sq_nonneg ((harmonic Q : ℝ)^2)]
    nlinarith only [h2, hH, sq_nonneg (harmonic Q : ℝ)]
  apply (pow_le_pow_iff_left₀
    (sum_nonneg (fun q _ => div_nonneg (modulusBound_nonneg q) (Nat.cast_nonneg q)))
    (mul_nonneg (modulusBound_nonneg Q) (by positivity)) (by decide : 4 ≠ 0)).mp
  rw [mul_pow, modulusBound_fourth]
  exact (sum_modulusBound_div_fourth Q).trans
    (mul_le_mul_of_nonneg_left hH4 (by positivity))

lemma sum_modulusBound_le (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, modulusBound q) ≤ (Q : ℝ)*modulusBound Q := by
  calc
    _ ≤ ∑ _q ∈ Icc 1 Q, modulusBound Q :=
      sum_le_sum (fun q hq => modulusBound_mono (mem_Icc.mp hq).2)
    _ = _ := by simp

lemma rectangleError_nonneg (q B C : ℕ) : 0 ≤ rectangleError q B C := by
  have hH := harmonic_natCast_nonneg (q-1)
  unfold rectangleError
  positivity

noncomputable def rectangleMeanKernel (Q B C : ℕ) : ℝ :=
  modulusBound Q*((B : ℝ)+Q)*(1+(harmonic Q : ℝ))^2+(C : ℝ)*(harmonic Q : ℝ)

lemma sum_rectangleError_le (Q B C : ℕ) :
    (∑ q ∈ Icc 1 Q, rectangleError q B C) ≤ rectangleMeanKernel Q B C := by
  let H : ℝ := harmonic Q
  have hH : 0 ≤ H := harmonic_natCast_nonneg Q
  have hBH : 0 ≤ (B : ℝ)*H := by positivity
  have hK := modulusBound_nonneg Q
  calc
    _ ≤ ∑ q ∈ Icc 1 Q,
        ((B : ℝ)*H*(modulusBound q/(q : ℝ))+H^2*modulusBound q+(C : ℝ)/q) := by
      apply sum_le_sum
      intro q hq
      have hsmall : (harmonic (q-1) : ℝ) ≤ H :=
        harmonic_cast_mono ((Nat.sub_le q 1).trans (mem_Icc.mp hq).2)
      have hHq := harmonic_natCast_nonneg (q-1)
      calc
        _ ≤ modulusBound q*((B : ℝ)/q+H)*H+(C : ℝ)/q := by
          dsimp [rectangleError, modulusBound]
          gcongr
        _ = _ := by ring
    _ = (B : ℝ)*H*(∑ q ∈ Icc 1 Q, modulusBound q/(q : ℝ))+
        H^2*(∑ q ∈ Icc 1 Q, modulusBound q)+(C : ℝ)*H := by
      simp only [sum_add_distrib, ← mul_sum]
      congr 1
      dsimp [H]
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        div_eq_mul_inv, mul_sum]
    _ ≤ (B : ℝ)*H*(modulusBound Q*(1+H)) + H^2*((Q : ℝ)*modulusBound Q)+(C : ℝ)*H := by
      gcongr
      · exact sum_modulusBound_div_le Q
      · exact sum_modulusBound_le Q
    _ = modulusBound Q*((B : ℝ)*(H*(1+H))+(Q : ℝ)*H^2)+(C : ℝ)*H := by ring
    _ ≤ modulusBound Q*((B : ℝ)*(1+H)^2+(Q : ℝ)*(1+H)^2)+(C : ℝ)*H := by
      gcongr <;> nlinarith only [hH]
    _ = _ := by unfold rectangleMeanKernel; dsimp [H]; ring

end Erdos821.Kloosterman

namespace Erdos821.AnalyticSieve
open Erdos821.Kloosterman

/-- A density-free mean over prime moduli, with two unrestricted cofactor
intervals. No distribution assumption on the input weight is used. -/
theorem doubleCofactor_prime_modulus_mean (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (P : Finset ℕ) (Q B C X : ℕ) (M N : ℤ) (u : ∀ q : ℕ, (ZMod q)ˣ)
    (hP : ∀ q ∈ P, q.Prime ∧ q ≤ Q)
    (hunit : ∀ q ∈ P, ∀ n ∈ Icc 1 X, f n ≠ 0 → n.Coprime q) :
    (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N B C X -
      doubleCofactorLocalMain f q B C X|) ≤
        rectangleMeanKernel Q B C * restrictedMass f X := by
  calc
    _ ≤ ∑ q ∈ P, rectangleError q B C * restrictedMass f X := by
      apply sum_le_sum
      intro q hq
      letI : Fact q.Prime := ⟨(hP q hq).1⟩
      exact doubleCofactorWeight_error f hf (u q) M N B C X (hunit q hq)
    _ = (∑ q ∈ P, rectangleError q B C)*restrictedMass f X := by rw [sum_mul]
    _ ≤ (∑ q ∈ Icc 1 Q, rectangleError q B C)*restrictedMass f X := by
      apply mul_le_mul_of_nonneg_right _ (restrictedMass_nonneg f hf X)
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact mem_Icc.mpr ⟨(hP q hq).1.pos, (hP q hq).2⟩
      · intro q _ _
        exact rectangleError_nonneg q B C
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_rectangleError_le Q B C)
      (restrictedMass_nonneg f hf X)

end Erdos821.AnalyticSieve
