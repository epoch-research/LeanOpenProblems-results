import Submission.SquarefreeRectangleCounts
import Submission.DoubleCofactorPrimeScales

/-!
# A retained-weight mean over squarefree moduli

The rectangle bound is summed over any family of squarefree moduli, with
phi(q)/q^2 as local density. The two unrestricted cofactor intervals remain.
-/
open Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.Kloosterman
open Erdos821.AnalyticSieve

lemma squarefreeBound_le_primeFactor_multiple (q : ℕ) :
    squarefreeBound q ≤ (3 : ℝ)^q.primeFactors.card*modulusBound q := by
  have hpow : (3 : ℝ)^q.primeFactors.card ≤ ((3 : ℝ)^q.primeFactors.card)^4 :=
    le_self_pow₀ (one_le_pow₀ (by norm_num)) (by decide)
  have hmul := mul_le_mul_of_nonneg_right hpow (show 0 ≤ (q : ℝ)^3 by positivity)
  apply (pow_le_pow_iff_left₀ (squarefreeBound_nonneg q)
    (mul_nonneg (by positivity) (modulusBound_nonneg q)) (by decide : 4 ≠ 0)).mp
  rw [squarefreeBound_fourth, mul_pow, modulusBound_fourth]
  nlinarith only [hmul,show 0 ≤ ((3 : ℝ)^q.primeFactors.card)^4*(q : ℝ)^3 by positivity]

lemma squarefreeBound_divisor_factor (q : ℕ) (hq : Squarefree q) :
    squarefreeBound q*q.divisors.card ≤ (6 : ℝ)^q.primeFactors.card*modulusBound q := by
  have hh := mul_le_mul_of_nonneg_right (squarefreeBound_le_primeFactor_multiple q)
    (Nat.cast_nonneg (α := ℝ) q.divisors.card)
  rw [Erdos821.card_divisors_squarefree q hq, Nat.cast_pow, Nat.cast_ofNat] at hh ⊢
  apply hh.trans_eq
  rw [show (3 : ℝ)^q.primeFactors.card*modulusBound q*2^q.primeFactors.card =
    (3^q.primeFactors.card*2^q.primeFactors.card)*modulusBound q by ring, ← mul_pow]
  norm_num

lemma squarefreeRectangleError_le (q B C : ℕ) (hq : Squarefree q) :
    squarefreeRectangleError q B C ≤ (6 : ℝ)^q.primeFactors.card*rectangleError q B C := by
  have hH := harmonic_natCast_nonneg (q-1)
  have h1 := mul_le_mul_of_nonneg_right (squarefreeBound_divisor_factor q hq)
    (show 0 ≤ ((B : ℝ)/q+(harmonic (q-1) : ℝ))*(harmonic (q-1) : ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤3) (by norm_num : (3 : ℝ)≤6) q.primeFactors.card)
    (show 0 ≤ (C : ℝ)/q by positivity)
  unfold squarefreeRectangleError rectangleError modulusBound at *
  nlinarith only [h1,h2]

lemma exists_uniform_six_primeFactor_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ Q q : ℕ, 0 < q → q ≤ Q →
      (6 : ℝ)^q.primeFactors.card ≤ A*(Q : ℝ)^δ := by
  obtain ⟨A,hA,HA⟩ := Sieve.exists_card_pow_le_const_product_rpow 6 δ (by norm_num) hδ
  refine ⟨A,hA,?_⟩
  intro Q q hq hqQ
  apply (HA q.primeFactors (fun p hp => Nat.pos_of_mem_primeFactors hp)).trans
  apply mul_le_mul_of_nonneg_left _ hA.le
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast
    (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)).trans hqQ) hδ.le

lemma sum_squarefreeRectangleError_le (P : Finset ℕ) (Q B C : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hP : ∀ q ∈ P, Squarefree q ∧ q ≤ Q)
    (hbound : ∀ q ∈ P, (6 : ℝ)^q.primeFactors.card ≤ A) :
    (∑ q ∈ P, squarefreeRectangleError q B C) ≤ A*rectangleMeanKernel Q B C := by
  calc
    _ ≤ ∑ q ∈ P, A*rectangleError q B C := by
      apply sum_le_sum
      intro q hq
      exact (squarefreeRectangleError_le q B C (hP q hq).1).trans
        (mul_le_mul_of_nonneg_right (hbound q hq) (rectangleError_nonneg q B C))
    _ = A*(∑ q ∈ P, rectangleError q B C) := by rw [mul_sum]
    _ ≤ A*(∑ q ∈ Icc 1 Q, rectangleError q B C) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero (hP q hq).1.ne_zero, (hP q hq).2⟩
      · intro q _ _
        exact rectangleError_nonneg q B C
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_rectangleError_le Q B C) hA

end Erdos821.Kloosterman

namespace Erdos821.AnalyticSieve
open Erdos821.Kloosterman

noncomputable def squarefreeCofactorMain (f : ArithmeticFunction ℝ) (q B C X : ℕ) : ℝ :=
  (B : ℝ)*C*q.totient/(q : ℝ)^2*restrictedMass f X

lemma unit_squarefree_doubleRow_eq (q : ℕ) [NeZero q] (u : (ZMod q)ˣ)
    (n : ℕ) (hn : n.Coprime q) (M N : ℤ) (B C : ℕ) :
    doubleCofactorRow q u n M N B C =
      (ringRectangleCount q M N B C (↑((u*((ZMod.isUnit_iff_coprime n q).mpr hn).unit)⁻¹) : ZMod q) : ℝ) := by
  let v : (ZMod q)ˣ := u*((ZMod.isUnit_iff_coprime n q).mpr hn).unit
  have hv : (v : ZMod q)=(u : ZMod q)*(n : ZMod q) := by simp [v]
  have he (x y : ZMod q) : (u : ZMod q)*x*y*(n : ZMod q)=1 ↔
      x*y=(↑(v⁻¹) : ZMod q) := by
    rw [show (u : ZMod q)*x*y*(n : ZMod q)=(v : ZMod q)*(x*y) by rw [hv]; ring]
    have hh := Units.mul_right_inj v (b := x*y) (c := (↑(v⁻¹) : ZMod q))
    simpa only [v.mul_inv] using hh
  simp only [doubleCofactorRow, ringRectangleCount, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  simp only [he]
  split_ifs <;> rfl

lemma squarefree_doubleCofactorRow_error (q : ℕ) [NeZero q] (hq : Squarefree q)
    (u : (ZMod q)ˣ) (n : ℕ) (hn : n.Coprime q) (M N : ℤ) (B C : ℕ) :
    |doubleCofactorRow q u n M N B C-(B : ℝ)*C*q.totient/(q : ℝ)^2| ≤
      squarefreeRectangleError q B C := by
  rw [unit_squarefree_doubleRow_eq q u n hn]
  exact ringRectangleCount_error_local hq M N B C _

theorem squarefree_doubleCofactorWeight_error (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (q : ℕ) [NeZero q] (hq : Squarefree q) (u : (ZMod q)ˣ) (M N : ℤ) (B C X : ℕ)
    (hunit : ∀ n ∈ Icc 1 X, f n ≠ 0 → n.Coprime q) :
    |doubleCofactorWeight f q u M N B C X-squarefreeCofactorMain f q B C X| ≤
      squarefreeRectangleError q B C*restrictedMass f X := by
  have he : doubleCofactorWeight f q u M N B C X-squarefreeCofactorMain f q B C X =
      ∑ n ∈ Icc 1 X, f n*(doubleCofactorRow q u n M N B C-(B : ℝ)*C*q.totient/(q : ℝ)^2) := by
    simp only [doubleCofactorWeight, squarefreeCofactorMain, restrictedMass,
      mul_sum, mul_sub, sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro n _
    ring
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Icc 1 X, f n*squarefreeRectangleError q B C := by
      apply sum_le_sum
      intro n hn
      by_cases hz : f n=0
      · simp [hz]
      rw [abs_mul, abs_of_nonneg (hf n)]
      exact mul_le_mul_of_nonneg_left
        (squarefree_doubleCofactorRow_error q hq u n (hunit n hn hz) M N B C) (hf n)
    _ = _ := by rw [← sum_mul, mul_comm]; rfl

/-- A finite mean estimate with no lower bound on the retained input mass. -/
theorem doubleCofactor_squarefree_modulus_mean (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : ArithmeticFunction ℝ, (∀ n, 0 ≤ f n) →
      ∀ P : Finset ℕ, ∀ Q B C X : ℕ, ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
      (∀ q ∈ P, Squarefree q ∧ q ≤ Q) →
      (∀ q ∈ P, ∀ n ∈ Icc 1 X, f n ≠ 0 → n.Coprime q) →
      (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N B C X-squarefreeCofactorMain f q B C X|) ≤
        A*(Q : ℝ)^δ*rectangleMeanKernel Q B C*restrictedMass f X := by
  obtain ⟨A,hA,HA⟩ := exists_uniform_six_primeFactor_bound δ hδ
  refine ⟨A,hA,?_⟩
  intro f hf P Q B C X M N u hP hunit
  calc
    _ ≤ ∑ q ∈ P, squarefreeRectangleError q B C*restrictedMass f X := by
      apply sum_le_sum
      intro q hq
      letI : NeZero q := ⟨(hP q hq).1.ne_zero⟩
      exact squarefree_doubleCofactorWeight_error f hf q (hP q hq).1 (u q) M N B C X (hunit q hq)
    _ = (∑ q ∈ P, squarefreeRectangleError q B C)*restrictedMass f X := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (sum_squarefreeRectangleError_le P Q B C (A*(Q : ℝ)^δ) (by positivity) hP
        (fun q hq => HA Q q (Nat.pos_of_ne_zero (hP q hq).1.ne_zero) (hP q hq).2))
      (restrictedMass_nonneg f hf X)

end Erdos821.AnalyticSieve
