import Submission.ModularRectangleCounts

/-!
# Two free cofactor variables with a retained arithmetic weight

The prime-modulus rectangle bound is summed against the actual restricted
weight. The input mass can be arbitrarily small. There is no assertion that
any successor is prime or that the restricted weight has positive mass.
-/
open Finset ArithmeticFunction
open scoped Classical BigOperators
namespace Erdos821.AnalyticSieve
open Erdos821.Kloosterman

noncomputable def doubleCofactorRow (q : ℕ) (u : (ZMod q)ˣ) (n : ℕ)
    (M N : ℤ) (B C : ℕ) : ℝ :=
  ∑ i ∈ range B, ∑ j ∈ range C,
    if (u : ZMod q)*((M+i : ℤ) : ZMod q)*((N+j : ℤ) : ZMod q)*(n : ZMod q)=1 then 1 else 0

noncomputable def doubleCofactorWeight (f : ArithmeticFunction ℝ) (q : ℕ) (u : (ZMod q)ˣ)
    (M N : ℤ) (B C X : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 X, f n * doubleCofactorRow q u n M N B C

noncomputable def doubleCofactorLocalMain (f : ArithmeticFunction ℝ)
    (q B C X : ℕ) : ℝ :=
  (B : ℝ)*C*((q : ℝ)-1)/(q : ℝ)^2 * restrictedMass f X

section PrimeModulus
variable {q : ℕ} [Fact q.Prime]
noncomputable local instance : DecidableEq (ZMod q) := fun a b => Classical.propDecidable (a=b)

lemma unit_doubleCofactorRow_eq (u : (ZMod q)ˣ) (n : ℕ) (hn : n.Coprime q)
    (M N : ℤ) (B C : ℕ) :
    doubleCofactorRow q u n M N B C =
      (rectangleCount M N B C (((u : ZMod q)*(n : ZMod q))⁻¹) : ℝ) := by
  have hn0 : (n : ZMod q) ≠ 0 := isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime n q).mpr hn)
  have hprod : (u : ZMod q)*(n : ZMod q) ≠ 0 := mul_ne_zero u.ne_zero hn0
  have he (x y : ZMod q) : (u : ZMod q)*x*y*(n : ZMod q)=1 ↔
      x*y=((u : ZMod q)*(n : ZMod q))⁻¹ := by
    rw [show (u : ZMod q)*x*y*(n : ZMod q)=(x*y)*((u : ZMod q)*(n : ZMod q)) by ring]
    exact mul_eq_one_iff_eq_inv₀ hprod
  simp only [doubleCofactorRow, rectangleCount, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, he]

lemma unit_doubleCofactorRow_error (u : (ZMod q)ˣ) (n : ℕ) (hn : n.Coprime q)
    (M N : ℤ) (B C : ℕ) :
    |doubleCofactorRow q u n M N B C - (B : ℝ)*C*((q : ℝ)-1)/(q : ℝ)^2| ≤
      rectangleError q B C := by
  rw [unit_doubleCofactorRow_eq u n hn]
  apply rectangleCount_error_local
  apply inv_ne_zero
  exact mul_ne_zero u.ne_zero (isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime n q).mpr hn))

/-- The actual mass is retained, with no lower-density assumption. -/
theorem doubleCofactorWeight_error (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (u : (ZMod q)ˣ) (M N : ℤ) (B C X : ℕ)
    (hunit : ∀ n ∈ Icc 1 X, f n ≠ 0 → n.Coprime q) :
    |doubleCofactorWeight f q u M N B C X - doubleCofactorLocalMain f q B C X| ≤
      rectangleError q B C * restrictedMass f X := by
  have he : doubleCofactorWeight f q u M N B C X - doubleCofactorLocalMain f q B C X =
      ∑ n ∈ Icc 1 X, f n *
        (doubleCofactorRow q u n M N B C - (B : ℝ)*C*((q : ℝ)-1)/(q : ℝ)^2) := by
    simp only [doubleCofactorWeight, doubleCofactorLocalMain, restrictedMass,
      mul_sum, mul_sub, sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro n _
    ring
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Icc 1 X, f n * rectangleError q B C := by
      apply sum_le_sum
      intro n hn
      by_cases hz : f n=0
      · simp [hz]
      rw [abs_mul, abs_of_nonneg (hf n)]
      exact mul_le_mul_of_nonneg_left
        (unit_doubleCofactorRow_error u n (hunit n hn hz) M N B C) (hf n)
    _ = _ := by rw [← sum_mul, mul_comm]; rfl

end PrimeModulus
end Erdos821.AnalyticSieve
