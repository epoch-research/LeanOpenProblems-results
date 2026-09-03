import Submission.SquarefreeCofactorScales

/-!
# Two-cofactor squarefree-modulus means with nonunit inputs

The main term retains the input mass coprime to each individual modulus.
There is no coprimality or primality condition on the nonnegative weight.
This is a distribution estimate, not a lower bound for prime successors.
-/
open Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
open Erdos821.Kloosterman
set_option maxHeartbeats 3000000

noncomputable def unitRestrictedWeight (f : ArithmeticFunction ℝ) (q : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n.Coprime q then f n else 0, by simp⟩

lemma unitRestrictedWeight_nonneg (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (q n : ℕ) : 0 ≤ unitRestrictedWeight f q n := by
  simp only [unitRestrictedWeight, ArithmeticFunction.coe_mk]
  split_ifs <;> first | exact hf n | exact le_rfl

lemma unitRestrictedWeight_support (f : ArithmeticFunction ℝ) (q n : ℕ)
    (hn : unitRestrictedWeight f q n ≠ 0) : n.Coprime q := by
  by_contra h
  exact hn (by simp [unitRestrictedWeight, h])

noncomputable def restrictedUnitMass (f : ArithmeticFunction ℝ) (q X : ℕ) : ℝ :=
  restrictedMass (unitRestrictedWeight f q) X

lemma restrictedUnitMass_eq_sub (f : ArithmeticFunction ℝ) (q X : ℕ) :
    restrictedUnitMass f q X = restrictedMass f X-restrictedNonunitMass f q X := by
  simp only [restrictedUnitMass, restrictedMass, restrictedNonunitMass,
    unitRestrictedWeight, ArithmeticFunction.coe_mk, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  by_cases h : n.Coprime q <;> simp [h]

lemma restrictedUnitMass_nonneg (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n) (q X : ℕ) :
    0 ≤ restrictedUnitMass f q X :=
  restrictedMass_nonneg _ (unitRestrictedWeight_nonneg f hf q) X

lemma restrictedUnitMass_le (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n) (q X : ℕ) :
    restrictedUnitMass f q X ≤ restrictedMass f X := by
  rw [restrictedUnitMass_eq_sub]
  exact sub_le_self _ (restrictedNonunitMass_nonneg f hf q X)

lemma nonunit_doubleCofactorRow_zero (q n : ℕ) (u : (ZMod q)ˣ)
    (hn : ¬n.Coprime q) (M N : ℤ) (B C : ℕ) :
    doubleCofactorRow q u n M N B C = 0 := by
  apply sum_eq_zero
  intro i _
  apply sum_eq_zero
  intro j _
  have hnot : (u : ZMod q)*((M+i : ℤ) : ZMod q)*((N+j : ℤ) : ZMod q)*(n : ZMod q) ≠ 1 := by
    intro he
    exact hn ((ZMod.isUnit_iff_coprime n q).mp (IsUnit.of_mul_eq_one_right _ he))
  simp only [hnot, if_false]

lemma doubleCofactorWeight_unitRestriction (f : ArithmeticFunction ℝ) (q : ℕ)
    (u : (ZMod q)ˣ) (M N : ℤ) (B C X : ℕ) :
    doubleCofactorWeight (unitRestrictedWeight f q) q u M N B C X =
      doubleCofactorWeight f q u M N B C X := by
  unfold doubleCofactorWeight
  apply sum_congr rfl
  intro n _
  by_cases hn : n.Coprime q
  · simp [unitRestrictedWeight, hn]
  · simp [unitRestrictedWeight, hn, nonunit_doubleCofactorRow_zero q n u hn M N B C]

noncomputable def squarefreeCofactorUnitMain (f : ArithmeticFunction ℝ) (q B C X : ℕ) : ℝ :=
  (B : ℝ)*C*q.totient/(q : ℝ)^2*restrictedUnitMass f q X

/-- The single-modulus error retains only the contributing input mass. -/
theorem squarefree_doubleCofactorWeight_unit_error (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (q : ℕ) [NeZero q] (hq : Squarefree q)
    (u : (ZMod q)ˣ) (M N : ℤ) (B C X : ℕ) :
    |doubleCofactorWeight f q u M N B C X-squarefreeCofactorUnitMain f q B C X| ≤
      squarefreeRectangleError q B C*restrictedUnitMass f q X := by
  have h := squarefree_doubleCofactorWeight_error (unitRestrictedWeight f q)
    (unitRestrictedWeight_nonneg f hf q) q hq u M N B C X
    (fun n _ hn => unitRestrictedWeight_support f q n hn)
  simpa only [doubleCofactorWeight_unitRestriction, squarefreeCofactorMain,
    squarefreeCofactorUnitMain, restrictedUnitMass] using h

lemma squarefreeRectangleError_nonneg (q B C : ℕ) : 0 ≤ squarefreeRectangleError q B C := by
  have hH := harmonic_natCast_nonneg (q-1)
  have hK := squarefreeBound_nonneg q
  unfold squarefreeRectangleError
  positivity

/-- No support restrictions on f occur in this finite mean. -/
theorem doubleCofactor_squarefree_nonunit_mean (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : ArithmeticFunction ℝ, (∀ n, 0 ≤ f n) →
      ∀ P : Finset ℕ, ∀ Q B C X : ℕ, ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
      (∀ q ∈ P, Squarefree q ∧ q ≤ Q) →
      (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N B C X-squarefreeCofactorUnitMain f q B C X|) ≤
        A*(Q : ℝ)^δ*rectangleMeanKernel Q B C*restrictedMass f X := by
  obtain ⟨A,hA,HA⟩ := exists_uniform_six_primeFactor_bound δ hδ
  refine ⟨A,hA,?_⟩
  intro f hf P Q B C X M N u hP
  calc
    _ ≤ ∑ q ∈ P, squarefreeRectangleError q B C*restrictedMass f X := by
      apply sum_le_sum
      intro q hq
      letI : NeZero q := ⟨(hP q hq).1.ne_zero⟩
      exact (squarefree_doubleCofactorWeight_unit_error f hf q (hP q hq).1 (u q) M N B C X).trans
        (mul_le_mul_of_nonneg_left (restrictedUnitMass_le f hf q X) (squarefreeRectangleError_nonneg q B C))
    _ = (∑ q ∈ P, squarefreeRectangleError q B C)*restrictedMass f X := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (sum_squarefreeRectangleError_le P Q B C (A*(Q : ℝ)^δ) (by positivity) hP
        (fun q hq => HA Q q (Nat.pos_of_ne_zero (hP q hq).1.ne_zero) (hP q hq).2))
      (restrictedMass_nonneg f hf X)

/-- Uniform in every nonnegative arithmetic weight, with the correct
modulus-dependent coprime main term. -/
theorem eventually_doubleCofactor_squarefree_nonunit_relative (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ f : ArithmeticFunction ℝ, (∀ n, 0 ≤ f n) →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ rectangleModulusScale m) →
      ∀ X : ℕ, ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
      (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N
        (rectangleIntervalScale m) (rectangleIntervalScale m) X-
          squarefreeCofactorUnitMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X|) ≤
        η*(rectangleIntervalScale m : ℝ)^2*restrictedMass f X := by
  obtain ⟨A,hA,HA⟩ := doubleCofactor_squarefree_nonunit_mean (1/72) (by norm_num)
  filter_upwards [eventually_squarefree_rectangle_kernel_relative A η hA.le hη] with m hm
  intro f hf P hP X M N u
  exact (HA f hf P _ _ _ X M N u hP).trans
    (mul_le_mul_of_nonneg_right hm (restrictedMass_nonneg f hf X))

end Erdos821.AnalyticSieve
