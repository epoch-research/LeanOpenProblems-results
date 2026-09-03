import Submission.SquarefreeCofactorMean

/-!
# A beyond-half range for two cofactor intervals at squarefree moduli

At L=2^(64m), Q=2^(72m), the mean error is o(L^2 F), uniformly over
squarefree moduli at most Q. The relative level is Q=(L^2)^(9/16).
-/
open Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.Kloosterman
open Erdos821.AnalyticSieve

lemma rectangleModulusScale_small_rpow (m : ℕ) :
    (rectangleModulusScale m : ℝ)^(1/72 : ℝ) = (2 : ℝ)^m := by
  simp only [rectangleModulusScale, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast_mul (by norm_num)]
  have he : ((72*m : ℕ) : ℝ)*(1/72) = (m : ℝ) := by push_cast; ring
  rw [he, Real.rpow_natCast]

theorem eventually_squarefree_rectangle_kernel_relative (A η : ℝ) (hA : 0 ≤ A) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      A*(rectangleModulusScale m : ℝ)^(1/72 : ℝ)*
        rectangleMeanKernel (rectangleModulusScale m) (rectangleIntervalScale m) (rectangleIntervalScale m) ≤
          η*(rectangleIntervalScale m : ℝ)^2 := by
  have ht := (tendsto_shifted_poly_div_two_pow 2).const_mul (22000*A)
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually_lt_const hη] with m hm
  have hcoef : 22000*A*((m : ℝ)+1)^2 ≤ η*(2 : ℝ)^m := by
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^m)).mp
    simpa only [mul_div_assoc] using hm.le
  rw [rectangleModulusScale_small_rpow]
  calc
    _ ≤ A*(2 : ℝ)^m*(22000*((m : ℝ)+1)^2*(2 : ℝ)^(126*m)) :=
      mul_le_mul_of_nonneg_left (rectangleMeanKernel_scale_bound m) (by positivity)
    _ = (22000*A*((m : ℝ)+1)^2)*(2 : ℝ)^(127*m) := by
      rw [show A*(2 : ℝ)^m*(22000*((m : ℝ)+1)^2*(2 : ℝ)^(126*m)) =
        (22000*A*((m : ℝ)+1)^2)*((2 : ℝ)^m*(2 : ℝ)^(126*m)) by ring, ← pow_add]
      congr 2
      omega
    _ ≤ (η*(2 : ℝ)^m)*(2 : ℝ)^(127*m) := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = η*(rectangleIntervalScale m : ℝ)^2 := by
      simp only [rectangleIntervalScale, Nat.cast_pow, Nat.cast_ofNat]
      rw [mul_assoc, ← pow_add, ← pow_mul]
      congr 2
      omega

end Erdos821.Kloosterman

namespace Erdos821.AnalyticSieve
open Erdos821.Kloosterman

/-- A uniform relative mean for nonnegative weights coprime to the chosen
squarefree moduli. No density assumption is imposed on the weight. -/
theorem eventually_doubleCofactor_squarefree_relative (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ f : ArithmeticFunction ℝ, (∀ n, 0 ≤ f n) →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ rectangleModulusScale m) →
      ∀ X : ℕ, (∀ q ∈ P, ∀ n ∈ Icc 1 X, f n ≠ 0 → n.Coprime q) →
      ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
      (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N
        (rectangleIntervalScale m) (rectangleIntervalScale m) X-
          squarefreeCofactorMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X|) ≤
        η*(rectangleIntervalScale m : ℝ)^2*restrictedMass f X := by
  obtain ⟨A,hA,HA⟩ := doubleCofactor_squarefree_modulus_mean (1/72) (by norm_num)
  filter_upwards [eventually_squarefree_rectangle_kernel_relative A η hA.le hη] with m hm
  intro f hf P hP X hunit M N u
  exact (HA f hf P _ _ _ X M N u hP hunit).trans
    (mul_le_mul_of_nonneg_right hm (restrictedMass_nonneg f hf X))

/-- Prime support above Q is one sufficient condition for the coprimality
hypothesis. This does not assert any lower bound for prime successors. -/
theorem eventually_doubleCofactor_squarefree_prime_weight (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ f : ArithmeticFunction ℝ, (∀ n, 0 ≤ f n) →
      (∀ n, f n ≠ 0 → n.Prime ∧ rectangleModulusScale m < n) →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ rectangleModulusScale m) →
      ∀ X : ℕ, ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
      (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N
        (rectangleIntervalScale m) (rectangleIntervalScale m) X-
          squarefreeCofactorMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X|) ≤
        η*(rectangleIntervalScale m : ℝ)^2*restrictedMass f X := by
  filter_upwards [eventually_doubleCofactor_squarefree_relative η hη] with m hm
  intro f hf hs P hP X M N u
  apply hm f hf P hP X _ M N u
  intro q hq n _ hn
  obtain ⟨hnp,hqn⟩ := hs n hn
  rw [hnp.coprime_iff_not_dvd]
  exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (hP q hq).1.ne_zero)
    ((hP q hq).2.trans_lt hqn)

end Erdos821.AnalyticSieve
