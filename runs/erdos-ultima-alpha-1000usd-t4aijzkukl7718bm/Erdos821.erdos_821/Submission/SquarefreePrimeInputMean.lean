import Submission.SquarefreeCofactorNonunits
import Submission.PeriodicCofactorMean

/-!
# Two-cofactor means for prime inputs below the modulus cutoff

The nonunit correction is bounded by reciprocal prime input mass. A lower
input cutoff 2^m suffices when the modulus cutoff is 2^(72m); the old
requirement that every input prime exceed the modulus cutoff is removed.
All estimates retain two free cofactor intervals and assert no prime-
successor lower bound.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
open Erdos821.Kloosterman
set_option maxHeartbeats 3000000

lemma squarefreeCofactor_main_difference (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (q B C X : ℕ) :
    |squarefreeCofactorUnitMain f q B C X-squarefreeCofactorMain f q B C X| =
      (B : ℝ)*C*q.totient/(q : ℝ)^2*restrictedNonunitMass f q X := by
  have hU := restrictedNonunitMass_nonneg f hf q X
  unfold squarefreeCofactorUnitMain squarefreeCofactorMain
  rw [restrictedUnitMass_eq_sub]
  rw [show (B : ℝ)*C*q.totient/(q : ℝ)^2*(restrictedMass f X-restrictedNonunitMass f q X)-
    (B : ℝ)*C*q.totient/(q : ℝ)^2*restrictedMass f X =
    -((B : ℝ)*C*q.totient/(q : ℝ)^2*restrictedNonunitMass f q X) by ring]
  rw [abs_neg, abs_of_nonneg (by positivity)]

lemma squarefreeCofactor_main_difference_le (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (q B C X : ℕ) (hq : 0 < q) :
    |squarefreeCofactorUnitMain f q B C X-squarefreeCofactorMain f q B C X| ≤
      (B : ℝ)*C*(restrictedNonunitMass f q X/(q : ℝ)) := by
  rw [squarefreeCofactor_main_difference f hf]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hc : (B : ℝ)*C*q.totient/(q : ℝ)^2 ≤ (B : ℝ)*C/(q : ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hqR) hqR).mpr
    have h := mul_le_mul_of_nonneg_left hφ (show 0 ≤ (B : ℝ)*C*q by positivity)
    nlinarith only [h]
  have h := mul_le_mul_of_nonneg_right hc (restrictedNonunitMass_nonneg f hf q X)
  convert h using 1; ring

lemma squarefreeCofactor_prime_main_correction (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hprime : ∀ n, f n ≠ 0 → n.Prime)
    (P : Finset ℕ) (Q B C X : ℕ) (hP : P ⊆ Icc 1 Q) :
    (∑ q ∈ P, |squarefreeCofactorUnitMain f q B C X-squarefreeCofactorMain f q B C X|) ≤
      (B : ℝ)*C*(harmonic Q : ℝ)*primeReciprocalMass f X := by
  calc
    _ ≤ ∑ q ∈ P, (B : ℝ)*C*(restrictedNonunitMass f q X/(q : ℝ)) := by
      apply sum_le_sum
      intro q hq
      exact squarefreeCofactor_main_difference_le f hf q B C X (mem_Icc.mp (hP hq)).1
    _ = (B : ℝ)*C*∑ q ∈ P, restrictedNonunitMass f q X/(q : ℝ) := by rw [mul_sum]
    _ ≤ (B : ℝ)*C*∑ q ∈ Icc 1 Q, restrictedNonunitMass f q X/(q : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum_of_subset_of_nonneg hP (fun q _ _ =>
        div_nonneg (restrictedNonunitMass_nonneg f hf q X) (Nat.cast_nonneg _))
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (prime_weight_nonunit_mean f hf hprime Q X)
        (show 0 ≤ (B : ℝ)*C by positivity)
      simpa only [mul_assoc] using h

/-- A finite estimate valid for prime inputs in any size range. The
reciprocal input mass is explicit and is not replaced by an ambient error. -/
theorem doubleCofactor_squarefree_prime_mean (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : ArithmeticFunction ℝ, (∀ n, 0 ≤ f n) →
      (∀ n, f n ≠ 0 → n.Prime) →
      ∀ P : Finset ℕ, ∀ Q B C X : ℕ, ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
      (∀ q ∈ P, Squarefree q ∧ q ≤ Q) →
      (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N B C X-squarefreeCofactorMain f q B C X|) ≤
        A*(Q : ℝ)^δ*rectangleMeanKernel Q B C*restrictedMass f X+
          (B : ℝ)*C*(harmonic Q : ℝ)*primeReciprocalMass f X := by
  obtain ⟨A,hA,HA⟩ := doubleCofactor_squarefree_nonunit_mean δ hδ
  refine ⟨A,hA,?_⟩
  intro f hf hprime P Q B C X M N u hP
  have hsub : P ⊆ Icc 1 Q := fun q hq => mem_Icc.mpr
    ⟨Nat.pos_of_ne_zero (hP q hq).1.ne_zero, (hP q hq).2⟩
  calc
    _ ≤ ∑ q ∈ P, (|doubleCofactorWeight f q (u q) M N B C X-squarefreeCofactorUnitMain f q B C X|+
        |squarefreeCofactorUnitMain f q B C X-squarefreeCofactorMain f q B C X|) := by
      apply sum_le_sum
      intro q _
      exact abs_sub_le _ _ _
    _ = _ := sum_add_distrib
    _ ≤ _ := _root_.add_le_add (HA f hf P Q B C X M N u hP)
      (squarefreeCofactor_prime_main_correction f hf hprime P Q B C X hsub)

lemma eventually_rectangle_prime_nonunit_coefficient (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, (harmonic (rectangleModulusScale m) : ℝ)/(2 : ℝ)^m ≤ η := by
  have H := (tendsto_shifted_poly_div_two_pow 1).const_mul (73 : ℝ)
  simp only [pow_one, mul_zero] at H
  filter_upwards [H.eventually_lt_const hη] with m hm
  have hh := harmonic_two_pow_le (72*m)
  have hh' : (harmonic (rectangleModulusScale m) : ℝ) ≤ 73*((m : ℝ)+1) := by
    unfold rectangleModulusScale
    push_cast at hh
    nlinarith only [hh, Nat.cast_nonneg (α := ℝ) m]
  exact (div_le_div_of_nonneg_right hh' (by positivity)).trans
    (by simpa only [mul_div_assoc] using hm.le)

/-- Density-free relative mean for ANY prime-supported weight above 2^m.
The upper input cutoff X is unrestricted, and may lie below Q. -/
theorem eventually_doubleCofactor_small_prime_relative (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ f : ArithmeticFunction ℝ, (∀ n, 0 ≤ f n) →
      (∀ n, f n ≠ 0 → n.Prime ∧ 2^m ≤ n) →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ rectangleModulusScale m) →
      ∀ X : ℕ, ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
      (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N
        (rectangleIntervalScale m) (rectangleIntervalScale m) X-
          squarefreeCofactorMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X|) ≤
        η*(rectangleIntervalScale m : ℝ)^2*restrictedMass f X := by
  filter_upwards [eventually_doubleCofactor_squarefree_nonunit_relative (η/2) (half_pos hη),
    eventually_rectangle_prime_nonunit_coefficient (η/2) (half_pos hη)] with m hmain hcoef
  intro f hf hs P hP X M N u
  have hsub : P ⊆ Icc 1 (rectangleModulusScale m) := fun q hq => mem_Icc.mpr
    ⟨Nat.pos_of_ne_zero (hP q hq).1.ne_zero, (hP q hq).2⟩
  have hcor := squarefreeCofactor_prime_main_correction f hf (fun n hn => (hs n hn).1)
    P (rectangleModulusScale m) (rectangleIntervalScale m) (rectangleIntervalScale m) X hsub
  have hrec := primeReciprocalMass_le f hf (2^m) X (by positivity) (fun n hn => (hs n hn).2)
  have hc : (∑ q ∈ P, |squarefreeCofactorUnitMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X-
      squarefreeCofactorMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X|) ≤
        (η/2)*(rectangleIntervalScale m : ℝ)^2*restrictedMass f X := by
    apply hcor.trans
    have h1 := mul_le_mul_of_nonneg_left hrec
      (show 0 ≤ (rectangleIntervalScale m : ℝ)*rectangleIntervalScale m*(harmonic (rectangleModulusScale m) : ℝ) by
        positivity [harmonic_natCast_nonneg (rectangleModulusScale m)])
    have h2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (show 0 ≤ (rectangleIntervalScale m : ℝ)^2 by positivity))
      (restrictedMass_nonneg f hf X)
    push_cast at h1
    apply h1.trans
    convert h2 using 1; ring
  have hh : (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N
      (rectangleIntervalScale m) (rectangleIntervalScale m) X-
      squarefreeCofactorMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X|) ≤
      (η/2)*(rectangleIntervalScale m : ℝ)^2*restrictedMass f X+
      (η/2)*(rectangleIntervalScale m : ℝ)^2*restrictedMass f X := by
    calc
      _ ≤ ∑ q ∈ P, (|doubleCofactorWeight f q (u q) M N
          (rectangleIntervalScale m) (rectangleIntervalScale m) X-
          squarefreeCofactorUnitMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X|+
          |squarefreeCofactorUnitMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X-
          squarefreeCofactorMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X|) :=
        sum_le_sum (fun _ _ => abs_sub_le _ _ _)
      _ = _ := sum_add_distrib
      _ ≤ _ := _root_.add_le_add (hmain f hf P hP X M N u) hc
  nlinarith only [hh]

end Erdos821.AnalyticSieve
