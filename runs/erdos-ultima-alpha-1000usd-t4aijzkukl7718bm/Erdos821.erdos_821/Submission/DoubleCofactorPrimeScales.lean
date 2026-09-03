import Submission.RectangleMeanKernel

/-!
# A beyond-half cofactor range over prime moduli

For two intervals of length L=2^(64*m), the prime-modulus cutoff is
Q=2^(72*m), so Q^16=(L^2)^9. The mean error is o(L^2*F), uniformly in any
nonnegative prime-supported weight of mass F supported above Q.

This retains two free cofactor intervals. It is not a prime-only progression
estimate, and it does not include composite moduli or prime successors.
-/
open Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.Kloosterman
open Erdos821.AnalyticSieve

lemma modulusBound_power_four (k : ℕ) :
    modulusBound (2^(4*k)) ≤ 2*(2 : ℝ)^(3*k) := by
  apply (pow_le_pow_iff_left₀ (modulusBound_nonneg _) (by positivity) (by decide : 4 ≠ 0)).mp
  rw [modulusBound_fourth, Nat.cast_pow, Nat.cast_ofNat, mul_pow, ← pow_mul, ← pow_mul]
  have he : 4*k*3=3*k*4 := by omega
  rw [he]
  norm_num only [show (2 : ℝ)^4=16 by norm_num]
  nlinarith only [show 0 ≤ (2 : ℝ)^(3*k*4) by positivity]

lemma harmonic_two_pow_le (k : ℕ) : (harmonic (2^k) : ℝ) ≤ 1+(k : ℝ) := by
  have hh := harmonic_le_one_add_log (2^k)
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hh
  have hl : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)).trans_eq (by norm_num)
  have hprod : (k : ℝ)*Real.log 2 ≤ k := by
    nlinarith only [hl,Nat.cast_nonneg (α := ℝ) k]
  exact hh.trans (_root_.add_le_add le_rfl hprod)

noncomputable def rectangleIntervalScale (m : ℕ) : ℕ := 2^(64*m)
noncomputable def rectangleModulusScale (m : ℕ) : ℕ := 2^(72*m)

lemma rectangleScale_power_relation (m : ℕ) :
    rectangleModulusScale m ^ 16 = (rectangleIntervalScale m ^ 2)^9 := by
  simp only [rectangleModulusScale, rectangleIntervalScale, ← pow_mul]
  congr 1
  omega

lemma rectangleIntervalScale_lt_modulus (m : ℕ) (hm : 1 ≤ m) :
    rectangleIntervalScale m < rectangleModulusScale m := by
  unfold rectangleIntervalScale rectangleModulusScale
  apply Nat.pow_lt_pow_right (by decide)
  omega

lemma rectangleMeanKernel_scale_bound (m : ℕ) :
    rectangleMeanKernel (rectangleModulusScale m) (rectangleIntervalScale m) (rectangleIntervalScale m) ≤
      22000*((m : ℝ)+1)^2*(2 : ℝ)^(126*m) := by
  let H : ℝ := harmonic (rectangleModulusScale m)
  have hH : 0 ≤ H := harmonic_natCast_nonneg _
  have hHbound : H ≤ 73*((m : ℝ)+1) := by
    have hh := harmonic_two_pow_le (72*m)
    change H ≤ _ at hh
    push_cast at hh
    nlinarith only [hh,Nat.cast_nonneg (α := ℝ) m]
  have hH1bound : 1+H ≤ 74*((m : ℝ)+1) := by
    nlinarith only [hHbound,Nat.cast_nonneg (α := ℝ) m]
  have hK : modulusBound (rectangleModulusScale m) ≤ 2*(2 : ℝ)^(54*m) := by
    simpa only [rectangleModulusScale, show 4*(18*m)=72*m by omega,
      show 3*(18*m)=54*m by omega] using modulusBound_power_four (18*m)
  have hBQ : (rectangleIntervalScale m : ℝ)+rectangleModulusScale m ≤ 2*(2 : ℝ)^(72*m) := by
    have hb : (2 : ℝ)^(64*m) ≤ (2 : ℝ)^(72*m) := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    dsimp [rectangleIntervalScale, rectangleModulusScale]
    push_cast
    linarith only [hb]
  have hp : (2 : ℝ)^(54*m)*(2 : ℝ)^(72*m)=(2 : ℝ)^(126*m) := by
    rw [← pow_add]
    congr 1
    omega
  have hsmall : (2 : ℝ)^(64*m) ≤ (2 : ℝ)^(126*m) := by
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have hm1 : 1 ≤ (m : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hmm : (m : ℝ)+1 ≤ ((m : ℝ)+1)^2 := by nlinarith only [hm1]
  have hfirst : modulusBound (rectangleModulusScale m)*
      ((rectangleIntervalScale m : ℝ)+rectangleModulusScale m)*(1+H)^2 ≤
        21904*((m : ℝ)+1)^2*(2 : ℝ)^(126*m) := by
    calc
      _ ≤ (2*(2 : ℝ)^(54*m))*(2*(2 : ℝ)^(72*m))*(74*((m : ℝ)+1))^2 := by
        gcongr
      _ = _ := by rw [show (2*(2 : ℝ)^(54*m))*(2*(2 : ℝ)^(72*m)) =
          4*((2 : ℝ)^(54*m)*(2 : ℝ)^(72*m)) by ring, hp]; ring
  have hsecond : (rectangleIntervalScale m : ℝ)*H ≤
      73*((m : ℝ)+1)^2*(2 : ℝ)^(126*m) := by
    calc
      _ ≤ (rectangleIntervalScale m : ℝ)*(73*((m : ℝ)+1)) :=
        mul_le_mul_of_nonneg_left hHbound (Nat.cast_nonneg _)
      _ ≤ (2 : ℝ)^(126*m)*(73*((m : ℝ)+1)^2) := by
        dsimp [rectangleIntervalScale]
        push_cast
        gcongr
      _ = _ := by ring
  unfold rectangleMeanKernel
  change _+_ ≤ _
  nlinarith only [hfirst,hsecond,show 0 ≤ ((m : ℝ)+1)^2*(2 : ℝ)^(126*m) by positivity]

/-- The explicit logarithmic loss is absorbed by a fixed exponential saving. -/
theorem eventually_rectangleMeanKernel_relative (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      rectangleMeanKernel (rectangleModulusScale m) (rectangleIntervalScale m) (rectangleIntervalScale m) ≤
        η*(rectangleIntervalScale m : ℝ)^2 := by
  have ht := (tendsto_shifted_poly_div_two_pow 2).const_mul (22000 : ℝ)
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually_lt_const hη] with m hm
  have hcoef : 22000*((m : ℝ)+1)^2 ≤ η*(2 : ℝ)^m := by
    have hh := (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^m)).mp
      (show (22000*((m : ℝ)+1)^2)/(2 : ℝ)^m ≤ η by simpa only [mul_div_assoc] using hm.le)
    exact hh
  calc
    _ ≤ 22000*((m : ℝ)+1)^2*(2 : ℝ)^(126*m) := rectangleMeanKernel_scale_bound m
    _ ≤ (η*(2 : ℝ)^m)*(2 : ℝ)^(126*m) := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = η*(2 : ℝ)^(127*m) := by rw [mul_assoc, ← pow_add]; congr 2; omega
    _ ≤ η*(rectangleIntervalScale m : ℝ)^2 := by
      dsimp [rectangleIntervalScale]
      push_cast
      rw [← pow_mul]
      apply mul_le_mul_of_nonneg_left _ hη.le
      apply pow_le_pow_right₀ (by norm_num)
      omega

end Erdos821.Kloosterman

namespace Erdos821.AnalyticSieve
open Erdos821.Kloosterman

/-- Uniform relative error for any retained prime weight above the modulus
cutoff. Only prime moduli are included, and both cofactor intervals remain. -/
theorem eventually_doubleCofactor_prime_relative (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ f : ArithmeticFunction ℝ,
      (∀ n, 0 ≤ f n) →
      (∀ n, f n ≠ 0 → n.Prime ∧ rectangleModulusScale m < n) →
      ∀ P : Finset ℕ, (∀ q ∈ P, q.Prime ∧ q ≤ rectangleModulusScale m) →
      ∀ X : ℕ, ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
        (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N
          (rectangleIntervalScale m) (rectangleIntervalScale m) X -
            doubleCofactorLocalMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X|) ≤
          η*(rectangleIntervalScale m : ℝ)^2*restrictedMass f X := by
  filter_upwards [eventually_rectangleMeanKernel_relative η hη] with m hm
  intro f hf hs P hP X M N u
  have hunit : ∀ q ∈ P, ∀ n ∈ Icc 1 X, f n ≠ 0 → n.Coprime q := by
    intro q hq n _ hn
    obtain ⟨hnp,hqn⟩ := hs n hn
    rw [hnp.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt (hP q hq).1.pos ((hP q hq).2.trans_lt hqn)
  exact (doubleCofactor_prime_modulus_mean f hf P _ _ _ X M N u hP hunit).trans
    (mul_le_mul_of_nonneg_right hm (restrictedMass_nonneg f hf X))

/-- An arbitrary subset of the primes is allowed. This specialization does
not claim that the subset, or the retained mass, is large. -/
theorem eventually_doubleCofactor_prime_subset (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ S : Set ℕ, ∀ X : ℕ, ∀ M N : ℤ,
      ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
        let f := mangoldtRestriction {n : ℕ | n ∈ S ∧ n.Prime ∧ rectangleModulusScale m < n}
        (∑ q ∈ (rectangleModulusScale m + 1).primesBelow,
          |doubleCofactorWeight f q (u q) M N (rectangleIntervalScale m) (rectangleIntervalScale m) X -
            doubleCofactorLocalMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X|) ≤
          η*(rectangleIntervalScale m : ℝ)^2*restrictedMass f X := by
  filter_upwards [eventually_doubleCofactor_prime_relative η hη] with m hm
  intro S X M N u
  apply hm _ (mangoldtRestriction_nonneg _) _ _ _ X M N u
  · intro n hn
    by_cases hs : n ∈ S ∧ n.Prime ∧ rectangleModulusScale m < n
    · exact hs.2
    · exfalso
      apply hn
      simp only [mangoldtRestriction, ArithmeticFunction.coe_mk, Set.mem_setOf_eq, hs, if_false]
  · intro q hq
    have hh := Nat.mem_primesBelow.mp hq
    exact ⟨hh.2, by omega⟩

end Erdos821.AnalyticSieve
