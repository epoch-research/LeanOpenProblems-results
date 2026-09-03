import Submission.BuchstabTiltedSource
import Submission.PrimeExpCubeTransfer
import Submission.PrimeDoubleOuterProfile

/-! The complete finite double-prime contribution for the slow source profile.
This is an arithmetic error estimate, not a Jacobsthal endpoint theorem. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real MeasureTheory WeightedMertens ContinuousBuchstab
set_option maxHeartbeats 2400000

noncomputable def primeDoubleSlowSum (R : ℕ) (L : ℝ) : ℝ :=
  exp (2/3 : ℝ)*∑ p ∈ (R+1).primesBelow, (1/(p : ℝ))*
    ∑ q ∈ (p+1).primesBelow,
      exp (-(2/3 : ℝ)*(L-log (p : ℝ))/log (q : ℝ))/((q : ℝ)*log (q : ℝ))

lemma primeDoubleSlowSum_nonneg (R : ℕ) (L : ℝ) : 0 ≤ primeDoubleSlowSum R L := by
  unfold primeDoubleSlowSum
  apply mul_nonneg (exp_pos _).le
  apply sum_nonneg
  intro p hp
  apply mul_nonneg (by positivity)
  apply sum_nonneg
  intro q hq
  exact div_nonneg (exp_pos _).le (mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _))

lemma primeDoubleSlowSum_split_upper (R : ℕ) (hR : 2 ≤ R) (L : ℝ)
    (hRL : 3*log (R : ℝ) ≤ L) :
    primeDoubleSlowSum R L ≤ exp (2/3 : ℝ)*
      ((∑ p ∈ (R+1).primesBelow,
        exp ((-2/3 : ℝ)*(L-log (p : ℝ))/log (p : ℝ))/((2/3 : ℝ)*(p : ℝ)*(L-log (p : ℝ))))+
      8*smoothProfileError*exp (2/3 : ℝ)*
        (∑ p ∈ (R+1).primesBelow,
          exp (-((2/3 : ℝ)*L)/log (p : ℝ))/((p : ℝ)*log (p : ℝ)^2))) := by
  unfold primeDoubleSlowSum
  apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
  have hh : (∑ p ∈ (R+1).primesBelow, (1/(p : ℝ))*
      ∑ q ∈ (p+1).primesBelow,
        exp (-(2/3 : ℝ)*(L-log (p : ℝ))/log (q : ℝ))/((q : ℝ)*log (q : ℝ))) ≤
      ∑ p ∈ (R+1).primesBelow, (1/(p : ℝ))*
        (exp (-((2/3 : ℝ)*(L-log (p : ℝ)))/log (p : ℝ))*
          (1/((2/3 : ℝ)*(L-log (p : ℝ)))+8*smoothProfileError/log (p : ℝ)^2)) := by
    apply sum_le_sum
    intro p hp
    obtain ⟨hpp,hpR⟩ := mem_primes.mp hp
    have hl := log_le_log (by exact_mod_cast hpp.pos : (0 : ℝ) < p)
      (by exact_mod_cast hpR : (p : ℝ) ≤ R)
    have hi := prime_reciprocalExpSquare_sum_upper p hpp.two_le ((2/3 : ℝ)*(L-log (p : ℝ)))
      (by linarith)
    apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 1/p)
    simpa only [neg_mul] using hi
  apply hh.trans_eq
  rw [mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast (mem_primes.mp hp).1.one_lt)
  have he : exp (-((2/3 : ℝ)*(L-log (p : ℝ)))/log (p : ℝ)) =
      exp (2/3 : ℝ)*exp (-((2/3 : ℝ)*L)/log (p : ℝ)) := by
    rw [← exp_add]
    congr 1
    field_simp
    ring
  have he' : (-2/3 : ℝ)*(L-log (p : ℝ))/log (p : ℝ) =
      -((2/3 : ℝ)*(L-log (p : ℝ)))/log (p : ℝ) := by ring
  rw [he',he]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (mem_primes.mp hp).1.ne_zero
  have hlR := log_le_log (by exact_mod_cast (mem_primes.mp hp).1.pos : (0 : ℝ) < p)
    (by exact_mod_cast (mem_primes.mp hp).2 : (p : ℝ) ≤ R)
  have hLu : L-log (p : ℝ) ≠ 0 := by linarith
  field_simp

lemma primeDoubleSlowSum_full_upper (R : ℕ) (hR : 2 ≤ R) (L : ℝ)
    (hRL : 3*log (R : ℝ) ≤ L) :
    primeDoubleSlowSum R L ≤ exp (4/3-(2/3 : ℝ)*L/log (R : ℝ))*
      (3/(4*L)+2*smoothProfileError/((2/3 : ℝ)*log (R : ℝ)*(L-log (R : ℝ)))+
        8*smoothProfileError*
          ((((2/3 : ℝ)*L)/log (R : ℝ)+1)/((2/3 : ℝ)*L)^2+
            10*smoothProfileError/log (R : ℝ)^3)) := by
  have hU : (1/2 : ℝ) ≤ log (R : ℝ) :=
    (by linarith [log_two_gt_d9] : (1/2 : ℝ) ≤ log 2).trans
      (log_le_log (by norm_num) (by exact_mod_cast hR))
  have hlp : 0 < log (R : ℝ) := by linarith
  have hmain := (prime_doubleOuterProfile_upper R hR L hRL).trans
    (add_le_add (integral_doubleOuterProfile_upper L (1/2) (log (R : ℝ)) (by norm_num) hU hRL) le_rfl)
  have herror := prime_reciprocalExpCube_sum_upper R hR ((2/3 : ℝ)*L) (by linarith)
  have herr := mul_le_mul_of_nonneg_left herror
    (show 0 ≤ 8*smoothProfileError*exp (2/3 : ℝ) by have := smoothProfileError_pos; positivity)
  have hsum := add_le_add hmain herr
  have hscaled := mul_le_mul_of_nonneg_left hsum (exp_pos (2/3 : ℝ)).le
  apply (primeDoubleSlowSum_split_upper R hR L hRL).trans
  apply hscaled.trans_eq
  unfold doubleOuterProfile
  have he1 : exp ((-2/3 : ℝ)*(L/log (R : ℝ)-1)) =
      exp (2/3 : ℝ)*exp (-((2/3 : ℝ)*L)/log (R : ℝ)) := by
    rw [← exp_add]
    congr 1
    ring
  have he2 : exp ((-2/3 : ℝ)*(L-log (R : ℝ))/log (R : ℝ)) =
      exp (2/3 : ℝ)*exp (-((2/3 : ℝ)*L)/log (R : ℝ)) := by
    rw [← exp_add]
    congr 1
    field_simp
    ring
  have he3 : exp (4/3-(2/3 : ℝ)*L/log (R : ℝ)) =
      exp (2/3 : ℝ)*exp (2/3 : ℝ)*exp (-((2/3 : ℝ)*L)/log (R : ℝ)) := by
    rw [← exp_add,← exp_add]
    congr 1
    ring
  rw [he1,he2,he3]
  ring

lemma doublePrime_remainder_bound (U L E : ℝ) (hU : 0 < U) (hUL : 3*U ≤ L) (hE : 0 ≤ E) :
    2*E/((2/3 : ℝ)*U*(L-U))+
      8*E*((((2/3 : ℝ)*L)/U+1)/((2/3 : ℝ)*L)^2+10*E/U^3) ≤
        8*E/U^2+80*E^2/U^3 := by
  have hL : 0 < L := by linarith
  have hdiff : 0 < L-U := by linarith
  have hfirst : 2*E/((2/3 : ℝ)*U*(L-U)) ≤ (3/2)*E/U^2 := by
    apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hU)).mpr
    have hh := mul_nonneg (mul_nonneg hE hU.le) (show 0 ≤ L-3*U by linarith)
    nlinarith only [hh]
  have hz : (2/3 : ℝ)*L/U ≥ 2 := (le_div_iff₀ hU).mpr (by linarith)
  have hsecond : (((2/3 : ℝ)*L)/U+1)/((2/3 : ℝ)*L)^2 ≤ (3/4)/U^2 := by
    apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hU)).mpr
    have hh : (((2/3 : ℝ)*L)/U+1)*U^2 = ((2/3 : ℝ)*L)*U+U^2 := by field_simp <;> ring
    rw [hh]
    have h := mul_nonneg (show 0 ≤ (2/3 : ℝ)*L-2*U by linarith)
      (show 0 ≤ 3*((2/3 : ℝ)*L)+2*U by positivity)
    nlinarith only [h]
  have hm := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ 8*E by positivity)
  have he : 0 ≤ E/U^2 := by positivity
  ring_nf at hfirst hm he ⊢
  linarith only [hfirst,hm,he]

/-- A single finite bound for the two arithmetic sums, with the continuous
leading constant and both lower-order Mertens errors retained. -/
theorem primeDoubleSlowSum_upper (R : ℕ) (hR : 2 ≤ R) (L : ℝ)
    (hRL : 3*log (R : ℝ) ≤ L) :
    primeDoubleSlowSum R L ≤ exp (4/3-(2/3 : ℝ)*L/log (R : ℝ))*
      (3/(4*L)+8*smoothProfileError/log (R : ℝ)^2+
        80*smoothProfileError^2/log (R : ℝ)^3) := by
  have hU : 0 < log (R : ℝ) := log_pos (by exact_mod_cast (show 1 < R by omega))
  have hh := doublePrime_remainder_bound (log (R : ℝ)) L smoothProfileError hU hRL smoothProfileError_pos.le
  apply (primeDoubleSlowSum_full_upper R hR L hRL).trans
  apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
  linarith only [hh]

#print axioms primeDoubleSlowSum_upper
end Erdos970.RecursiveSieve.Buchstab
