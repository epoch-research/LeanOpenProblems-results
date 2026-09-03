import Submission.PoolSuccessorSieve
import Submission.CofactorSuccessorScales

/-!
# Scaled prime-successor bound with a retained multiplier pool

This is an upper sieve, not a prime-successor lower bound. All mass in the
main term is actual restricted mass; the error is ambient D*B*N.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
open Sieve
set_option maxHeartbeats 4000000

lemma doubled_pool_poly_sieve_saving (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) (m : ℕ) :
    C*(2 : ℝ)^m*(K*(((2*m : ℕ) : ℝ)+1)^7/(2 : ℝ)^(2*m)) ≤
      (128*C*K)*((m : ℝ)+1)^7/(2 : ℝ)^m := by
  have hpow : (((2*m : ℕ) : ℝ)+1)^7 ≤ 128*((m : ℝ)+1)^7 := by
    have hh : ((2*m : ℕ) : ℝ)+1 ≤ 2*((m : ℝ)+1) := by push_cast; linarith
    have hp := pow_le_pow_left₀ (by positivity) hh 7
    simpa only [mul_pow,show (2 : ℝ)^7=128 by norm_num] using hp
  have htwo : (0 : ℝ)<2^m := by positivity
  rw [show (2 : ℝ)^(2*m)=((2 : ℝ)^m)^2 by rw [mul_comm 2 m,pow_mul]]
  have he : C*(2 : ℝ)^m*(K*(((2*m : ℕ) : ℝ)+1)^7/((2 : ℝ)^m)^2) =
      C*K*(((2*m : ℕ) : ℝ)+1)^7/(2 : ℝ)^m := by field_simp
  rw [he]
  apply div_le_div_of_nonneg_right _ htwo.le
  have hh := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hK)
  nlinarith only [hh]


/-- Averaging the multiplier pool is retained through the Selberg sieve.
There is no prime-variable-only restriction on the modulus level. -/
theorem exists_pool_unit_successor_power_saving (a b s l v t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hs : 2*a+1 ≤ s)
    (hl : 1 ≤ l) (ht : 1 ≤ t) (hlevel : 2*b+1 ≤ l+t) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ArithmeticFunction ℝ,
      (∀ n, 0 ≤ f n) → (∀ n, f n ≤ vonMangoldt n) →
      ∀ m D B X : ℕ, cofactorScale s (2*m) ≤ B →
        cofactorScale l (2*m) ≤ D*B → D*B ≤ cofactorScale v (2*m) →
        X ≤ cofactorScale t (2*m) →
      ∀ P J : Finset ℕ, P ⊆ Icc 1 D →
      (∀ p ∈ J, p.Prime ∧ p ≤ cofactorScale b m) →
      (∀ c ∈ P, ∀ p ∈ J, c.Coprime p) →
      (∀ n ∈ Icc 1 X, f n ≠ 0 → ∀ p ∈ J, n.Coprime p) →
      poolPrimeSuccessorWeight f P 0 B X (cofactorScale b m) ≤
        (P.card : ℝ)*(B : ℝ)*restrictedMass f X*(oneRootDenominator J (cofactorScale b m))⁻¹+
          K*((m : ℝ)+1)^7/(2 : ℝ)^m*((D*B : ℕ) : ℝ)*(cofactorScale t (2*m) : ℝ) := by
  let ε : ℝ := 1/(256*((2*b : ℕ) : ℝ))
  have hb : 1 ≤ b := ha.trans hab
  obtain ⟨C,hC,HC⟩ := exists_pool_successor_sieve_bound ε (by dsimp [ε]; positivity)
  obtain ⟨K,hK,HK⟩ := exists_pool_unit_natural_power_saving a b s l v t ha hab hs hl ht hlevel
  refine ⟨128*C*K,by positivity,?_⟩
  intro f hf hΛ m D B X hB hDB hDBup hX P J hP hJ hunitP hunit
  have hsup := pool_sieve_unit_support f P J X (cofactorScale b m) hunitP hunit
  have hS : poolSieveModuli J (cofactorScale b m) ⊆ Icc 1 (cofactorScale b (2*m)) := by
    rw [← cofactorScale_square]
    exact poolSieveModuli_subset J (cofactorScale b m) (fun p hp => (hJ p hp).1)
  have hmean := HK f hf hΛ (2*m) D B X hB hDB hDBup hX P
    (poolSieveModuli J (cofactorScale b m)) hP hS (fun _ => -1) hsup.1 hsup.2
  have hsieve := HC f hf P J 0 B X (cofactorScale b m) (cofactorScale_pos b m) hJ
  simp only [Nat.sub_zero] at hsieve
  rw [cofactorScale_square] at hsieve
  have hweight : (cofactorScale b (2*m) : ℝ)^ε = (2 : ℝ)^m := by
    rw [cofactorScale_double]
    exact cofactorScale_rpow (2*b) m (by omega)
  rw [hweight] at hsieve
  apply hsieve.trans
  apply _root_.add_le_add le_rfl
  have hmean' : (∑ d ∈ poolSieveModuli J (cofactorScale b m), poolSuccessorDiscrepancy f P 0 B X d) ≤
      K*(((2*m : ℕ) : ℝ)+1)^7/(2 : ℝ)^(2*m)*((D*B : ℕ) : ℝ)*(cofactorScale t (2*m) : ℝ) := by
    simpa only [poolSuccessorDiscrepancy,Nat.sub_zero] using hmean
  apply (mul_le_mul_of_nonneg_left hmean' (show 0 ≤ C*(2 : ℝ)^m by positivity)).trans
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (doubled_pool_poly_sieve_saving C K hC.le hK.le m)
      (Nat.cast_nonneg (D*B))) (Nat.cast_nonneg (cofactorScale t (2*m)))
  simpa only [mul_assoc] using hh

end Erdos821.AnalyticSieve
