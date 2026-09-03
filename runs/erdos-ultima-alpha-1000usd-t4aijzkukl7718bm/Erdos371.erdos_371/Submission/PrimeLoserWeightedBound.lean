import Submission.PrimeLoserWeighted

/-! Iterating the cofactor-weighted halving estimate. This supplies a finite
bound of order N*K*log(K)/log(z)^2 for the weighted high-prime loser count. -/
namespace Erdos371
open Finset FiniteSieve

noncomputable def weightedLoserMainCoefficient (B X z : ℕ) : ℝ :=
  8*Real.exp 19*(1+Real.log X)/((B+1 : ℝ)*(Real.log (z+1 : ℝ))^2)

noncomputable def weightedLoserErrorCoefficient (B z : ℕ) : ℝ :=
  2*(z+1 : ℝ)^64/(B+1 : ℝ)^3

lemma cofactorWeightedPrimePairCount_polynomial_bound (B X z N : ℕ)
    (hz : 1 ≤ z) (hNX : N ≤ X*(B+1)) (hNB : N ≤ (B+1)^2) :
    cofactorWeightedPrimePairCount N (N/(B+1)) z ≤
      weightedLoserMainCoefficient B X z*(N : ℝ)^2+
        weightedLoserErrorCoefficient B z*(N : ℝ)^3 := by
  let K := N/(B+1)
  have hB0 : (0 : ℝ) < B+1 := by positivity
  have hKX : K ≤ X := Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using hNX)
  have hKB : K ≤ B+1 := Nat.div_le_of_le_mul (by simpa only [pow_two] using hNB)
  have hKN : K*(B+1) ≤ N := Nat.div_mul_le_self N (B+1)
  have hKK : K^2 ≤ N := by nlinarith
  have hK : (K : ℝ) ≤ (N : ℝ)/(B+1 : ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (Nat.cast_div_le (α := ℝ) (m := N) (n := B+1))
  have hA0 : 0 ≤ weightedLoserMainCoefficient B X z := by
    unfold weightedLoserMainCoefficient
    have := Real.log_natCast_nonneg X
    positivity
  have hD0 : 0 ≤ weightedLoserErrorCoefficient B z := by
    unfold weightedLoserErrorCoefficient
    positivity
  by_cases hK0 : K = 0
  · change cofactorWeightedPrimePairCount N K z ≤ _
    rw [hK0]
    simp only [cofactorWeightedPrimePairCount,show Icc 1 0 = (∅ : Finset ℕ) by decide,sum_empty]
    positivity
  · have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK0
    have hlog : Real.log K ≤ Real.log X := Real.log_le_log hKpos (by exact_mod_cast hKX)
    have hmul := mul_le_mul hK (show 1+Real.log K ≤ 1+Real.log X by linarith)
      (show 0 ≤ 1+Real.log K by have := Real.log_natCast_nonneg K; positivity)
      (div_nonneg (Nat.cast_nonneg N) hB0.le)
    have hmain := mul_le_mul_of_nonneg_left hmul
      (show 0 ≤ 8*Real.exp 19*N/(Real.log (z+1 : ℝ))^2 by positivity)
    have herr := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg K) hK 3)
      (show 0 ≤ 2*(z+1 : ℝ)^64 by positivity)
    simp only [div_pow] at herr
    have hb := cofactorWeightedPrimePairCount_bound N K z hz hKK
    apply hb.trans
    unfold weightedLoserMainCoefficient weightedLoserErrorCoefficient
    convert add_le_add hmain herr using 1 <;>
      simp only [div_eq_mul_inv,mul_inv_rev] <;> ring

lemma bothAboveSet_empty_of_endpoint_le (B N : ℕ) (hN : N ≤ B+1) :
    bothAboveSet B N = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hnN,hp,_⟩ := mem_filter.mp hn
  have hnN' := mem_range.mp hnN
  have hpn := Nat.maxPrimeFac_le (n := n)
  omega

/-- A finite weighted count estimate. Its cofactor dependence is X*log X
when X is comparable to N/(B+1), saving a logarithm over the uniform weight. -/
theorem weightedLoserCount_polynomial_bound (B X z N : ℕ)
    (hB : 1 ≤ B) (hz : 1 ≤ z) (hzB : z ≤ B)
    (hNX : N ≤ X*(B+1)) (hNB : N ≤ (B+1)^2) :
    weightedLoserCount B N ≤
      28*weightedLoserMainCoefficient B X z*(N : ℝ)^2+
        14*weightedLoserErrorCoefficient B z*(N : ℝ)^3 := by
  let A := weightedLoserMainCoefficient B X z
  let D := weightedLoserErrorCoefficient B z
  have hA : 0 ≤ A := by
    dsimp only [A,weightedLoserMainCoefficient]
    have := Real.log_natCast_nonneg X
    positivity
  have hD : 0 ≤ D := by dsimp only [D,weightedLoserErrorCoefficient]; positivity
  suffices ∀ n ≤ N, weightedLoserCount B n ≤ 28*A*(n : ℝ)^2+14*D*(n : ℝ)^3 by
    exact this N le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnN
    by_cases hnB : n ≤ B+1
    · simp only [weightedLoserCount,bothAboveSet_empty_of_endpoint_le B n hnB,sum_empty]
      positivity
    · have hn2 : 2 ≤ n := by omega
      have hm : n/2 < n := Nat.div_lt_self (by omega) (by norm_num)
      have hhalf := ih (n/2) hm (by omega)
      have hw := weightedLoserCount_halving B n z hB hzB hn2
      have hs := cofactorWeightedPrimePairCount_polynomial_bound B X z n hz
        (hnN.trans hNX) (hnN.trans hNB)
      change cofactorWeightedPrimePairCount n (n/(B+1)) z ≤ A*(n : ℝ)^2+D*(n : ℝ)^3 at hs
      have hb : weightedLoserCount B n ≤
          3*(28*A*((n/2 : ℕ) : ℝ)^2+14*D*((n/2 : ℕ) : ℝ)^3)+
            7*(A*(n : ℝ)^2+D*(n : ℝ)^3) := by linarith
      have htwo : 2*((n/2 : ℕ) : ℝ) ≤ n := by
        exact_mod_cast (show 2*(n/2) ≤ n by omega)
      have hpow2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2*(n/2 : ℕ)) htwo 2
      have hpow3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2*(n/2 : ℕ)) htwo 3
      have h2 := mul_le_mul_of_nonneg_left hpow2 hA
      have h3 := mul_le_mul_of_nonneg_left hpow3 hD
      have h3pos : 0 ≤ D*((n/2 : ℕ) : ℝ)^3 := by positivity
      apply hb.trans
      nlinarith

/-- Expanded version of the finite bound, with absolute constants. -/
theorem weightedLoserCount_bound (B X z N : ℕ)
    (hB : 1 ≤ B) (hz : 1 ≤ z) (hzB : z ≤ B)
    (hNX : N ≤ X*(B+1)) (hNB : N ≤ (B+1)^2) :
    weightedLoserCount B N ≤
      224*Real.exp 19*(N : ℝ)^2*(1+Real.log X)/
        ((B+1 : ℝ)*(Real.log (z+1 : ℝ))^2)+
      28*(N : ℝ)^3*(z+1 : ℝ)^64/(B+1 : ℝ)^3 := by
  convert weightedLoserCount_polynomial_bound B X z N hB hz hzB hNX hNB using 1
  unfold weightedLoserMainCoefficient weightedLoserErrorCoefficient
  ring

#print axioms cofactorWeightedPrimePairCount_polynomial_bound
#print axioms weightedLoserCount_bound
end Erdos371
