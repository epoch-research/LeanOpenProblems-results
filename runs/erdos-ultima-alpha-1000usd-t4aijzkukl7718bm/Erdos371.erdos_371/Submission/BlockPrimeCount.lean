import FormalConjecturesUtil

/-! An elementary prime-count lower bound sufficient for the entropy transfer.
It uses central binomial coefficients, not the prime number theorem. -/
namespace Erdos371.BlockPrimes
open Finset

lemma two_pow_le_centralBinom (n : ℕ) : 2^n ≤ Nat.centralBinom n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : 2 * Nat.centralBinom n ≤ Nat.centralBinom (n+1) := by
      apply Nat.le_of_mul_le_mul_left (c := n+1) _ (by omega)
      rw [Nat.succ_mul_centralBinom_succ]
      nlinarith [Nat.centralBinom_pos n]
    rw [pow_succ']
    exact (Nat.mul_le_mul_left 2 ih).trans hc

lemma centralBinom_le_pow_prime_count (n : ℕ) (hn : 0 < n) :
    Nat.centralBinom n ≤ (2*n)^((2*n+1).primesBelow.card) := by
  have he : (∏ p ∈ (2*n+1).primesBelow, p^(Nat.centralBinom n).factorization p) =
      Nat.centralBinom n := by
    rw [Nat.primesBelow, prod_filter]
    have hp : (∏ p ∈ range (2*n+1),
        if Nat.Prime p then p^(Nat.centralBinom n).factorization p else 1) =
        ∏ p ∈ range (2*n+1), p^(Nat.centralBinom n).factorization p := by
      apply prod_congr rfl
      intro p _
      split_ifs with h
      · rfl
      · rw [Nat.factorization_eq_zero_of_not_prime _ h, pow_zero]
    rw [hp, Nat.prod_pow_factorization_centralBinom]
  rw [← he, ← prod_const]
  exact prod_le_prod' fun p _ => Nat.pow_factorization_choose_le (by omega : 0 < 2*n)

lemma prime_count_log_lower (n : ℕ) (hn : 0 < n) :
    n*Real.log 2 ≤ ((2*n+1).primesBelow.card : ℝ)*Real.log (2*n : ℕ) := by
  have hb := (two_pow_le_centralBinom n).trans (centralBinom_le_pow_prime_count n hn)
  have h := Real.log_le_log (by positivity : (0 : ℝ) < (2:ℝ)^n)
    (show (2 : ℝ)^n ≤ ((2*n : ℕ) : ℝ)^((2*n+1).primesBelow.card) by exact_mod_cast hb)
  simpa only [Real.log_pow] using h

/-- Primes whose double gap fits inside a block of length H. -/
def halfBlockPrimes (H : ℕ) : Finset ℕ := (H/2+1).primesBelow

lemma mem_halfBlockPrimes {H p : ℕ} : p ∈ halfBlockPrimes H ↔ p.Prime ∧ 2*p ≤ H := by
  simp only [halfBlockPrimes, Nat.mem_primesBelow]
  constructor
  · rintro ⟨hp,hprime⟩
    exact ⟨hprime, by omega⟩
  · rintro ⟨hprime,hp⟩
    exact ⟨by omega,hprime⟩

lemma halfBlockPrimes_nonempty (H : ℕ) (hH : 4 ≤ H) : (halfBlockPrimes H).Nonempty :=
  ⟨2, mem_halfBlockPrimes.mpr ⟨Nat.prime_two, by omega⟩⟩

/-- The lower bound is uniform for every block length H>=8. -/
theorem halfBlockPrimes_card_lower (H : ℕ) (hH : 8 ≤ H) :
    (Real.log 2 / 8) * H / Real.log H ≤ ((halfBlockPrimes H).card : ℝ) := by
  let n := H/4
  have hn : 0 < n := by dsimp [n]; omega
  have hsub : (2*n+1).primesBelow ⊆ halfBlockPrimes H := by
    intro p hp
    obtain ⟨hpn,hp⟩ := Nat.mem_primesBelow.mp hp
    exact mem_halfBlockPrimes.mpr ⟨hp, by dsimp [n] at hpn; omega⟩
  have hcard : (((2*n+1).primesBelow).card : ℝ) ≤ ((halfBlockPrimes H).card : ℝ) :=
    Nat.cast_le.mpr (card_le_card hsub)
  have hlog0 : 0 ≤ Real.log (2*n : ℕ) := Real.log_natCast_nonneg _
  have hlog : Real.log (2*n : ℕ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < 2*n))
      (by exact_mod_cast (by dsimp [n]; omega : 2*n ≤ H))
  have hcount := prime_count_log_lower n hn
  have hupper := mul_le_mul hcard hlog hlog0 (Nat.cast_nonneg _)
  have hnlarge : (H : ℝ)/8 ≤ n := by
    have h : H ≤ 8*n := by dsimp [n]; omega
    have hc : (H : ℝ) ≤ 8*n := by exact_mod_cast h
    linarith
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlow := mul_le_mul_of_nonneg_right hnlarge htwo.le
  have hHlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  apply (div_le_iff₀ hHlog).mpr
  nlinarith

#print axioms halfBlockPrimes_card_lower
end Erdos371.BlockPrimes
