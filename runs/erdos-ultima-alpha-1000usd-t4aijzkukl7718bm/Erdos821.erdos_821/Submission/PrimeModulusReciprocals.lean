import Submission.StrongMangoldt

/-!
# Reciprocal mass of prime moduli in a fixed logarithmic interval

A linear theta bound at the sparse geometric scales, together with Chebyshev's
upper bound, populates every sufficiently wide fixed-ratio block. Summing the
blocks removes a logarithmic loss from the reciprocal-modulus main term.
-/

open scoped BigOperators
open Finset ArithmeticFunction Filter

namespace Erdos821.AnalyticSieve

lemma mangoldtSum_eq_psi (N : ℕ) : mangoldtSum N = Chebyshev.psi (N : ℝ) := by
  unfold mangoldtSum Chebyshev.psi
  rw [Nat.floor_natCast]
  congr 1

lemma progression_scale_theta_lower {s : ℕ} (hs : 1 ≤ s) :
    (progressionScaleN s : ℝ) / 16 ≤ Chebyshev.theta (progressionScaleN s) := by
  have hlin : 2048 * s ≤ 2 ^ (32 * s) := by
    calc
      _ ≤ 2 ^ (31 * s) * 2 ^ s := Nat.mul_le_mul
        (by
          have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 11 ≤ 31 * s by omega)
          norm_num at h ⊢
          exact h) Nat.lt_two_pow_self.le
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hN1 : (1 : ℝ) ≤ progressionScaleN s := by
    simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat]
    exact one_le_pow₀ (by norm_num)
  have hlog : Real.log (progressionScaleN s) ≤ 64 * (s : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using log_two_pow_le (64 * s)
  have herr : 2 * Real.sqrt (progressionScaleN s) * Real.log (progressionScaleN s) ≤
      (progressionScaleN s : ℝ) / 16 := by
    rw [sqrt_progressionScaleN]
    have hlin' : 2048 * (s : ℝ) ≤ (2 : ℝ) ^ (32 * s) := by exact_mod_cast hlin
    have hm := mul_le_mul_of_nonneg_right hlin' (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (32 * s))
    have heq : (2 : ℝ) ^ (32 * s) * (2 : ℝ) ^ (32 * s) = (progressionScaleN s : ℝ) := by
      simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
      congr 1
      omega
    rw [heq] at hm
    have hh := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ (32 * s))
    nlinarith
  have hdiff := (le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hN1)
  have hmain := progression_scale_mangoldt_lower hs
  rw [mangoldtSum_eq_psi] at hmain
  linarith

lemma sum_primeModuliBetween_eq_nat (D Q : ℕ) (f : ℕ → ℝ) :
    (∑ q ∈ primeModuliBetween D Q, f q) =
      ∑ p ∈ (Q + 1).primesBelow.filter (fun p => D ≤ p), f p := by
  apply Finset.sum_bij (fun (q : ℕ+) _ => (q : ℕ))
  · intro q hq
    obtain ⟨hp, hD, hQ⟩ := mem_primeModuliBetween.mp hq
    exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hp⟩, hD⟩
  · intro q hq r hr h
    exact PNat.coe_injective h
  · intro p hp
    obtain ⟨hp, hD⟩ := mem_filter.mp hp
    obtain ⟨hQ, hprime⟩ := Nat.mem_primesBelow.mp hp
    refine ⟨⟨p, hprime.pos⟩, ?_, rfl⟩
    exact mem_primeModuliBetween.mpr ⟨hprime, hD, by change p ≤ Q; omega⟩
  · intro q hq
    rfl

lemma theta_add_prime_moduli_log (D Q : ℕ) (hDQ : D ≤ Q) :
    Chebyshev.theta (D : ℝ) +
      (∑ q ∈ primeModuliBetween (D + 1) Q, Real.log (q : ℕ)) = Chebyshev.theta (Q : ℝ) := by
  rw [sum_primeModuliBetween_eq_nat (D + 1) Q (fun n : ℕ => Real.log (n : ℝ)), Erdos821.Sieve.theta_nat_eq_sum_primesBelow,
    Erdos821.Sieve.theta_nat_eq_sum_primesBelow]
  have hfilter : (Q + 1).primesBelow.filter (fun p => p ≤ D) = (D + 1).primesBelow := by
    ext p
    simp only [mem_filter, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨_, hp⟩, hpD⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpD, hp⟩
      exact ⟨⟨by omega, hp⟩, by omega⟩
  have hnot : (Q + 1).primesBelow.filter (fun p => ¬p ≤ D) =
      (Q + 1).primesBelow.filter (fun p => D + 1 ≤ p) := by
    ext p
    simp only [mem_filter, Nat.not_le, Nat.succ_le_iff]
  have h := Finset.sum_filter_add_sum_filter_not (Q + 1).primesBelow (fun p => p ≤ D)
    (fun p => Real.log (p : ℝ))
  rw [hfilter, hnot] at h
  exact h

lemma progressionScaleN_monotone : Monotone progressionScaleN := by
  intro a b hab
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 64 hab)

lemma progression_scale_previous {s : ℕ} (hs : 1 ≤ s) :
    progressionScaleN (s - 1) * 2 ^ 64 = progressionScaleN s := by
  simp only [progressionScaleN, ← pow_add]
  congr 1
  omega

def dyadicPrimeModuli (j : ℕ) : Finset ℕ+ :=
  primeModuliBetween (progressionScaleN (j - 1) + 1) (progressionScaleN j)

lemma dyadic_prime_moduli_log_lower {j : ℕ} (hj : 1 ≤ j) :
    (progressionScaleN j : ℝ) / 32 ≤
      ∑ q ∈ dyadicPrimeModuli j, Real.log (q : ℕ) := by
  have hlow := progression_scale_theta_lower hj
  have hu := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α := ℝ) (progressionScaleN (j - 1)))
  have hlog4 : Real.log 4 ≤ 3 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4) using 1 <;> norm_num
  have hu' : Chebyshev.theta (progressionScaleN (j - 1)) ≤ 3 * (progressionScaleN (j - 1) : ℝ) :=
    hu.trans (mul_le_mul_of_nonneg_right hlog4 (Nat.cast_nonneg _))
  have hprev := progression_scale_previous hj
  have hprev' : 96 * (progressionScaleN (j - 1) : ℝ) ≤ (progressionScaleN j : ℝ) := by
    exact_mod_cast (show 96 * progressionScaleN (j - 1) ≤ progressionScaleN j from by
      rw [← hprev]
      nlinarith)
  have heq := theta_add_prime_moduli_log (progressionScaleN (j - 1)) (progressionScaleN j)
    (progressionScaleN_monotone (Nat.sub_le _ _))
  change (progressionScaleN j : ℝ) / 32 ≤ ∑ q ∈ primeModuliBetween _ _, Real.log (q : ℕ)
  linarith

lemma dyadic_prime_moduli_reciprocal_lower {j : ℕ} (hj : 1 ≤ j) :
    1 / (2048 * (j : ℝ)) ≤ ∑ q ∈ dyadicPrimeModuli j, (((q : ℕ).totient : ℝ))⁻¹ := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hN : (0 : ℝ) < progressionScaleN j := by unfold progressionScaleN; positivity
  have hsum : (∑ q ∈ dyadicPrimeModuli j, Real.log (q : ℕ)) ≤
      64 * (j : ℝ) * ((dyadicPrimeModuli j).card : ℝ) := by
    calc
      _ ≤ ∑ q ∈ dyadicPrimeModuli j, 64 * (j : ℝ) := by
        apply sum_le_sum
        intro q hq
        have hqN := (mem_primeModuliBetween.mp hq).2.2
        have hlog := log_nat_mono hqN
        have hlogN := log_two_pow_le (64 * j)
        simp only [Nat.cast_mul, Nat.cast_ofNat] at hlogN
        exact hlog.trans hlogN
      _ = _ := by simp [mul_comm]
  have hcount : (progressionScaleN j : ℝ) ≤ 2048 * (j : ℝ) * ((dyadicPrimeModuli j).card : ℝ) := by
    have h := dyadic_prime_moduli_log_lower hj
    linarith
  change (progressionScaleN j : ℝ) ≤ 2048 * (j : ℝ) *
    ((primeModuliBetween (progressionScaleN (j - 1) + 1) (progressionScaleN j)).card : ℝ) at hcount
  apply le_trans _ (moduli_reciprocal_ge_card _ _ (by unfold progressionScaleN; positivity))
  apply (div_le_div_iff₀ (by positivity) hN).mpr
  nlinarith

lemma dyadicPrimeModuli_disjoint {i j : ℕ} (hij : i < j) :
    Disjoint (dyadicPrimeModuli i) (dyadicPrimeModuli j) := by
  apply Finset.disjoint_left.mpr
  intro q hqi hqj
  have hqiN := (mem_primeModuliBetween.mp hqi).2.2
  have hqjN := (mem_primeModuliBetween.mp hqj).2.1
  have hi : i ≤ j - 1 := by omega
  have hN := progressionScaleN_monotone hi
  omega

/-- A quantitative reciprocal lower bound across any interval of geometric blocks. -/
theorem prime_moduli_reciprocal_ge_block_count (A B : ℕ) (hAB : A < B) :
    ((B - A : ℕ) : ℝ) / (2048 * (B : ℝ)) ≤
      ∑ q ∈ primeModuliBetween (progressionScaleN A) (progressionScaleN B),
        (((q : ℕ).totient : ℝ))⁻¹ := by
  classical
  let I := Finset.Ioc A B
  have hB : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hdisj : (↑I : Set ℕ).PairwiseDisjoint dyadicPrimeModuli := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact dyadicPrimeModuli_disjoint h
    · exact (dyadicPrimeModuli_disjoint h).symm
  have hsub : I.biUnion dyadicPrimeModuli ⊆
      primeModuliBetween (progressionScaleN A) (progressionScaleN B) := by
    intro q hq
    obtain ⟨j, hjI, hqj⟩ := mem_biUnion.mp hq
    obtain ⟨hAj, hjB⟩ := mem_Ioc.mp hjI
    obtain ⟨hp, hlo, hhi⟩ := mem_primeModuliBetween.mp hqj
    have hNlo := progressionScaleN_monotone (show A ≤ j - 1 by omega)
    have hNhi := progressionScaleN_monotone hjB
    exact mem_primeModuliBetween.mpr ⟨hp, by omega, hhi.trans hNhi⟩
  calc
    _ = ∑ j ∈ I, (1 : ℝ) / (2048 * (B : ℝ)) := by simp [I, div_eq_mul_inv]
    _ ≤ ∑ j ∈ I, ∑ q ∈ dyadicPrimeModuli j, (((q : ℕ).totient : ℝ))⁻¹ := by
      apply sum_le_sum
      intro j hj
      obtain ⟨hAj, hjB⟩ := mem_Ioc.mp hj
      apply le_trans _ (dyadic_prime_moduli_reciprocal_lower (by omega : 1 ≤ j))
      have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2048 hjB)
    _ = ∑ q ∈ I.biUnion dyadicPrimeModuli, (((q : ℕ).totient : ℝ))⁻¹ := (Finset.sum_biUnion hdisj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Fixed positive reciprocal mass for the scaled intervals used in the second sieve. -/
theorem sieved_scale_moduli_reciprocal_lower (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) :
    1 / (131072 * (r : ℝ)) ≤
      ∑ q ∈ primeModuliBetween (progressionScaleD (256 * r * m) (192 * m))
        (progressionScaleQ (256 * r * m) (192 * m)), (((q : ℕ).totient : ℝ))⁻¹ := by
  let A := (128 * r - 9) * m
  let B := (128 * r - 6) * m
  have hgap : B = A + 3 * m := by
    have hh : 128 * r - 6 = (128 * r - 9) + 3 := by omega
    dsimp [B, A]
    rw [hh]
    ring
  have hAB : A < B := by omega
  have hD : progressionScaleD (256 * r * m) (192 * m) = progressionScaleN A := by
    unfold progressionScaleD progressionScaleN A
    congr 1
    simp only [Nat.sub_mul, Nat.mul_sub]
    congr 1 <;> ring
  have hQ : progressionScaleQ (256 * r * m) (192 * m) = progressionScaleN B := by
    unfold progressionScaleQ progressionScaleN B
    congr 1
    simp only [Nat.sub_mul, Nat.mul_sub]
    congr 1 <;> ring
  rw [hD, hQ]
  apply le_trans _ (prime_moduli_reciprocal_ge_block_count A B hAB)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hBR : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hdiff : B - A = 3 * m := by omega
  have hBle : B ≤ 128 * r * m := Nat.mul_le_mul_right m (Nat.sub_le _ _)
  rw [hdiff]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hBle' : (B : ℝ) ≤ 128 * (r : ℝ) * m := by exact_mod_cast hBle
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

end Erdos821.AnalyticSieve
