import Submission.PrimeModulusReciprocals
import Submission.Progressions

/-!
# An unconditional supply of large smooth composite moduli

Products of a fixed number of distinct primes in a geometric block are
squarefree, smooth, and numerous enough to retain polynomial reciprocal mass.
This file does not assert any prime-distribution estimate for these moduli.
-/

open scoped Classical BigOperators
open Nat Finset Filter

namespace Erdos821

set_option maxHeartbeats 2000000

open AnalyticSieve

noncomputable def geometricBlockPrimes (m : ℕ) : Finset ℕ :=
  (progressionScaleN (m + 1) + 1).primesBelow.filter
    (fun p => progressionScaleN m + 1 ≤ p)

lemma mem_geometricBlockPrimes {m p : ℕ} : p ∈ geometricBlockPrimes m ↔
    p.Prime ∧ progressionScaleN m < p ∧ p ≤ progressionScaleN (m + 1) := by
  simp only [geometricBlockPrimes, mem_filter, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hpN, hp⟩, hlo⟩
    exact ⟨hp, by omega, by omega⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact ⟨⟨by omega, hp⟩, by omega⟩

lemma geometric_block_prime_count (m : ℕ) :
    progressionScaleN m ≤ 2048 * (m + 1) * (geometricBlockPrimes m).card := by
  have hmass := dyadic_prime_moduli_log_lower (show 1 ≤ m + 1 by omega)
  have hcard : (dyadicPrimeModuli (m + 1)).card = (geometricBlockPrimes m).card := by
    simp only [dyadicPrimeModuli, Nat.add_sub_cancel, card_primeModuliBetween, geometricBlockPrimes]
  have hup : (∑ q ∈ dyadicPrimeModuli (m + 1), Real.log (q : ℕ)) ≤
      64 * ((m + 1 : ℕ) : ℝ) * ((dyadicPrimeModuli (m + 1)).card : ℝ) := by
    calc
      _ ≤ ∑ q ∈ dyadicPrimeModuli (m + 1), 64 * ((m + 1 : ℕ) : ℝ) := by
        apply sum_le_sum
        intro q hq
        apply (log_nat_mono (mem_primeModuliBetween.mp hq).2.2).trans
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using log_two_pow_le (64 * (m + 1))
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
  rw [hcard] at hup
  have hc : (progressionScaleN (m + 1) : ℝ) ≤
      2048 * ((m + 1 : ℕ) : ℝ) * ((geometricBlockPrimes m).card : ℝ) := by linarith
  exact (progressionScaleN_monotone (Nat.le_succ m)).trans (by exact_mod_cast hc)

noncomputable def primeProductModuli (r m : ℕ) : Finset ℕ :=
  ((geometricBlockPrimes m).powersetCard r).image (fun S => ∏ p ∈ S, p)

def primeProductMassConstant (r : ℕ) : ℕ := 2 ^ (64 * r) * 4096 ^ r * r.factorial

lemma primeProductMassConstant_pos (r : ℕ) : 0 < primeProductMassConstant r := by
  unfold primeProductMassConstant
  positivity

lemma primeProductModuli_card (r m : ℕ) :
    (primeProductModuli r m).card = (geometricBlockPrimes m).card.choose r := by
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p)
      (↑((geometricBlockPrimes m).powersetCard r) : Set (Finset ℕ)) := by
    intro S hS T hT hprod
    change S ∈ (geometricBlockPrimes m).powersetCard r at hS
    change T ∈ (geometricBlockPrimes m).powersetCard r at hT
    have hSS : S ⊆ geometricBlockPrimes m := (mem_powersetCard.mp hS).1
    have hTT : T ⊆ geometricBlockPrimes m := (mem_powersetCard.mp hT).1
    have hSP : ∀ p ∈ S, p.Prime := fun p hp =>
      (mem_geometricBlockPrimes.mp (hSS hp)).1
    have hTP : ∀ p ∈ T, p.Prime := fun p hp =>
      (mem_geometricBlockPrimes.mp (hTT hp)).1
    have h := congrArg Nat.primeFactors hprod
    simpa only [Nat.primeFactors_prod hSP, Nat.primeFactors_prod hTP] using h
  unfold primeProductModuli
  rw [Finset.card_image_of_injOn hinj, Finset.card_powersetCard]

lemma primeProductModuli_properties {r m d : ℕ} (hd : d ∈ primeProductModuli r m) :
    0 < d ∧ Squarefree d ∧ d.primeFactors.card = r ∧
      (progressionScaleN m) ^ r ≤ d ∧ d ≤ (progressionScaleN (m + 1)) ^ r := by
  obtain ⟨S, hS, rfl⟩ := mem_image.mp hd
  obtain ⟨hSP, hcard⟩ := mem_powersetCard.mp hS
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (mem_geometricBlockPrimes.mp (hSP hp)).1
  refine ⟨Finset.prod_pos (fun p hp => (hprime p hp).pos), ?_, ?_, ?_, ?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)
    · exact fun p hp => (hprime p hp).squarefree
  · rw [Nat.primeFactors_prod hprime, hcard]
  · calc
      _ = ∏ _p ∈ S, progressionScaleN m := by simp [hcard]
      _ ≤ _ := Finset.prod_le_prod' (fun p hp => (mem_geometricBlockPrimes.mp (hSP hp)).2.1.le)
  · calc
      _ ≤ ∏ _p ∈ S, progressionScaleN (m + 1) :=
        Finset.prod_le_prod' (fun p hp => (mem_geometricBlockPrimes.mp (hSP hp)).2.2)
      _ = _ := by simp [hcard]

lemma primeProductModuli_smooth {r m d : ℕ} (hm : 2 ≤ m) (hd : d ∈ primeProductModuli r m) :
    d ∈ Nat.smoothNumbers (2 ^ (128 * m)) := by
  obtain ⟨S, hS, rfl⟩ := mem_image.mp hd
  apply prod_smooth S id (2 ^ (128 * m))
  intro p hp
  have hpP := mem_geometricBlockPrimes.mp ((mem_powersetCard.mp hS).1 hp)
  apply Nat.mem_smoothNumbers'.mpr
  intro q hq hqd
  apply (Nat.le_of_dvd hpP.1.pos hqd).trans_lt
  apply hpP.2.2.trans_lt
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

lemma pow_card_le_choose_mul (n r : ℕ) (hrn : 2 * r ≤ n) :
    n ^ r ≤ 2 ^ r * r.factorial * n.choose r := by
  calc
    _ ≤ (2 * (n + 1 - r)) ^ r := Nat.pow_le_pow_left (by omega) r
    _ = 2 ^ r * (n + 1 - r) ^ r := mul_pow _ _ _
    _ ≤ 2 ^ r * (r.factorial * n.choose r) := Nat.mul_le_mul_left _
      (by rw [← Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.pow_sub_le_descFactorial n r)
    _ = _ := by ring

lemma primeProductModuli_polynomial_count (r m : ℕ)
    (hsmall : 4096 * r * (m + 1) ≤ progressionScaleN m) :
    (progressionScaleN m) ^ r ≤ 4096 ^ r * r.factorial * (m + 1) ^ r * (primeProductModuli r m).card := by
  let n := (geometricBlockPrimes m).card
  have hc : progressionScaleN m ≤ 2048 * (m + 1) * n := geometric_block_prime_count m
  have hrn : 2 * r ≤ n := by nlinarith
  have hp := pow_card_le_choose_mul n r hrn
  calc
    _ ≤ (2048 * (m + 1) * n) ^ r := Nat.pow_le_pow_left hc r
    _ = 2048 ^ r * (m + 1) ^ r * n ^ r := by simp only [mul_pow]
    _ ≤ 2048 ^ r * (m + 1) ^ r * (2 ^ r * r.factorial * n.choose r) := Nat.mul_le_mul_left _ hp
    _ = _ := by
      rw [primeProductModuli_card]
      change _ = 4096 ^ r * r.factorial * (m + 1) ^ r * n.choose r
      rw [show (4096 : ℕ) = 2048 * 2 by norm_num, mul_pow]
      ring

lemma sum_inv_totient_ge_card (D : Finset ℕ) (Q : ℕ)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ Q) :
    (D.card : ℝ) / Q ≤ ∑ d ∈ D, (Nat.totient d : ℝ)⁻¹ := by
  calc
    _ = ∑ _d ∈ D, (1 : ℝ) / Q := by simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply sum_le_sum
      intro d hd
      have hφ : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr (hD d hd).1
      have hφQ : (Nat.totient d : ℝ) ≤ Q := by exact_mod_cast (Nat.totient_le d).trans (hD d hd).2
      simpa only [one_div] using div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hφ hφQ

/-- The reciprocal mass of the smooth composite modulus family loses only a polynomial. -/
theorem primeProductModuli_reciprocal_lower (r m : ℕ)
    (hsmall : 4096 * r * (m + 1) ≤ progressionScaleN m) :
    1 / ((primeProductMassConstant r : ℝ) * ((m : ℝ) + 1) ^ r) ≤
      ∑ d ∈ primeProductModuli r m, (Nat.totient d : ℝ)⁻¹ := by
  have hmass : (0 : ℝ) < primeProductMassConstant r := by exact_mod_cast primeProductMassConstant_pos r
  have hQ : (0 : ℝ) < (progressionScaleN (m + 1)) ^ r := by unfold progressionScaleN; positivity
  have hc := primeProductModuli_polynomial_count r m hsmall
  have hN : progressionScaleN (m + 1) = progressionScaleN m * 2 ^ 64 := by
    simpa only [Nat.add_sub_cancel] using (progression_scale_previous (show 1 ≤ m + 1 by omega)).symm
  have hbound : (progressionScaleN (m + 1)) ^ r ≤
      primeProductMassConstant r * (m + 1) ^ r * (primeProductModuli r m).card := by
    have hpow : (progressionScaleN (m + 1)) ^ r =
        (progressionScaleN m) ^ r * 2 ^ (64 * r) := by
      rw [hN, mul_pow, pow_mul]
    rw [hpow]
    calc
      _ = 2 ^ (64 * r) * (progressionScaleN m) ^ r := mul_comm _ _
      _ ≤ 2 ^ (64 * r) * (4096 ^ r * r.factorial * (m + 1) ^ r * (primeProductModuli r m).card) :=
        Nat.mul_le_mul_left _ hc
      _ = _ := by unfold primeProductMassConstant; ring
  apply le_trans _ (sum_inv_totient_ge_card (primeProductModuli r m) ((progressionScaleN (m + 1)) ^ r)
    (fun d hd => ⟨(primeProductModuli_properties hd).1, (primeProductModuli_properties hd).2.2.2.2⟩))
  have hden : (0 : ℝ) < (primeProductMassConstant r : ℝ) * ((m : ℝ) + 1) ^ r :=
    mul_pos hmass (pow_pos (by have := Nat.cast_nonneg (α := ℝ) m; linarith) _)
  have hQ' : (0 : ℝ) < ((progressionScaleN (m + 1) ^ r : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow] using hQ
  apply (div_le_div_iff₀ hden hQ').mpr
  have hb : ((progressionScaleN (m + 1) ^ r : ℕ) : ℝ) ≤
      (primeProductMassConstant r : ℝ) * ((m : ℝ) + 1) ^ r * ((primeProductModuli r m).card : ℝ) := by
    exact_mod_cast hbound
  simpa only [one_mul, mul_comm, mul_left_comm, mul_assoc] using hb

/-- These moduli account for all but a smooth cofactor, and stay below the
level N^(1-1/t), once m is sufficiently large compared with t. -/
lemma primeProductModuli_progression_parameters (t m : ℕ) (ht : 3 ≤ t) (hm : max 2 (t - 2) ≤ m)
    {d : ℕ} (hd : d ∈ primeProductModuli (t - 2) m) :
    d ∈ Nat.smoothNumbers (2 ^ (128 * m)) ∧
      2 ^ (64 * t * m) ≤ d * 2 ^ (128 * m) ∧
      Squarefree d ∧ d.primeFactors.card = t - 2 ∧
      d ∈ Finset.Icc 1 (2 ^ (64 * (t - 1) * m)) := by
  obtain ⟨hdpos, hdsq, hdcard, hdlo, hdhi⟩ := primeProductModuli_properties hd
  have hr : t - 2 + 2 = t := by omega
  have hprod : (progressionScaleN m) ^ (t - 2) * 2 ^ (128 * m) = 2 ^ (64 * t * m) := by
    simp only [progressionScaleN, ← pow_mul, ← pow_add]
    congr 1
    nlinarith
  have hdQ : d ≤ 2 ^ (64 * (t - 1) * m) := by
    apply hdhi.trans
    simp only [progressionScaleN, ← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    have hmr : t - 2 ≤ m := (le_max_right _ _).trans hm
    have ht1 : t - 1 = (t - 2) + 1 := by omega
    rw [ht1]
    nlinarith
  refine ⟨primeProductModuli_smooth ((le_max_left _ _).trans hm) hd, ?_, hdsq, hdcard,
    mem_Icc.mpr ⟨hdpos, hdQ⟩⟩
  rw [← hprod]
  exact Nat.mul_le_mul_right _ hdlo

end Erdos821
