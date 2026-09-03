import Submission.GeometricDistributionCriterion

/-!
# Exact binomial moments for the smooth product modulus aggregate

The aggregate progression count is exactly a binomial moment of the number
of block-prime divisors of p-1. Size restrictions make its overcount bounded
by t-1, independently of the scale m. These are finite identities and upper
bounds; no missing lower bound for this moment is assumed or proved here.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

noncomputable def blockPrimeDivisors (m n : ℕ) : Finset ℕ :=
  (geometricBlockPrimes m).filter (fun q => q ∣ n)

lemma prime_product_divisor_count_eq_choose (r m n : ℕ) :
    ((primeProductModuli r m).filter (fun d => d ∣ n)).card =
      (blockPrimeDivisors m n).card.choose r := by
  have hfilter : ((geometricBlockPrimes m).powersetCard r).filter
      (fun S => (∏ q ∈ S, q) ∣ n) = (blockPrimeDivisors m n).powersetCard r := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hSP, hSc⟩, hprod⟩
      refine ⟨?_, hSc⟩
      intro q hq
      exact Finset.mem_filter.mpr ⟨hSP hq, (Finset.dvd_prod_of_mem id hq).trans hprod⟩
    · rintro ⟨hSB, hSc⟩
      have hSP : S ⊆ geometricBlockPrimes m := hSB.trans (Finset.filter_subset _ _)
      refine ⟨⟨hSP, hSc⟩, ?_⟩
      exact (Sieve.prod_primes_dvd_iff S
        (fun q hq => (mem_geometricBlockPrimes.mp (hSP hq)).1) n).mpr
          (fun q hq => (Finset.mem_filter.mp (hSB hq)).2)
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ q ∈ S, q)
      (↑((blockPrimeDivisors m n).powersetCard r) : Set (Finset ℕ)) := by
    intro S hS T hT heq
    change S ∈ (blockPrimeDivisors m n).powersetCard r at hS
    change T ∈ (blockPrimeDivisors m n).powersetCard r at hT
    have hSB : S ⊆ blockPrimeDivisors m n := (Finset.mem_powersetCard.mp hS).1
    have hTB : T ⊆ blockPrimeDivisors m n := (Finset.mem_powersetCard.mp hT).1
    have hSP : S ⊆ geometricBlockPrimes m := hSB.trans (Finset.filter_subset _ _)
    have hTP : T ⊆ geometricBlockPrimes m := hTB.trans (Finset.filter_subset _ _)
    have hprS : ∀ q ∈ S, q.Prime := fun q hq => (mem_geometricBlockPrimes.mp (hSP hq)).1
    have hprT : ∀ q ∈ T, q.Prime := fun q hq => (mem_geometricBlockPrimes.mp (hTP hq)).1
    have h := congrArg Nat.primeFactors heq
    simpa only [Nat.primeFactors_prod hprS, Nat.primeFactors_prod hprT] using h
  unfold primeProductModuli
  rw [Finset.filter_image, hfilter, Finset.card_image_of_injOn hinj, Finset.card_powersetCard]

/-- The progression aggregate is a factorial/binomial moment, not a first
moment of the count of individual prime divisors. -/
theorem prime_product_progression_sum_eq_binomial_moment (r m N : ℕ) :
    (∑ d ∈ primeProductModuli r m, progressionPrimeCount d N) =
      ∑ p ∈ (N + 1).primesBelow, (blockPrimeDivisors m (p - 1)).card.choose r := by
  have hswap := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := primeProductModuli r m) (t := (N + 1).primesBelow)
    (fun d p : ℕ => d ∣ p - 1)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hswap
  unfold progressionPrimeCount
  rw [hswap]
  exact Finset.sum_congr rfl (fun p _ => prime_product_divisor_count_eq_choose r m (p - 1))

theorem geometric_smooth_deficit_eq_binomial_moment (t m : ℕ) :
    geometricSmoothModulusDeficit t m =
      (((2 ^ (64 * t * m) + 1).primesBelow.card : ℝ) *
        (∑ d ∈ primeProductModuli (t - 2) m, (d.totient : ℝ)⁻¹)) -
      ∑ p ∈ (2 ^ (64 * t * m) + 1).primesBelow,
        (((blockPrimeDivisors m (p - 1)).card.choose (t - 2) : ℕ) : ℝ) := by
  have h := prime_product_progression_sum_eq_binomial_moment (t - 2) m (2 ^ (64 * t * m))
  have hR := congrArg (fun n : ℕ => (n : ℝ)) h
  simp only [Nat.cast_sum] at hR
  unfold geometricSmoothModulusDeficit
  rw [hR]

lemma block_prime_divisor_card_lt (t m n : ℕ) (hm : 1 ≤ m)
    (hn : 0 < n) (hN : n < 2 ^ (64 * t * m)) :
    (blockPrimeDivisors m n).card < t := by
  let P := blockPrimeDivisors m n
  have hprime : ∀ q ∈ P, q.Prime := fun q hq =>
    (mem_geometricBlockPrimes.mp (Finset.mem_filter.mp hq).1).1
  have hprod : (∏ q ∈ P, q) ∣ n :=
    (Sieve.prod_primes_dvd_iff P hprime n).mpr (fun q hq => (Finset.mem_filter.mp hq).2)
  have hY : 1 < progressionScaleN m := by
    unfold progressionScaleN
    have h := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) (show 0 < 64 * m by omega)
    simpa only [pow_zero] using h
  have hpow : (progressionScaleN m) ^ P.card < (progressionScaleN m) ^ t := by
    calc
      _ = ∏ _q ∈ P, progressionScaleN m := by simp
      _ ≤ ∏ q ∈ P, q := Finset.prod_le_prod' (fun q hq =>
        (mem_geometricBlockPrimes.mp (Finset.mem_filter.mp hq).1).2.1.le)
      _ ≤ n := Nat.le_of_dvd hn hprod
      _ < 2 ^ (64 * t * m) := hN
      _ = _ := by unfold progressionScaleN; rw [← pow_mul]; congr 1; ring
  exact (Nat.pow_lt_pow_iff_right hY).mp hpow

lemma prime_product_divisor_count_le_at_scale (t m n : ℕ) (ht : 2 ≤ t)
    (hm : 1 ≤ m) (hn : 0 < n) (hN : n < 2 ^ (64 * t * m)) :
    ((primeProductModuli (t - 2) m).filter (fun d => d ∣ n)).card ≤ t - 1 := by
  rw [prime_product_divisor_count_eq_choose]
  have hc : (blockPrimeDivisors m n).card ≤ t - 1 := by
    have h := block_prime_divisor_card_lt t m n hm hn hN
    omega
  calc
    _ ≤ (t - 1).choose (t - 2) := Nat.choose_le_choose (t - 2) hc
    _ = t - 1 := by
      rw [show t - 1 = (t - 2) + 1 by omega, Nat.choose_succ_self_right]

/-- The overcount in the finite smooth-prime transfer is at most t-1,
not a polynomial of degree t-2 in the scale index. -/
theorem prime_product_progression_sum_le_smooth_count (t m : ℕ) (ht : 3 ≤ t)
    (hm : max 2 (t - 2) ≤ m) :
    (∑ d ∈ primeProductModuli (t - 2) m, progressionPrimeCount d (2 ^ (64 * t * m))) ≤
      (t - 1) * (((2 ^ (64 * t * m) + 1).primesBelow).filter
        (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * m)))).card := by
  let D := primeProductModuli (t - 2) m
  let P := (2 ^ (64 * t * m) + 1).primesBelow
  let G := P.filter (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * m)))
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p - 1 < 2 ^ (64 * t * m) := by
    have h := Nat.mem_primesBelow.mp hp
    exact ⟨h.2, by have := h.2.two_le; omega⟩
  have hswap : (∑ d ∈ D, progressionPrimeCount d (2 ^ (64 * t * m))) =
      ∑ p ∈ P, (D.filter (fun d => d ∣ p - 1)).card := by
    simpa only [progressionPrimeCount, Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := D) (t := P) (fun d p : ℕ => d ∣ p - 1))
  change _ ≤ (t - 1) * G.card
  rw [hswap]
  have hrestrict : (∑ p ∈ P, (D.filter (fun d => d ∣ p - 1)).card) =
      ∑ p ∈ G, (D.filter (fun d => d ∣ p - 1)).card := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    obtain ⟨hdD, hdp⟩ := Finset.mem_filter.mp hd
    have hdprops := primeProductModuli_progression_parameters t m ht hm hdD
    have hs := smooth_of_large_smooth_divisor
      (Nat.sub_pos_of_lt (hP p hp).1.one_lt) hdprops.1 hdp
      ((hP p hp).2.trans_le hdprops.2.1)
    exact hnot (Finset.mem_filter.mpr ⟨hp, hs⟩)
  rw [hrestrict]
  calc
    _ ≤ ∑ _p ∈ G, (t - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpP := (Finset.mem_filter.mp hp).1
      exact prime_product_divisor_count_le_at_scale t m (p - 1) (by omega) (by omega)
        (Nat.sub_pos_of_lt (hP p hpP).1.one_lt) (hP p hpP).2
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm]

/-- A sharper finite consequence of the same explicit signed-deficit
hypothesis. The hypothesis remains unproved; only the overcount is improved. -/
theorem geometric_signed_deficit_sharp_smooth_prime_count (t m : ℕ) (ht : 3 ≤ t)
    (hm : max 2 (t - 2) ≤ m)
    (hsmall : 4096 * (t - 2) * (m + 1) ≤ progressionScaleN m)
    (hbudget : 256 * t * primeProductMassConstant (t - 2) ≤ m + 1)
    (herr : geometricSmoothModulusDeficit t m ≤
      (2 : ℝ) ^ (64 * t * m) / ((m : ℝ) + 1) ^ t) :
    2 ^ (64 * t * m) ≤
      (256 * t * primeProductMassConstant (t - 2) * (t - 1)) * (m + 1) ^ (t - 1) *
        (((2 ^ (64 * t * m) + 1).primesBelow).filter
          (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * m)))).card := by
  let r := t - 2
  let N := 2 ^ (64 * t * m)
  let z : ℝ := (m : ℝ) + 1
  let C := primeProductMassConstant r
  let D := primeProductModuli r m
  let P := (N + 1).primesBelow
  let G := P.filter (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * m)))
  let S : ℝ := ∑ d ∈ D, (d.totient : ℝ)⁻¹
  let T : ℝ := ∑ d ∈ D, (progressionPrimeCount d N : ℝ)
  have hC : (0 : ℝ) < C := by exact_mod_cast primeProductMassConstant_pos r
  have hz : 0 < z := by dsimp [z]; positivity
  have hS : 1 / ((C : ℝ) * z ^ r) ≤ S := primeProductModuli_reciprocal_lower r m hsmall
  have hP : (N : ℝ) ≤ (128 * (t : ℝ)) * z * (P.card : ℝ) := by
    dsimp [N, z, P]
    exact_mod_cast geometric_total_prime_count_lower t m ht (by omega)
  have he : (P.card : ℝ) * S - (N : ℝ) / z ^ (r + 2) ≤ T := by
    have he' : geometricSmoothModulusDeficit t m ≤ (N : ℝ) / z ^ (r + 2) := by
      simpa only [N, r, Nat.sub_add_cancel (by omega : 2 ≤ t),
        Nat.cast_pow, Nat.cast_ofNat] using herr
    change (P.card : ℝ) * S - T ≤ (N : ℝ) / z ^ (r + 2) at he'
    linarith only [he']
  have hbudget' : 2 * (128 * (t : ℝ)) * (C : ℝ) ≤ z := by
    have h : (256 : ℝ) * t * C ≤ (m : ℝ) + 1 := by exact_mod_cast hbudget
    dsimp [z]
    nlinarith only [h]
  have hcount := polynomial_main_survives (N : ℝ) (P.card : ℝ) S T (128 * (t : ℝ)) (C : ℝ) z r
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity) hC hz hP hS he hbudget'
  have hT : T ≤ ((t - 1 : ℕ) : ℝ) * (G.card : ℝ) := by
    dsimp [T, D, r, N, G, P]
    exact_mod_cast prime_product_progression_sum_le_smooth_count t m ht hm
  have hfinal : (N : ℝ) ≤
      ((256 * t * C * (t - 1) : ℕ) : ℝ) * z ^ (t - 1) * (G.card : ℝ) := by
    calc
      _ ≤ 2 * (128 * (t : ℝ)) * C * z ^ (r + 1) * T := hcount
      _ ≤ 2 * (128 * (t : ℝ)) * C * z ^ (r + 1) *
          (((t - 1 : ℕ) : ℝ) * (G.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
      _ = _ := by
        have hrt : r + 1 = t - 1 := by dsimp [r]; omega
        rw [hrt]
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        ring
  dsimp [N, C, r, z, G, P] at hfinal
  exact_mod_cast hfinal

end Erdos821
