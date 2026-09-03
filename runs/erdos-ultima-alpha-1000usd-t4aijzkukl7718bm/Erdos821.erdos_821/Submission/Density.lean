import Submission.Work

/-!
# A strengthened necessary-and-sufficient series condition for Erdős 821

This file contains conditional reductions, not a settlement of the conjecture.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma smoothShiftedPredecessors_antitone : Antitone smoothShiftedPredecessors := by
  intro k K hk d hd
  refine ⟨hd.1, fun q hq => ?_⟩
  exact (Nat.pow_le_pow_right (Nat.one_le_of_lt (Nat.prime_of_mem_primeFactors hq).one_lt)
    hk).trans (hd.2 q hq)

/-- The full conjecture requires divergence at every exponent below one,
not merely infinitude of each smooth shifted-prime set. -/
lemma not_summable_smooth_shifted_all_exponents_of_erdos_821
    (H : ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite)
    (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : s < 1) :
    ¬Summable ((smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s))) := by
  classical
  intro hsum
  obtain ⟨B, hB⟩ := exists_nat_gt (1 / (1 - s))
  let K := max k B
  have hkK : k ≤ K := le_max_left _ _
  have hK : 1 ≤ K := hk.trans hkK
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hBK : (B : ℝ) ≤ K := by exact_mod_cast (le_max_right k B)
  have hsK : s ≤ 1 - 1 / (2 * (K : ℝ)) := by
    have hprod : 1 < (K : ℝ) * (1 - s) :=
      (div_lt_iff₀ (sub_pos.mpr hs)).mp (hB.trans_le hBK)
    have he : 1 / (2 * (K : ℝ)) ≤ 1 - s := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mpr
      nlinarith
    linarith
  apply not_summable_smooth_shifted_of_erdos_821 H K hK
  refine hsum.of_nonneg_of_le (fun d => Set.indicator_nonneg
    (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) d) ?_
  intro d
  by_cases hd : d ∈ smoothShiftedPredecessors K
  · have hdk : d ∈ smoothShiftedPredecessors k := smoothShiftedPredecessors_antitone hkK hd
    rw [Set.indicator_of_mem hd, Set.indicator_of_mem hdk]
    have hd1 : (1 : ℝ) ≤ d := by
      have hdpos : 0 < d := by
        have hdp := hd.1.two_le
        omega
      exact_mod_cast hdpos
    exact Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  · rw [Set.indicator_of_notMem hd]
    exact Set.indicator_nonneg (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) d

/-- A stronger-looking series formulation is in fact equivalent to the
original conjecture. No unconditional divergence claim is made here. -/
lemma erdos_821_iff_smooth_shifted_all_exponents :
    (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite) ↔
      ∀ k : ℕ, 1 ≤ k → ∀ s : ℝ, s < 1 →
        ¬Summable ((smoothShiftedPredecessors k).indicator (fun d : ℕ => (d : ℝ) ^ (-s))) := by
  constructor
  · exact not_summable_smooth_shifted_all_exponents_of_erdos_821
  · intro H
    apply erdos_821_iff_smooth_shifted_nonsummable.mpr
    intro k hk
    apply H k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have he : (0 : ℝ) < 1 / (2 * (k : ℝ)) := by positivity
    linarith

/-- In particular, the original conjecture implies infinitely many primes
whose predecessors are smooth to any fixed root scale. -/
lemma infinite_smooth_shifted_of_erdos_821
    (H : ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite)
    (k : ℕ) (hk : 1 ≤ k) : (smoothShiftedPredecessors k).Infinite := by
  classical
  by_contra h
  have hfin := Set.not_infinite.mp h
  apply not_summable_smooth_shifted_all_exponents_of_erdos_821 H k hk 0 (by norm_num)
  apply summable_of_finite_support
  exact hfin.subset Set.support_indicator_subset


/-- At each fixed smoothness scale, the conjecture forces the counting
exponent of shifted primes to be one, along arbitrarily large dyadic scales. -/
lemma full_dyadic_density_of_erdos_821
    (H : ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite)
    (k : ℕ) (hk : 1 ≤ k) (t : ℕ) (ht : 2 ≤ t) (M : ℕ) :
    ∃ L : ℕ, M ≤ L ∧ 2 ^ ((t - 1) * L) ≤
      ((Finset.range (2 ^ (t * L))).filter (fun d => d ∈ smoothShiftedPredecessors k)).card := by
  classical
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hden : (0 : ℝ) < 2 * t := by positivity
  let e : ℝ := 1 / (2 * (t : ℝ))
  have he : 0 < e := one_div_pos.mpr hden
  have heid : (2 * (t : ℝ)) * e = 1 := mul_one_div_cancel hden.ne'
  have hehalf : e ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hs : 0 ≤ 1 - e := by linarith
  have ha : ((t - 1 : ℕ) : ℝ) < (t : ℝ) * (1 - e) := by
    rw [Nat.cast_sub (show 1 ≤ t by omega), Nat.cast_one]
    nlinarith
  exact exists_large_dyadic_count_of_not_summable (smoothShiftedPredecessors k)
    t (t - 1) (1 - e) (by omega) hs ha
    (not_summable_smooth_shifted_all_exponents_of_erdos_821 H k hk (1 - e) (by linarith)) M

/-- A counting formulation equivalent to the original conjecture. The two
parameters are independent: `k` fixes the root-smoothness scale, while increasing
`t` requires the counting exponent to approach one. -/
lemma erdos_821_iff_full_dyadic_density :
    (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite) ↔
      ∀ k : ℕ, 1 ≤ k → ∀ t : ℕ, 2 ≤ t → ∀ M : ℕ,
        ∃ L : ℕ, M ≤ L ∧ 2 ^ ((t - 1) * L) ≤
          ((Finset.range (2 ^ (t * L))).filter
            (fun d => d ∈ smoothShiftedPredecessors k)).card := by
  classical
  constructor
  · exact full_dyadic_density_of_erdos_821
  · intro H
    apply erdos_821_of_dyadic_smooth_prime_density
    intro t ht M
    obtain ⟨L, hLM, hcount⟩ := H t (by omega) t (by omega) M
    let D := (Finset.range (2 ^ (t * L))).filter (fun d => d ∈ smoothShiftedPredecessors t)
    let P := D.image (fun d => d + 1)
    refine ⟨L, hLM, P, ?_, ?_⟩
    · intro p hp
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hdlt, hdS⟩ := Finset.mem_filter.mp hd
      have hdprime : (d + 1).Prime := hdS.1
      have hdlt' : d < 2 ^ (t * L) := Finset.mem_range.mp hdlt
      refine ⟨hdprime, by omega, ?_⟩
      simp only [Nat.add_sub_cancel]
      apply Nat.mem_smoothNumbers'.mpr
      intro q hq hqd
      have hd0 : d ≠ 0 := by intro h; subst d; exact Nat.not_prime_one hdprime
      have hqmem : q ∈ d.primeFactors := hq.mem_primeFactors hqd hd0
      have hqpow : q ^ t < (2 ^ L) ^ t := by
        calc
          q ^ t ≤ d := hdS.2 q hqmem
          _ < 2 ^ (t * L) := hdlt'
          _ = (2 ^ L) ^ t := by rw [← pow_mul]; congr 1; ring
      exact (Nat.pow_lt_pow_iff_left (by omega : t ≠ 0)).mp hqpow
    · have hcard : P.card = D.card := Finset.card_image_of_injective _
          (fun a b hab => Nat.add_right_cancel hab)
      rw [hcard]
      exact hcount

#print axioms erdos_821_iff_full_dyadic_density

#print axioms erdos_821_iff_smooth_shifted_all_exponents
#print axioms infinite_smooth_shifted_of_erdos_821

end Erdos821
