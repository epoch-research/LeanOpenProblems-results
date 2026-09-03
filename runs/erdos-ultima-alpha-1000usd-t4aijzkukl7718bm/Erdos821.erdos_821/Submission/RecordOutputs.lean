import Submission.RecordPairs
import Submission.PrimeStripping

/-!
# Smoothness of normalized record outputs

At a positive-exponent normalized record of the unrestricted totient
multiplicity, a large prime divisor of the output can be stripped at subpower
cost. Consequently sufficiently large record outputs are smooth to every
fixed root scale. This is smoothness relative to the output, not relative to
each prime predecessor, and does not settle Erdős 821.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma normalized_record_g_le (n j : ℕ) (_hn : 0 < n) (hj : 0 < j)
    (s : ℝ)
    (hrec : ∀ d : ℕ, d ≤ n →
      (g d : ℝ) / (d : ℝ) ^ s ≤ (g n : ℝ) / (n : ℝ) ^ s)
    (hjn : j ≤ n) :
    (g j : ℝ) ≤ (g n : ℝ) / (n : ℝ) ^ s * (j : ℝ) ^ s := by
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hj) s)).mp
    (hrec j hjn)

lemma normalized_record_prime_power_bound (n q K : ℕ) (hn : 0 < n)
    (hg : 0 < g n) (hq : q.Prime) (hqd : q ∣ n)
    (hK : 1 ≤ K) (hnq : n ≤ q ^ K) (s : ℝ) (hs : 0 ≤ s)
    (hrec : ∀ d : ℕ, d ≤ n →
      (g d : ℝ) / (d : ℝ) ^ s ≤ (g n : ℝ) / (n : ℝ) ^ s) :
    (n : ℝ) ^ (s / K) ≤
      ((K : ℝ) + 1) * ((n.divisors.card : ℝ) + 1) ^ (K + 1) := by
  let r := ordCompl[q] n
  let A := (g n : ℝ) / (n : ℝ) ^ s
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgR : (0 : ℝ) < g n := by exact_mod_cast hg
  have hA : 0 < A := div_pos hgR (Real.rpow_pos_of_pos hnR s)
  have hrpos : 0 < r := Nat.ordCompl_pos q hn.ne'
  have hrn : r ∣ n := Nat.ordCompl_dvd n q
  have hDr : r.divisors.card ≤ n.divisors.card :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' hrn)
  have hsum : (∑ d ∈ r.divisors, (g d : ℝ)) ≤
      ((n.divisors.card : ℝ) + 1) * A * (r : ℝ) ^ s := by
    calc
      (∑ d ∈ r.divisors, (g d : ℝ)) ≤
          ∑ _d ∈ r.divisors, A * (r : ℝ) ^ s := by
        apply Finset.sum_le_sum
        intro d hd
        have hdpos := Nat.pos_of_mem_divisors hd
        have hdr := Nat.le_of_dvd hrpos (Nat.dvd_of_mem_divisors hd)
        exact (normalized_record_g_le n d hn hdpos s hrec
          (hdr.trans (Nat.le_of_dvd hn hrn))).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg d) (by exact_mod_cast hdr) hs) hA.le)
      _ = (r.divisors.card : ℝ) * A * (r : ℝ) ^ s := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ _ := by
        gcongr
        exact (by exact_mod_cast hDr : (r.divisors.card : ℝ) ≤ n.divisors.card).trans
          (le_add_of_nonneg_right (by norm_num))
  have hstrip : (g n : ℝ) ≤
      ((K : ℝ) + 1) * ((n.divisors.card : ℝ) + 1) ^ K *
        ∑ d ∈ r.divisors, (g d : ℝ) := by
    exact_mod_cast g_le_valuation_factor_mul_sum_ordCompl n q K hn hq
      (Nat.factorization_le_of_le_pow hnq)
  have hroot := ordCompl_le_rpow_of_le_prime_pow hn hq hqd hK hnq
  have hb : (g n : ℝ) ≤
      (((K : ℝ) + 1) * ((n.divisors.card : ℝ) + 1) ^ (K + 1)) *
        A * (n : ℝ) ^ ((1 - 1 / K) * s) := by
    calc
      (g n : ℝ) ≤ ((K : ℝ) + 1) * ((n.divisors.card : ℝ) + 1) ^ K *
          (((n.divisors.card : ℝ) + 1) * A * (r : ℝ) ^ s) :=
        hstrip.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
      _ = (((K : ℝ) + 1) * ((n.divisors.card : ℝ) + 1) ^ (K + 1)) *
          A * (r : ℝ) ^ s := by rw [pow_succ]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          (r : ℝ) ^ s ≤ ((n : ℝ) ^ (1 - 1 / (K : ℝ))) ^ s :=
            Real.rpow_le_rpow (Nat.cast_nonneg r) hroot hs
          _ = _ := (Real.rpow_mul hnR.le _ _).symm
  have heq : A * (n : ℝ) ^ ((1 - 1 / K) * s) =
      (g n : ℝ) / (n : ℝ) ^ (s / K) := by
    dsimp [A]
    rw [div_mul_eq_mul_div, mul_div_assoc, ← Real.rpow_sub hnR,
      show (1 - 1 / (K : ℝ)) * s - s = -(s / K) by ring,
      Real.rpow_neg hnR.le]
    rfl
  rw [mul_assoc, heq, ← mul_div_assoc] at hb
  have hb' := (le_div_iff₀ (Real.rpow_pos_of_pos hnR (s / K))).mp hb
  exact (mul_le_mul_iff_right₀ hgR).mp (by simpa only [mul_comm] using hb')

lemma eventually_normalized_record_output_smooth (K : ℕ) (hK : 1 ≤ K)
    (s : ℝ) (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, 0 < g n →
      (∀ d : ℕ, d ≤ n →
        (g d : ℝ) / (d : ℝ) ^ s ≤ (g n : ℝ) / (n : ℝ) ^ s) →
      ∀ q ∈ n.primeFactors, q ^ K < n := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have he : 0 < s / (2 * (K : ℝ)) := div_pos hs (by positivity)
  filter_upwards [eventually_const_mul_divisors_pow_le_rpow (K + 1)
    ((K : ℝ) + 1) (s / (2 * K)) (by positivity) he,
    eventually_ge_atTop 2] with n hnB hn hg hrec q hq
  by_contra h
  have hnq : n ≤ q ^ K := Nat.le_of_not_gt h
  have hbound := normalized_record_prime_power_bound n q K (by omega) hg
    (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
    hK hnq s hs.le hrec
  have hlt : (n : ℝ) ^ (s / (2 * K)) < (n : ℝ) ^ (s / K) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (show 1 < n by omega))
    have hhalf : s / (2 * (K : ℝ)) = (s / K) / 2 := by ring
    rw [hhalf]
    have := div_pos hs hKR
    linarith
  exact (not_lt_of_ge (hbound.trans hnB)) hlt

/-- Every attained positive exponent can still be attained at arbitrarily
large root-smooth record outputs. The exponent is preserved, not increased. -/
lemma exists_smooth_normalized_record_of_infinite_g_gt (δ s : ℝ)
    (hs : 0 < s) (hsδ : s < δ)
    (H : {n : ℕ | (n : ℝ) ^ δ < (g n : ℝ)}.Infinite)
    (K : ℕ) (hK : 1 ≤ K) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ (n : ℝ) ^ δ < (g n : ℝ) ∧
      (∀ d : ℕ, d ≤ n →
        (g d : ℝ) / (d : ℝ) ^ s ≤ (g n : ℝ) / (n : ℝ) ^ s) ∧
      ∀ q ∈ n.primeFactors, q ^ K < n := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_normalized_record_output_smooth K hK s hs)
  obtain ⟨n, hn, hgn, hrec⟩ :=
    exists_large_normalized_record_at g δ s hsδ H (max N T)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hgpos : 0 < g n := by
    exact_mod_cast (Real.rpow_pos_of_pos hnpos δ).trans hgn
  exact ⟨n, (le_max_left _ _).trans_lt hn, hgn, hrec,
    hT n ((le_max_right _ _).trans hn.le) hgpos hrec⟩

lemma infinite_smooth_outputs_of_infinite_g_gt (δ : ℝ) (hδ : 0 < δ)
    (H : {n : ℕ | (n : ℝ) ^ δ < (g n : ℝ)}.Infinite)
    (K : ℕ) (hK : 1 ≤ K) :
    {n : ℕ | (n : ℝ) ^ δ < (g n : ℝ) ∧
      ∀ q ∈ n.primeFactors, q ^ K < n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, hg, _, hsm⟩ := exists_smooth_normalized_record_of_infinite_g_gt
    δ (δ / 2) (half_pos hδ) (by linarith) H K hK N
  exact ⟨n, ⟨hg, hsm⟩, hn⟩

/-- Unconditionally, polynomial multiplicity occurs at record outputs that
are smooth to any specified fixed root scale. This concerns the output n;
it supplies no root-smoothness estimate relative to the sizes of the primes
whose predecessors divide n. -/
theorem exists_fixed_positive_power_smooth_record_outputs :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ K : ℕ, 1 ≤ K → ∀ N : ℕ,
      ∃ n : ℕ, N < n ∧ (n : ℝ) ^ δ < (g n : ℝ) ∧
        (∀ d : ℕ, d ≤ n →
          (g d : ℝ) / (d : ℝ) ^ (δ / 2) ≤
            (g n : ℝ) / (n : ℝ) ^ (δ / 2)) ∧
        ∀ q ∈ n.primeFactors, q ^ K < n := by
  obtain ⟨δ, hδ, hδ1, H⟩ := exists_positive_power_gOddSquarefree
  have HG : {n : ℕ | (n : ℝ) ^ δ < (g n : ℝ)}.Infinite := by
    apply H.mono
    intro n hn
    change (n : ℝ) ^ δ < (gOddSquarefree n : ℝ) at hn
    change (n : ℝ) ^ δ < (g n : ℝ)
    have hle : (gOddSquarefree n : ℝ) ≤ (g n : ℝ) := by
      exact_mod_cast (gOddSquarefree_le_gSquarefree n).trans (gSquarefree_le_g n)
    exact hn.trans_le hle
  refine ⟨δ, hδ, hδ1, fun K hK N => ?_⟩
  exact exists_smooth_normalized_record_of_infinite_g_gt δ (δ / 2)
    (half_pos hδ) (by linarith) HG K hK N

#print axioms normalized_record_prime_power_bound
#print axioms eventually_normalized_record_output_smooth
#print axioms exists_smooth_normalized_record_of_infinite_g_gt
#print axioms infinite_smooth_outputs_of_infinite_g_gt
#print axioms exists_fixed_positive_power_smooth_record_outputs

end Erdos821
