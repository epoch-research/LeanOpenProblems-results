import Submission.Work

/-!
# Counting smooth shifted primes using large smooth moduli

The finite counting lemmas below are unconditional. The final application to
Erdős 821 has an explicit hypothesis on averaged progression counts; this
hypothesis has not been established.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

/-- If a smooth divisor accounts for all but a sufficiently small cofactor,
the whole number is smooth. -/
lemma smooth_of_large_smooth_divisor {m d y : ℕ}
    (hm : 0 < m) (hd : d ∈ Nat.smoothNumbers y) (hdm : d ∣ m)
    (hlarge : m < d * y) : m ∈ Nat.smoothNumbers y := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd.1
  have hquotpos : 0 < m / d := Nat.div_pos (Nat.le_of_dvd hm hdm) hdpos
  have hquotlt : m / d < y := (Nat.div_lt_iff_lt_mul hdpos).mpr (by simpa [mul_comm] using hlarge)
  have hquot : m / d ∈ Nat.smoothNumbers y := by
    apply Nat.mem_smoothNumbers'.mpr
    intro q hq hqd
    exact (Nat.le_of_dvd hquotpos hqd).trans_lt hquotlt
  simpa only [Nat.mul_div_cancel' hdm] using Nat.mul_mem_smoothNumbers hd hquot

/-- Squarefree divisors with exactly `r` prime factors inject into the
`r`-element subsets of the prime factors of the number being divided. -/
lemma squarefree_divisor_count_le_choose (D : Finset ℕ) (m r : ℕ)
    (hm : m ≠ 0)
    (hD : ∀ d ∈ D, Squarefree d ∧ d.primeFactors.card = r) :
    (D.filter (fun d => d ∣ m)).card ≤ m.primeFactors.card.choose r := by
  classical
  rw [← Finset.card_powersetCard]
  apply Finset.card_le_card_of_injOn Nat.primeFactors
  · intro d hd
    obtain ⟨hdD, hdm⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_powersetCard.mpr ⟨Nat.primeFactors_mono hdm hm, (hD d hdD).2⟩
  · intro d hd e he h
    have hdD := (Finset.mem_filter.mp hd).1
    have heD := (Finset.mem_filter.mp he).1
    rw [← Nat.prod_primeFactors_of_squarefree (hD d hdD).1,
      ← Nat.prod_primeFactors_of_squarefree (hD e heD).1, h]

lemma card_primeFactors_le_of_le_two_pow {m E : ℕ} (hm : 0 < m)
    (hbound : m ≤ 2 ^ E) : m.primeFactors.card ≤ E := by
  have hprod : 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p := by
    calc
      2 ^ m.primeFactors.card = ∏ _p ∈ m.primeFactors, 2 := by simp
      _ ≤ _ := Finset.prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  exact hprod.trans ((Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)).trans hbound)

/-- Double counting progressions to large smooth squarefree moduli. Repeated
counting costs at most `E^r`, rather than the total number of moduli. -/
lemma large_smooth_moduli_ap_sum_le (D P : Finset ℕ) (E y r : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ E)
    (hD : ∀ d ∈ D, d ∈ Nat.smoothNumbers y ∧ 2 ^ E ≤ d * y ∧
      Squarefree d ∧ d.primeFactors.card = r) :
    (∑ d ∈ D, (P.filter (fun p => d ∣ p - 1)).card) ≤
      (P.filter (fun p => p - 1 ∈ Nat.smoothNumbers y)).card * E ^ r := by
  classical
  have hswap : (∑ d ∈ D, (P.filter (fun p => d ∣ p - 1)).card) =
      ∑ p ∈ P, (D.filter (fun d => d ∣ p - 1)).card := by
    simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := D) (t := P) (fun d p : ℕ => d ∣ p - 1))
  rw [hswap]
  calc
    (∑ p ∈ P, (D.filter (fun d => d ∣ p - 1)).card) =
        ∑ p ∈ P with p - 1 ∈ Nat.smoothNumbers y,
          (D.filter (fun d => d ∣ p - 1)).card := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _) 
      intro p hp hn
      have hnot : p - 1 ∉ Nat.smoothNumbers y := by simpa [hp] using hn
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      obtain ⟨hdD, hdp⟩ := Finset.mem_filter.mp hd
      have hpprime := (hP p hp).1
      have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hpprime.one_lt
      apply hnot
      apply smooth_of_large_smooth_divisor hpos (hD d hdD).1 hdp
      exact (Nat.sub_lt (by omega) (by decide : 0 < 1)).trans_le
        ((hP p hp).2.trans (hD d hdD).2.1)
    _ ≤ ∑ _p ∈ P with _p - 1 ∈ Nat.smoothNumbers y, E ^ r := by
      apply Finset.sum_le_sum
      intro p hp
      have hpP := (Finset.mem_filter.mp hp).1
      have hpos : 0 < p - 1 := Nat.sub_pos_of_lt (hP p hpP).1.one_lt
      calc
        (D.filter (fun d => d ∣ p - 1)).card ≤ (p - 1).primeFactors.card.choose r :=
          squarefree_divisor_count_le_choose D (p - 1) r hpos.ne'
            (fun d hd => (hD d hd).2.2)
        _ ≤ (p - 1).primeFactors.card ^ r := Nat.choose_le_pow _ _
        _ ≤ E ^ r := Nat.pow_le_pow_left
          (card_primeFactors_le_of_le_two_pow hpos
            ((Nat.sub_le p 1).trans (hP p hpP).2)) r
    _ = _ := by simp

#print axioms large_smooth_moduli_ap_sum_le



/-- A sufficient progression-count hypothesis for the full conjecture.

The missing input is the lower bound on the sum of progression counts. It is
not supplied by Dirichlet's infinitude theorem for fixed moduli. -/
lemma erdos_821_of_large_smooth_moduli_ap_counts
    (H : ∀ t : ℕ, 5 ≤ t → ∀ M : ℕ,
      ∃ L : ℕ, max M 3 ≤ L ∧ ∃ D : Finset ℕ,
        (∀ d ∈ D, d ∈ Nat.smoothNumbers (2 ^ L) ∧
          2 ^ (t * L) ≤ d * 2 ^ L ∧ Squarefree d ∧ d.primeFactors.card = t) ∧
        (t * L) ^ t * 2 ^ ((t - 1) * L) ≤
          ∑ d ∈ D, (((2 ^ (t * L) + 1).primesBelow).filter
            (fun p => d ∣ p - 1)).card) :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  classical
  apply erdos_821_of_dyadic_smooth_prime_density
  intro t ht M
  obtain ⟨L, hL, D, hD, hcount⟩ := H t ht M
  let P := (2 ^ (t * L) + 1).primesBelow
  let Q := P.filter (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ L))
  have hP : ∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) := by
    intro p hp
    obtain ⟨hpbound, hpprime⟩ := Nat.mem_primesBelow.mp hp
    exact ⟨hpprime, by omega⟩
  refine ⟨L, (le_max_left M 3).trans hL, Q, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpP, hpsmooth⟩ := Finset.mem_filter.mp hp
    exact ⟨(hP p hpP).1, (hP p hpP).2, hpsmooth⟩
  · have hup := large_smooth_moduli_ap_sum_le D P (t * L) (2 ^ L) t hP hD
    have hprod : (t * L) ^ t * 2 ^ ((t - 1) * L) ≤ (t * L) ^ t * Q.card := by
      simpa only [mul_comm] using hcount.trans hup
    have hpos : 0 < (t * L) ^ t := pow_pos (Nat.mul_pos (by omega) (by omega)) _
    exact le_of_mul_le_mul_left hprod hpos

#print axioms erdos_821_of_large_smooth_moduli_ap_counts

end Erdos821
