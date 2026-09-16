import Submission.Spec
open Nat Finset

lemma goldbach_from_A26 (h : A261627_conjecture) : goldbach_conjecture := by
  intro m hm
  rcases hm with ⟨hm4, hm_even⟩
  have ⟨k, hk⟩ := hm_even
  have hk2 : 2 ≤ k := by omega
  by_cases hk_lt : k < 7
  · interval_cases k
    · use 2, 2; refine ⟨by norm_num, by norm_num, by omega⟩
    · use 3, 3; refine ⟨by norm_num, by norm_num, by omega⟩
    · use 3, 5; refine ⟨by norm_num, by norm_num, by omega⟩
    · use 3, 7; refine ⟨by norm_num, by norm_num, by omega⟩
    · use 5, 7; refine ⟨by norm_num, by norm_num, by omega⟩
  · have hk_ge : 7 ≤ k := by omega
    have h_n : 6 < m / 2 := by omega
    have h_a26 := h (m / 2) h_n
    unfold A261627 at h_a26
    have h_pos : 0 < (filter (fun p =>
      let k := p * (if (m / 2) % 2 = 1 then 1 else 2) - 1
      k < m / 2 ∧ (m / 2 - k).Prime ∧ (m / 2 + k).Prime) (primesBelow (m / 2 + 1))).card := h_a26
    rw [Finset.card_pos] at h_pos
    rcases h_pos with ⟨q, hq⟩
    rw [mem_filter, mem_primesBelow] at hq
    rcases hq with ⟨hq_prime_bound, hq_cond⟩
    have hq_prime := hq_prime_bound.2
    have hq_ge_2 : 2 ≤ q := hq_prime.two_le
    
    dsimp only at hq_cond
    by_cases hn_odd : (m / 2) % 2 = 1
    · have h_if : (if (m / 2) % 2 = 1 then 1 else 2) = 1 := by rw [if_pos hn_odd]
      rw [h_if] at hq_cond
      rcases hq_cond with ⟨hk_lt2, hp_prime, hp'_prime⟩
      use m / 2 - (q * 1 - 1), m / 2 + (q * 1 - 1)
      refine ⟨hp_prime, hp'_prime, ?_⟩
      omega
    · have h_if : (if (m / 2) % 2 = 1 then 1 else 2) = 2 := by rw [if_neg hn_odd]
      rw [h_if] at hq_cond
      rcases hq_cond with ⟨hk_lt2, hp_prime, hp'_prime⟩
      use m / 2 - (q * 2 - 1), m / 2 + (q * 2 - 1)
      refine ⟨hp_prime, hp'_prime, ?_⟩
      omega
