import Submission.Spec
open Nat Finset

lemma lemoine_from_A26 (h : A261627_conjecture) : lemoine_conjecture := by
  intro m hm
  rcases hm with ⟨hm7, hm_odd⟩
  rcases eq_or_lt_of_le hm7 with rfl | hm9
  · use 3, 2
    norm_num
  · have h_n : 6 < m - 1 := by omega
    have h_a26 := h (m - 1) h_n
    unfold A261627 at h_a26
    have h_pos : 0 < (filter (fun p =>
      let k := p * (if (m - 1) % 2 = 1 then 1 else 2) - 1
      k < m - 1 ∧ (m - 1 - k).Prime ∧ (m - 1 + k).Prime) (primesBelow (m - 1 + 1))).card := h_a26
    rw [Finset.card_pos] at h_pos
    rcases h_pos with ⟨q, hq⟩
    rw [mem_filter, mem_primesBelow] at hq
    rcases hq with ⟨hq_prime_bound, hq_cond⟩
    have hq_prime := hq_prime_bound.2
    have hm_even : (m - 1) % 2 = 0 := by
      rcases hm_odd with ⟨c, hc⟩
      rw [hc]
      omega
    have h_if : (if (m - 1) % 2 = 1 then 1 else 2) = 2 := by
      rw [if_neg]
      omega
    dsimp only at hq_cond
    rw [h_if] at hq_cond
    rcases hq_cond with ⟨hk_lt, hp_prime, hp'_prime⟩
    have hk_eq : q * 2 - 1 < m - 1 := hk_lt
    use m - 1 - (q * 2 - 1), q
    refine ⟨hp_prime, hq_prime, ?_⟩
    -- to prove m = (m - 1 - (q * 2 - 1)) + 2 * q
    -- note q >= 2 since q is prime, so q * 2 - 1 >= 3
    have hq_ge_2 : 2 ≤ q := hq_prime.two_le
    omega
