import Submission.Harm

open Nat Finset BigOperators

namespace A357674dev

open Harm

/-- Product expansion: `∏(1+aᵢ) = ∑_{m<5} eₘ` when each `aᵢ` is divisible by `p`
(higher symmetric terms vanish mod `p^5`). -/
theorem prod_expand5 (p : ℕ) [Fact p.Prime] (a : ℕ → ZMod (p^5))
    (hp : 7 ≤ p) (hdvd : ∀ i ∈ Icc 1 (p-1), (p : ZMod (p^5)) ∣ a i) :
    ∏ i ∈ Icc 1 (p-1), (1 + a i)
      = ∑ m ∈ range 5, ∑ t ∈ (Icc 1 (p-1)).powersetCard m, ∏ j ∈ t, a j := by
  rw [Finset.prod_one_add, Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion]
  symm
  apply Finset.sum_subset
  · apply Finset.range_subset.mpr
    rw [Nat.card_Icc]; omega
  · intro i _ hni
    rw [Finset.mem_range, not_lt] at hni
    apply Finset.sum_eq_zero
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    obtain ⟨hts, htc⟩ := ht
    have hdv : (p : ZMod (p^5))^i ∣ ∏ j ∈ t, a j := by
      rw [← htc, ← Finset.prod_const]
      exact Finset.prod_dvd_prod_of_dvd t _ (fun j hj => hdvd j (hts hj))
    have h0 : (p : ZMod (p^5))^i = 0 := by
      have h5 : (p : ZMod (p^5))^5 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
      calc (p : ZMod (p^5))^i = (p : ZMod (p^5))^5 * (p : ZMod (p^5))^(i-5) := by
            rw [← pow_add]; congr 1; omega
        _ = 0 := by rw [h5, zero_mul]
    rw [h0] at hdv
    exact zero_dvd_iff.mp hdv

end A357674dev
