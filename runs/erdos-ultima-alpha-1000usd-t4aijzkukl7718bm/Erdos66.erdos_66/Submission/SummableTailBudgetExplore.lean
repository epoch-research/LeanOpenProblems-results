import FormalConjecturesUtil

/-! One threshold controls all finite sums in the tail of a nonnegative
summable sequence. -/
namespace Erdos66SummableTailBudget
open scoped Classical

lemma exists_tail_budget (f : ℕ → ℝ) (hf : Summable f) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ S : Finset ℕ, (∀ n ∈ S, N ≤ n) → (∑ n ∈ S, f n) < η := by
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hf η hη
  refine ⟨s.sup id + 1, fun S hS ↦ ?_⟩
  have hd : Disjoint S s := by
    rw [Finset.disjoint_left]
    intro n hn hns
    have hlo := hS n hn
    have hhi := Finset.le_sup (f := id) hns
    change n ≤ s.sup id at hhi
    omega
  exact (le_abs_self _).trans_lt (by simpa only [Real.norm_eq_abs] using hs S hd)

lemma summable_fourth_tail : Summable (fun n : ℕ ↦ 2 / ((n:ℝ)+2)^4) := by
  exact Summable.of_norm (summable_pow_div_add (α := ℝ) 2 4 2 (by norm_num))

lemma exists_fourth_tail_budget :
    ∃ N : ℕ, ∀ S : Finset ℕ, (∀ n ∈ S, N ≤ n) →
      (∑ n ∈ S, 2 / ((n:ℝ)+2)^4) < 1 :=
  exists_tail_budget _ summable_fourth_tail 1 (by norm_num)

end Erdos66SummableTailBudget
