import Submission.ComponentEight

/-! A fixed-start consequence of the verified bound-eight component certificate. -/

namespace Erdos952Investigation

lemma component8_walk_stays (x : ℕ → GaussianInt) (h0 : x 0 = 3)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < 8) :
    ∀ n, InComponent8 (x n) := by
  intro n
  induction n with
  | zero => simpa only [h0] using three_inComponent8
  | succ n ih => exact inComponent8_closed ih (h (n + 1)).1 (h n).2

lemma no_injective_component8_walk :
    ¬ ∃ x : ℕ → GaussianInt, x 0 = 3 ∧ Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < 8 := by
  rintro ⟨x, h0, hx, h⟩
  have hinf := Set.infinite_range_of_injective hx
  apply hinf
  apply inComponent8_finite.subset
  rintro z ⟨n, rfl⟩
  exact component8_walk_stays x h0 h n

lemma step_bound_gt_eight_from_three (x : ℕ → GaussianInt) (C : ℤ)
    (h0 : x 0 = 3) (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) : 8 < C := by
  by_contra hn
  have hC : C ≤ 8 := le_of_not_gt hn
  apply no_injective_component8_walk
  exact ⟨x, h0, hx, fun n => ⟨(h n).1, lt_of_lt_of_le (h n).2 hC⟩⟩

#print axioms no_injective_component8_walk
#print axioms step_bound_gt_eight_from_three

end Erdos952Investigation
