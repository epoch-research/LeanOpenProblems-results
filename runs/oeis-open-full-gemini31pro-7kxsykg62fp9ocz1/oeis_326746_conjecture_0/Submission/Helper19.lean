import Mathlib

lemma countP_le_filter {α} (l : List α) (p q : α → Bool) (h : ∀ x, p x = true → q x = true) :
  l.countP p ≤ l.countP q := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.countP_cons, List.countP_cons]
    split_ifs with hp hq
    · omega
    · have hq_true : q hd = true := h hd hp
      rw [hq_true] at hq
      contradiction
    · omega
    · omega
