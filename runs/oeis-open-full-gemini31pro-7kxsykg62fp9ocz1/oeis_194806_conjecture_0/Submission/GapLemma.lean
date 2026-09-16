import Mathlib

open Nat List

lemma gap_lemma (l : List ℕ) (K : ℕ) (hK : 1 ≤ K) (h_max : ∀ p ∈ l, p ≤ K) :
  l.prod ≤ K ^ 2 → ∃ a b, a * b = l.prod ∧ a ≤ K ∧ b ≤ K := by
  induction l with
  | nil =>
    intro _
    use 1, 1
    simp [hK]
  | cons p ps ih =>
    intro h_prod
    have hp : p ≤ K := h_max p (Mem.head ps)
    have h_max_ps : ∀ p ∈ ps, p ≤ K := fun q hq => h_max q (Mem.tail p hq)
    sorry
