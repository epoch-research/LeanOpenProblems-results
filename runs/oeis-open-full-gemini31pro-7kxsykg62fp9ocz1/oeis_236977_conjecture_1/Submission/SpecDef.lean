import Mathlib
import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  (Ico 1 ((n - 1) / 2 + 1)).sum fun k =>
    let m := totient k * totient (n - k)
    if sqrt m ^ 2 = m then 1 else 0

lemma a_pos_of_witness (n k : ℕ)
    (hk1 : k ∈ Ico 1 ((n - 1) / 2 + 1))
    (hk2 : (let m := totient k * totient (n - k); sqrt m ^ 2 == m) = true) :
    a n > 0 := by
  unfold a
  have h_le : (let m := totient k * totient (n - k); if sqrt m ^ 2 = m then 1 else 0) ≤
    (Ico 1 ((n - 1) / 2 + 1)).sum (fun k => let m := totient k * totient (n - k); if sqrt m ^ 2 = m then (1 : ℕ) else 0) := by
    apply single_le_sum (f := fun k => let m := totient k * totient (n - k); if sqrt m ^ 2 = m then 1 else 0)
    · intro i _
      dsimp
      split_ifs
      · exact Nat.zero_le 1
      · exact Nat.le_refl 0
    · exact hk1
  dsimp at h_le
  have h_eq : (totient k * totient (n - k)).sqrt ^ 2 = totient k * totient (n - k) := by
    exact of_decide_eq_true hk2
  rw [h_eq, if_pos rfl] at h_le
  exact h_le
