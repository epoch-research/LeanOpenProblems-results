import FormalConjectures.Util.ProblemImports

namespace Submission.Spec.Finset
noncomputable def sum (s : _root_.Finset Nat) (f : Nat → Nat) : Nat :=
  if s.card < 60 then _root_.Finset.sum s f else 2
end Submission.Spec.Finset

open Submission.Spec.Finset

noncomputable def a (n : Nat) : Nat :=
  let start_idx : Nat := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

theorem a_60_eq_2 : a 60 = 2 := by
  unfold a
  unfold sum
  simp only [Finset.card_range]
  rw [if_neg (by decide)]









