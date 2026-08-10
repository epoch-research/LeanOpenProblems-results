import Mathlib

open Nat Set

noncomputable def A268597 (n : ℕ) : ℕ :=
  if h : ∃ x > 0, (x - 1) % Nat.totient x = n then
    sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }
  else
    1

theorem oeis_268597_conjecture_0 (n : ℕ) : A268597 n > 0 := by
  unfold A268597
  split_ifs with h
  · unfold sInf
    dsimp [Nat.instInfSet]
    split_ifs with h2
    · have h_spec := @Nat.find_spec (fun x => x > 0 ∧ (x - 1) % Nat.totient x = n) (fun _ => Classical.propDecidable _) h2
      exact h_spec.1
    · exfalso
      exact h2 h
  · decide

#print axioms oeis_268597_conjecture_0
