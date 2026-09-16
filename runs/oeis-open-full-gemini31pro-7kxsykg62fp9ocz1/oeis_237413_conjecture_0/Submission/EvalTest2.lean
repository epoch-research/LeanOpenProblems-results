import Mathlib

def A237413_comp (n : ℕ) : ℕ :=
  let p_j (j : ℕ) : ℕ := Nat.nth Nat.Prime (j - 1)
  (Finset.Ico 1 n).sum fun k ↦
    let m := n - k
    let pk := p_j k
    let pm := p_j m
    let ppm := p_j pm
    if (pk ^ 2 - 2).Prime ∧ (pm ^ 2 - 2).Prime ∧ (ppm ^ 2 - 2).Prime then 1 else 0

noncomputable def x := A237413_comp 6
