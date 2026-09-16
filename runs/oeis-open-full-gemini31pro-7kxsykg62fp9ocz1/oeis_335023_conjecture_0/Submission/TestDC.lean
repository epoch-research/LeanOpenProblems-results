import Submission.DC

lemma dc_mod_step (a b : ℕ) (h1 : a + 1 ≠ b) (h2 : a + 1 < b) :
  dc_mod a b =
    let mid := (a + b) / 2
    let p1 := dc_mod a mid
    let p2 := dc_mod mid b
    ((p2.1 * p1.1) % P, (p2.1 * p1.2 + p2.2 * p1.1) % P) := by
  conv => lhs; rw [dc_mod.eq_def]
  dsimp
  split_ifs with h_eq h_lt
  · contradiction
  · rfl
