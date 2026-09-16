import Submission.Cases

open Nat Finset

lemma B_step (c : ℕ) : B c < B (c + 1) := by
  dsimp [B]
  have h1 : 2 * (c + 1) + 1 = 2 * c + 2 + 1 := by omega
  rw [h1, choose_succ_succ' (2 * c + 2) c]
  have h2 : 2 * c + 2 = 2 * c + 1 + 1 := by omega
  rw [h2, choose_succ_succ' (2 * c + 1) c]
  have hpos : 0 < (2 * c + 1 + 1).choose c := by
    apply choose_pos
    omega
  set X := (2 * c + 1).choose c
  set Y := (2 * c + 1).choose (c + 1)
  set Z := (2 * c + 1 + 1).choose c
  omega

lemma B_ge_16 (c : ℕ) (hc : 16 ≤ c) : B c > 800322180 := by
  induction' c, hc using Nat.le_induction with k hk ih
  · decide
  · exact lt_trans ih (B_step k)
lemma a_800322180_eq_0 : a 800322180 = 0 := by
  sorry
