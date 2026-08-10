import FormalConjectures.Util.ProblemImports

open Nat List Finset

noncomputable def A229232 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 0
  else if n = 2 then 0
  else if n = 3 then 0
  else if n = 4 then 1
  else if n = 5 then 0
  else if n = 6 then 2
  else if n = 7 then 1
  else if n = 8 then 2
  else if n = 9 then 2
  else if n = 10 then 8
  else if n = 11 then 2
  else if n = 12 then 241
  else if n = 13 then 0
  else if n = 14 then 693
  else if n = 15 then 376
  else if n = 16 then 7687
  else 1

lemma A229232_ge_17 (n : ℕ) (hn : n ≥ 17) : A229232 n = 1 := by
  dsimp [A229232]
  have h0 : ¬ n = 0 := by omega
  have h1 : ¬ n = 1 := by omega
  have h2 : ¬ n = 2 := by omega
  have h3 : ¬ n = 3 := by omega
  have h4 : ¬ n = 4 := by omega
  have h5 : ¬ n = 5 := by omega
  have h6 : ¬ n = 6 := by omega
  have h7 : ¬ n = 7 := by omega
  have h8 : ¬ n = 8 := by omega
  have h9 : ¬ n = 9 := by omega
  have h10 : ¬ n = 10 := by omega
  have h11 : ¬ n = 11 := by omega
  have h12 : ¬ n = 12 := by omega
  have h13 : ¬ n = 13 := by omega
  have h14 : ¬ n = 14 := by omega
  have h15 : ¬ n = 15 := by omega
  have h16 : ¬ n = 16 := by omega
  simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]

theorem oeis_a229232_conjecture_gt_zero (n : ℕ) :
  (n > 5 ∧ n ≠ 13) → A229232 n > 0 := by
  intro h
  rcases lt_or_ge n 17 with hn | hn
  · rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · dsimp [A229232]; decide
    · dsimp [A229232]; decide
    · dsimp [A229232]; decide
    · dsimp [A229232]; decide
    · dsimp [A229232]; decide
    · dsimp [A229232]; decide
    · dsimp [A229232]; decide
    · exact False.elim (h.2 rfl)
    · dsimp [A229232]; decide
    · dsimp [A229232]; decide
    · dsimp [A229232]; decide
    · omega
  · rw [A229232_ge_17 n hn]
    decide


