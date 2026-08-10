import FormalConjectures.Util.ProblemImports

open List Nat Function Set

def trim_trailing_zeros (l : List ℕ) : List ℕ :=
  (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

lemma dropWhile_replicate_zero (k : ℕ) (L : List ℕ) :
  (replicate k 0 ++ L).dropWhile (fun x => x = 0) = L.dropWhile (fun x => x = 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [replicate_succ, ih]

lemma replicate_append_zero (k : ℕ) : replicate k 0 ++ [0] = 0 :: replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [replicate_succ, ih]

lemma trim_trailing_zeros_append_replicate_zero (M : List ℕ) (k : ℕ) :
  trim_trailing_zeros (M ++ replicate k 0) = trim_trailing_zeros M := by
  dsimp [trim_trailing_zeros]
  have h_rev_rep : reverse (replicate k 0) = replicate k 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [replicate_succ, reverse_cons, ih, replicate_append_zero]
  rw [reverse_append, h_rev_rep]
  rw [dropWhile_replicate_zero]
