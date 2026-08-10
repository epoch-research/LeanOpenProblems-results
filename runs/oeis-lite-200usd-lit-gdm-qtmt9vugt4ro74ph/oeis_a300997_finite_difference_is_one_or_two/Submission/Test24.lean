import FormalConjectures.Util.ProblemImports

open List Nat Function Set

def trim_trailing_zeros (l : List ℕ) : List ℕ :=
  (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

def add_at : List ℕ → ℕ → List ℕ
  | [], 0 => [1]
  | [], i + 1 => 0 :: add_at [] i
  | x :: xs, 0 => (x + 1) :: xs
  | x :: xs, i + 1 => x :: add_at xs i

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

lemma reverse_replicate_zero (k : ℕ) : reverse (replicate k 0) = replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [replicate_succ, reverse_cons, ih, replicate_append_zero]

lemma trim_trailing_zeros_append_replicate_zero (M : List ℕ) (k : ℕ) :
  trim_trailing_zeros (M ++ replicate k 0) = trim_trailing_zeros M := by
  dsimp [trim_trailing_zeros]
  rw [reverse_append, reverse_replicate_zero]
  rw [dropWhile_replicate_zero]

lemma trim_trailing_zeros_add_at_replicate_zero (k i : ℕ) :
  trim_trailing_zeros (add_at (replicate k 0) i) = add_at [] i := by
  induction i generalizing k with
  | zero =>
    rcases k with _ | k
    · rfl
    · rw [replicate_succ]
      dsimp [add_at]
      -- Goal: trim_trailing_zeros (1 :: replicate k 0) = [1]
      -- which is trim_trailing_zeros ([1] ++ replicate k 0) = trim_trailing_zeros [1] = [1]
      have h : 1 :: replicate k 0 = [1] ++ replicate k 0 := rfl
      rw [h, trim_trailing_zeros_append_replicate_zero]
      rfl
  | succ j ih =>
    rcases k with _ | k
    · -- k = 0
      dsimp [add_at]
      -- Goal: trim_trailing_zeros (0 :: add_at [] j) = 0 :: add_at [] j
      -- Since add_at [] j has 1 at index j, it is of the form ... ++ [1] ++ replicate ... 0
      -- Actually, we can just prove a lemma about trim_trailing_zeros (0 :: L) when L is not all zeros
      sorry
    · rw [replicate_succ]
      dsimp [add_at]
      -- Goal: trim_trailing_zeros (0 :: add_at (replicate k 0) j) = 0 :: add_at [] j
      sorry
