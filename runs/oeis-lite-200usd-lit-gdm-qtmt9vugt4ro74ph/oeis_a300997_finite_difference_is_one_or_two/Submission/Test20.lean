import FormalConjectures.Util.ProblemImports

open List Nat Function Set

def trim_trailing_zeros (l : List ℕ) : List ℕ :=
  (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

def half_ceil (m : ℕ) : ℕ := (m + 1) / 2
def half_floor (m : ℕ) : ℕ := m / 2

def ca_step_carry : List ℕ → ℕ → List ℕ
  | [], c => [c]
  | x :: xs, c => (half_ceil x + c) :: ca_step_carry xs (half_floor x)

def ca_step (config : List ℕ) : List ℕ :=
  trim_trailing_zeros (ca_step_carry config 0)

lemma ca_step_carry_zero (L : List ℕ) (c : ℕ) :
  ca_step_carry (L ++ [0]) c = ca_step_carry L c ++ [0] := by
  induction L generalizing c with
  | nil =>
    dsimp [ca_step_carry]
    unfold half_ceil half_floor
    simp
  | cons x xs ih =>
    simp [ca_step_carry, ih]

lemma ca_step_carry_replicate_zero (L : List ℕ) (k : ℕ) (c : ℕ) :
  ca_step_carry (L ++ replicate k 0) c = ca_step_carry L c ++ replicate k 0 := by
  induction k generalizing L c with
  | zero => simp
  | succ k ih =>
    have h_rep : replicate (k + 1) 0 = [0] ++ replicate k 0 := rfl
    rw [h_rep]
    rw [← append_assoc]
    rw [ih (L ++ [0]) c]
    rw [ca_step_carry_zero]
    rw [append_assoc]

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

lemma ca_step_replicate_zero (L : List ℕ) (k : ℕ) :
  ca_step (L ++ replicate k 0) = ca_step L := by
  dsimp [ca_step]
  rw [ca_step_carry_replicate_zero]
  rw [trim_trailing_zeros_append_replicate_zero]
