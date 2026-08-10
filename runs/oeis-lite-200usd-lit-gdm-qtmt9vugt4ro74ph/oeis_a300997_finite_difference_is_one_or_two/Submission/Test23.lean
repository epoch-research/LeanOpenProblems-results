import FormalConjectures.Util.ProblemImports

open List Nat Function Set

def half_ceil (m : ℕ) : ℕ := (m + 1) / 2
def half_floor (m : ℕ) : ℕ := m / 2

def add_at : List ℕ → ℕ → List ℕ
  | [], 0 => [1]
  | [], i + 1 => 0 :: add_at [] i
  | x :: xs, 0 => (x + 1) :: xs
  | x :: xs, i + 1 => x :: add_at xs i

def trim_trailing_zeros (l : List ℕ) : List ℕ :=
  (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

def ca_step_carry : List ℕ → ℕ → List ℕ
  | [], c => [c]
  | x :: xs, c => (half_ceil x + c) :: ca_step_carry xs (half_floor x)

def ca_step (config : List ℕ) : List ℕ :=
  trim_trailing_zeros (ca_step_carry config 0)

def S (t : ℕ) (n : ℕ) : List ℕ :=
  (List.range t).foldl (fun acc _ => ca_step acc) [n]

def S_long (t : ℕ) (n : ℕ) : List ℕ :=
  (List.range t).foldl (fun acc _ => ca_step_carry acc 0) [n]

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

lemma exists_replicate_dropWhile_eq (L : List ℕ) :
  ∃ k, replicate k 0 ++ L.dropWhile (fun x => x = 0) = L := by
  induction L with
  | nil =>
    use 0
    rfl
  | cons x xs ih =>
    have hx : x = 0 ∨ x ≠ 0 := by omega
    rcases hx with rfl | hx
    · -- x = 0
      dsimp [dropWhile]
      rcases ih with ⟨k, hk⟩
      use k + 1
      simp [replicate_succ, hk]
    · -- x ≠ 0
      have h_drop : (x :: xs).dropWhile (fun x => x = 0) = x :: xs := by
        dsimp [dropWhile]
        simp [hx]
      use 0
      simp [h_drop]

lemma exists_trim_trailing_zeros_replicate (L : List ℕ) :
  ∃ k, L = trim_trailing_zeros L ++ replicate k 0 := by
  rcases exists_replicate_dropWhile_eq (reverse L) with ⟨k, hk⟩
  use k
  have h_rev : reverse (reverse L) = L := reverse_reverse L
  have h_rev2 : reverse (replicate k 0 ++ (reverse L).dropWhile (fun x => x = 0)) = L := by
    rw [hk, h_rev]
  rw [reverse_append, reverse_replicate_zero] at h_rev2
  exact h_rev2.symm

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

lemma trim_trailing_zeros_append_replicate_zero (M : List ℕ) (k : ℕ) :
  trim_trailing_zeros (M ++ replicate k 0) = trim_trailing_zeros M := by
  dsimp [trim_trailing_zeros]
  rw [reverse_append, reverse_replicate_zero]
  rw [dropWhile_replicate_zero]

lemma ca_step_trim_trailing_zeros (L : List ℕ) :
  ca_step (trim_trailing_zeros L) = ca_step L := by
  rcases exists_trim_trailing_zeros_replicate L with ⟨k, hk⟩
  dsimp [ca_step]
  conv =>
    rhs
    rw [hk]
  rw [ca_step_carry_replicate_zero]
  rw [trim_trailing_zeros_append_replicate_zero]

lemma S_succ (t : ℕ) (n : ℕ) : S (t+1) n = ca_step (S t n) := by
  dsimp [S]
  rw [range_succ, foldl_append]
  rfl

lemma S_long_succ (t : ℕ) (n : ℕ) : S_long (t+1) n = ca_step_carry (S_long t n) 0 := by
  dsimp [S_long]
  rw [range_succ, foldl_append]
  rfl

lemma ca_step_carry_length (L : List ℕ) (c : ℕ) : (ca_step_carry L c).length = L.length + 1 := by
  induction L generalizing c with
  | nil => rfl
  | cons x xs ih =>
    simp [ca_step_carry, ih]

lemma S_long_length (t : ℕ) (n : ℕ) : (S_long t n).length = t + 1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [S_long_succ, ca_step_carry_length, ih]

lemma ca_step_carry_succ_carry (xs : List ℕ) (c : ℕ) :
  ca_step_carry xs (c + 1) = add_at (ca_step_carry xs c) 0 := by
  induction xs generalizing c with
  | nil =>
    simp [ca_step_carry, add_at]
  | cons x xs ih =>
    simp [ca_step_carry, add_at]
    omega

lemma ca_step_carry_add_at_of_lt (L : List ℕ) (i : ℕ) (c : ℕ) (h : i < L.length) :
  ca_step_carry (add_at L i) c = add_at (ca_step_carry L c) i ∨
  ca_step_carry (add_at L i) c = add_at (ca_step_carry L c) (i + 1) := by
  induction L generalizing i c with
  | nil =>
    contradiction
  | cons x xs ih =>
    rcases i with _ | j
    · -- i = 0
      dsimp [add_at, ca_step_carry]
      have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
      rcases hx with h_even | h_odd
      · left
        have h_ceil : half_ceil (x + 1) = half_ceil x + 1 := by
          unfold half_ceil
          omega
        have h_floor : half_floor (x + 1) = half_floor x := by
          unfold half_floor
          omega
        rw [h_ceil, h_floor]
        congr 1
        omega
      · right
        have h_ceil : half_ceil (x + 1) = half_ceil x := by
          unfold half_ceil
          omega
        have h_floor : half_floor (x + 1) = half_floor x + 1 := by
          unfold half_floor
          omega
        rw [h_ceil, h_floor]
        congr 1
        exact ca_step_carry_succ_carry xs (half_floor x)
    · -- i = j + 1
      have h_lt : j < xs.length := by
        simp at h
        omega
      rcases ih j (half_floor x) h_lt with h_ih | h_ih
      · left
        dsimp [add_at, ca_step_carry]
        rw [h_ih]
      · right
        dsimp [add_at, ca_step_carry]
        rw [h_ih]

lemma S_long_add_at (n t : ℕ) : ∃ i, i < t + 1 ∧ S_long t (n+1) = add_at (S_long t n) i := by
  induction t with
  | zero =>
    use 0
    simp [S_long, add_at]
  | succ t ih =>
    rcases ih with ⟨i, hi_lt, hi_eq⟩
    rw [S_long_succ, S_long_succ, hi_eq]
    have h_lt : i < (S_long t n).length := by
      rw [S_long_length]
      exact hi_lt
    rcases ca_step_carry_add_at_of_lt (S_long t n) i 0 h_lt with h_left | h_right
    · use i
      constructor
      · omega
      · exact h_left
    · use i + 1
      constructor
      · omega
      · exact h_right

lemma trim_trailing_zeros_singleton (n : ℕ) (hn : n ≠ 0) : trim_trailing_zeros [n] = [n] := by
  dsimp [trim_trailing_zeros]
  have h_drop : dropWhile (fun x => x = 0) [n] = [n] := by
    dsimp [dropWhile]
    simp [hn]
  rw [h_drop]
  rfl

lemma S_eq_trim_S_long (t : ℕ) (n : ℕ) (hn : n ≠ 0) : S t n = trim_trailing_zeros (S_long t n) := by
  induction t with
  | zero =>
    dsimp [S, S_long]
    rw [trim_trailing_zeros_singleton n hn]
  | succ t ih =>
    rw [S_succ, S_long_succ]
    have h_rhs : trim_trailing_zeros (ca_step_carry (S_long t n) 0) = ca_step (S_long t n) := rfl
    rw [h_rhs]
    rw [← ca_step_trim_trailing_zeros (S_long t n)]
    rw [← ih]
