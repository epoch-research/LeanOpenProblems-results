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

lemma trim_trailing_zeros_append_replicate_zero (M : List ℕ) (k : ℕ) :
  trim_trailing_zeros (M ++ replicate k 0) = trim_trailing_zeros M := by
  dsimp [trim_trailing_zeros]
  rw [reverse_append, reverse_replicate_zero]
  -- We can just inline dropWhile_replicate_zero inline here:
  have h_drop : ∀ L, (replicate k 0 ++ L).dropWhile (fun x => x = 0) = L.dropWhile (fun x => x = 0) := by
    intro L
    induction k with
    | zero => simp
    | succ k ih => simp [replicate_succ, ih]
  rw [h_drop]

lemma dropWhile_append_of_not_all_zeros (A B : List ℕ) (h : ∃ x ∈ A, x ≠ 0) :
  (A ++ B).dropWhile (fun x => x = 0) = A.dropWhile (fun x => x = 0) ++ B := by
  induction A with
  | nil =>
    exfalso
    rcases h with ⟨x, hx, _⟩
    contradiction
  | cons y ys ih =>
    rcases h with ⟨x, hx, hx0⟩
    have h_or : y = 0 ∨ y ≠ 0 := by omega
    rcases h_or with rfl | hy
    · -- y = 0
      dsimp [dropWhile]
      have h_in : x ∈ ys := by
        simp at hx
        rcases hx with hx_y | hx_ys
        · contradiction
        · exact hx_ys
      have h_ys : ∃ x ∈ ys, x ≠ 0 := ⟨x, h_in, hx0⟩
      exact ih h_ys
    · -- y ≠ 0
      dsimp [dropWhile]
      simp [hy]

lemma reverse_not_all_zeros (L : List ℕ) (h : ∃ x ∈ L, x ≠ 0) : ∃ x ∈ reverse L, x ≠ 0 := by
  rcases h with ⟨x, hx, hx0⟩
  use x
  constructor
  · rw [mem_reverse]
    exact hx
  · exact hx0

lemma trim_trailing_zeros_cons_zero (L : List ℕ) (h : ∃ x ∈ L, x ≠ 0) :
  trim_trailing_zeros (0 :: L) = 0 :: trim_trailing_zeros L := by
  dsimp [trim_trailing_zeros]
  rw [reverse_cons]
  have h_not_zero : ∃ x ∈ reverse L, x ≠ 0 := reverse_not_all_zeros L h
  rw [dropWhile_append_of_not_all_zeros (reverse L) [0] h_not_zero]
  rw [reverse_append]
  rfl

lemma add_at_nil_not_all_zeros (i : ℕ) : ∃ x ∈ add_at [] i, x ≠ 0 := by
  induction i with
  | zero =>
    dsimp [add_at]
    use 1
    simp
  | succ j ih =>
    dsimp [add_at]
    rcases ih with ⟨x, hx, hx0⟩
    use x
    constructor
    · exact mem_cons_of_mem 0 hx
    · exact hx0

lemma add_at_not_all_zeros (L : List ℕ) (i : ℕ) : ∃ x ∈ add_at L i, x ≠ 0 := by
  induction L generalizing i with
  | nil =>
    exact add_at_nil_not_all_zeros i
  | cons x xs ih =>
    rcases i with _ | j
    · dsimp [add_at]
      use x + 1
      constructor
      · simp
      · omega
    · dsimp [add_at]
      rcases ih j with ⟨y, hy, hy0⟩
      use y
      constructor
      · exact mem_cons_of_mem x hy
      · exact hy0

lemma trim_trailing_zeros_add_at_replicate_zero (k i : ℕ) :
  trim_trailing_zeros (add_at (replicate k 0) i) = add_at [] i := by
  induction i generalizing k with
  | zero =>
    rcases k with _ | k
    · rfl
    · rw [replicate_succ]
      dsimp [add_at]
      have h : 1 :: replicate k 0 = [1] ++ replicate k 0 := rfl
      rw [h, trim_trailing_zeros_append_replicate_zero]
      rfl
  | succ j ih =>
    rcases k with _ | k
    · -- k = 0
      dsimp [add_at]
      have h_nz := add_at_nil_not_all_zeros j
      rw [trim_trailing_zeros_cons_zero (add_at [] j) h_nz]
      have ih_0 := ih 0
      dsimp [replicate] at ih_0
      rw [ih_0]
    · rw [replicate_succ]
      dsimp [add_at]
      have h_nz := add_at_not_all_zeros (replicate k 0) j
      rw [trim_trailing_zeros_cons_zero (add_at (replicate k 0) j) h_nz]
      rw [ih k]

lemma trim_trailing_zeros_replicate_zero (k : ℕ) : trim_trailing_zeros (replicate k 0) = [] := by
  dsimp [trim_trailing_zeros]
  rw [reverse_replicate_zero]
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [replicate_succ, ih]

lemma not_not_all_zeros_eq_replicate (L : List ℕ) (h : ¬ ∃ x ∈ L, x ≠ 0) : L = replicate L.length 0 := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    have hx : x = 0 := by
      by_contra h_nz
      apply h
      use x
      simp [h_nz]
    have hxs : ¬ ∃ y ∈ xs, y ≠ 0 := by
      intro h_ex
      apply h
      rcases h_ex with ⟨y, hy, hy0⟩
      use y
      simp [hy, hy0]
    rw [hx, ih hxs]
    simp [replicate_succ]

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

lemma trim_trailing_zeros_idem (L : List ℕ) : trim_trailing_zeros (trim_trailing_zeros L) = trim_trailing_zeros L := by
  rcases exists_trim_trailing_zeros_replicate L with ⟨k, hk⟩
  conv =>
    rhs
    rw [hk]
  rw [trim_trailing_zeros_append_replicate_zero]

lemma trim_trailing_zeros_cons (x : ℕ) (L : List ℕ) (h : ∃ y ∈ L, y ≠ 0) :
  trim_trailing_zeros (x :: L) = x :: trim_trailing_zeros L := by
  have hx : x = 0 ∨ x ≠ 0 := by omega
  rcases hx with rfl | hx0
  · exact trim_trailing_zeros_cons_zero L h
  · dsimp [trim_trailing_zeros]
    rw [reverse_cons]
    have h_not_zero : ∃ y ∈ reverse L, y ≠ 0 := reverse_not_all_zeros L h
    rw [dropWhile_append_of_not_all_zeros (reverse L) [x] h_not_zero]
    rw [reverse_append]
    rfl

lemma trim_trailing_zeros_add_at_append_replicate (A : List ℕ) (k i : ℕ) :
  trim_trailing_zeros (add_at (A ++ replicate k 0) i) = add_at (trim_trailing_zeros A) i := by
  induction A generalizing k i with
  | nil =>
    exact trim_trailing_zeros_add_at_replicate_zero k i
  | cons x xs ih =>
    rcases i with _ | j
    · -- i = 0
      dsimp [add_at]
      change trim_trailing_zeros (((x + 1) :: xs) ++ replicate k 0) = _
      rw [trim_trailing_zeros_append_replicate_zero]
      have h_ex : (∃ y ∈ xs, y ≠ 0) ∨ ¬ ∃ y ∈ xs, y ≠ 0 := Classical.em _
      rcases h_ex with h | h
      · -- Case 1: xs has a non-zero element
        have h_cons : ∃ y ∈ xs, y ≠ 0 := h
        rw [trim_trailing_zeros_cons (x+1) xs h_cons]
        rw [trim_trailing_zeros_cons x xs h_cons]
        rfl
      · -- Case 2: xs is all zeros
        have h_rep := not_not_all_zeros_eq_replicate xs h
        rw [h_rep]
        have h_x_or : x = 0 ∨ x ≠ 0 := by omega
        rcases h_x_or with rfl | hx0
        · -- x = 0
          have h_lhs : trim_trailing_zeros (1 :: replicate xs.length 0) = [1] := by
            have h_app : 1 :: replicate xs.length 0 = [1] ++ replicate xs.length 0 := rfl
            rw [h_app, trim_trailing_zeros_append_replicate_zero]
            dsimp [trim_trailing_zeros]
            rfl
          rw [h_lhs]
          have h_rhs : trim_trailing_zeros (0 :: replicate xs.length 0) = [] := by
            have h_app : 0 :: replicate xs.length 0 = replicate (xs.length + 1) 0 := rfl
            rw [h_app, trim_trailing_zeros_replicate_zero]
          rw [h_rhs]
          rfl
        · -- x ≠ 0
          have h_trim_x : trim_trailing_zeros [x] = [x] := by
            dsimp [trim_trailing_zeros]
            have h_drop : dropWhile (fun x => x = 0) [x] = [x] := by
              dsimp [dropWhile]
              simp [hx0]
            rw [h_drop]
            rfl
          have h_trim_x1 : trim_trailing_zeros [x + 1] = [x + 1] := by
            dsimp [trim_trailing_zeros]
            have h_drop : dropWhile (fun x => x = 0) [x + 1] = [x + 1] := by
              dsimp [dropWhile]
              simp
            rw [h_drop]
            rfl
          have h_lhs : trim_trailing_zeros ((x+1) :: replicate xs.length 0) = [x+1] := by
            have h_app : (x+1) :: replicate xs.length 0 = [x+1] ++ replicate xs.length 0 := rfl
            rw [h_app, trim_trailing_zeros_append_replicate_zero, h_trim_x1]
          rw [h_lhs]
          have h_rhs : trim_trailing_zeros (x :: replicate xs.length 0) = [x] := by
            have h_app : x :: replicate xs.length 0 = [x] ++ replicate xs.length 0 := rfl
            rw [h_app, trim_trailing_zeros_append_replicate_zero, h_trim_x]
          rw [h_rhs]
          rfl
    · -- i = j + 1
      dsimp [add_at]
      have h_nz : ∃ y ∈ add_at (xs ++ replicate k 0) j, y ≠ 0 := add_at_not_all_zeros _ _
      rw [trim_trailing_zeros_cons x (add_at (xs ++ replicate k 0) j) h_nz]
      rw [ih k j]
      have h_ex : (∃ y ∈ xs, y ≠ 0) ∨ ¬ ∃ y ∈ xs, y ≠ 0 := Classical.em _
      rcases h_ex with h | h
      · -- Case 1: xs has a non-zero element
        rw [trim_trailing_zeros_cons x xs h]
        rfl
      · -- Case 2: xs is all zeros
        have h_rep := not_not_all_zeros_eq_replicate xs h
        rw [h_rep]
        rw [trim_trailing_zeros_replicate_zero]
        have h_x_or : x = 0 ∨ x ≠ 0 := by omega
        rcases h_x_or with rfl | hx0
        · -- x = 0
          have h_rhs : trim_trailing_zeros (0 :: replicate xs.length 0) = [] := by
            have h_app : 0 :: replicate xs.length 0 = replicate (xs.length + 1) 0 := rfl
            rw [h_app, trim_trailing_zeros_replicate_zero]
          rw [h_rhs]
          rfl
        · -- x ≠ 0
          have h_trim_x : trim_trailing_zeros [x] = [x] := by
            dsimp [trim_trailing_zeros]
            have h_drop : dropWhile (fun x => x = 0) [x] = [x] := by
              dsimp [dropWhile]
              simp [hx0]
            rw [h_drop]
            rfl
          have h_rhs : trim_trailing_zeros (x :: replicate xs.length 0) = [x] := by
            have h_app : x :: replicate xs.length 0 = [x] ++ replicate xs.length 0 := rfl
            rw [h_app, trim_trailing_zeros_append_replicate_zero, h_trim_x]
          rw [h_rhs]
          rfl

lemma trim_trailing_zeros_add_at (L : List ℕ) (i : ℕ) :
  trim_trailing_zeros (add_at L i) = add_at (trim_trailing_zeros L) i := by
  rcases exists_trim_trailing_zeros_replicate L with ⟨k, hk⟩
  conv =>
    lhs
    congr
    rw [hk]
  rw [trim_trailing_zeros_add_at_append_replicate]
  rw [trim_trailing_zeros_idem]

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

lemma S_add_at (n t : ℕ) (hn : n ≠ 0) : ∃ i, S t (n+1) = add_at (S t n) i := by
  rcases S_long_add_at n t with ⟨i, hi_lt, hi_eq⟩
  use i
  rw [S_eq_trim_S_long t (n+1) (by omega)]
  rw [hi_eq]
  rw [trim_trailing_zeros_add_at]
  rw [← S_eq_trim_S_long t n hn]
