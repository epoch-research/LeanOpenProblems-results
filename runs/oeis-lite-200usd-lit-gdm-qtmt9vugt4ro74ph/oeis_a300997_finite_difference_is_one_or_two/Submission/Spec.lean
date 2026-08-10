import FormalConjectures.Util.ProblemImports

set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false

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

lemma add_at_replicate_one_self (m : ℕ) :
  add_at (replicate m 1) m = replicate (m + 1) 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [replicate_succ, add_at, ih]

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

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then
    0
  else
    let initial_config : List ℕ := [n]
    let target_config : List ℕ := List.replicate n 1

    -- State after t steps, computed by folding ca_step t times using foldl over a range.
    let S_local (t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => ca_step acc) initial_config

    -- The set of time steps k at which the configuration is stable.
    let stable_steps : Set ℕ := {k | S_local k = target_config}

    -- a(n) is the smallest k in this set, defined by the set infimum (sInf).
    sInf stable_steps

/--
Conjecture A300997: The finite difference of this sequence only contains 1's and 2's.
Specifically, $\forall n \ge 1, a(n+1) = a n + 1 ∨ a(n+1) = a n + 2$.
-/
lemma a_one : a 1 = 0 := by
  dsimp [a]
  have h0 : (0 : ℕ) ∈ {k | S k 1 = replicate 1 1} := by
    rfl
  have h_le : sInf {k | S k 1 = replicate 1 1} ≤ 0 := by
    apply Nat.sInf_le h0
  exact le_zero_iff.mp h_le

lemma S_zero_two : S 0 2 = [2] := rfl

lemma S_one_two : S 1 2 = [1, 1] := by
  dsimp [S, ca_step, ca_step_carry]
  unfold half_ceil half_floor trim_trailing_zeros
  rfl

lemma a_two : a 2 = 1 := by
  dsimp [a]
  set S_set := {k | S k 2 = replicate 2 1}
  have h1 : (1 : ℕ) ∈ S_set := by
    simp [S_set, S_one_two]
  have h_le : sInf S_set ≤ 1 := by
    apply Nat.sInf_le h1
  have h_nonempty : S_set.Nonempty := ⟨1, h1⟩
  have h_mem := Nat.sInf_mem h_nonempty
  have h0 : (0 : ℕ) ∉ S_set := by
    intro h
    simp [S_set, S_zero_two] at h
  have h_ne : sInf S_set ≠ 0 := by
    intro h
    rw [h] at h_mem
    exact h0 h_mem
  have : sInf S_set = 1 := by omega
  exact this

lemma a_eq_sInf (n : ℕ) (hn : n ≠ 0) : a n = sInf {k | S k n = replicate n 1} := by
  dsimp [a]
  split_ifs
  · contradiction
  · rfl

lemma a_three : a 3 = 3 := by
  dsimp [a]
  set S_set := {k | S k 3 = replicate 3 1}
  have h3 : (3 : ℕ) ∈ S_set := by
    decide
  have h_le : sInf S_set ≤ 3 := by
    apply Nat.sInf_le h3
  have h_nonempty : S_set.Nonempty := ⟨3, h3⟩
  have h_mem := Nat.sInf_mem h_nonempty
  have h0 : (0 : ℕ) ∉ S_set := by decide
  have h1 : (1 : ℕ) ∉ S_set := by decide
  have h2 : (2 : ℕ) ∉ S_set := by decide
  have h_ne0 : sInf S_set ≠ 0 := by
    intro h
    rw [h] at h_mem
    exact h0 h_mem
  have h_ne1 : sInf S_set ≠ 1 := by
    intro h
    rw [h] at h_mem
    exact h1 h_mem
  have h_ne2 : sInf S_set ≠ 2 := by
    intro h
    rw [h] at h_mem
    exact h2 h_mem
  have : sInf S_set = 3 := by omega
  exact this


lemma ca_step_carry_replicate_one_zero (n : ℕ) :
  ca_step_carry (replicate n 1) 0 = replicate n 1 ++ [0] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [replicate_succ, ca_step_carry, half_ceil, half_floor, ih]

lemma ca_step_carry_replicate_one_one (n : ℕ) :
  ca_step_carry (replicate (n + 1) 1) 1 = add_at (replicate (n + 1) 1) 0 ++ [0] := by
  simp [replicate_succ, ca_step_carry, half_ceil, half_floor, add_at, ca_step_carry_replicate_one_zero]

lemma ca_step_carry_add_at_replicate_one_self (n : ℕ) (hn : n ≥ 1) :
  ca_step_carry (add_at (replicate n 1) (n - 1)) 0 = add_at (replicate n 1) n := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    rcases n with _ | n
    · rfl
    · have hn_ge : n + 1 ≥ 1 := by omega
      have ih_val := ih hn_ge
      simp [replicate_succ, add_at, ca_step_carry, half_ceil, half_floor]
      exact ih_val

lemma ca_step_carry_add_at_replicate_one_lt (n' i : ℕ) (hi : i < n' + 1) :
  ca_step_carry (add_at (replicate (n' + 2) 1) i) 0 = add_at (replicate (n' + 2) 1) (i + 1) ++ [0] := by
  induction n' generalizing i with
  | zero =>
    rcases i with _ | i
    · rfl
    · omega
  | succ n' ih =>
    rcases i with _ | j
    · -- i = 0
      simp [replicate_succ, add_at, ca_step_carry, half_ceil, half_floor]
      exact ca_step_carry_replicate_one_zero n'
    · -- i = j + 1
      have hj : j < n' + 1 := by omega
      simp [replicate_succ, add_at, ca_step_carry, half_ceil, half_floor]
      exact ih j hj

lemma trim_trailing_zeros_replicate_one (n : ℕ) :
  trim_trailing_zeros (replicate n 1) = replicate n 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases n with _ | n
    · rfl
    · rw [replicate_succ]
      rw [trim_trailing_zeros_cons 1 (replicate (n + 1) 1)]
      · rw [ih]
      · use 1
        simp

lemma ca_step_add_at_replicate_one (n i : ℕ) (hi : i < n) :
  ca_step (add_at (replicate n 1) i) = add_at (replicate n 1) (i + 1) := by
  have h_cases : i = n - 1 ∨ i < n - 1 := by omega
  rcases h_cases with rfl | hi_lt
  · have hn : n ≥ 1 := by omega
    have h_n_sub_add : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [h_n_sub_add]
    dsimp [ca_step]
    rw [ca_step_carry_add_at_replicate_one_self n hn]
    rw [add_at_replicate_one_self]
    rw [trim_trailing_zeros_replicate_one]
  · rcases n with _ | n
    · omega
    · rcases n with _ | n'
      · omega
      · dsimp [ca_step]
        rw [ca_step_carry_add_at_replicate_one_lt n' i (by omega)]
        have h_append : add_at (replicate (n' + 2) 1) (i + 1) ++ [0] = add_at (replicate (n' + 2) 1) (i + 1) ++ replicate 1 0 := rfl
        rw [h_append, trim_trailing_zeros_append_replicate_zero]
        rw [trim_trailing_zeros_add_at, trim_trailing_zeros_replicate_one]


lemma ca_step_carry_sum (L : List ℕ) (c : ℕ) :
  (ca_step_carry L c).sum = L.sum + c := by
  induction L generalizing c with
  | nil => simp [ca_step_carry]
  | cons x xs ih =>
    simp [ca_step_carry, ih]
    unfold half_ceil half_floor
    omega


lemma S_long_sum (t : ℕ) (n : ℕ) : (S_long t n).sum = n := by
  induction t with
  | zero => simp [S_long]
  | succ t ih =>
    simp [S_long_succ, ca_step_carry_sum, ih]

lemma dropWhile_zero_sum (L : List ℕ) :
  (L.dropWhile (fun x => x = 0)).sum = L.sum := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    have hx : x = 0 ∨ x ≠ 0 := by omega
    rcases hx with rfl | hx0
    · simp [ih]
    · simp [hx0]


lemma trim_trailing_zeros_sum (L : List ℕ) : (trim_trailing_zeros L).sum = L.sum := by
  dsimp [trim_trailing_zeros]
  rw [List.sum_reverse, dropWhile_zero_sum, List.sum_reverse]


lemma S_sum (t : ℕ) (n : ℕ) (hn : n ≠ 0) : (S t n).sum = n := by
  rw [S_eq_trim_S_long t n hn, trim_trailing_zeros_sum, S_long_sum]


lemma sum_replicate_one (n : ℕ) : (replicate n 1).sum = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [replicate_succ, ih]
    omega


lemma add_at_sum (L : List ℕ) (i : ℕ) : (add_at L i).sum = L.sum + 1 := by
  induction L generalizing i with
  | nil =>
    induction i with
    | zero => rfl
    | succ j ih =>
      simp [add_at, ih]
  | cons x xs ih =>
    rcases i with _ | i
    · simp [add_at]
      omega
    · simp [add_at, ih]
      omega


lemma ca_step_carry_pos (L : List ℕ) (hL : ∀ x ∈ L, x ≥ 1) (c : ℕ) :
  ∀ x ∈ (ca_step_carry L c).dropLast, x ≥ 1 := by
  induction L generalizing c with
  | nil =>
    simp [ca_step_carry, List.dropLast]
  | cons y ys ih =>
    intro x hx
    rcases ys with _ | ⟨z, zs⟩
    · -- ys = []
      simp [ca_step_carry] at hx
      rcases hx with rfl
      unfold half_ceil
      have hy : y ≥ 1 := hL y (by simp)
      omega
    · -- ys = z :: zs
      simp [ca_step_carry] at hx
      rcases hx with rfl | hx
      · unfold half_ceil
        have hy : y ≥ 1 := hL y (by simp)
        omega
      · apply ih
        · intro w hw
          apply hL w
          simp [hw]
        · exact hx


lemma mem_dropWhile {α : Type _} {p : α → Bool} {L : List α} {x : α} (h : x ∈ L.dropWhile p) : x ∈ L := by
  induction L with
  | nil =>
    simp [dropWhile] at h
  | cons y ys ih =>
    by_cases hp : p y = true
    · simp [hp, dropWhile] at h
      exact mem_cons_of_mem y (ih h)
    · have hp_false : p y = false := by
        cases h_py : p y
        · rfl
        · contradiction
      rw [dropWhile, hp_false] at h
      exact h

lemma mem_trim_trailing_zeros (L : List ℕ) (x : ℕ) (hx : x ∈ trim_trailing_zeros L) : x ∈ L := by
  dsimp [trim_trailing_zeros] at hx
  have h_rev_mem : x ∈ reverse ((reverse L).dropWhile (fun x => x = 0)) := hx
  rw [mem_reverse] at h_rev_mem
  have h_drop_mem : x ∈ (reverse L).dropWhile (fun x => x = 0) := h_rev_mem
  have h_mem : x ∈ reverse L := mem_dropWhile h_drop_mem
  rw [mem_reverse] at h_mem
  exact h_mem


lemma trim_trailing_zeros_pos_of_dropLast_pos (M : List ℕ) (hM : ∀ x ∈ M.dropLast, x ≥ 1) :
  ∀ x ∈ trim_trailing_zeros M, x ≥ 1 := by
  induction M with
  | nil => simp [trim_trailing_zeros]
  | cons y ys ih =>
    intro x hx
    rcases ys with _ | ⟨z, zs⟩
    · -- M = [y]
      simp [trim_trailing_zeros] at hx
      by_cases hy : y = 0
      · subst hy
        simp [trim_trailing_zeros] at hx
      · simp [trim_trailing_zeros, hy] at hx
        subst hx
        omega
    · rcases zs with _ | ⟨w, ws⟩
      · -- M = [y, z]
        -- M.dropLast = [y]
        have hy_pos : y ≥ 1 := hM y (by simp [List.dropLast])
        by_cases hz : z = 0
        · subst hz
          have h_eq : x = y := by
            have hy_nz : y ≠ 0 := by omega
            simp [trim_trailing_zeros, hy_nz] at hx
            exact hx
          rw [h_eq]
          exact hy_pos
        · have h_nz_zs : ∃ u ∈ [z], u ≠ 0 := ⟨z, by simp, hz⟩
          rw [trim_trailing_zeros_cons y [z] h_nz_zs] at hx
          simp only [mem_cons] at hx
          rcases hx with rfl | hx
          · exact hy_pos
          · simp [trim_trailing_zeros, hz] at hx
            subst hx
            omega
      · -- M = y :: z :: w :: ws
        -- here, we have at least 3 elements, so z is in (z :: w :: ws).dropLast.
        -- Therefore z >= 1.
        have hy_pos : y ≥ 1 := hM y (by simp [List.dropLast])
        have hz_pos : z ≥ 1 := hM z (by simp [List.dropLast])
        have h_nz_ys : ∃ u ∈ z :: w :: ws, u ≠ 0 := ⟨z, by simp, by omega⟩
        rw [trim_trailing_zeros_cons y (z :: w :: ws) h_nz_ys] at hx
        simp only [mem_cons] at hx
        rcases hx with rfl | hx
        · exact hy_pos
        · apply ih (by
            intro u hu
            apply hM u
            simp [List.dropLast] at hu
            simp [List.dropLast, hu])
          exact hx


lemma ca_step_pos (L : List ℕ) (hL : ∀ x ∈ L, x ≥ 1) :
  ∀ x ∈ ca_step L, x ≥ 1 := by
  dsimp [ca_step]
  apply trim_trailing_zeros_pos_of_dropLast_pos
  exact ca_step_carry_pos L hL 0


lemma S_pos (t : ℕ) (n : ℕ) (hn : n ≠ 0) : ∀ x ∈ S t n, x ≥ 1 := by
  induction t with
  | zero =>
    dsimp [S]
    intro x hx
    simp at hx
    subst hx
    omega
  | succ t ih =>
    rw [S_succ]
    exact ca_step_pos (S t n) ih


lemma length_le_sum_of_pos (L : List ℕ) (hL : ∀ x ∈ L, x ≥ 1) : L.length ≤ L.sum := by
  induction L with
  | nil => rfl
  | cons y ys ih =>
    simp
    have hy : y ≥ 1 := hL y (by simp)
    have h_ys : ∀ x ∈ ys, x ≥ 1 := by
      intro x hx
      apply hL x
      simp [hx]
    have ih_ys := ih h_ys
    omega

lemma S_length_le (t : ℕ) (n : ℕ) (hn : n ≠ 0) : (S t n).length ≤ n := by
  have h_pos := S_pos t n hn
  have h_le := length_le_sum_of_pos (S t n) h_pos
  rw [S_sum t n hn] at h_le
  exact h_le

lemma add_at_length (L : List ℕ) (i : ℕ) : (add_at L i).length = max L.length (i + 1) := by
  induction L generalizing i with
  | nil =>
    induction i with
    | zero => rfl
    | succ j ih =>
      simp [add_at, ih]
  | cons x xs ih =>
    rcases i with _ | i
    · simp [add_at]
    · simp [add_at, ih]

lemma S_add_at_index_le (n t : ℕ) (hn : n ≠ 0) :
  ∃ i, i ≤ n ∧ S t (n + 1) = add_at (S t n) i := by
  rcases S_add_at n t hn with ⟨i, hi_eq⟩
  use i
  constructor
  · have h_len := S_length_le t (n+1) (by omega)
    rw [hi_eq] at h_len
    rw [add_at_length] at h_len
    omega
  · exact hi_eq

lemma ca_step_replicate_one (m : ℕ) :
  ca_step (replicate m 1) = replicate m 1 := by
  dsimp [ca_step]
  rw [ca_step_carry_replicate_one_zero]
  have h_append : replicate m 1 ++ [0] = replicate m 1 ++ replicate 1 0 := rfl
  rw [h_append, trim_trailing_zeros_append_replicate_zero]
  rw [trim_trailing_zeros_replicate_one]


lemma add_at_eq_replicate_one (L : List ℕ) (i n : ℕ) (h_len : L.length ≤ n)
  (h : add_at L i = replicate (n + 1) 1) : L = replicate n 1 := by
  induction L generalizing i n with
  | nil =>
    have h_sum := add_at_sum [] i
    rw [h, sum_replicate_one] at h_sum
    simp at h_sum
    subst h_sum
    rfl
  | cons y ys ih =>
    rcases n with _ | n
    · simp at h_len
    · rcases i with _ | i
      · dsimp [add_at] at h
        rw [replicate_succ] at h
        simp at h
        rcases h with ⟨hy, hys⟩
        have : y = 0 := by omega
        subst this
        rw [hys] at h_len
        simp at h_len
      · dsimp [add_at] at h
        rw [replicate_succ] at h
        simp at h
        rcases h with ⟨rfl, h_add⟩
        have h_len2 : ys.length ≤ n := by
          simp at h_len
          omega
        rw [ih i n h_len2 h_add]
        rfl


lemma stable_steps_subset (n : ℕ) (hn : n ≠ 0) :
  {k | S k (n + 1) = replicate (n + 1) 1} ⊆ {k | S k n = replicate n 1} := by
  intro k hk
  simp at hk
  simp
  rcases S_add_at_index_le n k hn with ⟨i, hi_le, hi_eq⟩
  have h_len := S_length_le k n hn
  rw [hi_eq] at hk
  exact add_at_eq_replicate_one (S k n) i n h_len hk


lemma foldl_ca_step_add_at (n i k : ℕ) (hi : i + k ≤ n) :
  (range k).foldl (fun acc _ => ca_step acc) (add_at (replicate n 1) i) = add_at (replicate n 1) (i + k) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    rw [range_succ, foldl_append]
    simp
    have h1 : i + k < n := by omega
    have ih1 : (range k).foldl (fun acc _ => ca_step acc) (add_at (replicate n 1) i) = add_at (replicate n 1) (i + k) := by
      apply ih
      omega
    rw [ih1]
    exact ca_step_add_at_replicate_one n (i + k) h1



lemma foldl_ca_step_map {α β : Type _} (f : α → β) (L : List α) (acc : List ℕ) :
  (L.map f).foldl (fun acc _ => ca_step acc) acc = L.foldl (fun acc _ => ca_step acc) acc := by
  induction L generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp [ih]


lemma S_set_nonempty (n : ℕ) (hn : n ≠ 0) :
  {k | S k n = replicate n 1}.Nonempty := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    rcases n with _ | n
    · use 0
      simp [S]
    · have hn : n + 1 ≠ 0 := by omega
      rcases ih hn with ⟨t, ht⟩
      have hn1 : n + 1 ≠ 0 := by omega
      rcases S_add_at_index_le (n+1) t hn1 with ⟨i, hi_le, hi_eq⟩
      rw [ht] at hi_eq
      have h_cases : i = n + 1 ∨ i < n + 1 := by omega
      rcases h_cases with rfl | hi_lt
      · use t
        change S t (n + 2) = replicate (n + 2) 1
        rw [hi_eq, add_at_replicate_one_self]
      · set k := n + 1 - i
        use t + k
        change S (t + k) (n + 2) = replicate (n + 2) 1
        have h_step : S (t + k) (n + 2) = (List.range k).foldl (fun acc _ => ca_step acc) (S t (n + 2)) := by
          dsimp [S]
          rw [List.range_add, foldl_append]
          exact foldl_ca_step_map (fun x => t + x) (List.range k) (S t (n + 2))
        rw [h_step, hi_eq]
        have h_sum : i + k ≤ n + 1 := by omega
        rw [foldl_ca_step_add_at (n+1) i k h_sum]
        have hk_eq : i + k = n + 1 := by omega
        rw [hk_eq]
        exact add_at_replicate_one_self (n + 1)


lemma a_le_succ (n : ℕ) (hn : n ≠ 0) :
  a (n + 1) ≤ a n + n := by
  have h_nonempty : {k | S k n = replicate n 1}.Nonempty := S_set_nonempty n hn
  have ht_mem : a n ∈ {k | S k n = replicate n 1} := by
    rw [a_eq_sInf n hn]
    exact Nat.sInf_mem h_nonempty
  simp at ht_mem
  rcases S_add_at_index_le n (a n) hn with ⟨i, hi_le, hi_eq⟩
  rw [ht_mem] at hi_eq
  have h_cases : n = i ∨ i < n := by omega
  rcases h_cases with rfl | hi_lt
  · -- i = n
    have h_a_np1 : a (n + 1) ≤ a n := by
      rw [a_eq_sInf (n + 1) (by omega)]
      apply Nat.sInf_le
      change S (a n) (n + 1) = replicate (n + 1) 1
      rw [hi_eq, add_at_replicate_one_self]
    omega
  · -- i < n
    set k := n - i
    have h_a_np1 : a (n + 1) ≤ a n + k := by
      rw [a_eq_sInf (n + 1) (by omega)]
      apply Nat.sInf_le
      change S (a n + k) (n + 1) = replicate (n + 1) 1
      have h_step : S (a n + k) (n + 1) = (List.range k).foldl (fun acc _ => ca_step acc) (S (a n) (n + 1)) := by
        dsimp [S]
        rw [List.range_add, foldl_append]
        exact foldl_ca_step_map (fun x => a n + x) (List.range k) (S (a n) (n + 1))
      rw [h_step, hi_eq]
      have h_sum : i + k ≤ n := by omega
      rw [foldl_ca_step_add_at n i k h_sum]
      have hk_eq : i + k = n := by omega
      rw [hk_eq]
      exact add_at_replicate_one_self n
    have hk_le : k ≤ n := by omega
    omega


def get_at (L : List ℕ) (n : ℕ) : ℕ :=
  match L, n with
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => get_at xs n

lemma get_at_add_at_index_zero (L : List ℕ) (n : ℕ) (h_len : L.length ≤ n) :
  get_at (add_at L (n + 1)) n = 0 := by
  induction L generalizing n with
  | nil =>
    induction n with
    | zero => rfl
    | succ j ih =>
      dsimp [add_at, get_at]
      exact ih (Nat.zero_le j)
  | cons x xs ih =>
    rcases n with _ | n
    · simp at h_len
    · dsimp [add_at, get_at]
      apply ih
      simp at h_len
      omega

lemma get_at_pos_of_pos (L : List ℕ) (hL : ∀ x ∈ L, x ≥ 1) (n : ℕ) (hn : n < L.length) :
  get_at L n ≥ 1 := by
  induction L generalizing n with
  | nil =>
    simp at hn
  | cons x xs ih =>
    rcases n with _ | n
    · dsimp [get_at]
      apply hL
      simp
    · dsimp [get_at]
      apply ih
      · intro y hy
        apply hL
        simp [hy]
      · simp at hn
        omega

lemma m_le_n_of_S (n t' m : ℕ) (hn : n ≠ 0)
  (h_len : (S (t' - 1) (n + 1)).length ≤ n)
  (h_S : S (t' - 1) (n + 2) = add_at (S (t' - 1) (n + 1)) m)
  (hm_le : m ≤ n + 1) :
  m ≤ n := by
  by_contra h_gt
  have h_eq : m = n + 1 := by omega
  subst h_eq
  have h_zero := get_at_add_at_index_zero (S (t' - 1) (n + 1)) n h_len
  rw [← h_S] at h_zero
  have h_pos := S_pos (t' - 1) (n + 2) (by omega)
  have h_len3 : n < (S (t' - 1) (n + 2)).length := by
    rw [h_S, add_at_length]
    have : n + 2 ≤ max (S (t' - 1) (n + 1)).length (n + 2) := by omega
    omega
  have h_val := get_at_pos_of_pos (S (t' - 1) (n + 2)) h_pos n h_len3
  rw [h_zero] at h_val
  omega

lemma add_at_replicate_one_ne (n j : ℕ) (hj : j < n) :
  add_at (replicate n 1) j ≠ replicate (n + 1) 1 := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    rcases j with _ | j
    · simp [replicate_succ, add_at]
    · simp [replicate_succ, add_at]
      intro h
      apply ih j (by omega) h

lemma eq_of_ca_step_add_at_replicate_one (m j : ℕ) (hj : j < m)
  (h : ca_step (add_at (replicate m 1) j) = replicate (m + 1) 1) : j = m - 1 := by
  by_contra h_ne
  have : j + 1 < m := by omega
  have h_ne2 := add_at_replicate_one_ne m (j + 1) this
  rw [ca_step_add_at_replicate_one m j hj] at h
  exact h_ne2 h



lemma S_ne_replicate_one_of_lt (n t : ℕ) (hn : n ≠ 0)
  (ht_mem : t = a n)
  (h_nonempty : {k | S k n = replicate n 1}.Nonempty)
  (i : ℕ) (hi_lt : i + 2 < n) (hi_eq : S t (n + 1) = add_at (replicate n 1) i)
  (k : ℕ) (hk : k ≤ t + 2) :
  S k (n + 1) ≠ replicate (n + 1) 1 := by
  have ht_mem_sInf : S t n = replicate n 1 := by
    have h_mem : t ∈ {k | S k n = replicate n 1} := by
      rw [ht_mem]
      rw [a_eq_sInf n hn]
      exact Nat.sInf_mem h_nonempty
    exact h_mem
  have h_mono : ∀ s ≤ 2, S (t + s) (n + 1) = add_at (replicate n 1) (i + s) := by
    intro s hs
    induction s with
    | zero =>
      simp
      exact hi_eq
    | succ s ih_s =>
      have hs_lt : s < 2 := by omega
      have ih_s_val := ih_s (by omega)
      have h_assoc : t + (s + 1) = (t + s) + 1 := by omega
      rw [h_assoc]
      rw [S_succ, ih_s_val]
      rw [ca_step_add_at_replicate_one n (i + s) (by omega)]
      congr 1
  by_contra h_eq
  have h_cases : k < t ∨ (t ≤ k ∧ k ≤ t + 2) := by omega
  rcases h_cases with hk_lt | ⟨ht_le, hk_le2⟩
  · have h_sub := stable_steps_subset n hn
    have h_k_stable : k ∈ {x | S x (n + 1) = replicate (n + 1) 1} := h_eq
    have h_k_n : k ∈ {x | S x n = replicate n 1} := h_sub h_k_stable
    simp at h_k_n
    have h_ge : k ≥ t := by
      rw [ht_mem]
      rw [a_eq_sInf n hn]
      apply Nat.sInf_le
      exact h_k_n
    omega
  · set s := k - t
    have hs_le : s ≤ 2 := by omega
    have h_ks : k = t + s := by omega
    have h_add := h_mono s hs_le
    rw [← h_ks] at h_add
    rw [h_add] at h_eq
    have h_ne := add_at_replicate_one_ne n (i + s) (by omega)
    exact h_ne h_eq


lemma index_ge_of_a_le (n t : ℕ) (hn : n ≠ 0)
  (ht_mem : t = a n)
  (h_nonempty : {k | S k n = replicate n 1}.Nonempty)
  (h_nonempty2 : {k | S k (n + 1) = replicate (n + 1) 1}.Nonempty)
  (h_le : a (n + 1) ≤ t + 2)
  (i : ℕ) (hi_eq : S t (n + 1) = add_at (replicate n 1) i) :
  i + 2 ≥ n := by
  by_contra h_lt
  simp at h_lt
  have h_ne : S (a (n + 1)) (n + 1) ≠ replicate (n + 1) 1 :=
    S_ne_replicate_one_of_lt n t hn ht_mem h_nonempty i h_lt hi_eq (a (n + 1)) h_le
  have h_mem : a (n + 1) ∈ {k | S k (n + 1) = replicate (n + 1) 1} := by
    rw [a_eq_sInf (n + 1) (by omega)]
    exact Nat.sInf_mem h_nonempty2
  simp at h_mem
  exact h_ne h_mem

lemma a_mono (n : ℕ) (hn : n ≠ 0) (h_nonempty : {k | S k (n + 1) = replicate (n + 1) 1}.Nonempty) :
  a n ≤ a (n + 1) := by
  rw [a_eq_sInf n hn, a_eq_sInf (n + 1) (by omega)]
  have h_subset := stable_steps_subset n hn
  have h_mem : sInf {k | S k (n + 1) = replicate (n + 1) 1} ∈ {k | S k (n + 1) = replicate (n + 1) 1} :=
    Nat.sInf_mem h_nonempty
  have h_mem_n : sInf {k | S k (n + 1) = replicate (n + 1) 1} ∈ {k | S k n = replicate n 1} :=
    h_subset h_mem
  exact Nat.sInf_le h_mem_n


lemma stable_steps_upward_closed (n x y : ℕ) (h_stable : S x n = replicate n 1) (h_le : x ≤ y) :
  S y n = replicate n 1 := by
  have : y = x + (y - x) := by omega
  rw [this]
  induction (y - x) with
  | zero => exact h_stable
  | succ d ih =>
    have h_assoc : x + (d + 1) = (x + d) + 1 := by omega
    rw [h_assoc]
    rw [S_succ, ih]
    exact ca_step_replicate_one n


lemma S_ne_replicate_one_of_lt_general (n t : ℕ) (hn : n ≠ 0)
  (h_stable : S t n = replicate n 1)
  (i : ℕ) (hi_lt : i + 2 < n) (hi_eq : S t (n + 1) = add_at (replicate n 1) i)
  (k : ℕ) (hk : k ≤ t + 2) :
  S k (n + 1) ≠ replicate (n + 1) 1 := by
  have h_mono : ∀ s ≤ 2, S (t + s) (n + 1) = add_at (replicate n 1) (i + s) := by
    intro s hs
    induction s with
    | zero =>
      simp
      exact hi_eq
    | succ s ih_s =>
      have hs_lt : s < 2 := by omega
      have hs_le : s ≤ 2 := by omega
      have h_ih := ih_s hs_le
      have h_assoc_s : t + (s + 1) = (t + s) + 1 := by omega
      have h_step : S (t + (s + 1)) (n + 1) = ca_step (S (t + s) (n + 1)) := by
        rw [h_assoc_s, S_succ]
      rw [h_step, h_ih]
      have h_eq1 : ca_step (add_at (replicate n 1) (i + s)) = add_at (replicate n 1) (i + s + 1) :=
        ca_step_add_at_replicate_one n (i + s) (by omega)
      have h_eq2 : i + s + 1 = i + (s + 1) := by omega
      rw [h_eq2] at h_eq1
      exact h_eq1
  have h_not_stable_s : ∀ s ≤ 2, S (t + s) (n + 1) ≠ replicate (n + 1) 1 := by
    intro s hs h_st
    have h_eq := h_mono s hs
    rw [h_st] at h_eq
    have h_len_eq : (add_at (replicate n 1) (i + s)).length = (replicate (n + 1) 1).length := by
      rw [h_eq]
    rw [add_at_length] at h_len_eq
    simp only [List.length_replicate] at h_len_eq
    rw [Nat.max_eq_left (by omega)] at h_len_eq
    omega
  have h_k_cases : k ≤ t ∨ (k > t ∧ k ≤ t + 2) := by omega
  rcases h_k_cases with hk_le | ⟨hk_gt, hk_le2⟩
  · intro h_st
    have h_st_t : S t (n + 1) = replicate (n + 1) 1 :=
      stable_steps_upward_closed (n + 1) k t h_st hk_le
    rw [hi_eq] at h_st_t
    have h_len_eq : (add_at (replicate n 1) i).length = (replicate (n + 1) 1).length := by
      rw [h_st_t]
    rw [add_at_length] at h_len_eq
    simp only [List.length_replicate] at h_len_eq
    rw [Nat.max_eq_left (by omega)] at h_len_eq
    omega
  · set s := k - t
    have hs_le : s ≤ 2 := by omega
    have h_eq : t + s = k := by omega
    intro h_st
    have h_st_eq : S (t + s) (n + 1) = replicate (n + 1) 1 := by
      rw [h_eq, h_st]
    exact h_not_stable_s s hs_le h_st_eq

lemma index_ge_of_a_le_general (n t : ℕ) (hn : n ≠ 0)
  (h_stable : S t n = replicate n 1)
  (h_nonempty2 : {k | S k (n + 1) = replicate (n + 1) 1}.Nonempty)
  (h_le : a (n + 1) ≤ t + 2)
  (i : ℕ) (hi_eq : S t (n + 1) = add_at (replicate n 1) i) :
  i + 2 ≥ n := by
  by_contra h_lt
  simp at h_lt
  have h_ne : S (a (n + 1)) (n + 1) ≠ replicate (n + 1) 1 :=
    S_ne_replicate_one_of_lt_general n t hn h_stable i h_lt hi_eq (a (n + 1)) h_le
  have h_mem : a (n + 1) ∈ {k | S k (n + 1) = replicate (n + 1) 1} := by
    rw [a_eq_sInf (n + 1) (by omega)]
    exact Nat.sInf_mem h_nonempty2
  simp at h_mem
  exact h_ne h_mem

lemma add_at_nil_injective (i1 i2 : ℕ) (h : add_at [] i1 = add_at [] i2) : i1 = i2 := by
  induction i1 generalizing i2 with
  | zero =>
    rcases i2 with _ | i2
    · rfl
    · dsimp [add_at] at h
      injection h with h1 h2
      contradiction
  | succ i1 ih =>
    rcases i2 with _ | i2
    · dsimp [add_at] at h
      injection h with h1 h2
      contradiction
    · dsimp [add_at] at h
      injection h with h1 h2
      have ih_val := ih i2 h2
      subst ih_val
      rfl

lemma add_at_injective (L : List ℕ) (i1 i2 : ℕ) (h : add_at L i1 = add_at L i2) : i1 = i2 := by
  induction L generalizing i1 i2 with
  | nil =>
    exact add_at_nil_injective i1 i2 h
  | cons x xs ih =>
    rcases i1 with _ | i1 <;> rcases i2 with _ | i2
    · rfl
    · dsimp [add_at] at h
      injection h with h1 h2
      omega
    · dsimp [add_at] at h
      injection h with h1 h2
      omega
    · dsimp [add_at] at h
      injection h with h1 h2
      have ih_val := ih i1 i2 h2
      subst ih_val
      rfl

lemma ca_step_add_at_index_ge (L : List ℕ) (i : ℕ) (hi_lt : i < L.length) :
  ∃ i', ca_step (add_at L i) = add_at (ca_step L) i' ∧ i' ≥ i := by
  dsimp [ca_step]
  rcases ca_step_carry_add_at_of_lt L i 0 hi_lt with h_left | h_right
  · use i
    constructor
    · rw [h_left]
      rw [trim_trailing_zeros_add_at]
    · omega
  · use i + 1
    constructor
    · rw [h_right]
      rw [trim_trailing_zeros_add_at]
    · omega

lemma S_index_mono_step (n : ℕ) (t : ℕ) (i_prev i_curr : ℕ)
  (hi_prev_eq : S t (n + 1) = add_at (S t n) i_prev)
  (hi_curr_eq : S (t + 1) (n + 1) = add_at (S (t + 1) n) i_curr)
  (hi_lt : i_prev < (S t n).length) :
  i_curr ≥ i_prev := by
  have h_step : S (t + 1) (n + 1) = ca_step (S t (n + 1)) := S_succ t (n + 1)
  rw [hi_prev_eq] at h_step
  rcases ca_step_add_at_index_ge (S t n) i_prev hi_lt with ⟨i', h_eq, h_ge⟩
  rw [h_step] at hi_curr_eq
  have h_step_n : S (t + 1) n = ca_step (S t n) := S_succ t n
  rw [h_step_n] at hi_curr_eq
  rw [h_eq] at hi_curr_eq
  have h_eq_index := add_at_injective (ca_step (S t n)) i_curr i' hi_curr_eq.symm
  subst h_eq_index
  exact h_ge


lemma ca_step_add_at_index_le (L : List ℕ) (i : ℕ) (hi_lt : i < L.length) :
  ∃ i', ca_step (add_at L i) = add_at (ca_step L) i' ∧ i' ≤ i + 1 := by
  dsimp [ca_step]
  rcases ca_step_carry_add_at_of_lt L i 0 hi_lt with h_left | h_right
  · use i
    constructor
    · rw [h_left]
      rw [trim_trailing_zeros_add_at]
    · omega
  · use i + 1
    constructor
    · rw [h_right]
      rw [trim_trailing_zeros_add_at]
    · omega

lemma S_index_le_step (n : ℕ) (t : ℕ) (i_prev i_curr : ℕ)
  (hi_prev_eq : S t (n + 1) = add_at (S t n) i_prev)
  (hi_curr_eq : S (t + 1) (n + 1) = add_at (S (t + 1) n) i_curr)
  (hi_lt : i_prev < (S t n).length) :
  i_curr ≤ i_prev + 1 := by
  have h_step : S (t + 1) (n + 1) = ca_step (S t (n + 1)) := S_succ t (n + 1)
  rw [hi_prev_eq] at h_step
  rcases ca_step_add_at_index_le (S t n) i_prev hi_lt with ⟨i', h_eq, h_le⟩
  rw [h_step] at hi_curr_eq
  have h_step_n : S (t + 1) n = ca_step (S t n) := S_succ t n
  rw [h_step_n] at hi_curr_eq
  rw [h_eq] at hi_curr_eq
  have h_eq_index := add_at_injective (ca_step (S t n)) i_curr i' hi_curr_eq.symm
  subst h_eq_index
  exact h_le


lemma a_ge_add_three_of_index_lt (n : ℕ) (hn : n ≠ 0) (i : ℕ) (hi_lt : i + 2 < n)
  (hi_eq : S (a n) (n + 1) = add_at (replicate n 1) i) :
  a (n + 1) ≥ a n + 3 := by
  have h_ne : S (a n + 2) (n + 1) ≠ replicate (n + 1) 1 := by
    apply S_ne_replicate_one_of_lt n (a n) hn rfl (S_set_nonempty n hn) i hi_lt hi_eq (a n + 2) (by omega)
  by_contra h_lt_a
  simp at h_lt_a
  have h_stable : S (a n + 2) (n + 1) = replicate (n + 1) 1 := by
    apply stable_steps_upward_closed (n + 1) (a (n + 1)) (a n + 2)
    · have h_non_np1 : {k | S k (n + 1) = replicate (n + 1) 1}.Nonempty := S_set_nonempty (n + 1) (by omega)
      exact Nat.sInf_mem h_non_np1
    · omega
  contradiction


lemma m_ge_i_prev (n' : ℕ) (hn_nz : n' + 1 ≠ 0) (t : ℕ) (ht : t ≥ a (n' + 1))
  (ht_lt : t < a (n' + 1 + 1))
  (i_prev : ℕ) (hi_prev_eq : S (a (n' + 1)) (n' + 1 + 1) = add_at (replicate (n' + 1) 1) i_prev)
  (m : ℕ) (hm : S t (n' + 1 + 1) = add_at (S t (n' + 1)) m) :
  m ≥ i_prev := by
  have h_stable_t : S t (n' + 1) = replicate (n' + 1) 1 := by
    apply stable_steps_upward_closed (n' + 1) (a (n' + 1)) t
    · have h_nonempty : {k | S k (n' + 1) = replicate (n' + 1) 1}.Nonempty := S_set_nonempty (n' + 1) hn_nz
      exact Nat.sInf_mem h_nonempty
    · exact ht
  rw [h_stable_t] at hm
  have : t = a (n' + 1) + (t - a (n' + 1)) := by omega
  generalize hk : t - a (n' + 1) = k
  rw [hk] at this
  rw [this] at hm
  induction k generalizing t m with
  | zero =>
    have : t = a (n' + 1) := by omega
    have h_eq : m = i_prev := by
      apply add_at_injective (replicate (n' + 1) 1) m i_prev
      have h_add_zero : a (n' + 1) + 0 = a (n' + 1) := by omega
      rw [h_add_zero] at hm
      exact hm.symm.trans hi_prev_eq
    omega
  | succ k ih =>
    rcases S_add_at_index_le (n' + 1) (a (n' + 1) + k) hn_nz with ⟨m_k, hm_k_le, hm_k⟩
    have h_stable : S (a (n' + 1) + k) (n' + 1) = replicate (n' + 1) 1 := by
      apply stable_steps_upward_closed (n' + 1) (a (n' + 1)) (a (n' + 1) + k)
      · have h_nonempty : {k | S k (n' + 1) = replicate (n' + 1) 1}.Nonempty := S_set_nonempty (n' + 1) hn_nz
        exact Nat.sInf_mem h_nonempty
      · omega
    rw [h_stable] at hm_k
    have h_lt_prev : m_k < n' + 1 := by
      by_contra h_ge
      simp at h_ge
      have h_eq_s : m_k = n' + 1 := by omega
      subst h_eq_s
      have h_st_k : S (a (n' + 1) + k) (n' + 1 + 1) = replicate (n' + 1 + 1) 1 := by
        rw [hm_k, add_at_replicate_one_self]
      have h_le_a : a (n' + 1 + 1) ≤ a (n' + 1) + k := by
        rw [a_eq_sInf (n' + 1 + 1) (by omega)]
        apply Nat.sInf_le
        exact h_st_k
      omega
    have ih_val := ih (a (n' + 1) + k) (by omega) (by omega) (by omega) h_stable hm_k
    have h_assoc : a (n' + 1) + (k + 1) = (a (n' + 1) + k) + 1 := by omega
    rw [h_assoc] at hm
    rw [← h_stable] at hm_k
    have h_stable2 : S (a (n' + 1) + k + 1) (n' + 1) = replicate (n' + 1) 1 := by
      apply stable_steps_upward_closed (n' + 1) (a (n' + 1)) (a (n' + 1) + k + 1)
      · have h_nonempty : {k | S k (n' + 1) = replicate (n' + 1) 1}.Nonempty := S_set_nonempty (n' + 1) hn_nz
        exact Nat.sInf_mem h_nonempty
      · omega
    rw [← h_stable2] at hm
    have h_ge : m ≥ m_k := by
      have h_lt : m_k < (S (a (n' + 1) + k) (n' + 1)).length := by
        rw [h_stable]
        simp
        omega
      apply S_index_mono_step (n' + 1) (a (n' + 1) + k) m_k m hm_k hm h_lt
    omega








lemma ca_step_cons_one (xs : List ℕ) (h_not_all : ∃ y ∈ ca_step_carry xs 0, y ≠ 0) :
  ca_step (1 :: xs) = 1 :: ca_step xs := by
  dsimp [ca_step]
  simp [ca_step_carry, half_ceil, half_floor]
  exact trim_trailing_zeros_cons 1 (ca_step_carry xs 0) h_not_all

lemma ca_step_carry_not_all_zeros_of_sum_pos (xs : List ℕ) (h_sum : xs.sum > 0) :
  ∃ y ∈ ca_step_carry xs 0, y ≠ 0 := by
  have h_carry : (ca_step_carry xs 0).sum > 0 := by
    rw [ca_step_carry_sum]
    omega
  by_contra h_all
  push_neg at h_all
  have h_sum_zero : (ca_step_carry xs 0).sum = 0 := by
    generalize ca_step_carry xs 0 = L at *
    induction L with
    | nil => rfl
    | cons z zs ih =>
      simp
      have hz : z = 0 := h_all z (List.Mem.head zs)
      have h_zs_sum : zs.sum = 0 := by
        apply ih
        · dsimp at h_carry
          omega
        · intro y hy
          exact h_all y (List.Mem.tail z hy)
      omega
  omega

lemma ca_step_add_at_add_at_replicate_one_ne (n : ℕ) (m : ℕ) (hm : m ≤ n) (hn : n ≥ 1) :
  ca_step (add_at (add_at (replicate n 1) (n - 1)) m) ≠ replicate (n + 2) 1 := by
  induction n generalizing m with
  | zero => contradiction
  | succ n' ih =>
    rcases n' with _ | n''
    · -- n' = 0, so n = 1
      rcases m with _ | m
      · decide
      · rcases m with _ | m
        · decide
        · omega
    · rcases n'' with _ | n'''
      · -- n'' = 0, so n' = 1, so n = 2
        rcases m with _ | m
        · decide
        · rcases m with _ | m
          · decide
          · rcases m with _ | m
            · decide
            · omega
      · -- n'' = n''' + 1 >= 1. Let's call n'' = n''' + 1.
        -- original n = n' + 1 = n'' + 2 = n''' + 3 >= 3
        -- n'' is of the form succ n'''. So n'' - 1 = n'''.
        set n'' : ℕ := n''' + 1
        have hn_ge2 : n'' + 2 ≥ 2 := by omega
        have hn_nz : n'' + 2 ≠ 0 := by omega
        rcases m with _ | m
        · -- m = 0
          have h_sub : n'' + 1 + 1 - 1 = n'' + 1 := by omega
          have h_step : ca_step (add_at (add_at (replicate (n'' + 2) 1) (n'' + 1)) 0) =
            1 :: 2 :: ca_step (add_at (replicate n'' 1) (n'' - 1)) := by
            have h_eq_zs : add_at (add_at (replicate (n'' + 2) 1) (n'' + 1)) 0 =
              2 :: 1 :: add_at (replicate n'' 1) (n'' - 1) := rfl
            rw [h_eq_zs]
            dsimp [ca_step]
            simp [ca_step_carry, half_ceil, half_floor]
            have h_nz1 : ∃ y ∈ 2 :: ca_step_carry (add_at (replicate n'' 1) (n'' - 1)) 0, y ≠ 0 := by
              use 2
              simp
            rw [trim_trailing_zeros_cons 1 (2 :: ca_step_carry (add_at (replicate n'' 1) (n'' - 1)) 0) h_nz1]
            have h_nz2 : ∃ y ∈ ca_step_carry (add_at (replicate n'' 1) (n'' - 1)) 0, y ≠ 0 := by
              apply ca_step_carry_not_all_zeros_of_sum_pos
              rw [add_at_sum, sum_replicate_one]
              omega
            rw [trim_trailing_zeros_cons 2 (ca_step_carry (add_at (replicate n'' 1) (n'' - 1)) 0) h_nz2]
          intro h_eq
          rw [h_sub] at h_eq
          rw [h_step] at h_eq
          have h_rep_target : replicate (n'' + 2 + 2) 1 = 1 :: 1 :: replicate (n'' + 2) 1 := rfl
          rw [h_rep_target] at h_eq
          simp at h_eq
        · -- m = m + 1
          have h_sub : n'' + 1 + 1 - 1 = n'' + 1 := by omega
          have h_step : ca_step (add_at (add_at (replicate (n'' + 2) 1) (n'' + 1)) (m + 1)) =
            1 :: ca_step (add_at (add_at (replicate (n'' + 1) 1) n'') m) := by
            have h_zs : add_at (replicate (n'' + 2) 1) (n'' + 1) = 1 :: add_at (replicate (n'' + 1) 1) n'' := rfl
            have h_X : add_at (add_at (replicate (n'' + 2) 1) (n'' + 1)) (m + 1) = 1 :: add_at (add_at (replicate (n'' + 1) 1) n'') m := by
              rw [h_zs]
              rfl
            rw [h_X]
            apply ca_step_cons_one
            apply ca_step_carry_not_all_zeros_of_sum_pos
            rw [add_at_sum, add_at_sum, sum_replicate_one]
            omega
          intro h_eq
          have h_eq_rewritten := h_eq
          rw [h_sub] at h_eq_rewritten
          rw [h_step] at h_eq_rewritten
          have h_rep_target : replicate (n'' + 2 + 2) 1 = 1 :: replicate (n'' + 3) 1 := rfl
          rw [h_rep_target] at h_eq_rewritten
          simp at h_eq_rewritten
          have hm_le2 : m ≤ n'' + 1 := by omega
          have hn_ge2' : n'' + 1 ≥ 1 := by omega
          exact ih m hm_le2 hn_ge2' h_eq_rewritten


lemma ca_step_add_at_add_at_replicate_one_index_ge (n : ℕ) (m : ℕ) (hm : m ≤ n) (hn : n ≥ 1)
  (h_m_ge : m + 2 ≥ n)
  (j : ℕ) (hj : ca_step (add_at (add_at (replicate n 1) (n - 1)) m) = add_at (replicate (n + 1) 1) j) :
  j + 2 ≥ n + 1 := by
  induction n generalizing m j with
  | zero => contradiction
  | succ n' ih =>
    rcases n' with _ | n''
    · -- n' = 0, so n = 1
      omega
    · rcases n'' with _ | n'''
      · -- n'' = 0, so n' = 1, so n = 2
        rcases m with _ | m
        · -- m = 0
          dsimp [add_at, ca_step, ca_step_carry, half_ceil, half_floor, S] at hj
          rcases j with _ | j
          · contradiction
          · rcases j with _ | j
            · omega
            · omega
        · rcases m with _ | m
          · -- m = 1
            rcases j with _ | j
            · contradiction
            · rcases j with _ | j
              · omega
              · omega
          · rcases m with _ | m
            · -- m = 2
              rcases j with _ | j
              · contradiction
              · rcases j with _ | j
                · omega
                · omega
            · omega
      · -- n'' = n''' + 1 >= 1. Let's call n'' = n''' + 1.
        -- original n = n' + 1 = n'' + 2 = n''' + 3 >= 3
        set n'' : ℕ := n''' + 1
        have hn_nz : n'' + 2 ≠ 0 := by omega
        rcases m with _ | m
        · -- m = 0
          omega
        · -- m = m + 1
          have h_sub : n'' + 1 + 1 - 1 = n'' + 1 := by omega
          have h_step : ca_step (add_at (add_at (replicate (n'' + 2) 1) (n'' + 1)) (m + 1)) =
            1 :: ca_step (add_at (add_at (replicate (n'' + 1) 1) n'') m) := by
            have h_zs : add_at (replicate (n'' + 2) 1) (n'' + 1) = 1 :: add_at (replicate (n'' + 1) 1) n'' := rfl
            have h_X : add_at (add_at (replicate (n'' + 2) 1) (n'' + 1)) (m + 1) = 1 :: add_at (add_at (replicate (n'' + 1) 1) n'') m := by
              rw [h_zs]
              rfl
            rw [h_X]
            apply ca_step_cons_one
            apply ca_step_carry_not_all_zeros_of_sum_pos
            rw [add_at_sum, add_at_sum, sum_replicate_one]
            omega
          rw [h_sub] at hj
          rw [h_step] at hj
          rcases j with _ | j
          · -- j = 0
            change 1 :: ca_step (add_at (add_at (replicate (n'' + 1) 1) n'') m) = add_at (replicate (n'' + 2 + 1) 1) 0 at hj
            simp only [replicate_succ] at hj
            dsimp [add_at] at hj
            injection hj with hj1 hj2
            contradiction
          · -- j = j + 1
            have hj_rewritten : ca_step (add_at (add_at (replicate (n'' + 1) 1) n'') m) =
              add_at (replicate (n'' + 2) 1) j := by
              change 1 :: ca_step (add_at (add_at (replicate (n'' + 1) 1) n'') m) = add_at (replicate (n'' + 2 + 1) 1) (j + 1) at hj
              simp only [replicate_succ] at hj
              dsimp [add_at] at hj
              injection hj with hj1 hj2
            have hm_le2 : m ≤ n'' + 1 := by omega
            have hn_ge2' : n'' + 1 ≥ 1 := by omega
            have h_m_ge2 : m + 2 ≥ n'' + 1 := by omega
            have ih_val := ih m hm_le2 hn_ge2' h_m_ge2 j hj_rewritten
            omega


lemma ca_step_carry_not_all_zeros_of_carry_pos (xs : List ℕ) (c : ℕ) (hc : c > 0) :
  ∃ y ∈ ca_step_carry xs c, y ≠ 0 := by
  induction xs generalizing c with
  | nil =>
    use c
    simp [ca_step_carry]
    omega
  | cons z zs ih =>
    use half_ceil z + c
    simp [ca_step_carry]
    omega

lemma ca_step_add_at_add_at_replicate_one_index_le (n : ℕ) (m : ℕ) (hm : m ≤ n) (hn : n ≥ 1)
  (j : ℕ) (hj : ca_step (add_at (add_at (replicate n 1) (n - 1)) m) = add_at (replicate (n + 1) 1) j) :
  j ≤ m + 2 := by
  induction n generalizing m j with
  | zero => contradiction
  | succ n' ih =>
    rcases n' with _ | n''
    · -- n' = 0, so n = 1
      rcases m with _ | m
      · -- m = 0
        have hj_eval : ca_step (add_at (add_at (replicate 1 1) (1 - 1)) 0) = [2, 1] := by decide
        rw [hj_eval] at hj
        rcases j with _ | j
        · omega
        · rcases j with _ | j
          · injection hj with h1 h2
            contradiction
          · have h_len := congrArg List.length hj
            rw [add_at_length] at h_len; simp [replicate] at h_len
      · rcases m with _ | m
        · -- m = 1
          have hj_eval : ca_step (add_at (add_at (replicate 1 1) (1 - 1)) 1) = [1, 2] := by decide
          rw [hj_eval] at hj
          rcases j with _ | j
          · injection hj with h1 h2
            contradiction
          · rcases j with _ | j
            · omega
            · have h_len := congrArg List.length hj
              rw [add_at_length] at h_len; simp [replicate] at h_len
        · omega
    · rcases n'' with _ | n'''
      · -- n'' = 0, so n = 2
        rcases m with _ | m
        · -- m = 0
          have hj_eval : ca_step (add_at (add_at (replicate 2 1) (2 - 1)) 0) = [1, 2, 1] := by decide
          rw [hj_eval] at hj
          rcases j with _ | j
          · injection hj with h1 h2
          · rcases j with _ | j
            · omega
            · rcases j with _ | j
              · injection hj with h1 h2
                injection h2 with h3 h4
                contradiction
              · have h_len := congrArg List.length hj
                rw [add_at_length] at h_len; simp [replicate] at h_len
        · rcases m with _ | m
          · -- m = 1
            have hj_eval : ca_step (add_at (add_at (replicate 2 1) (2 - 1)) 1) = [1, 2, 1] := by decide
            rw [hj_eval] at hj
            rcases j with _ | j
            · injection hj with h1 h2
              contradiction
            · rcases j with _ | j
              · omega
              · rcases j with _ | j
                · injection hj with h1 h2
                  injection h2 with h3 h4
                  contradiction
                · have h_len := congrArg List.length hj
                  rw [add_at_length] at h_len; simp [replicate] at h_len
          · rcases m with _ | m
            · -- m = 2
              have hj_eval : ca_step (add_at (add_at (replicate 2 1) (2 - 1)) 2) = [1, 1, 2] := by decide
              rw [hj_eval] at hj
              rcases j with _ | j
              · injection hj with h1 h2
                contradiction
              · rcases j with _ | j
                · injection hj with h1 h2
                  injection h2 with h3 h4
                  contradiction
                · rcases j with _ | j
                  · omega
                  · have h_len := congrArg List.length hj
                    rw [add_at_length] at h_len; simp [replicate] at h_len
            · omega
      · -- n'' = n''' + 1 >= 1. Let's call n'' = n''' + 1.
        -- original n = n' + 1 = n'' + 2 = n''' + 3 >= 3
        set n'' : ℕ := n''' + 1
        have hn_nz : n'' + 2 ≠ 0 := by omega
        rcases m with _ | m
        · -- m = 0
          rcases j with _ | j
          · omega
          · rcases j with _ | j
            · omega
            · rcases j with _ | j
              · omega
              · have h_sub : n'' + 1 + 1 - 1 = n'' + 1 := by omega
                rw [h_sub] at hj
                simp only [replicate_succ, ca_step, ca_step_carry, half_ceil, half_floor, add_at] at hj
                have h_num1 : (1 + 1 + 1) / 2 + 0 = 1 := by decide
                have h_num2 : (1 + 1) / 2 = 1 := by decide
                rw [h_num1, h_num2] at hj
                have h_nz : ∃ y ∈ ca_step_carry (add_at (replicate (n'' + 1) 1) n'') 1, y ≠ 0 := by
                  apply ca_step_carry_not_all_zeros_of_carry_pos
                  omega
                rw [replicate_succ] at h_nz
                rw [trim_trailing_zeros_cons 1 (ca_step_carry (add_at (1 :: replicate n'' 1) n'') 1) h_nz] at hj
                injection hj with hj1 hj2
                dsimp [n'', ca_step_carry, half_ceil, half_floor, add_at] at hj2
                have h_nz2 : ∃ y ∈ ca_step_carry (add_at (replicate (n''' + 1) 1) n''') 0, y ≠ 0 := by
                  apply ca_step_carry_not_all_zeros_of_sum_pos
                  rw [add_at_sum, sum_replicate_one]
                  omega
                rw [trim_trailing_zeros_cons 2 (ca_step_carry (add_at (replicate (n''' + 1) 1) n''') 0) h_nz2] at hj2
                injection hj2 with hj3 hj4
                contradiction
        · -- m = m + 1
          have h_sub : n'' + 1 + 1 - 1 = n'' + 1 := by omega
          have h_step : ca_step (add_at (add_at (replicate (n'' + 1 + 1) 1) (n'' + 1)) (m + 1)) =
            1 :: ca_step (add_at (add_at (replicate (n'' + 1) 1) n'') m) := by
            have h_zs : add_at (replicate (n'' + 1 + 1) 1) (n'' + 1) = 1 :: add_at (replicate (n'' + 1) 1) n'' := rfl
            have h_X : add_at (add_at (replicate (n'' + 1 + 1) 1) (n'' + 1)) (m + 1) = 1 :: add_at (add_at (replicate (n'' + 1) 1) n'') m := by
              rw [h_zs]
              rfl
            rw [h_X]
            apply ca_step_cons_one
            apply ca_step_carry_not_all_zeros_of_sum_pos
            rw [add_at_sum, add_at_sum, sum_replicate_one]
            omega
          rw [h_sub] at hj
          rw [h_step] at hj
          rcases j with _ | j
          · -- j = 0
            change 1 :: ca_step (add_at (add_at (replicate (n'' + 1) 1) n'') m) = add_at (replicate (n'' + 1 + 1 + 1) 1) 0 at hj
            simp only [replicate_succ] at hj
            dsimp [add_at] at hj
            injection hj with hj1 hj2
            contradiction
          · -- j = j + 1
            have hj_rewritten : ca_step (add_at (add_at (replicate (n'' + 1) 1) n'') m) =
              add_at (replicate (n'' + 1 + 1) 1) j := by
              change 1 :: ca_step (add_at (add_at (replicate (n'' + 1) 1) n'') m) = add_at (replicate (n'' + 1 + 1 + 1) 1) (j + 1) at hj
              simp only [replicate_succ] at hj
              dsimp [add_at] at hj
              injection hj with hj1 hj2
            have hm_le2 : m ≤ n'' + 1 := by omega
            have hn_ge2' : n'' + 1 ≥ 1 := by omega
            have ih_val := ih m hm_le2 hn_ge2' j hj_rewritten
            omega




lemma a_ge_add_one_strong (n : ℕ) : ∀ k ≤ n, k ≠ 0 → a (k + 1) ≥ a k + 1 := by
  induction n with
  | zero =>
    intro k hk hk0
    omega
  | succ n ih =>
    intro k hk hk0
    have h_cases : k ≤ n ∨ k = n + 1 := by omega
    rcases h_cases with hk_le | rfl
    · exact ih k hk_le hk0
    · -- k = n + 1
      rcases n with _ | n'
      · -- n = 0 (so k = 1)
        rw [a_one, a_two]
      · rcases n' with _ | n''
        · -- n = 1 (so k = 2)
          rw [a_two, a_three]
          decide
        · -- n = n'' + 2 >= 2
          set n : ℕ := n'' + 2
          have hn_nz : n ≠ 0 := by omega
          have ih_val := ih n (by omega) hn_nz
          have ih_val2 : a n ≥ a (n - 1) + 1 := by
            have h_le : n - 1 ≤ n'' + 2 := by omega
            have h_nz : n - 1 ≠ 0 := by omega
            exact ih (n - 1) h_le h_nz
          change a (n + 2) ≥ a (n + 1) + 1
          by_contra h_lt
          simp at h_lt
          have h_nonempty2 : {k | S k (n + 1) = replicate (n + 1) 1}.Nonempty := S_set_nonempty (n + 1) (by omega)
          have h_nonempty3 : {k | S k (n + 2) = replicate (n + 2) 1}.Nonempty := S_set_nonempty (n + 2) (by omega)
          have h_mono2 : a (n + 1) ≤ a (n + 2) := a_mono (n + 1) (by omega) h_nonempty3
          have h_eq : a (n + 2) = a (n + 1) := by omega
          have h_t'_stable : S (a (n + 1)) (n + 2) = replicate (n + 2) 1 := by
            have h_mem : a (n + 2) ∈ {k | S k (n + 2) = replicate (n + 2) 1} := Nat.sInf_mem h_nonempty3
            simp at h_mem
            rw [h_eq] at h_mem
            exact h_mem
          have h_t'_stable_np1 : S (a (n + 1)) (n + 1) = replicate (n + 1) 1 := Nat.sInf_mem h_nonempty2
          have ht'_ge_1 : a (n + 1) ≥ 1 := by omega
          have h_not_stable : S (a (n + 1) - 1) (n + 1) ≠ replicate (n + 1) 1 := by
            intro h_st
            have ht'_le : a (n + 1) ≤ a (n + 1) - 1 := by
              dsimp [a]
              apply Nat.sInf_le
              exact h_st
            omega
          have hn_sub : a (n + 1) - 1 ≥ a n := by
            have := ih_val
            have := ht'_ge_1
            omega
          have h_n_st : S (a (n + 1) - 1) n = replicate n 1 := by
            apply stable_steps_upward_closed n (a n) (a (n + 1) - 1)
            · have := S_set_nonempty n (by omega)
              exact Nat.sInf_mem this
            · exact hn_sub
          have hn_st2 : S (a (n + 1) - 1) (n + 1) = add_at (S (a (n + 1) - 1) n) (n - 1) := by
            rcases S_add_at_index_le n (a (n + 1) - 1) hn_nz with ⟨j, hj_le, hj_eq⟩
            have hj_cases : j = n ∨ j < n := by omega
            rcases hj_cases with rfl | hj_lt
            · rw [h_n_st] at hj_eq
              rw [add_at_replicate_one_self] at hj_eq
              have : S (a (n + 1) - 1) (n + 1) = replicate (n + 1) 1 := hj_eq
              contradiction
            · have hj_eq2 : j = n - 1 := by
                have h_step : ca_step (add_at (replicate n 1) j) = replicate (n + 1) 1 := by
                  have h_step_trans : S (a (n + 1)) (n + 1) = ca_step (S (a (n + 1) - 1) (n + 1)) := by
                    have : a (n + 1) = (a (n + 1) - 1) + 1 := by omega
                    nth_rw 1 [this]
                    rw [S_succ]
                  rw [h_step_trans] at h_t'_stable_np1
                  rw [hj_eq, h_n_st] at h_t'_stable_np1
                  exact h_t'_stable_np1
                rw [ca_step_add_at_replicate_one n j hj_lt] at h_step
                have h_len := add_at_length (replicate n 1) (j + 1)
                rw [h_step] at h_len
                simp at h_len
                omega
              rw [hj_eq2] at hj_eq
              exact hj_eq
          have h_n_stable : S (a (n + 1) - 1) (n + 1) = add_at (replicate n 1) (n - 1) := by
            rw [hn_st2, h_n_st]
          rcases S_add_at_index_le (n + 1) (a (n + 1) - 1) (by omega) with ⟨m, hm_le, hm_eq⟩
          have hm_le_n : m ≤ n := by
            have h_len : (S (a (n + 1) - 1) (n + 1)).length ≤ n := by
              rw [h_n_stable]
              rw [add_at_length]
              simp
              omega
            apply m_le_n_of_S n (a (n + 1)) m hn_nz h_len hm_eq hm_le
          have h_step_st : S (a (n + 1)) (n + 2) = ca_step (S (a (n + 1) - 1) (n + 2)) := by
            have : a (n + 1) = (a (n + 1) - 1) + 1 := by omega
            nth_rw 1 [this]
            rw [S_succ]
          rw [h_t'_stable] at h_step_st
          rw [hm_eq] at h_step_st
          rw [h_n_stable] at h_step_st
          have h_ne := ca_step_add_at_add_at_replicate_one_ne n m hm_le_n (by omega)
          exact h_ne h_step_st.symm

lemma a_ge_add_one (n : ℕ) (hn : n ≠ 0) : a (n + 1) ≥ a n + 1 := by
  apply a_ge_add_one_strong n n (by omega) hn


lemma add_at_append_left (A B : List ℕ) (i : ℕ) (hi : i < A.length) :
  add_at (A ++ B) i = add_at A i ++ B := by
  induction A generalizing i with
  | nil =>
    simp at hi
  | cons x xs ih =>
    rcases i with _ | i
    · rfl
    · simp [add_at]
      apply ih
      simp at hi; omega

lemma add_at_append_right (A B : List ℕ) (i : ℕ) :
  add_at (A ++ B) (A.length + i) = A ++ add_at B i := by
  induction A generalizing i with
  | nil =>
    simp [add_at]
  | cons x xs ih =>
    rw [cons_append]
    have : (x :: xs).length + i = (xs.length + i) + 1 := by simp; omega
    rw [this]
    change x :: add_at (xs ++ B) (xs.length + i) = x :: (xs ++ add_at B i)
    rw [ih]


lemma ca_step_peel (k : ℕ) (L : List ℕ) (hL : L.sum > 0) :
  ca_step (replicate k 1 ++ L) = replicate k 1 ++ ca_step L := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h_sum : (replicate k 1 ++ L).sum > 0 := by
      rw [List.sum_append]
      omega
    have h_not_all := ca_step_carry_not_all_zeros_of_sum_pos (replicate k 1 ++ L) h_sum
    rw [replicate_succ]
    change ca_step (1 :: (replicate k 1 ++ L)) = 1 :: (replicate k 1 ++ ca_step L)
    rw [ca_step_cons_one (replicate k 1 ++ L) h_not_all]
    rw [ih]

lemma ca_step_sum (L : List ℕ) : (ca_step L).sum = L.sum := by
  dsimp [ca_step]
  rw [trim_trailing_zeros_sum, ca_step_carry_sum]
  simp

lemma foldl_ca_step_sum (k : ℕ) (L : List ℕ) :
  ((List.range k).foldl (fun acc _ => ca_step acc) L).sum = L.sum := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp
    rw [ca_step_sum, ih]

lemma foldl_ca_step_peel (k : ℕ) (m : ℕ) (L : List ℕ) (hL : L.sum > 0) :
  (List.range k).foldl (fun acc _ => ca_step acc) (List.replicate m 1 ++ L) =
    List.replicate m 1 ++ (List.range k).foldl (fun acc _ => ca_step acc) L := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h_step : ∀ acc, (List.range (k + 1)).foldl (fun acc _ => ca_step acc) acc =
      ca_step ((List.range k).foldl (fun acc _ => ca_step acc) acc) := by
      intro acc
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [h_step, h_step]
    rw [ih L hL]
    rw [ca_step_peel]
    rw [foldl_ca_step_sum]
    exact hL

lemma carry_index_ge_of_ge_a (n : ℕ) (hn : n ≠ 0) (t : ℕ) (ht : t ≥ a n)
  (h_le : a (n + 1) ≤ a n + 2)
  (m : ℕ) (hm : S t (n + 1) = add_at (S t n) m) :
  m + 2 ≥ n := by
  have h_diff : t = a n + (t - a n) := by omega
  generalize hk : t - a n = k
  rw [h_diff] at hm
  induction k generalizing t m with
  | zero =>
    have h_eq_t : t = a n := by omega
    subst h_eq_t
    simp at hm
    have h_stable : S (a n) n = replicate n 1 := by
      have h_a_eq : a n = sInf {k | S k n = replicate n 1} := a_eq_sInf n hn
      rw [h_a_eq]
      exact Nat.sInf_mem (S_set_nonempty n hn)
    rw [h_stable] at hm
    have h_nonempty : {k | S k n = replicate n 1}.Nonempty := S_set_nonempty n hn
    have h_nonempty2 : {k | S k (n + 1) = replicate (n + 1) 1}.Nonempty := S_set_nonempty (n + 1) (by omega)
    apply index_ge_of_a_le n (a n) hn rfl h_nonempty h_nonempty2 h_le m hm
  | succ k ih =>
    rcases S_add_at_index_le n (a n + k) hn with ⟨m_k, hm_k_le, hm_k⟩
    have h_stable : S (a n + k) n = replicate n 1 := by
      apply stable_steps_upward_closed n (a n) (a n + k)
      · have h_a_eq : a n = sInf {k | S k n = replicate n 1} := a_eq_sInf n hn
        rw [h_a_eq]
        exact Nat.sInf_mem (S_set_nonempty n hn)
      · omega
    have h_cases : m_k = n ∨ m_k < n := by omega
    rcases h_cases with h_mk_eq | h_mk_lt
    · -- m_k = n
      have hm_k2 := hm_k
      rw [h_mk_eq] at hm_k2
      have h_st_k : S (a n + k) (n + 1) = replicate (n + 1) 1 := by
        rw [hm_k2, h_stable, add_at_replicate_one_self]
      have h_st_succ : S t (n + 1) = replicate (n + 1) 1 := by
        apply stable_steps_upward_closed (n + 1) (a n + k) t h_st_k (by omega)
      have h_index_eq : a n + (t - a n) = t := by omega
      have hm_simplified := hm
      rw [h_index_eq] at hm_simplified
      rw [h_st_succ] at hm_simplified
      have h_stable_t : S t n = replicate n 1 := by
        apply stable_steps_upward_closed n (a n) t
        · have h_a_eq : a n = sInf {k | S k n = replicate n 1} := a_eq_sInf n hn
          rw [h_a_eq]
          exact Nat.sInf_mem (S_set_nonempty n hn)
        · omega
      rw [h_stable_t] at hm_simplified
      have h_eq_m : m = n := by
        apply add_at_injective (replicate n 1) m n
        rw [← add_at_replicate_one_self n] at hm_simplified
        exact hm_simplified.symm
      omega
    · have h_ih := ih (a n + k) (by omega) m_k
      have h_sub_k : a n + k - a n = k := by omega
      have h_index_eq_k : a n + (a n + k - a n) = a n + k := by omega
      rw [h_index_eq_k, h_sub_k] at h_ih
      have h_ge_prev : m_k + 2 ≥ n := h_ih hm_k rfl rfl
      have h_ge : m ≥ m_k := by
        have h_lt : m_k < (S (a n + k) n).length := by
          rw [h_stable]
          simp
          omega
        have h_eq_t_succ : t = a n + k + 1 := by omega
        have h_index_eq_succ : a n + (t - a n) = t := by omega
        have hm_simplified := hm
        rw [h_index_eq_succ] at hm_simplified
        rw [h_eq_t_succ] at hm_simplified
        apply S_index_mono_step n (a n + k) m_k m hm_k hm_simplified h_lt
      omega


lemma ca_step_add_at_add_at_replicate_one_special_step1 (n : ℕ) (hn : n ≥ 2) :
  add_at (add_at (replicate (n + 1) 1) (n + 1 - 2)) (n + 1) = 1 :: add_at (add_at (replicate n 1) (n - 2)) n := by
  rcases n with _ | n'
  · contradiction
  · rcases n' with _ | n''
    · contradiction
    · rfl

lemma ca_step_add_at_add_at_replicate_one_special_step2 (n : ℕ) (hn : n ≥ 2) :
  add_at (add_at (replicate (n + 1) 1) (n + 1 - 1)) (n + 1) = 1 :: add_at (add_at (replicate n 1) (n - 1)) n := by
  rcases n with _ | n'
  · contradiction
  · rcases n' with _ | n''
    · contradiction
    · rfl

lemma ca_step_add_at_add_at_replicate_one_special (n : ℕ) (hn : n ≥ 2) :
  ca_step (add_at (add_at (replicate n 1) (n - 2)) n) = add_at (add_at (replicate n 1) (n - 1)) n := by
  induction n, hn using Nat.le_induction with
  | base =>
    rfl
  | succ n hn ih =>
    rw [ca_step_add_at_add_at_replicate_one_special_step1 n hn]
    rw [ca_step_add_at_add_at_replicate_one_special_step2 n hn]
    set L := add_at (add_at (replicate n 1) (n - 2)) n
    have h_sum : L.sum > 0 := by
      dsimp [L]
      rw [add_at_sum, add_at_sum, sum_replicate_one]
      omega
    have h_not_all := ca_step_carry_not_all_zeros_of_sum_pos L h_sum
    have h_ca : ca_step (1 :: L) = 1 :: ca_step L := by
      dsimp [ca_step, ca_step_carry]
      change trim_trailing_zeros (1 :: ca_step_carry L 0) = 1 :: trim_trailing_zeros (ca_step_carry L 0)
      rw [trim_trailing_zeros_cons 1 (ca_step_carry L 0) h_not_all]
    rw [h_ca, ih]

lemma ca_step_add_at_add_at_replicate_one_special2_step (n : ℕ) (hn : n ≥ 1) :
  add_at (add_at (replicate (n + 1) 1) (n + 1 - 1)) (n + 1) = 1 :: add_at (add_at (replicate n 1) (n - 1)) n := by
  rcases n with _ | n'
  · contradiction
  · rfl

lemma ca_step_add_at_add_at_replicate_one_special2 (n : ℕ) (hn : n ≥ 1) :
  ca_step (add_at (add_at (replicate n 1) (n - 1)) n) = add_at (replicate (n + 1) 1) n := by
  induction n, hn using Nat.le_induction with
  | base =>
    rfl
  | succ n hn ih =>
    rw [ca_step_add_at_add_at_replicate_one_special2_step n hn]
    set L := add_at (add_at (replicate n 1) (n - 1)) n
    have h_sum : L.sum > 0 := by
      dsimp [L]
      rw [add_at_sum, add_at_sum, sum_replicate_one]
      omega
    have h_not_all := ca_step_carry_not_all_zeros_of_sum_pos L h_sum
    have h_ca : ca_step (1 :: L) = 1 :: ca_step L := by
      dsimp [ca_step, ca_step_carry]
      change trim_trailing_zeros (1 :: ca_step_carry L 0) = 1 :: trim_trailing_zeros (ca_step_carry L 0)
      rw [trim_trailing_zeros_cons 1 (ca_step_carry L 0) h_not_all]
    rw [h_ca, ih]
    have h_rep : replicate (n + 1 + 1) 1 = 1 :: replicate (n + 1) 1 := List.replicate_succ
    rw [h_rep]
    rfl


lemma a_le_add_two_step (n' : ℕ) (hn_nz : n' + 1 + 1 ≠ 0)
  (ih_val : a (n' + 1 + 1) ≤ a (n' + 1) + 2 ∧
            (∀ t ≥ a (n' + 1 + 1) - 1, ∀ m, S t (n' + 1 + 2) = add_at (S t (n' + 1 + 1)) m → m + 2 ≥ n' + 1)) :
  a (n' + 1 + 1 + 1) ≤ a (n' + 1 + 1) + 2 ∧
  (∀ t ≥ a (n' + 1 + 1 + 1) - 1, ∀ m, S t (n' + 1 + 1 + 2) = add_at (S t (n' + 1 + 1 + 1)) m → m + 2 ≥ n' + 1 + 1) := by
      have h_le_np1 := ih_val.1
      have h_carry_np1 := ih_val.2
      have h_part1 : a (n' + 1 + 1 + 1) ≤ a (n' + 1 + 1) + 2 := by
        have h_nonempty : {k | S k (n' + 1 + 1) = replicate (n' + 1 + 1) 1}.Nonempty := S_set_nonempty (n' + 1 + 1) hn_nz
        have h_nonempty2 : {k | S k (n' + 1 + 1 + 1) = replicate (n' + 1 + 1 + 1) 1}.Nonempty := S_set_nonempty (n' + 1 + 1 + 1) (by omega)
        rcases S_add_at_index_le (n' + 1 + 1) (a (n' + 1 + 1)) hn_nz with ⟨i, hi_le, hi_eq⟩
        have ht_mem : S (a (n' + 1 + 1)) (n' + 1 + 1) = replicate (n' + 1 + 1) 1 := by
          have h_mem : a (n' + 1 + 1) ∈ {k | S k (n' + 1 + 1) = replicate (n' + 1 + 1) 1} := by
            rw [a_eq_sInf (n' + 1 + 1) hn_nz]
            exact Nat.sInf_mem h_nonempty
          exact h_mem
        rw [ht_mem] at hi_eq
        have h_ge : i + 2 ≥ n' + 1 + 1 := by
          by_contra h_lt
          have h_lt_norm : i + 2 < n' + 1 + 1 := by omega
          have h_gt : a (n' + 1 + 1 + 1) ≥ a (n' + 1 + 1) + 3 := by
            apply a_ge_add_three_of_index_lt (n' + 1 + 1) hn_nz i h_lt_norm hi_eq
          have h_ge1 : a (n' + 1 + 1) ≥ a (n' + 1) + 1 := by
            apply a_ge_add_one_strong (n' + 1) (n' + 1) (by omega) (by omega)
          have ht_ge1 : a (n' + 1 + 1) ≥ 1 := by omega
          set t := a (n' + 1 + 1) - 1
          have hn_sub : t ≥ a (n' + 1 + 1) - 1 := by omega
          have hn_sub2 : t ≥ a (n' + 1) := by omega
          have h_n_st : S t (n' + 1) = replicate (n' + 1) 1 := by
            apply stable_steps_upward_closed (n' + 1) (a (n' + 1)) t
            · have h_non : {k | S k (n' + 1) = replicate (n' + 1) 1}.Nonempty := S_set_nonempty (n' + 1) (by omega)
              exact Nat.sInf_mem h_non
            · exact hn_sub2
          have h_not_stable : S t (n' + 1 + 1) ≠ replicate (n' + 1 + 1) 1 := by
            intro h_st
            have ht'_le : a (n' + 1 + 1) ≤ t := by
              rw [a_eq_sInf (n' + 1 + 1) hn_nz]
              apply Nat.sInf_le
              exact h_st
            omega
          have hn_st2 : S t (n' + 1 + 1) = add_at (S t (n' + 1)) (n' + 1 - 1) := by
            rcases S_add_at_index_le (n' + 1) t (by omega) with ⟨j, hj_le, hj_eq⟩
            have hj_cases : j = n' + 1 ∨ j < n' + 1 := by omega
            rcases hj_cases with rfl | hj_lt
            · rw [h_n_st] at hj_eq
              rw [add_at_replicate_one_self] at hj_eq
              contradiction
            · have hj_eq2 : j = n' + 1 - 1 := by
                have h_step : ca_step (add_at (replicate (n' + 1) 1) j) = replicate (n' + 1 + 1) 1 := by
                  have h_step_trans : S (a (n' + 1 + 1)) (n' + 1 + 1) = ca_step (S t (n' + 1 + 1)) := by
                    have : a (n' + 1 + 1) = t + 1 := by omega
                    nth_rw 1 [this]
                    rw [S_succ]
                  have h_t'_stable_np1 : S (a (n' + 1 + 1)) (n' + 1 + 1) = replicate (n' + 1 + 1) 1 := ht_mem
                  rw [h_step_trans] at h_t'_stable_np1
                  rw [hj_eq, h_n_st] at h_t'_stable_np1
                  exact h_t'_stable_np1
                rw [ca_step_add_at_replicate_one (n' + 1) j hj_lt] at h_step
                have h_len := add_at_length (replicate (n' + 1) 1) (j + 1)
                rw [h_step] at h_len
                simp at h_len
                omega
              rw [hj_eq2] at hj_eq
              exact hj_eq
          have h_n_stable : S t (n' + 1 + 1) = add_at (replicate (n' + 1) 1) (n' + 1 - 1) := by
            rw [hn_st2, h_n_st]
          rcases S_add_at_index_le (n' + 1 + 1) t hn_nz with ⟨m, hm_le, hm_eq⟩
          have hm_le_n : m ≤ n' + 1 := by
            have h_len : (S t (n' + 1 + 1)).length ≤ n' + 1 := by
              rw [h_n_stable]
              rw [add_at_length]
              simp
            apply m_le_n_of_S (n' + 1) (a (n' + 1 + 1)) m (by omega) h_len hm_eq hm_le
          have h_step_st : S (a (n' + 1 + 1)) (n' + 1 + 1 + 1) = ca_step (S t (n' + 1 + 1 + 1)) := by
            have : a (n' + 1 + 1) = t + 1 := by omega
            nth_rw 1 [this]
            rw [S_succ]
          have h_m_ge_cases : m + 2 ≥ n' + 1 ∨ m + 2 < n' + 1 := by omega
          rcases h_m_ge_cases with h_m_ge | h_m_lt
          · have h_ge_curr : i + 2 ≥ n' + 1 + 1 := by
              apply ca_step_add_at_add_at_replicate_one_index_ge (n' + 1) m hm_le_n (by omega) h_m_ge i
              rw [hi_eq] at h_step_st
              rw [hm_eq] at h_step_st
              rw [h_n_stable] at h_step_st
              exact h_step_st.symm
            omega
          · have h_ge_curr : m + 2 ≥ n' + 1 := h_carry_np1 t hn_sub m hm_eq
            omega
        have h_cases : n' + 1 + 1 = i ∨ i < n' + 1 + 1 := by omega
        rcases h_cases with rfl | hi_lt
        · rw [a_eq_sInf (n' + 1 + 1 + 1) (by omega)]
          have h_le_inf : sInf {k | S k (n' + 1 + 1 + 1) = replicate (n' + 1 + 1 + 1) 1} ≤ a (n' + 1 + 1) := by
            apply Nat.sInf_le
            change S (a (n' + 1 + 1)) (n' + 1 + 1 + 1) = replicate (n' + 1 + 1 + 1) 1
            rw [hi_eq, add_at_replicate_one_self]
          omega
        · set k := n' + 1 + 1 - i
          have h_k_le : k ≤ 2 := by omega
          rw [a_eq_sInf (n' + 1 + 1 + 1) (by omega)]
          have h_le : sInf {x | S x (n' + 1 + 1 + 1) = replicate (n' + 1 + 1 + 1) 1} ≤ a (n' + 1 + 1) + k := by
            apply Nat.sInf_le
            change S (a (n' + 1 + 1) + k) (n' + 1 + 1 + 1) = replicate (n' + 1 + 1 + 1) 1
            have h_step : S (a (n' + 1 + 1) + k) (n' + 1 + 1 + 1) = (List.range k).foldl (fun acc _ => ca_step acc) (S (a (n' + 1 + 1)) (n' + 1 + 1 + 1)) := by
              dsimp [S]
              rw [List.range_add, foldl_append]
              exact foldl_ca_step_map (fun x => a (n' + 1 + 1) + x) (List.range k) (S (a (n' + 1 + 1)) (n' + 1 + 1 + 1))
            rw [h_step, hi_eq]
            have h_sum : i + k ≤ n' + 1 + 1 := by omega
            rw [foldl_ca_step_add_at (n' + 1 + 1) i k h_sum]
            have hk_eq : i + k = n' + 1 + 1 := by omega
            rw [hk_eq]
            exact add_at_replicate_one_self (n' + 1 + 1)
          omega
      -- Now we prove the second part:
      -- ∀ t ≥ a N, ∀ m, S t (N + 2) = add_at (S t (N + 1)) m → m + 2 ≥ N
      -- where N = n' + 1 + 1 = n' + 2
      set N := n' + 1 + 1
      have hN_nz : N ≠ 0 := by dsimp [N]; omega
      have h_mono_prev : a (N - 1) ≤ a N :=
        a_mono (N - 1) (by dsimp [N]; omega) (S_set_nonempty N hN_nz)
      have h_stable_n : S (a N) N = replicate N 1 := by
        have h_a_eq : a N = sInf {k | S k N = replicate N 1} := a_eq_sInf N (by omega)
        rw [h_a_eq]
        exact Nat.sInf_mem (S_set_nonempty N (by omega))
      rcases S_add_at_index_le N (a N) hN_nz with ⟨i_prev, hi_prev_le, hi_prev⟩
      have h_ip_lt : i_prev < N := by
        by_contra h_ge
        have h_eq : i_prev = N := by omega
        have h_eq_st : S (a N) (N + 1) = replicate (N + 1) 1 := by
          rw [hi_prev, h_stable_n, h_eq, add_at_replicate_one_self]
        have h_le_inf : a (N + 1) ≤ a N := by
          rw [a_eq_sInf (N + 1) (by omega)]
          apply Nat.sInf_le
          exact h_eq_st
        have h_not_st_simp : a (N + 1) > a N := by
          have h_ge1 : a (N + 1) ≥ a N + 1 := a_ge_add_one N hN_nz
          omega
        omega
      have h_i_prev_ge : i_prev + 2 ≥ N := by
        apply index_ge_of_a_le_general N (a N) (by omega) h_stable_n (S_set_nonempty (N + 1) (by omega)) h_part1 i_prev
        rw [hi_prev, h_stable_n]
      rcases S_add_at_index_le (N + 1) (a N) (by dsimp [N]; omega) with ⟨m_0, hm_0_le, hm_0⟩
      have h_ge_m0 : m_0 + 2 ≥ N := by
        have h_ge1 : a (N + 1) ≥ a N + 1 := a_ge_add_one N hN_nz
        have h_cases2 : a (N + 1) = a N + 1 ∨ a (N + 1) = a N + 2 := by omega
        rcases h_cases2 with h_eq1_an | h_eq2_an
        · -- Case 1: a (N + 1) = a N + 1
          have h_i_prev_cases : i_prev = N - 1 ∨ i_prev = N - 2 ∨ (N ≥ 3 ∧ i_prev = N - 3) := by dsimp [N]; omega
          rcases h_i_prev_cases with rfl | rfl | h_ip_nm3
          · -- i_prev = N - 1
            sorry
          · -- i_prev = N - 2
            have h_stable_np1 : S (a N + 1) (N + 1) = add_at (replicate N 1) (N - 1) := by
              have h_step : S (a N + 1) (N + 1) = ca_step (S (a N) (N + 1)) := S_succ (a N) (N + 1)
              rw [h_step, hi_prev, h_stable_n]
              have h_eq1 : ca_step (add_at (replicate N 1) (N - 2)) = add_at (replicate N 1) (N - 2 + 1) :=
                ca_step_add_at_replicate_one N (N - 2) (by dsimp [N]; omega)
              have h_eq2 : N - 2 + 1 = N - 1 := by omega
              rw [h_eq2] at h_eq1
              exact h_eq1
            have h_not_stable : S (a N + 1) (N + 1) ≠ replicate (N + 1) 1 := by
              rw [h_stable_np1]
              exact add_at_replicate_one_ne N (N - 1) (by dsimp [N]; omega)
            have h_stable_at_an_p1 : S (a N + 1) (N + 1) = replicate (N + 1) 1 := by
              rw [← h_eq1_an]
              have h_nonempty : {k | S k (N + 1) = replicate (N + 1) 1}.Nonempty := S_set_nonempty (N + 1) (by omega)
              exact Nat.sInf_mem h_nonempty
            contradiction
          · -- i_prev = N - 3
            have h_stable_np1 : S (a N + 1) (N + 1) = add_at (replicate N 1) (N - 2) := by
              have h_step : S (a N + 1) (N + 1) = ca_step (S (a N) (N + 1)) := S_succ (a N) (N + 1)
              rw [h_step, hi_prev, h_stable_n, h_ip_nm3.2]
              have h_eq1 : ca_step (add_at (replicate N 1) (N - 3)) = add_at (replicate N 1) (N - 3 + 1) :=
                ca_step_add_at_replicate_one N (N - 3) (by dsimp [N]; omega)
              have h_eq2 : N - 3 + 1 = N - 2 := by omega
              rw [h_eq2] at h_eq1
              exact h_eq1
            have h_not_stable : S (a N + 1) (N + 1) ≠ replicate (N + 1) 1 := by
              rw [h_stable_np1]
              exact add_at_replicate_one_ne N (N - 2) (by dsimp [N]; omega)
            have h_stable_at_an_p1 : S (a N + 1) (N + 1) = replicate (N + 1) 1 := by
              rw [← h_eq1_an]
              have h_nonempty : {k | S k (N + 1) = replicate (N + 1) 1}.Nonempty := S_set_nonempty (N + 1) (by omega)
              exact Nat.sInf_mem h_nonempty
            contradiction
        · -- Case 2: a (N + 1) = a N + 2
          sorry
      have h_carry_N_k : ∀ k, ∀ m, a N + k ≥ a (N + 1) - 1 → S (a N + k) (N + 2) = add_at (S (a N + k) (N + 1)) m → m + 2 ≥ N := by
        intro k
        induction k with
        | zero =>
          intro m h_ge_T0 hm
          simp at hm
          have hm_eq : m = m_0 := by
            apply add_at_injective (S (a N) (N + 1)) m m_0
            rw [← hm, hm_0]
          subst hm_eq
          exact h_ge_m0
        | succ k ih =>
          intro m h_ge_T0 hm
          rcases S_add_at_index_le (N + 1) (a N + k) (by omega) with ⟨m_k, hm_k_le, hm_k⟩
          have h_cases_st : a (N + 1) ≤ a N + k ∨ a (N + 1) > a N + k := by omega
          rcases h_cases_st with h_st | h_not_st
          · have h_stable : S (a N + k) (N + 1) = replicate (N + 1) 1 := by
              apply stable_steps_upward_closed (N + 1) (a (N + 1)) (a N + k)
              · have h_a_eq : a (N + 1) = sInf {k | S k (N + 1) = replicate (N + 1) 1} := a_eq_sInf (N + 1) (by omega)
                rw [h_a_eq]
                have h_nonempty : {k | S k (N + 1) = replicate (N + 1) 1}.Nonempty := S_set_nonempty (N + 1) (by omega)
                exact Nat.sInf_mem h_nonempty
              · exact h_st
            have h_cases : m_k = N + 1 ∨ m_k < N + 1 := by omega
            rcases h_cases with h_mk_eq | h_mk_lt
            · -- m_k = N + 1
              have hm_k2 := hm_k
              rw [h_mk_eq] at hm_k2
              have h_st_k : S (a N + k) (N + 2) = replicate (N + 2) 1 := by
                rw [hm_k2, h_stable, add_at_replicate_one_self]
              have h_st_succ : S (a N + k + 1) (N + 2) = replicate (N + 2) 1 := by
                apply stable_steps_upward_closed (N + 2) (a N + k) (a N + k + 1) h_st_k (by omega)
              have hm_simplified := hm
              have h_assoc : a N + (k + 1) = a N + k + 1 := by omega
              rw [h_assoc] at hm_simplified
              rw [h_st_succ] at hm_simplified
              have h_stable_t : S (a N + k + 1) (N + 1) = replicate (N + 1) 1 := by
                apply stable_steps_upward_closed (N + 1) (a (N + 1)) (a N + k + 1)
                · have h_a_eq : a (N + 1) = sInf {k | S k (N + 1) = replicate (N + 1) 1} := a_eq_sInf (N + 1) (by omega)
                  rw [h_a_eq]
                  have h_nonempty : {k | S k (N + 1) = replicate (N + 1) 1}.Nonempty := S_set_nonempty (N + 1) (by omega)
                  exact Nat.sInf_mem h_nonempty
                · omega
              rw [h_stable_t] at hm_simplified
              have h_eq_m : m = N + 1 := by
                apply add_at_injective (replicate (N + 1) 1) m (N + 1)
                rw [← add_at_replicate_one_self (N + 1)] at hm_simplified
                exact hm_simplified.symm
              omega
            · have h_ih := ih m_k (by omega) hm_k
              have h_ge : m ≥ m_k := by
                have h_lt : m_k < (S (a N + k) (N + 1)).length := by
                  rw [h_stable]
                  simp
                  omega
                apply S_index_mono_step (N + 1) (a N + k) m_k m hm_k hm h_lt
              omega
          · -- h_not_st : a (N + 1) > a N + k
            have h_k_le_one : k = 0 ∨ k = 1 := by omega
            rcases h_k_le_one with rfl | rfl
            · have h_cases_an : a (N + 1) = a N + 1 ∨ a (N + 1) = a N + 2 := by
                have h_le_an : a (N + 1) ≤ a N + 2 := h_part1
                have h_ge_an : a (N + 1) ≥ a N + 1 := a_ge_add_one N hN_nz
                omega
              rcases h_cases_an with h1 | h2
              · -- Case 1: a (N + 1) = a N + 1
                have hi_prev_lt : i_prev < N := by
                  by_contra h_ge
                  have h_eq : i_prev = N := by omega
                  have h_eq_st : S (a N) (N + 1) = replicate (N + 1) 1 := by
                    rw [hi_prev, h_stable_n, h_eq, add_at_replicate_one_self]
                  have h_le_inf : a (N + 1) ≤ a N := by
                    rw [a_eq_sInf (N + 1) (by omega)]
                    apply Nat.sInf_le
                    exact h_eq_st
                  have h_not_st_simp : a (N + 1) > a N := by omega
                  omega
                have h_ge_prev : N ≤ m_k + 2 := by
                  apply ih m_k
                  · change a N + 0 ≥ a (N + 1) - 1
                    omega
                  · exact hm_k
                have h_cases_mk : m_k < N ∨ m_k ≥ N := by omega
                rcases h_cases_mk with h_mk_lt_n | h_mk_ge_n
                · have h_ge : m_k ≤ m := by
                    have h_lt : m_k < (S (a N) (N + 1)).length := by
                      rw [hi_prev]
                      rw [add_at_length]
                      rw [h_stable_n]
                      simp only [List.length_replicate]
                      rw [Nat.max_eq_left (by omega)]
                      omega
                    apply S_index_mono_step (N + 1) (a N) m_k m hm_k hm h_lt
                  omega
                · have h_len : (S (a N) (N + 1)).length ≤ N := by
                    rw [hi_prev]
                    rw [add_at_length]
                    rw [h_stable_n]
                    simp only [List.length_replicate]
                    rw [Nat.max_eq_left hi_prev_lt]
                  have hm_k_eq : S (a N) (N + 2) = add_at (S (a N) (N + 1)) m_k := hm_k
                  have hm_k_le_n : m_k ≤ N := by
                    apply m_le_n_of_S N (a N + 1) m_k (by dsimp [N]; omega) h_len hm_k hm_k_le
                  have h_mk_eq_n : m_k = N := by omega
                  have h_carry_prev : i_prev + 2 ≥ N - 1 := h_carry_np1 (a N) (by omega) i_prev hi_prev
                  have h_i_prev_cases : i_prev = N - 1 ∨ i_prev = N - 2 ∨ (N ≥ 3 ∧ i_prev = N - 3) := by dsimp [N]; omega
                  rcases h_i_prev_cases with h_ip_nm1 | h_ip_nm2 | h_ip_nm3
                  · have h_stable_np1 : S (a N + 1) (N + 1) = replicate (N + 1) 1 := by
                      have h_step : S (a N + 1) (N + 1) = ca_step (S (a N) (N + 1)) := S_succ (a N) (N + 1)
                      rw [h_step, hi_prev, h_stable_n, h_ip_nm1]
                      have h_eq1 : ca_step (add_at (replicate N 1) (N - 1)) = add_at (replicate N 1) (N - 1 + 1) :=
                        ca_step_add_at_replicate_one N (N - 1) (by dsimp [N]; omega)
                      have h_eq2 : N - 1 + 1 = N := by omega
                      rw [h_eq2] at h_eq1
                      rw [h_eq1]
                      exact add_at_replicate_one_self N
                    have h_stable_np2 : S (a N + 1) (N + 2) = add_at (replicate (N + 1) 1) N := by
                      rw [S_succ (a N) (N + 2), hm_k_eq, hi_prev, h_stable_n, h_ip_nm1, h_mk_eq_n]
                      exact ca_step_add_at_add_at_replicate_one_special2 N (by dsimp [N]; omega)
                    have h_eq_m : m = N := by
                      apply add_at_injective (replicate (N + 1) 1) m N
                      have hm_rewritten := hm
                      rw [h_stable_np1] at hm_rewritten
                      rw [← hm_rewritten, h_stable_np2]
                    omega
                  · have h_stable_np1 : S (a N + 1) (N + 1) = add_at (replicate N 1) (N - 1) := by
                      have h_step : S (a N + 1) (N + 1) = ca_step (S (a N) (N + 1)) := S_succ (a N) (N + 1)
                      rw [h_step, hi_prev, h_stable_n, h_ip_nm2]
                      have h_eq1 : ca_step (add_at (replicate N 1) (N - 2)) = add_at (replicate N 1) (N - 2 + 1) :=
                        ca_step_add_at_replicate_one N (N - 2) (by dsimp [N]; omega)
                      have h_eq2 : N - 2 + 1 = N - 1 := by omega
                      rw [h_eq2] at h_eq1
                      exact h_eq1
                    have h_calc : ca_step (add_at (add_at (replicate N 1) (N - 2)) N) = add_at (add_at (replicate N 1) (N - 1)) N :=
                      ca_step_add_at_add_at_replicate_one_special N (by dsimp [N]; omega)
                    have h_calc2 : S (a N + 1) (N + 2) = add_at (add_at (replicate N 1) (N - 1)) N := by
                      rw [S_succ (a N) (N + 2), hm_k_eq, hi_prev, h_stable_n, h_ip_nm2, h_mk_eq_n]
                      exact h_calc
                    have h_eq_m : m = N := by
                      apply add_at_injective (add_at (replicate N 1) (N - 1)) m N
                      have h_rewritten := h_calc2
                      rw [hm, h_stable_np1] at h_rewritten
                      exact h_rewritten
                    omega
                  · have hN_ge_3 : N ≥ 3 := h_ip_nm3.1
                    have h_ip_nm3_eq : i_prev = N - 3 := h_ip_nm3.2
                    have h_eq_st : S (a N + 2) (N + 1) = replicate (N + 1) 1 := by
                      apply stable_steps_upward_closed (N + 1) (a (N + 1)) (a N + 2)
                      · have h_a_eq : a (N + 1) = sInf {k | S k (N + 1) = replicate (N + 1) 1} := a_eq_sInf (N + 1) (by dsimp [N] at *; omega)
                        rw [h_a_eq]
                        have h_nonempty : {k | S k (N + 1) = replicate (N + 1) 1}.Nonempty := S_set_nonempty (N + 1) (by dsimp [N] at *; omega)
                        exact Nat.sInf_mem h_nonempty
                      · exact h_part1
                    have h_calc : S (a N + 2) (N + 1) = add_at (replicate N 1) (N - 1) := by
                      rw [S_succ (a N + 1) (N + 1), S_succ (a N) (N + 1), hi_prev, h_stable_n, h_ip_nm3_eq]
                      have h_eq1 : ca_step (add_at (replicate N 1) (N - 3)) = add_at (replicate N 1) (N - 3 + 1) :=
                        ca_step_add_at_replicate_one N (N - 3) (by dsimp [N] at *; omega)
                      have h_eq2 : N - 3 + 1 = N - 2 := by omega
                      rw [h_eq2] at h_eq1
                      rw [h_eq1]
                      have h_eq3 : ca_step (add_at (replicate N 1) (N - 2)) = add_at (replicate N 1) (N - 2 + 1) :=
                        ca_step_add_at_replicate_one N (N - 2) (by dsimp [N]; omega)
                      have h_eq4 : N - 2 + 1 = N - 1 := by dsimp [N]; omega
                      rw [h_eq4] at h_eq3
                      exact h_eq3
                    rw [h_calc] at h_eq_st
                    have h_len_eq : (add_at (replicate N 1) (N - 1)).length = (replicate (N + 1) 1).length := by
                      rw [h_eq_st]
                    rw [add_at_length] at h_len_eq
                    simp only [List.length_replicate] at h_len_eq
                    rw [Nat.max_eq_left (by dsimp [N]; omega)] at h_len_eq
                    omega
              · -- Case 2: a (N + 1) = a N + 2
                have h_mk_eq_m0 : m_k = m_0 := by
                  apply add_at_injective (S (a N) (N + 1)) m_k m_0
                  rw [← hm_k, hm_0]
                have h_len : (S (a N) (N + 1)).length ≤ N := by
                  rw [hi_prev]
                  rw [add_at_length]
                  rw [h_stable_n]
                  simp only [List.length_replicate]
                  rw [Nat.max_eq_left h_ip_lt]
                have hm_k_le_n : m_k ≤ N := by
                  rw [h_mk_eq_m0]
                  apply m_le_n_of_S N (a N + 1) m_0 (by dsimp [N]; omega) h_len hm_0 hm_0_le
                have h_cases_mk : m_k < N ∨ m_k = N := by omega
                rcases h_cases_mk with h_mk_lt_n | rfl
                · have h_ge : m ≥ m_k := by
                    have h_lt : m_k < (S (a N) (N + 1)).length := by
                      rw [hi_prev]
                      rw [add_at_length]
                      rw [h_stable_n]
                      simp only [List.length_replicate]
                      rw [Nat.max_eq_left h_ip_lt]
                      exact h_mk_lt_n
                    apply S_index_mono_step (N + 1) (a N) m_k m hm_k hm h_lt
                  have h_ge_m0_rewritten : m_k + 2 ≥ N := by
                    rw [h_mk_eq_m0]
                    exact h_ge_m0
                  omega
                · -- m_k = N
                  sorry
            · have h_ge_prev : N ≤ m_k + 2 := ih m_k (by omega) hm_k
              have h_cases_mk : m_k < N ∨ m_k ≥ N := by dsimp [N]; omega
              rcases h_cases_mk with h_mk_lt_n | h_mk_ge_n
              · have h_ge : m_k ≤ m := by
                  have h_lt : m_k < (S (a N + 1) (N + 1)).length := by
                    rcases S_add_at_index_le N (a N + 1) (by dsimp [N]; omega) with ⟨i_1, hi_1_le, hi_1⟩
                    have h_stable_n : S (a N + 1) N = replicate N 1 := by
                      apply stable_steps_upward_closed N (a N) (a N + 1)
                      · have h_a_eq : a N = sInf {k | S k N = replicate N 1} := a_eq_sInf N (by dsimp [N]; omega)
                        rw [h_a_eq]
                        exact Nat.sInf_mem (S_set_nonempty N (by dsimp [N]; omega))
                      · dsimp [N]; omega
                    rw [hi_1]
                    rw [add_at_length]
                    rw [h_stable_n]
                    simp only [List.length_replicate]
                    have hi_1_lt : i_1 < N := by
                      by_contra h_ge'
                      have h_eq' : i_1 = N := by dsimp [N]; omega
                      have h_eq_st : S (a N + 1) (N + 1) = replicate (N + 1) 1 := by
                        rw [hi_1, h_stable_n, h_eq', add_at_replicate_one_self]
                      have h_le_an : a (N + 1) ≤ a N + 1 := by
                        rw [a_eq_sInf (N + 1) (by dsimp [N]; omega)]
                        apply Nat.sInf_le
                        exact h_eq_st
                      have h_not_st_simp : a (N + 1) > a N + 1 := h_not_st
                      omega
                    rw [Nat.max_eq_left hi_1_lt]
                    omega
                  apply S_index_mono_step (N + 1) (a N + 1) m_k m hm_k hm h_lt
                dsimp [N]; omega
              · have h_stable_n : S (a N + 1) N = replicate N 1 := by
                  apply stable_steps_upward_closed N (a N) (a N + 1)
                  · have h_a_eq : a N = sInf {k | S k N = replicate N 1} := a_eq_sInf N (by dsimp [N]; omega)
                    rw [h_a_eq]
                    exact Nat.sInf_mem (S_set_nonempty N (by dsimp [N]; omega))
                  · dsimp [N] at *; omega
                rcases S_add_at_index_le N (a N + 1) (by dsimp [N]; omega) with ⟨i_1, hi_1_le, hi_1⟩
                have hi_1_lt : i_1 < N := by
                  by_contra h_ge
                  have h_eq : i_1 = N := by dsimp [N]; omega
                  have h_eq_st : S (a N + 1) (N + 1) = replicate (N + 1) 1 := by
                    rw [hi_1, h_stable_n, h_eq, add_at_replicate_one_self]
                  have h_le_an : a (N + 1) ≤ a N + 1 := by
                    rw [a_eq_sInf (N + 1) (by dsimp [N]; omega)]
                    apply Nat.sInf_le
                    exact h_eq_st
                  have h_not_st_simp : a (N + 1) > a N + 1 := h_not_st
                  omega
                have h_len : (S (a N + 1) (N + 1)).length ≤ N := by
                  rw [hi_1]
                  rw [add_at_length]
                  rw [h_stable_n]
                  simp only [List.length_replicate]
                  rw [Nat.max_eq_left hi_1_lt]
                have hm_k_le_n : m_k ≤ N := by
                  apply m_le_n_of_S N (a N + 2) m_k (by dsimp [N]; omega) h_len hm_k hm_k_le
                have h_mk_eq_n : m_k = N := by dsimp [N]; omega
                have h_carry_prev : i_1 + 2 ≥ N - 1 := h_carry_np1 (a N + 1) (by dsimp [N] at *; omega) i_1 hi_1
                have h_i_1_cases : i_1 = N - 1 ∨ i_1 = N - 2 ∨ (N ≥ 3 ∧ i_1 = N - 3) := by dsimp [N]; omega
                rcases h_i_1_cases with h_i1_nm1 | h_i1_nm2 | h_i1_nm3
                · have h_stable_np1 : S (a N + 2) (N + 1) = replicate (N + 1) 1 := by
                    have h_step : S (a N + 2) (N + 1) = ca_step (S (a N + 1) (N + 1)) := S_succ (a N + 1) (N + 1)
                    rw [h_step, hi_1, h_stable_n, h_i1_nm1]
                    have h_eq1 : ca_step (add_at (replicate N 1) (N - 1)) = add_at (replicate N 1) (N - 1 + 1) :=
                      ca_step_add_at_replicate_one N (N - 1) (by dsimp [N]; omega)
                    rw [h_eq1]
                    exact add_at_replicate_one_self N
                  have h_stable_np2 : S (a N + 2) (N + 2) = add_at (replicate (N + 1) 1) N := by
                    rw [S_succ (a N + 1) (N + 2), hm_k, hi_1, h_stable_n, h_i1_nm1, h_mk_eq_n]
                    exact ca_step_add_at_add_at_replicate_one_special2 N (by dsimp [N]; omega)
                  have h_eq_m : m = N := by
                    apply add_at_injective (replicate (N + 1) 1) m N
                    have hm_rewritten := hm
                    rw [h_stable_np1] at hm_rewritten
                    rw [← hm_rewritten, h_stable_np2]
                  omega
                · have h_eq_st : S (a N + 2) (N + 1) = replicate (N + 1) 1 := by
                    apply stable_steps_upward_closed (N + 1) (a (N + 1)) (a N + 2)
                    · have h_a_eq : a (N + 1) = sInf {k | S k (N + 1) = replicate (N + 1) 1} := a_eq_sInf (N + 1) (by dsimp [N] at *; omega)
                      rw [h_a_eq]
                      have h_nonempty : {k | S k (N + 1) = replicate (N + 1) 1}.Nonempty := S_set_nonempty (N + 1) (by dsimp [N] at *; omega)
                      exact Nat.sInf_mem h_nonempty
                    · dsimp [N] at *; omega
                  have h_calc : S (a N + 2) (N + 1) = add_at (replicate N 1) (N - 1) := by
                    have h_step : S (a N + 2) (N + 1) = ca_step (S (a N + 1) (N + 1)) := S_succ (a N + 1) (N + 1)
                    rw [h_step, hi_1, h_stable_n, h_i1_nm2]
                    have h_eq1 : ca_step (add_at (replicate N 1) (N - 2)) = add_at (replicate N 1) (N - 2 + 1) :=
                      ca_step_add_at_replicate_one N (N - 2) (by dsimp [N]; omega)
                    have h_eq2 : N - 2 + 1 = N - 1 := by omega
                    rw [h_eq2] at h_eq1
                    exact h_eq1
                  rw [h_calc] at h_eq_st
                  have h_len_eq : (add_at (replicate N 1) (N - 1)).length = (replicate (N + 1) 1).length := by
                    rw [h_eq_st]
                  rw [add_at_length] at h_len_eq
                  simp only [List.length_replicate] at h_len_eq
                  rw [Nat.max_eq_left (by dsimp [N] at *; omega)] at h_len_eq
                  omega
                · have hN_ge_3 : N ≥ 3 := h_i1_nm3.1
                  have h_i1_nm3_eq : i_1 = N - 3 := h_i1_nm3.2
                  have h_eq_st : S (a N + 2) (N + 1) = replicate (N + 1) 1 := by
                    apply stable_steps_upward_closed (N + 1) (a (N + 1)) (a N + 2)
                    · have h_a_eq : a (N + 1) = sInf {k | S k (N + 1) = replicate (N + 1) 1} := a_eq_sInf (N + 1) (by dsimp [N] at *; omega)
                      rw [h_a_eq]
                      have h_nonempty : {k | S k (N + 1) = replicate (N + 1) 1}.Nonempty := S_set_nonempty (N + 1) (by dsimp [N] at *; omega)
                      exact Nat.sInf_mem h_nonempty
                    · dsimp [N] at *; omega
                  have h_calc : S (a N + 2) (N + 1) = add_at (replicate N 1) (N - 2) := by
                    have h_step : S (a N + 2) (N + 1) = ca_step (S (a N + 1) (N + 1)) := S_succ (a N + 1) (N + 1)
                    rw [h_step, hi_1, h_stable_n, h_i1_nm3_eq]
                    have h_eq1 : ca_step (add_at (replicate N 1) (N - 3)) = add_at (replicate N 1) (N - 3 + 1) :=
                      ca_step_add_at_replicate_one N (N - 3) (by dsimp [N] at *; omega)
                    have h_eq2 : N - 3 + 1 = N - 2 := by omega
                    rw [h_eq2] at h_eq1
                    exact h_eq1
                  rw [h_calc] at h_eq_st
                  have h_len_eq : (add_at (replicate N 1) (N - 2)).length = (replicate (N + 1) 1).length := by
                    rw [h_eq_st]
                  rw [add_at_length] at h_len_eq
                  simp only [List.length_replicate] at h_len_eq
                  rw [Nat.max_eq_left (by dsimp [N]; omega)] at h_len_eq
                  omega
      have h_carry_N : ∀ t ≥ a (N + 1) - 1, ∀ m, S t (N + 2) = add_at (S t (N + 1)) m → m + 2 ≥ N := by
        intro t ht m hm
        have h_ge1 : a (N + 1) ≥ a N + 1 := a_ge_add_one N hN_nz
        have h_ge := h_carry_N_k (t - a N) m
        have h_index_eq : a N + (t - a N) = t := by omega
        rw [h_index_eq] at h_ge
        apply h_ge ht hm
      constructor
      · exact h_part1
      · exact h_carry_N

lemma a_le_add_two_helper (n : ℕ) (hn : n ≠ 0) :
  a (n + 1) ≤ a n + 2 ∧
  (∀ t ≥ a (n + 1) - 1, ∀ m, S t (n + 2) = add_at (S t (n + 1)) m → m + 2 ≥ n) := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    rcases n with _ | n'
    · -- n = 1
      constructor
      · rw [a_one, a_two]
        omega
      · intro t ht m hm
        omega
    · -- n >= 2
      exact a_le_add_two_step n' (by omega) (ih (by omega))

lemma carry_index_ge_of_ge_a_two (n : ℕ) (hn : n ≠ 0) (t : ℕ) (ht : t ≥ a (n + 1) - 1)
  (h_le : a (n + 1) ≤ a n + 2)
  (m : ℕ) (hm : S t (n + 2) = add_at (S t (n + 1)) m) :
  m + 2 ≥ n :=
  (a_le_add_two_helper n hn).2 t ht m hm

lemma a_le_add_two (n : ℕ) (hn : n ≠ 0) :
  a (n + 1) ≤ a n + 2 :=
  (a_le_add_two_helper n hn).1







theorem oeis_a300997_finite_difference_is_one_or_two :
  ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  intro n hn
  rcases n with _ | n
  · contradiction
  rcases n with _ | n
  · -- n = 1
    rw [a_one, a_two]
    left
    rfl
  · have hn_nz : n + 2 ≠ 0 := by omega
    change a (n + 2 + 1) = a (n + 2) + 1 ∨ a (n + 2 + 1) = a (n + 2) + 2
    have h_le := a_le_add_two (n + 2) hn_nz
    have h_ge := a_ge_add_one (n + 2) hn_nz
    omega

#print axioms oeis_a300997_finite_difference_is_one_or_two
