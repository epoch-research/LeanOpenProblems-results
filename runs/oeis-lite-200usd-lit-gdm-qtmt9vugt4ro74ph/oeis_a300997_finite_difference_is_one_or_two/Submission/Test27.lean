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

lemma exists_trim_trailing_zeros_replicate (L : List ℕ) :
  ∃ k, L = trim_trailing_zeros L ++ replicate k 0 := by
  rcases exists_replicate_dropWhile_eq (reverse L) with ⟨k, hk⟩
  use k
  have h_rev : reverse (reverse L) = L := reverse_reverse L
  have h_rev2 : reverse (replicate k 0 ++ (reverse L).dropWhile (fun x => x = 0)) = L := by
    rw [hk, h_rev]
  rw [reverse_append, reverse_replicate_zero] at h_rev2
  exact h_rev2.symm

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
      rw [trim_trailing_zeros_append_replicate_zero ((x + 1) :: xs) k]
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
            rfl
          rw [h_lhs]
          have h_rhs : trim_trailing_zeros (0 :: replicate xs.length 0) = [] := by
            have h_app : 0 :: replicate xs.length 0 = replicate (xs.length + 1) 0 := rfl
            rw [h_app, trim_trailing_zeros_replicate_zero]
          rw [h_rhs]
          rfl
        · -- x ≠ 0
          have h_lhs : trim_trailing_zeros ((x+1) :: replicate xs.length 0) = [x+1] := by
            have h_app : (x+1) :: replicate xs.length 0 = [x+1] ++ replicate xs.length 0 := rfl
            rw [h_app, trim_trailing_zeros_append_replicate_zero]
            rfl
          rw [h_lhs]
          have h_rhs : trim_trailing_zeros (x :: replicate xs.length 0) = [x] := by
            have h_app : x :: replicate xs.length 0 = [x] ++ replicate xs.length 0 := rfl
            rw [h_app, trim_trailing_zeros_append_replicate_zero]
            rfl
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
        have h_x_or : x = 0 ∨ x ≠ 0 := by omega
        rcases h_x_or with rfl | hx0
        · -- x = 0
          have h_rhs : trim_trailing_zeros (0 :: replicate xs.length 0) = [] := by
            have h_app : 0 :: replicate xs.length 0 = replicate (xs.length + 1) 0 := rfl
            rw [h_app, trim_trailing_zeros_replicate_zero]
          rw [h_rhs]
          rfl
        · -- x ≠ 0
          have h_rhs : trim_trailing_zeros (x :: replicate xs.length 0) = [x] := by
            have h_app : x :: replicate xs.length 0 = [x] ++ replicate xs.length 0 := rfl
            rw [h_app, trim_trailing_zeros_append_replicate_zero]
            rfl
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
