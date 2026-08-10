import FormalConjectures.Util.ProblemImports

open List Nat Function Set

def trim_trailing_zeros (l : List ℕ) : List ℕ :=
  (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

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
      -- Since y = 0, x must be in ys
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

def add_at : List ℕ → ℕ → List ℕ
  | [], 0 => [1]
  | [], i + 1 => 0 :: add_at [] i
  | x :: xs, 0 => (x + 1) :: xs
  | x :: xs, i + 1 => x :: add_at xs i

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
