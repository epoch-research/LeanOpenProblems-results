import FormalConjectures.Util.ProblemImports
open Nat

def check_range (f : ℕ → Bool) (start len : ℕ) : Bool :=
  match len with
  | 0 => true
  | l + 1 => f start && check_range f (start + 1) l

theorem check_range_iff (f : ℕ → Bool) (start len : ℕ) :
    check_range f start len = true ↔ ∀ i, start ≤ i ∧ i < start + len → f i = true := by
  induction len generalizing start with
  | zero =>
    simp [check_range]
  | succ len ih =>
    simp only [check_range, Bool.and_eq_true]
    rw [ih]
    constructor
    · intro ⟨h_start, h_rest⟩ i hi
      rcases hi with ⟨hi1, hi2⟩
      by_cases h_eq : i = start
      · subst h_eq; exact h_start
      · have : start + 1 ≤ i := by omega
        exact h_rest i ⟨by omega, by omega⟩
    · intro h
      constructor
      · exact h start ⟨by omega, by omega⟩
      · intro i hi
        exact h i ⟨by omega, by omega⟩

def check_range_2d (f : ℕ → Bool) (start num_blocks block_size : ℕ) : Bool :=
  match num_blocks with
  | 0 => true
  | b + 1 => check_range f start block_size && check_range_2d f (start + block_size) b block_size

theorem check_range_2d_iff (f : ℕ → Bool) (start num_blocks block_size : ℕ) :
    check_range_2d f start num_blocks block_size = true ↔ ∀ i, start ≤ i ∧ i < start + num_blocks * block_size → f i = true := by
  induction num_blocks generalizing start with
  | zero =>
    simp [check_range_2d]
  | succ num_blocks ih =>
    simp only [check_range_2d, Bool.and_eq_true]
    rw [check_range_iff, ih]
    simp only [add_mul, one_mul]
    constructor
    · intro ⟨h_block, h_rest⟩ i hi
      by_cases h_split : i < start + block_size
      · exact h_block i ⟨hi.1, h_split⟩
      · have : start + block_size ≤ i := by omega
        have h_rest_goal : start + block_size ≤ i ∧ i < start + block_size + num_blocks * block_size := by
          refine ⟨this, ?_⟩
          omega
        exact h_rest i h_rest_goal
    · intro h
      constructor
      · intro i hi
        exact h i ⟨hi.1, by omega⟩
      · intro i hi
        have h_goal : start ≤ i ∧ i < start + (num_blocks * block_size + block_size) := by
          refine ⟨by omega, ?_⟩
          omega
        exact h i h_goal
