import FormalConjectures.Util.ProblemImports

def mem_fast (m : ℕ) : List ℕ → Bool
  | [] => false
  | x :: xs => (m == x) || mem_fast m xs

theorem mem_fast_iff (m : ℕ) (l : List ℕ) : mem_fast m l = true ↔ m ∈ l := by
  induction l with
  | nil =>
    simp [mem_fast]
  | cons x xs ih =>
    simp only [mem_fast, Bool.or_eq_true, beq_iff_eq, ih, List.mem_cons]
