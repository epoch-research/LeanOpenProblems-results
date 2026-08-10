import FormalConjectures.Util.ProblemImports

open List Nat Function Set

def add_at : List ℕ → ℕ → List ℕ
  | [], 0 => [1]
  | [], i + 1 => 0 :: add_at [] i
  | x :: xs, 0 => (x + 1) :: xs
  | x :: xs, i + 1 => x :: add_at xs i

def half_ceil (m : ℕ) : ℕ := (m + 1) / 2
def half_floor (m : ℕ) : ℕ := m / 2

def ca_step_long (config : List ℕ) : List ℕ :=
  let base_masses := config.map half_ceil ++ [0]
  let received_masses := 0 :: config.map half_floor
  List.zipWith Nat.add base_masses received_masses

lemma ca_step_long_add_at (L : List ℕ) (i : ℕ) :
  ca_step_long (add_at L i) = add_at (ca_step_long L) i ∨
  ca_step_long (add_at L i) = add_at (ca_step_long L) (i + 1) := by
  sorry
