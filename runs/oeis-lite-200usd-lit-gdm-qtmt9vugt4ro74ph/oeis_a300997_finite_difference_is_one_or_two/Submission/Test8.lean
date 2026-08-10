import FormalConjectures.Util.ProblemImports

open List Nat Function Set

def add_at : List ℕ → ℕ → List ℕ
  | [], 0 => [1]
  | [], i + 1 => 0 :: add_at [] i
  | x :: xs, 0 => (x + 1) :: xs
  | x :: xs, i + 1 => x :: add_at xs i

def half_ceil (m : ℕ) : ℕ := (m + 1) / 2
def half_floor (m : ℕ) : ℕ := m / 2

def ca_step_carry : List ℕ → ℕ → List ℕ
  | [], c => [c]
  | x :: xs, c => (half_ceil x + c) :: ca_step_carry xs (half_floor x)

lemma ca_step_carry_eq (L : List ℕ) (c : ℕ) :
  ca_step_carry L c = zipWith Nat.add (map half_ceil L ++ [0]) (c :: map half_floor L) := by
  induction L generalizing c with
  | nil =>
    simp [ca_step_carry]
  | cons x xs ih =>
    simp [ca_step_carry, ih]
