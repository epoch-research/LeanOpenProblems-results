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
      -- Case analysis on x % 2
      have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
      rcases hx with h_even | h_odd
      · left
        -- x even
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
        -- x odd
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
