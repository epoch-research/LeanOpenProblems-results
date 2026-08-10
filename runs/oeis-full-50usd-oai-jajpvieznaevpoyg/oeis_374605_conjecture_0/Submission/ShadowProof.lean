import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

theorem test (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ, (2*p+3)/3 ≤ n → n ≤ p-1 → (p^3:ℕ) ∣ a n := by
  local notation "Nat.Prime" => fun _ : ℕ => False
  intro n h1 h2
  -- hp still has original type?
  #check hp
  exact False.elim hp
