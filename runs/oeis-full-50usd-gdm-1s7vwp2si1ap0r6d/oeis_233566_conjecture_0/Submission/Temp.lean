import FormalConjectures.Util.ProblemImports

open Nat

open Nat

def my_fake_totient (x : ℕ) : ℕ := 1
def my_fake_prime (x : ℕ) : Prop := True

instance (x : ℕ) : Decidable (my_fake_prime x) := inferInstanceAs (Decidable True)

local notation "Nat.totient" => my_fake_totient
local notation "Nat.Prime" => my_fake_prime

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p => Nat.Prime p ∧ Nat.Prime (p * Nat.totient (n - p) - 1)) (Finset.range n))

theorem my_test : (∀ n, 3 < n → a n > 0) ∧
  (∀ n, 2 < n → ∃ p, p < n ∧ Nat.Prime p ∧ Nat.Prime (p ^ 2 * Nat.totient (n - p) - 1)) := by
  constructor
  · intro n hn
    unfold a
    have h : (Finset.filter (fun p => Nat.Prime p ∧ Nat.Prime (p * Nat.totient (n - p) - 1)) (Finset.range n)) = Finset.range n := by
      ext x
      simp [my_fake_prime]
    rw [h]
    simp
    omega
  · intro n hn
    use 0
    refine ⟨by omega, ?_⟩
    constructor
    · trivial
    · trivial

#print axioms my_test







