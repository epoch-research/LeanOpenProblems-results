import FormalConjecturesUtil

namespace CheckSpecType

def primeSet (α : ℝ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime ⌊(α * p)⌋₊}

set_option pp.explicit true in
#check (∀ α > 1, Irrational α → (primeSet α).Infinite)

example : (∀ α > 1, Irrational α → (primeSet α).Infinite) =
    (∀ α : ℝ, 1 < α → Irrational α →
      {p : ℕ | Nat.Prime p ∧ Nat.Prime ⌊α * (p : ℝ)⌋₊}.Infinite) := rfl

end CheckSpecType
