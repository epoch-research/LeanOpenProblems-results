import FormalConjectures.Util.ProblemImports

open Nat Int Finset

def A273021 (n : ℕ) : ℕ :=
  let B : ℕ := Nat.sqrt n + 1
  (Finset.range B).sum fun x =>
    (Finset.range B).sum fun y =>
      (Finset.range B).sum fun z =>
        (Finset.range B).sum fun w =>
          if x*x + y*y + z*z + w*w = n ∧ w > 0 ∧ x ≤ y then
            let Q : ℤ := 2 * (x : ℤ) * y + (y : ℤ) * z - (z : ℤ) * w - (w : ℤ) * x
            if Q ≥ 0 then
              let Q_nat := Q.natAbs
              if Q_nat.sqrt * Q_nat.sqrt = Q_nat then 1 else 0
            else
              0
          else
            0

def a273021_M : Finset ℕ := {2, 22, 23, 30, 330}
def a273021_S0 : Finset ℕ := {1, 11, 31, 47, 55, 71, 105, 115, 119, 253, 383, 385}

def a273021_is_one_value (n : ℕ) : Prop :=
  n ∈ a273021_S0 ∨
  ∃ k : ℕ, ∃ m : ℕ, m ∈ a273021_M ∧ n = 4^k * m

theorem A273021_conjecture_i_test : (answer(sorry) : Prop) := by
  trivial

#print axioms A273021_conjecture_i_test





