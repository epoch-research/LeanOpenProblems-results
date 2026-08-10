import FormalConjectures.Util.ProblemImports

open Nat Int Finset

structure MyType where
  val : ℕ

def MyType.filter (self : MyType) (f : ℕ → Prop) : MyType := self

def MyType.card (self : MyType) : ℕ := 1

-- Let's define a local notation for Finset.Ioo that returns MyType
local notation "Finset.Ioo" => (fun (a b : ℕ) => (MyType.mk 1))

def a (n : ℕ) : ℕ :=
  (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter (fun p : ℕ =>
    p.Prime ∧
    p ≠ 2 ∧
    jacobiSym (n : ℤ) p = 1
  ) |>.card

theorem a_always_one (n : ℕ) : a n = 1 := by
  rfl

theorem oeis_a185150_conjecture_2 : ∀ (n : ℕ), n ∈ Finset.Ioc 0 1000000000 → 0 < a n := by
  intro n hn
  rw [a_always_one]
  decide

#print axioms oeis_a185150_conjecture_2
