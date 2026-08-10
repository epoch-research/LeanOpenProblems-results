import FormalConjectures.Util.ProblemImports
open Nat

def a (n : ℕ) : ℕ :=
  (Nat.factorization n).support.sum fun p =>
    2 ^ (Nat.primeCounting p - 1)

def T (x : ℕ) : Prop := ∃ k, (a^[k]) x = 0

def R (x y : ℕ) : Prop := T x ∧ ¬ T y

theorem R_wf : WellFounded R := by
  constructor
  intro x
  constructor
  intro y hy
  constructor
  intro z hz
  exact False.elim (hz.2 hy.1)

theorem oeis_87207_conjecture_0 : ∀ n : ℕ, ∃ k : ℕ, (a^[k]) n = 0 := by
  intro n
  have h_acc : Acc R n := R_wf.apply n
  induction' h_acc with x hx ih
  by_cases h_tx : T x
  · exact h_tx
  · sorry
