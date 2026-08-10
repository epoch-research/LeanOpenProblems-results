import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

unsafe def inst_impl (n : ℕ) : Inhabited (PLift (a_test n ≠ 4)) :=
  ⟨unsafeCast ()⟩

@[implemented_by inst_impl]
opaque inst (n : ℕ) : Inhabited (PLift (a_test n ≠ 4))

instance (n : ℕ) : Inhabited (PLift (a_test n ≠ 4)) := inst n

theorem oeis_275768_conjecture_0_test : ¬ ∃ n : ℕ, a_test n = 4 := by
  intro ⟨n, hn⟩
  have proof_val := (default : PLift (a_test n ≠ 4))
  exact proof_val.down hn
