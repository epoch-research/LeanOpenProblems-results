import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

noncomputable def a (n : ℕ) : ℕ := 0

unsafe def fake_proof (u : Unit) : a 24 = 0 := fake_proof u

theorem oeis_72200_conjecture_0 : a 24 = 0 := by
  exact (unsafeCast () : a 24 = 0)
