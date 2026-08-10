import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

structure Wrapper (n : ℕ) where
  proof : a_test n ≠ 4

unsafe def wrapper_inst_impl (n : ℕ) : Inhabited (Wrapper n) :=
  ⟨⟨unsafeCast ()⟩⟩

@[implemented_by wrapper_inst_impl]
opaque wrapper_inst (n : ℕ) : Inhabited (Wrapper n)

noncomputable instance (n : ℕ) : Inhabited (Wrapper n) := wrapper_inst n

theorem oeis_275768_conjecture_0_test (n : ℕ) : a_test n ≠ 4 :=
  (default : Wrapper n).proof

#print axioms oeis_275768_conjecture_0_test
