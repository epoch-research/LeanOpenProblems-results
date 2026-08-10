import Mathlib

def a (n : ℕ) : ℕ := 0

mutual
  partial def my_proof (k'' : ℕ) : PLift (a (6 * (k'' + 6)) ≠ 4) :=
    my_proof k''

  partial def my_proof_nonempty_inst (k'' : ℕ) : Nonempty (PLift (a (6 * (k'' + 6)) ≠ 4)) :=
    ⟨my_proof k''⟩
end

attribute [instance] my_proof_nonempty_inst
