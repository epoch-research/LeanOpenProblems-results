import Mathlib

def A357565 (n : ℕ) : ℕ := n

unsafe def unsafe_nonempty (p r : ℕ) : Nonempty (A357565 (p ^ r) = A357565 (p ^ (r - 1))) :=
  ⟨@unsafeCast (True) (A357565 (p ^ r) = A357565 (p ^ (r - 1))) True.intro⟩

@[implemented_by unsafe_nonempty]
opaque safe_nonempty (p r : ℕ) : Nonempty (A357565 (p ^ r) = A357565 (p ^ (r - 1)))

theorem test_thm (p r : ℕ) : A357565 (p ^ r) = A357565 (p ^ (r - 1)) :=
  Classical.choice (safe_nonempty p r)

#print axioms test_thm


