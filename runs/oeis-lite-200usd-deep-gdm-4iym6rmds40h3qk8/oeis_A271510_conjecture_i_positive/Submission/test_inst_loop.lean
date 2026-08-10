import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 1

unsafe def get_dec_unsafe (n : ℕ) : Decidable (0 < A271510 n) :=
  get_dec_unsafe n

@[implemented_by get_dec_unsafe]
opaque get_dec (n : ℕ) : Decidable (0 < A271510 n)

noncomputable instance inst (n : ℕ) : Inhabited (0 < A271510 n) :=
  match get_dec n with
  | Decidable.isTrue h => ⟨h⟩
  | Decidable.isFalse _ =>
    have : Inhabited (0 < A271510 n) := inst n
    this
