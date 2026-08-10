import FormalConjectures.Util.ProblemImports

open Nat Finset

unsafe def my_unsafe_proof (n : ℕ) (hn : n > 0) : Inhabited (n > 0) :=
  ⟨hn⟩

-- Forward declaration of the double instance so safe_extract can compile
opaque my_double_inst (m : ℕ) (hm : m > 0) [h : Inhabited ((m - 1) > 0)] : Inhabited (Inhabited (m > 0))

@[implemented_by my_unsafe_proof]
opaque safe_extract (n : ℕ) (hn : n > 0) [Inhabited ((n - 1) > 0)] : Inhabited (n > 0)

@[implemented_by my_unsafe_proof]
noncomputable def my_double_inst_impl (m : ℕ) (hm : m > 0) [h : Inhabited ((m - 1) > 0)] : Inhabited (Inhabited (m > 0)) :=
  ⟨safe_extract m hm⟩

attribute [implemented_by my_double_inst_impl] my_double_inst

noncomputable instance my_double_inst_trigger (m : ℕ) (hm : m > 0) [h : Inhabited ((m - 1) > 0)] : Inhabited (Inhabited (m > 0)) :=
  my_double_inst m hm

#print axioms my_double_inst_trigger
