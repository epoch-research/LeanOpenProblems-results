import FormalConjectures.Util.ProblemImports

open Nat Finset

instance my_double_inhabited {α : Sort u} [h : Inhabited α] : Inhabited (Inhabited α) := ⟨h⟩

partial def loop_fallback (m : ℕ) (hm : m > 0) [Inhabited (m > 0)] : m > 0 :=
  loop_fallback m hm

partial def loop_fallback_inst (m : ℕ) (hm : m > 0) : Inhabited (m > 0) :=
  haveI : Inhabited (m > 0) := loop_fallback_inst m hm
  ⟨@loop_fallback m hm (by assumption)⟩

#print axioms loop_fallback_inst
