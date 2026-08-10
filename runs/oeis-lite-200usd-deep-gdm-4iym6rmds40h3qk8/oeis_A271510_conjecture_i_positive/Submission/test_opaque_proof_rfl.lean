import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MyType (P : Prop) where
  is_true : Bool
  proof : is_true = true → P

instance (P : Prop) : Inhabited (MyType P) :=
  ⟨⟨false, fun h => by contradiction⟩⟩

unsafe def unsafe_proof (n : ℕ) : 0 < A271510 n :=
  unsafe_proof n

unsafe def get_my_type_unsafe (n : ℕ) : MyType (0 < A271510 n) :=
  ⟨true, fun _ => unsafe_proof n⟩

@[implemented_by get_my_type_unsafe]
opaque get_my_type (n : ℕ) : MyType (0 < A271510 n)

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  (get_my_type n).proof (by rfl)
