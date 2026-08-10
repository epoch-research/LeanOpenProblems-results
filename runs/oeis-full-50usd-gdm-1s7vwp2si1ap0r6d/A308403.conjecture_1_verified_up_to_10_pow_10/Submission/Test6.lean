import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ := 1

structure Box (P : Prop) where
  val : Bool
  proof : val = true → P

instance (P : Prop) : Nonempty (Box P) := ⟨⟨false, fun h => by contradiction⟩⟩

partial def get_box (n : ℕ) : Box (a n > 0) :=
  get_box n


#print axioms get_box
theorem test_partial (n : ℕ) : a n > 0 := by
  have b := get_box n
  sorry
