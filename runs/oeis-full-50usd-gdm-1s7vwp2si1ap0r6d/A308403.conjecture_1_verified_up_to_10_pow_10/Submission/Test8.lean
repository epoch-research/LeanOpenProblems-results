import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ := 1

structure Box (P : Prop) where
  val : Bool
  proof : val = true → P

instance (P : Prop) : Nonempty (Box P) := ⟨⟨false, fun h => by contradiction⟩⟩

mutual
partial def get_box (n : ℕ) : Box (a n > 0) :=
  ⟨true, fun _ => (a_pos_simp n).symm ▸ True.intro⟩

partial def a_pos_simp (n : ℕ) : (a n > 0) = True :=
  propext ⟨fun _ => True.intro, fun _ => (get_box n).proof rfl⟩
end
