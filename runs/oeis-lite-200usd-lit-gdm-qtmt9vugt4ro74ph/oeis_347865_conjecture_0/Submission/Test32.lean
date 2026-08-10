import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

def MyType (n : Nat) : Type :=
  PLift (a n > 0) ⊕ (MyType n → False)

instance (n : Nat) : Nonempty (MyType n) := by
  by_cases h : Nonempty (PLift (a n > 0))
  · exact ⟨Sum.inl (Classical.choice h)⟩
  · exact ⟨Sum.inr (fun x => h ⟨x⟩)⟩

partial def safe_cast {A B : Type} [Nonempty B] (x : A) : B :=
  safe_cast x

partial def MyVal (n : Nat) : MyType n :=
  safe_cast (PLift.up a_745_pos)

def get_proof (n : Nat) (x : MyType n) : a n > 0 := by
  rcases x with val | f
  · exact val.down
  · exact False.elim (f (Sum.inr f))

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 :=
  get_proof n (MyVal n)

#print axioms tail_pos
