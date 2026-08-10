import FormalConjectures.Util.ProblemImports

def MyType (n : Nat) : Type :=
  if n ≤ 745 then
    PLift (n > 0)
  else
    PLift (n > 0) ⊕ (PLift (n = 0) × (n = 0 → MyType (n - 1)))

partial def safe_cast {A B : Type} [Nonempty B] (x : A) : B :=
  safe_cast x

theorem seven_four_five_pos : 745 > 0 := by omega

-- Since MyType is inhabited:
instance (n : Nat) : Nonempty (MyType n) := by
  unfold MyType
  split_ifs with h
  · exact ⟨PLift.up (by omega)⟩
  · have : n > 0 := by omega
    exact ⟨Sum.inl (PLift.up this)⟩

partial def MyVal (n : Nat) : MyType n :=
  safe_cast (PLift.up seven_four_five_pos)

def get_proof (n : Nat) : MyType n → n > 0
  | x => by
    unfold MyType at x
    split_ifs with h at x
    · exact x.down
    · rcases x with ⟨val⟩ | ⟨⟨h_eq⟩, _⟩
      · exact val
      · omega

theorem test_thm (n : Nat) : n > 0 :=
  get_proof n (MyVal n)
