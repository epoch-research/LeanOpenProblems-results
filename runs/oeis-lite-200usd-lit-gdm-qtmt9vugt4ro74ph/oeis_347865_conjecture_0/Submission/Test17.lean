import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

def MyType (n : Nat) : Type :=
  if n < 745 then
    Unit
  else if n = 745 then
    PLift (a 745 > 0)
  else
    PLift (a n > 0) ⊕ (PLift (a n = 0) × (a n = 0 → MyType (n - 1)))

instance (n : Nat) : Nonempty (PLift (a n > 0) ⊕ PLift (PLift (a n > 0) → False)) := by
  by_cases h : a n > 0
  · exact ⟨Sum.inl (PLift.up h)⟩
  · exact ⟨Sum.inr (PLift.up (fun x => h x.down))⟩

partial def safe_cast {A B : Type} [Nonempty B] (x : A) : B :=
  safe_cast x

partial def get_proof_either (n : Nat) (hn : n ≥ 745) (x : MyType n) : PLift (a n > 0) ⊕ PLift (PLift (a n > 0) → False) := by
  unfold MyType at x
  split at x
  · omega
  · split at x
    · rename_i h_eq
      subst h_eq
      exact Sum.inl x
    · rcases x with val | ⟨⟨h_eq⟩, h_rec⟩
      · exact Sum.inl val
      · have x' := h_rec h_eq
        have res_sub := get_proof_either (n - 1) (by omega) x'
        exact safe_cast res_sub
