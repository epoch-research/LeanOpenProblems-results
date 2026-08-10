import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

def MyType (n : Nat) : Type :=
  if n < 745 then
    Unit
  else if n = 745 then
    PLift (a 745 > 0)
  else
    PLift (a n > 0) ⊕ (PLift (a n = 0) × (a n = 0 → MyType (n - 1)))

instance (n : Nat) : Nonempty (PLift (a n > 0) ⊕ (PLift (a n > 0) → False)) := by
  by_cases h : a n > 0
  · exact ⟨Sum.inl (PLift.up h)⟩
  · exact ⟨Sum.inr (fun x => h x.down)⟩

partial def get_proof_either (n : Nat) (hn : n ≥ 745) (x : MyType n) : PLift (a n > 0) ⊕ (PLift (a n > 0) → False) :=
  get_proof_either n hn x
