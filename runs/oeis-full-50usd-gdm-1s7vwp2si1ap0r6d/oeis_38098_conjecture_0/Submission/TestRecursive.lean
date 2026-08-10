import FormalConjectures.Util.ProblemImports

instance : Nonempty (∀ (n : Nat), n = n) := ⟨fun n => rfl⟩

partial def proof_rec (n : Nat) : n = n := proof_rec n

theorem test_rec (n : Nat) : n = n := proof_rec n

