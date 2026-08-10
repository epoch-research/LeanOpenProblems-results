import FormalConjectures.Util.ProblemImports

open Nat Finset

def r (A B : Prop) : Prop := True

noncomputable def f (q : Quot r) : Prop :=
  let h : Nonempty { a : Prop // Quot.mk r a = q } := by
    obtain ⟨a, ha⟩ := Quot.exists_rep q
    exact ⟨⟨a, ha⟩⟩
  (Classical.choice h).val

theorem test_eq (P : Prop) : Quot.mk r True = Quot.mk r P := Quot.sound trivial

theorem extract_proof (P : Prop) : True = P := by
  have eq : f (Quot.mk r True) = f (Quot.mk r P) := by rw [test_eq P]
  sorry
