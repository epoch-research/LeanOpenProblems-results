import FormalConjectures.Util.ProblemImports

structure IProp where
  P : Prop
  p : P

def allRel (_ _ : IProp) : Prop := True

def liftedProp : Quot allRel → Prop :=
  Quot.lift (fun x : IProp => x.P) (by
    intro x y h
    apply propext
    exact ⟨fun _ => y.p, fun _ => x.p⟩)

example : liftedProp (Quot.mk allRel ⟨True, trivial⟩) := by
  change True
  trivial

-- Try to force an arbitrary target via quotient equality: this should fail.
axiom Target : Prop
example : Target := by
  let q := Quot.mk allRel ⟨True, trivial⟩
  have hq : q = Quot.mk allRel ⟨True, trivial⟩ := rfl
  -- liftedProp q is true, not Target
  have hp : liftedProp q := by trivial
  exact ?_
