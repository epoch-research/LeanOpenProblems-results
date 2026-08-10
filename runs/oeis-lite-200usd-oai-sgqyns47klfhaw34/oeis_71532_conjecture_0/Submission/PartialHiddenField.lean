import FormalConjectures.Util.ProblemImports

structure W (P : Prop) where
  q : Prop
  hq : q → False
  hp : q → P

instance (P : Prop) : Nonempty (W P) := ⟨{ q := False, hq := id, hp := False.elim }⟩

partial def wLoop (P : Prop) : W P := wLoop P

-- Body tries to set q=True but use recursive fields.
partial def wBad (P : Prop) : W P :=
  { q := True
    hq := fun ht => (wBad P).hq ht
    hp := fun ht => (wBad P).hp ht }

#check wBad
#print axioms wBad
#reduce (wBad False).q

-- If projections unfold, this would be dangerous; try to prove q=True.
example (P : Prop) : (wBad P).q = True := by
  native_decide
