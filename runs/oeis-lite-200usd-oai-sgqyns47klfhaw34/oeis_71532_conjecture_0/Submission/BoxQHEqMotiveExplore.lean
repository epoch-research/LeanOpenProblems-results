import FormalConjectures.Util.ProblemImports

def r (P Q : Prop) : Prop := True
abbrev Q := Quot r
def q (P : Prop) : Q := Quot.mk r P
inductive BoxQ : Q → Type where
| mk {P : Prop} (h : P) : BoxQ (q P)

def boxP (P : Prop) : BoxQ (q P) := by
  have hq : q True = q P := Quot.sound trivial
  exact hq ▸ BoxQ.mk trivial

theorem arbitrary (P : Prop) : P := by
  let b := boxP P
  have hb : b ≍ boxP P := HEq.rfl
  refine BoxQ.rec (motive := fun a t => t ≍ boxP P → P) ?minor b hb
  intro A h heq
  -- context: h : A, heq : HEq (BoxQ.mk h) (boxP P)
  trace_state
  -- Try cases heq
  cases heq
  trace_state
  exact h

#print axioms boxP
#print axioms arbitrary
