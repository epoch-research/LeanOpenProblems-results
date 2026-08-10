import FormalConjectures.Util.ProblemImports
axiom P : Prop

inductive MyRel : Prop → Prop → Prop where | mk : MyRel True False | refl (p) : MyRel p p

def qtrue : Quot MyRel := Quot.mk MyRel True
def qfalse : Quot MyRel := Quot.mk MyRel False

example : qtrue = qfalse := Quot.sound MyRel.mk

example : False := by
  have hq : qtrue = qfalse := Quot.sound MyRel.mk
  -- Try quotient exactness is not available
  -- show any simplification consequences
  have ht : Quot.lift (fun p : Prop => p) (by intro a b h; cases h <;> simp) qtrue := trivial
  -- cannot form lift because respects relation would need True=False case
  exact ht
