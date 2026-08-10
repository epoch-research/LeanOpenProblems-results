import FormalConjectures.Util.ProblemImports

def R (P Q : Prop) : Prop := True

def qtrue : Quot R := Quot.mk R True
def qfalse : Quot R := Quot.mk R False

-- Try dependent elimination into Prop
#check Quot.inductionOn
-- def val (q : Quot R) : Prop := Quot.inductionOn q (fun P : Prop => P)
-- theorem boom : False := by
--   have hq : qtrue = qfalse := Quot.sound trivial
--   change (Quot.inductionOn qfalse (fun P : Prop => P))
--   rw [← hq]
--   trivial
