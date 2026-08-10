import FormalConjectures.Util.ProblemImports

-- Raw Quot over universal relation on Prop
abbrev UQuot := @Quot Prop (fun _ _ => True)

def qtrue : UQuot := Quot.mk _ True
def qfalse : UQuot := Quot.mk _ False

example : qtrue = qfalse := Quot.sound trivial

-- Can equality of quotient classes force underlying relation only (trivial), not Prop equality.
example : True := Quot.exact (show qtrue = qfalse from Quot.sound trivial)

-- Try dependent rec to encode representative-sensitive Prop: rejected unless respects relation.
-- def badLift : UQuot → Prop := Quot.lift (fun P : Prop => P) (by intro a b h; exact propext ?_)

