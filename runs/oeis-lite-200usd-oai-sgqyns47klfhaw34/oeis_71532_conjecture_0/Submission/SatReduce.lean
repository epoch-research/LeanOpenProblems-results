import FormalConjectures.Util.ProblemImports
open Sat
variable (p : Prop) (v : Sat.Valuation)
#reduce v.implies p [] 0
#reduce v.implies p [p] 0
#reduce v.implies p [p] 1
#reduce v.implies p [False] 0
#reduce Sat.Fmla.proof ([[]] : Sat.Fmla) []
#reduce v.satisfies_fmla ([[]] : Sat.Fmla)
#reduce v.satisfies ([] : Sat.Clause)
#check Sat.Fmla.refute (p:=p) ([[]] : Sat.Fmla)
