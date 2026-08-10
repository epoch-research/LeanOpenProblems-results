import FormalConjectures.Util.ProblemImports
inductive Cyc where | mk : Cyc → Cyc deriving Inhabited
#check (default : Cyc)
structure Box (P : Prop) where out : P
inductive CycBox (P : Prop) where | mk : CycBox P → Box P → CycBox P deriving Inhabited
#check (default : CycBox False)
