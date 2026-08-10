import FormalConjectures.Util.ProblemImports

partial def loopNat (_ : Unit) : Nat := loopNat ()

-- Try defining proof by recursion on an opaque Nat; base still required.
def aux (P : Prop) : Nat → Prop
| 0 => True
| _+1 => P

-- No proof of aux at opaque Nat gives P unless can prove nonzero.
#check loopNat
#reduce loopNat ()

example (P : Prop) : aux P (loopNat ()) := by
  -- exact ? no
  unfold aux
  -- stuck
  sorry
