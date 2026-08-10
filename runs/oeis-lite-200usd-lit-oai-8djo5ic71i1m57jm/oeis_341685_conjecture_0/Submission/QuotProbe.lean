import FormalConjectures.Util.ProblemImports
#check Quot.out
#check Quot.out_eq
#check Quot.out_eq'
#check Quot.exists_rep
#check Quot.ind
#check Quot.lift
#check Quot.sound

namespace QP

def r (p q : Prop) := p
example : Quot r := Quot.mk r True
#check (Quot.out_eq (Quot.mk r False))
#check (Quot.out_eq' (Quot.mk r False))

example : False := by
  let qF := Quot.mk r False
  let qT := Quot.mk r True
  have hEq : qT = qF := Quot.sound True.intro
  -- try suggestions
  have h1 := Quot.out_eq' qF
  have h2 := Quot.out_eq' qT
  dsimp [r] at h1 h2
  guard_target = False
  apply?
end QP
