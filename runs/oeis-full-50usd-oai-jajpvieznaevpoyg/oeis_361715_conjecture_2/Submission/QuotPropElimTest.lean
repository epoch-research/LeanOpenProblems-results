import FormalConjectures.Util.ProblemImports

universe u

def badPred {α : Sort u} {r : α → α → Prop} (x : α) (P : Prop) (q : Quot r) : Prop :=
  match q with
  | Quot.mk _ a => if h : a = x then True else P

example (P : Prop) : P := by
  let α := Bool
  let r : α → α → Prop := fun _ _ => True
  let q0 : Quot r := Quot.mk r false
  let q1 : Quot r := Quot.mk r true
  have hq : q0 = q1 := Quot.sound trivial
  have ht : badPred false P q0 := by
    dsimp [badPred, q0]
    simp
  have hp : badPred false P q1 := by
    simpa [hq] using ht
  dsimp [badPred, q1] at hp
  simpa using hp
