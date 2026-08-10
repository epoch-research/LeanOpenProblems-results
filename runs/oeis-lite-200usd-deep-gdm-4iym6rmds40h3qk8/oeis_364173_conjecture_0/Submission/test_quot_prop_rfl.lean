import FormalConjectures.Util.ProblemImports

def R (A B : True) : Prop := True

def Q : Prop := Quot R

theorem q_sound_rfl (A B : True) : Quot.mk R A = Quot.mk R B := rfl

