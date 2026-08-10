import FormalConjectures.Util.ProblemImports
#check Quot.sound
#check Quot.exact
#check Quot.eq
#check Quotient.exact
#check Quotient.sound

def R (_ _ : Unit) : Prop := False
example : Quot.mk R () = Quot.mk R () := rfl
-- example : False := Quot.exact (r := R) (rfl : Quot.mk R () = Quot.mk R ())
#check (Quot.exact (r := R) (rfl : Quot.mk R () = Quot.mk R ()))
