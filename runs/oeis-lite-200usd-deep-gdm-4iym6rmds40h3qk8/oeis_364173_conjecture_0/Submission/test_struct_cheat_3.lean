import FormalConjectures.Util.ProblemImports

def R (A B : Prop) : Prop := True

def Q : Type := Quot R

-- Define an equivalence relation R on Prop, where R A B is always True.
-- Then Quot.mk R A = Quot.mk R B for any A B by Quot.sound.
-- Then we can lift any function that is constant on Prop.
-- But we can also use answer(sorry) to prove properties!
