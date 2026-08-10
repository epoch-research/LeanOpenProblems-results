def f {U : Type} (x : U) : U := x

def my_prop : Prop := True

#check f (True.intro)
