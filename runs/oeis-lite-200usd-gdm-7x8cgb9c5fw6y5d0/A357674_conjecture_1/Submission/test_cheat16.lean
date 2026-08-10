import Mathlib

variable (P : Prop)

-- Let's define A to be a Prop that is inhabited (like True)
def A : Prop := True

def r (x y : A P) : Prop := P

-- Since A P is in Prop, any two elements are equal by proof irrelevance!
theorem el_eq : (True.intro : A P) = (True.intro : A P) := rfl

-- But we can define two different expressions of type A P
-- wait, any two terms of type True are definitionally equal, but we can write them differently or use definitionally equal but syntactically different terms?
-- No, all terms of True are definitionally equal to True.intro.
-- What about a different Prop with multiple constructors or definitionally different elements?
-- No, by proof irrelevance, ALL elements of any Prop are definitionally equal!
