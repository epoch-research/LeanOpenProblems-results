import Mathlib

-- Let's define a relation on Prop
def R (A B : Prop) : Prop := True

-- Is R an equivalence relation?
-- Let's define a quotient over Prop
-- Wait, Quot is defined for Type, not Prop. Let's see if we can define a Quot on Prop.
#check @Quot
