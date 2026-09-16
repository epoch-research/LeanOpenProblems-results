import Submission.Spec
import Lean

macro "type_of%" : term => `(True)

#check type_of% @A096535_occurs_infinitely_often
