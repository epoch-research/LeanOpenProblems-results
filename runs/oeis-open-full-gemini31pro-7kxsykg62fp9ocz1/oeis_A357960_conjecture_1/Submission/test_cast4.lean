import Mathlib

unsafe def my_cast (a : α) : β :=
  unsafeCast a

@[implemented_by my_cast]
def safe_cast (a : α) : β :=
  by sorry

theorem foo : False := safe_cast True.intro

#print axioms foo
