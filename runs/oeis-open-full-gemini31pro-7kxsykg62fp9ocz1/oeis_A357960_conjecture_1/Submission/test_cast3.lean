import Mathlib

unsafe def my_cast (a : α) : β :=
  unsafeCast a

#print axioms my_cast
