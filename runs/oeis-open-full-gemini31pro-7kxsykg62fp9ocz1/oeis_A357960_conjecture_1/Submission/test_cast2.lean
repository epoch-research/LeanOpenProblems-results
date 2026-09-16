import Mathlib

unsafe def my_cast (a : α) : β :=
  unsafeCast a

-- can I do an unsafe theorem?
unsafe theorem foo : False := my_cast True.intro

