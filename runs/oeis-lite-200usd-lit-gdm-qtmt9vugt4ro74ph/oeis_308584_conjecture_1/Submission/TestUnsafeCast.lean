import FormalConjectures.Util.ProblemImports

open Nat Finset

unsafe def my_cast {α β : Type} (a : α) : β :=
  unsafeCast a
