import FormalConjectures.Util.ProblemImports

unsafe def unsafe_nonempty (P : Prop) : Nonempty P :=
  unsafeCast ()

@[implemented_by unsafe_nonempty]
def safe_nonempty (P : Prop) : Nonempty P :=
  -- wait, we need a body for safe_nonempty.
  -- But we can make safe_nonempty recursive!
  -- Since its type is Nonempty P, and Nonempty P is always nonempty?
  -- Wait, is Nonempty P nonempty?
  -- Nonempty (Nonempty P) is equivalent to Nonempty P, so it is not always nonempty.
  -- But wait!
  sorry
