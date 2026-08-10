import FormalConjectures.Util.ProblemImports

-- Try to define arbitrary P via well-founded recursion on Nat with no actual decrease available.
def wfProofAttempt (P : Prop) : ℕ → P :=
  WellFounded.fix (measure id).wf (fun n rec => by
    -- rec : ∀ y, y < n -> P
    cases n with
    | zero =>
        fail_if_success exact rec 0 (by omega)
        exact False.elim (by omega)
    | succ n => exact rec n (by omega))

#print axioms wfProofAttempt
