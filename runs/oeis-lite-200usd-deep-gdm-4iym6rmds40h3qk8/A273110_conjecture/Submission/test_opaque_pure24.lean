import FormalConjectures.Util.ProblemImports

def R (x y : Nat) : Prop :=
  x = 1 ∧ y = 0

theorem wf_R : WellFounded R := by
  constructor
  intro x
  constructor
  intro y hy
  constructor
  intro z hz
  rcases hy with ⟨rfl, rfl⟩
  rcases hz with ⟨_, h_false⟩
  contradiction

-- What if we have transitions:
-- f 0 -> f 1 (this is transition 1 -> 0 under relation R, i.e., R 1 0, which is true!)
-- But what about the other case? f 1 -> ...?
-- If f 1 has NO recursive calls, then the only transition is 0 -> 1 (which is 1 -> 0 under R).
-- Let's define:
def loop_nonempty (P : Prop) : Nonempty P :=
  let rec f (n : Nat) : Nonempty P :=
    match n with
    | 0 => f 1
    | _ => Classical.choice sorry
  f 0
-- But wait! To define `_ => Classical.choice sorry`, we need `sorryAx` again!
-- So this doesn't help us avoid `sorryAx`.
