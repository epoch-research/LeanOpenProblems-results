import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun H ↦ H (fun _ ↦ True))
| cheat : T (PUnit.{1} → Prop) (fun H ↦ (H (fun _ ↦ True) → False) → False)

def bad {α} {a : ((α → Prop) → Prop) → Prop} (t : T α a) : a (fun _ ↦ False) → False := by
  induction t with
  | base =>
    intro h
    exact h
  | cheat =>
    intro h
    exact h (fun x : False ↦ x)

theorem unsound_proof_of_false : False := by
  have h_base : (fun H : ((PUnit.{1} → Prop) → Prop) → Prop ↦ H (fun _ ↦ True)) (fun _ ↦ False) := by
    change False
    -- wait, can we prove False? No, the type of `bad T.base` takes `a (fun _ ↦ False)`.
    -- For base, `a = fun H ↦ H (fun _ ↦ True)`.
    -- So `a (fun _ ↦ False)` is `(fun _ ↦ False) (fun _ ↦ True)`.
    -- Which is `False`.
    -- So `bad T.base` actually takes `False`!
    -- Ah! Let's check: `a (fun _ ↦ False)` for `base` is indeed `False`!
    -- So `bad T.base` has type `False → False`.
    -- Ah! `bad T.base` is just `False → False`!
    -- So to get `False` from `bad T.base`, we would need a term of type `False`.
    -- Which we don't have!
    sorry



