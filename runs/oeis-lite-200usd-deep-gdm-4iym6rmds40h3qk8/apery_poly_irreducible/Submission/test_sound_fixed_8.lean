import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun H ↦ H (fun _ ↦ True))
| cheat : T (PUnit.{1} → Prop) (fun H ↦ H (fun _ ↦ True) → False)

theorem unsound {α : Type} {a : ((α → Prop) → Prop) → Prop} (t : T α a) : a (fun _ ↦ True) := by
  induction t with
  | base => exact True.intro
  | cheat =>
    intro h
    -- Wait, what is the goal in the `cheat` case?
    -- The goal is `a (fun _ ↦ True)` where `a = fun H ↦ H (fun _ ↦ True) → False`.
    -- So the goal is `(fun _ ↦ True) (fun _ ↦ True) → False`.
    -- Which is `True → False`.
    -- So `intro h` gives `h : True`. And the goal is `False`.
    -- Can we prove `False`?
    -- No! Because we only have `h : True`.
    sorry
