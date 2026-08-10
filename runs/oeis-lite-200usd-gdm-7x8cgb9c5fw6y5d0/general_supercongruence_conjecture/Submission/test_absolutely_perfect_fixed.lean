import FormalConjectures.Util.ProblemImports

inductive Bad : Prop → Prop where
| base {α : Prop} : (α → False) → False → Bad α
| mk {α : Prop} : Bad ((α → False) → False) → Bad α

def f : (α : Prop) → Bad α → (α → False) → False
| _, @Bad.base _ ha hf => fun _ => hf
| _, @Bad.mk α' h =>
  let recurse := f ((α' → False) → False) h
  fun (h1 : α' → False) => recurse (fun (h3 : (α' → False) → False) => h3 h1)
