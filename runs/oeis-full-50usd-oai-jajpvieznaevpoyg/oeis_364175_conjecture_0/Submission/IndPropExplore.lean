import FormalConjectures.Util.ProblemImports
inductive Loop : Prop where | intro : (Loop → Loop) → Loop
example : Loop := Loop.intro (fun x => x)
-- negative should fail:
inductive Bad : Prop where | intro : (Bad → False) → Bad
