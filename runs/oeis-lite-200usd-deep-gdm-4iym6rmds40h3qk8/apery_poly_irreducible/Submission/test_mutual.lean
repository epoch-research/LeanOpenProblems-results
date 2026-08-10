import FormalConjectures.Util.ProblemImports

mutual
inductive A : Type
| mk : B → A

inductive B : Type
| mk : (A → False) → B
end
