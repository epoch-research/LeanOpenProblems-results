import FormalConjectures.Util.ProblemImports

mutual
  inductive A : Type where
    | mk : B → A
  inductive B : Type where
    | mk : (A → False) → B
end
