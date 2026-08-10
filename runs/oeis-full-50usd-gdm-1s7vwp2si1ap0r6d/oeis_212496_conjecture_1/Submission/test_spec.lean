import FormalConjectures.Util.ProblemImports

mutual
  inductive A
    | mk : B → A
  inductive B
    | mk : (A → False) → B
end
