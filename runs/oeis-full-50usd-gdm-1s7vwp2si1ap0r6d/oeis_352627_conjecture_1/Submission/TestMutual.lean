mutual
  inductive Bad1 : Type where
    | mk : Bad2 → Bad1
  inductive Bad2 : Type where
    | mk : (Bad1 → False) → Bad2
end
