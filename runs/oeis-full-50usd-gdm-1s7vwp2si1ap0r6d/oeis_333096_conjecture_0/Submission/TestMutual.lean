mutual
  inductive Bad1
  | mk1 : Bad2 → Bad1

  inductive Bad2
  | mk2 : (Bad1 → False) → Bad2
end
