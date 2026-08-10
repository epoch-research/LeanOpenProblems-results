mutual
  inductive Foo (α : Type 1) : Type 1
  | mk : Bar α → Foo α

  inductive Bar (α : Type 1) : Type 1
  | mk : (Foo α → α) → Bar α
end
