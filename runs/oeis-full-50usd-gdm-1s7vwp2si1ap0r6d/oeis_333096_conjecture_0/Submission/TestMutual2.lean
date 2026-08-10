mutual
  inductive Foo
  | mk : (Bar → Foo) → Foo
  inductive Bar
  | mk : (Foo → Bar) → Bar
end
