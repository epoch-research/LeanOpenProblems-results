inductive Bad2 : Type 1
| mk1 : (Type 0 → Bad2) → Bad2

mutual
  instance instBad2 : Inhabited Bad2 where
    default := Bad2.mk1 (fun _ => instBad2.default)
end
