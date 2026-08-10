mutual
  inductive Unsound : Prop
  | mk : Unsound2 → Unsound

  inductive Unsound2 : Prop
  | mk : (Unsound → Unsound) → Unsound2
end
