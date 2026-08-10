class Bad where
  β : Prop

inductive Ind [inst : Bad] : Prop where
  | mk : (inst.β → False) → Ind

instance instActive : Nat → Bad
  | 0 => ⟨False⟩
  | n + 1 => ⟨@Ind (instActive n)⟩
