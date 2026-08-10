class Bad where
  β : Prop

inductive Ind [inst : Bad] : Prop where
  | mk : (inst.β → False) → Ind

instance instLoop : Bad := ⟨@Ind instLoop⟩
