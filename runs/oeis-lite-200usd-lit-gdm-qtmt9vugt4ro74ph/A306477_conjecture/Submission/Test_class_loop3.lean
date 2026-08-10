class Bad where
  β : Prop

inductive Ind [inst : Bad] : Prop where
  | mk : (inst.β → False) → Ind

instance instActive (u : Unit) : Bad where
  β := @Ind (instActive u)
