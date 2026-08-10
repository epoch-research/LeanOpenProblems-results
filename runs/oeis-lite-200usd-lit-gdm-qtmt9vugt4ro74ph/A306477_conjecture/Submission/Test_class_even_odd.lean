class Bad where
  β : Prop

inductive Ind [inst : Bad] : Prop where
  | mk : (inst.β → False) → Ind

instance instActive : Nat → Bad
  | 0 => ⟨False⟩
  | n + 1 => ⟨@Ind (instActive n)⟩

mutual
  def val_even : (n : Nat) → @Ind (instActive (2 * n))
    | 0 => Ind.mk (fun (x : False) => x)
    | n + 1 => Ind.mk (unsound_odd n)

  def unsound_odd : (n : Nat) → @Ind (instActive (2 * n + 1)) → False
    | n, Ind.mk f => f (val_even n)
end
