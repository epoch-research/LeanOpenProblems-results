inductive Opt (p : Prop) : Type where
  | none : Opt p
  | some : p → Opt p

structure Bad (α : Type) : Type where
  β : Prop
  val : Opt β

inductive Ind (α : Type) (inst : Bad α) : Prop where
  | mk : (inst.β → False) → Ind α inst

def instActive : Nat → Bad Unit
  | 0 => ⟨False, Opt.none⟩
  | n + 1 => ⟨Ind Unit (instActive n), Opt.none⟩

mutual
  def val : (n : Nat) → Ind Unit (instActive n)
    | 0 => Ind.mk (fun x => x)
    | n + 1 => Ind.mk (unsound n)

  def unsound : (n : Nat) → Ind Unit (instActive n) → False
    | 0, y => unsound 1 (val 1)
    | n + 1, Ind.mk f => f (val n)
end
