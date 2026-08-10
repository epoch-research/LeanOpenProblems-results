inductive Opt (p : Prop) : Type where
  | none : Opt p
  | some : p → Opt p

structure Bad (α : Type) : Type where
  β : Prop
  val : Opt β

inductive Ind (α : Type) (inst : Bad α) : Prop where
  | mk : (inst.β → False) → Ind α inst

mutual
  def instActive : Nat → Bad Unit
    | 0 => ⟨False, Opt.none⟩
    | n + 1 => ⟨Ind Unit (instActive n), Opt.some (Ind.mk (unsound n))⟩

  def unsound : (n : Nat) → (instActive n).β → False
    | 0 => fun (x : False) => x
    | n + 1 => fun (y : Ind Unit (instActive n)) =>
        match y with
        | Ind.mk f => f (val_n n)

  def val_n : (k : Nat) → Ind Unit (instActive k)
    | k => match (instActive (k + 1)).val with
           | Opt.some x => x
end

def proof_of_false : False :=
  unsound 1 (val_n 0)
