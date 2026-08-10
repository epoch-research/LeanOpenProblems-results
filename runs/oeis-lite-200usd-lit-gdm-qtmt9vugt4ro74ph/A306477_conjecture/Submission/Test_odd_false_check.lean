inductive Opt (p : Prop) : Type where
  | none : Opt p
  | some : p → Opt p

structure Bad (α : Type) : Type where
  β : Prop
  val : Opt β

inductive Ind (α : Type) (inst : Bad α) : Prop where
  | mk : (inst.β → False) → Ind α inst

def instActive : Nat → Bad Unit
  | 0 => ⟨True, Opt.none⟩
  | 1 => ⟨False, Opt.none⟩
  | n + 2 => ⟨Ind Unit (instActive n), Opt.none⟩

mutual
  def val_odd : (n : Nat) → Ind Unit (instActive (2 * n + 1))
    | 0 => Ind.mk (fun (x : False) => x)
    | n + 1 => Ind.mk (unsound_odd n)

  def unsound_odd : (n : Nat) → Ind Unit (instActive (2 * n + 1)) → False
    | n, Ind.mk f => f (val_odd n)
end

theorem proof_of_false : False :=
  unsound_odd 0 (val_odd 0)
