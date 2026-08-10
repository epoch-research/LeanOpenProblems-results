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
  | n + 1 => ⟨Ind Unit (instActive n), Opt.none⟩

mutual
  def val : (n : Nat) → Ind Unit (instActive (2 * n + 1))
    | n => Ind.mk (unsound n)

  def unsound : (n : Nat) → Ind Unit (instActive (2 * n)) → False
    | 0, Ind.mk f => f True.intro
    | n + 1, Ind.mk f => f (val n)
end

mutual
  def val_even : (n : Nat) → Ind Unit (instActive (2 * n))
    | 0 => Ind.mk (fun (_ : True) => unsound 0 (val 0))
    | n + 1 => Ind.mk (unsound_odd n)

  def unsound_odd : (n : Nat) → Ind Unit (instActive (2 * n + 1)) → False
    | n, Ind.mk f => f (val_even n)
end

theorem proof_of_false : False :=
  unsound 1 (val_even 1)



