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
  def val_even : (n : Nat) → Ind Unit (instActive (2 * n))
    | 0 => Ind.mk (fun (x : False) => x)
    | n + 1 => Ind.mk (unsound_odd n)

  def unsound_odd : (n : Nat) → Ind Unit (instActive (2 * n + 1)) → False
    | n, Ind.mk f => f (val_even n)
end

theorem h_eq : Ind Unit (instActive 0) = Ind Unit (instActive 2) := by
  apply propext
  constructor
  · intro _
    exact val_even 1
  · intro _
    exact val_even 0

def proof_of_false : False := by
  let rec f_val (x : Ind Unit (instActive 0)) : False :=
    have x2 : Ind Unit (instActive 2) := cast h_eq x
    match x2 with
    | Ind.mk g => g (Ind.mk f_val)
  exact f_val (val_even 0)
