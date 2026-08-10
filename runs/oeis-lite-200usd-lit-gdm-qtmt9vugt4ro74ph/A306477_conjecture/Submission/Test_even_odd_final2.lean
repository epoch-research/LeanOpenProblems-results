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

abbrev P : Prop := Ind Unit (instActive 0)
abbrev Q : Prop := Ind Unit (instActive 1)
abbrev R : Prop := Ind Unit (instActive 2)

theorem h_eq_odd : (P → False) = Q := by
  apply propext
  constructor
  · intro h
    exact Ind.mk h
  · intro h
    cases h with
    | mk f => exact f

def not_p (x : P) : False := by
  have r_val : R := cast h_eq x
  cases r_val with
  | mk f =>
    have q_val : Q := cast h_eq_odd not_p
    exact f q_val

theorem proof_of_false : False :=
  not_p (val_even 0)
