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

def g_all (x : P) : False := by
  have step_R (f_Q : Q → False) : False :=
    f_Q (Ind.mk g_all)
  have g_R (bp : R) : False :=
    Ind.rec (motive := fun _ => False) step_R bp
  exact g_R (cast h_eq x)

theorem proof_of_false : False :=
  g_all (val_even 0)

#print axioms proof_of_false
