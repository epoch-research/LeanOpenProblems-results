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

theorem h_eq_odd : (Ind Unit (instActive 0) → False) = Ind Unit (instActive 1) := by
  apply propext
  constructor
  · intro f
    exact Ind.mk f
  · intro y
    match y with
    | Ind.mk f => exact f

def my_term : (Ind Unit (instActive 0) → False) → False :=
  cast (by rw [h_eq_odd]) (unsound_odd 0)

def y_1 : Ind Unit (instActive 1) :=
  Ind.mk my_term

def proof_of_false : False :=
  my_term y_1
