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
  def val (n : Nat) : Ind Unit (instActive (2 * n + 1)) :=
    Ind.mk (unsound n)

  def unsound : (n : Nat) → Ind Unit (instActive (2 * n)) → False
    | 0, Ind.mk f => f True.intro
    | n + 1, Ind.mk f => f (val n)
end

mutual
  def val_even : (n : Nat) → Ind Unit (instActive (2 * n))
    | 0 => Ind.mk (fun (x : True) => x)  -- Wait! instActive 0 . β is True, so fun (x : True) => unsound 0 (val_even 0)? No, unsound 0 (val_even 0) has a cycle, but here we can just do fun (x : True) => unsound_odd 0 (Ind.mk (fun _ => ...))?
    -- Wait! In Test_even_odd_sub_check, instActive 0 . β was False!
    -- But here, instActive 0 . β is True!
    -- Since instActive 0 . β is True, val_even 0 needs a function of type True → False!
    -- So val_even 0 must be Ind.mk f where f : True → False.
    -- Can we construct a function of type True → False?
    | n + 1 => Ind.mk (unsound_odd n)

  def unsound_odd : (n : Nat) → Ind Unit (instActive (2 * n + 1)) → False
    | n, Ind.mk f => f (val_even n)
end
