inductive Opt (p : Prop) : Type where
  | none : Opt p
  | some : p → Opt p

structure Bad (α : Type) : Type where
  β : Prop
  val : Opt β

inductive Ind (α : Type) (inst : Bad α) : Prop where
  | mk : (inst.β → False) → Ind α inst

mutual
  def instActive : Bad Unit :=
    ⟨Ind Unit (instLow Unit), Opt.none⟩

  def instLow (α : Type) : Bad α :=
    ⟨Ind Unit instActive, Opt.some (Ind.mk unsound)⟩

  def unsound (y : Ind Unit instActive) : False :=
    match y with
    | Ind.mk f => f (match (instLow Unit).val with | Opt.some x => x)
end
