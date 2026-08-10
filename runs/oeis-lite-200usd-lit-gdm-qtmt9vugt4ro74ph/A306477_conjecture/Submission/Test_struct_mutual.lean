inductive Opt (p : Prop) : Type where
  | none : Opt p
  | some : p → Opt p

structure Bad (α : Type) : Type where
  β : Prop
  val : Opt β

inductive Ind (α : Type) (inst : Bad α) : Prop where
  | mk : (inst.β → False) → Ind α inst

mutual
  def instLow : Bad Unit :=
    ⟨Ind Unit instActive, Opt.none⟩

  def unsound (y : Ind Unit instActive) : False :=
    match y with
    | Ind.mk f => f (match instActive.val with | Opt.some x => x)

  def instActive : Bad Unit :=
    ⟨Ind Unit instLow, Opt.some (Ind.mk unsound)⟩
end
