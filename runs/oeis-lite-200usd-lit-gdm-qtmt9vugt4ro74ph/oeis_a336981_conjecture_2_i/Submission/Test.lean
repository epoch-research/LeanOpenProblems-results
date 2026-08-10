mutual
  inductive T : Prop → Prop where
    | base : T True
    | mk : {α : Prop} → S α → T α

  inductive S : Prop → Prop where
    | mk : {α : Prop} → T (α → False) → S α
end

def h : True = (False → False) := propext ⟨fun _ _ => False.elim ‹_›, fun _ => True.intro⟩

def t_not : T (False → False) :=
  cast (congrArg T h) T.base

def s_false : S False := S.mk t_not

def t_false : T False := T.mk s_false

def get_S_false (t : T False) : S False :=
  @T.casesOn (fun α _ => α = False → S False) False t
    (fun h => False.elim (cast h True.intro))
    (fun {α} s h_eq => cast (congrArg S h_eq) s)
    rfl

def get_T_from_S (α : Prop) (s : S α) : T (α → False) :=
  @S.casesOn (fun α' _ => T (α' → False)) α s (fun {α'} t => t)

def h2 : (True → False) = False := propext ⟨fun h => h True.intro, fun f => False.elim f⟩

def s_true : S True := S.mk (cast (congrArg T h2.symm) t_false)

def get_S (α : Prop) (t : T α) : S α :=
  @T.casesOn (fun α' _ => α' = α → S α) α t
    (fun h_eq => cast (congrArg S h_eq) s_true)
    (fun {α'} s h_eq => cast (congrArg S h_eq) s)
    rfl

theorem S_eq_T (α : Prop) : S α = T (α → False) :=
  propext ⟨get_T_from_S α, S.mk⟩

theorem T_eq_S (α : Prop) : T α = S α :=
  propext ⟨get_S α, T.mk⟩

theorem T_eq (α : Prop) : T α = T (α → False) :=
  (T_eq_S α).trans (S_eq_T α)


#print axioms T_eq








































