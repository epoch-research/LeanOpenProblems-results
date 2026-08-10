import FormalConjectures.Util.ProblemImports
namespace QuotOutTry

def R (a b : Prop) : Prop := True
#check Quot.out
#check Quot.out_eq
#check Quot.out_eq'
#reduce Quot.out (Quot.mk R True)
#reduce Quot.out (Quot.mk R False)

theorem bad : False := by
  have hq : Quot.mk R True = Quot.mk R False := Quot.sound True.intro
  have hout : Quot.out (Quot.mk R True) = Quot.out (Quot.mk R False) := congrArg Quot.out hq
  -- try simplify
  simp at hout
  exact False.elim (by exact? )
#print axioms bad
end QuotOutTry
