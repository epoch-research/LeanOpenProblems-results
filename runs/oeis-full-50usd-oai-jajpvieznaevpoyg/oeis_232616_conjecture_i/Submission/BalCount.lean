import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Nat

def primeCountRange : Nat → Nat → Nat
  | lo, 0 => 0
  | lo, 1 => if Nat.Prime lo then 1 else 0
  | lo, len+2 =>
      let h := (len+2)/2
      primeCountRange lo h + primeCountRange (lo+h) (len+2-h)
termination_by lo len => len
decreasing_by
  · exact Nat.div_lt_self (Nat.succ_pos _) (by norm_num)
  · have hpos : 0 < (len + 2) / 2 := Nat.div_pos (by omega) (by norm_num)
    exact Nat.sub_lt (by omega) hpos

def primeCountBelow (N : Nat) := primeCountRange 0 N

#eval primeCountBelow 31
#eval primeCountBelow 8165753

-- theorem count_bal_rfl : primeCountBelow 8165753 = 550171 := rfl

theorem count_bal_test : primeCountBelow 8165753 = 550171 := by
  native_decide
#print axioms count_bal_test

theorem count_bal_test2 : primeCountBelow 8165753 = 550171 := by
  decide
#print axioms count_bal_test2
