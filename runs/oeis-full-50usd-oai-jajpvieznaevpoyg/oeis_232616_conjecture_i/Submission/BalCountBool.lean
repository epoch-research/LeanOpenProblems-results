import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def isPrimeBool (n : Nat) : Bool := n.minFac == n && n != 1

def primeCountRangeB : Nat → Nat → Nat
  | lo, 0 => 0
  | lo, 1 => if isPrimeBool lo then 1 else 0
  | lo, len+2 =>
      let h := (len+2)/2
      primeCountRangeB lo h + primeCountRangeB (lo+h) (len+2-h)
termination_by lo len => len
decreasing_by
  · exact Nat.div_lt_self (Nat.succ_pos _) (by norm_num)
  · have hpos : 0 < (len + 2) / 2 := Nat.div_pos (by omega) (by norm_num)
    exact Nat.sub_lt (by omega) hpos

def primeCountBelowB (N : Nat) := primeCountRangeB 0 N

#eval primeCountBelowB 8165753

theorem countB : primeCountBelowB 8165753 = 550171 := by
  decide
#print axioms countB
