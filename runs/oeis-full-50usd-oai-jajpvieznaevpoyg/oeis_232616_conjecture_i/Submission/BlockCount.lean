import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def isPrimeBool (n : Nat) : Bool := n.minFac == n && n != 1

def countBlock : Nat → Nat → Nat
  | 0, lo => if isPrimeBool lo then 1 else 0
  | d+1, lo => countBlock d lo + countBlock d (lo + 2^d)

def count8165753 : Nat :=
  countBlock 22 0 + countBlock 21 4194304 + countBlock 20 6291456 +
  countBlock 19 7340032 + countBlock 18 7864320 + countBlock 15 8126464 +
  countBlock 12 8159232 + countBlock 11 8163328 + countBlock 8 8165376 +
  countBlock 6 8165632 + countBlock 5 8165696 + countBlock 4 8165728 +
  countBlock 3 8165744 + countBlock 0 8165752

#eval count8165753

theorem count8165753_eq : count8165753 = 550171 := by
  decide
#print axioms count8165753_eq
