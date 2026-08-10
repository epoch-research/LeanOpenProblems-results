import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def smallPrime (i : Nat) : Nat := [2,3,5].getD i 1

def phiFrom : Nat → Nat → Nat
| 0, n => n
| i+1, n => phiFrom i n - phiFrom i (n / smallPrime i)

lemma phi_0_30 : phiFrom 0 30 = 30 := rfl
lemma phi_0_15 : phiFrom 0 15 = 15 := rfl
lemma phi_1_30 : phiFrom 1 30 = 15 := by simp [phiFrom, smallPrime, phi_0_30, phi_0_15]

#eval phiFrom 3 30
