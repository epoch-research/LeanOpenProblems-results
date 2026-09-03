import FormalConjecturesUtil

/-! A positive symmetric six-term rational square sequence.
This is not an integral point set construction or a settlement of Erdős 213. -/
namespace Erdos213.BuchiSymmetricInput

def root : Fin 6 → ℚ := ![241/60,209/60,191/60,191/60,209/60,241/60]

theorem six_square_identities (k : Fin 6) :
    root k ^ 2 = ((k.val : ℚ)-5/2)^2 + 35581/3600 := by
  fin_cases k <;> norm_num [root]

theorem positive_height : (0 : ℚ) < 35581/3600 := by norm_num

theorem six_square_values (k : Fin 6) :
    IsSquare (((k.val : ℚ)-5/2)^2 + 35581/3600) :=
  ⟨root k, by simpa only [sq] using (six_square_identities k).symm⟩

theorem seventh_not_square : ¬IsSquare ((7 : ℚ)^2 + 35581/900) := by
  decide +kernel

#print axioms six_square_values
#print axioms seventh_not_square
end Erdos213.BuchiSymmetricInput
