import Submission.OctahedralColor
namespace Erdos213.OctahedralLocal

/-- The integer normalized chord form corresponding to a code. -/
def intCodeValue (a b c : ℤ) (k : Fin 44) : ℤ :=
  (if k.val < 22 then 1 else 2) * forms a b c ⟨k.val%22, Nat.mod_lt _ (by norm_num)⟩


end Erdos213.OctahedralLocal
