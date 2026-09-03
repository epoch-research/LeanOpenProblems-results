import FormalConjecturesUtil
/-! Finite closed-walk certificate for a cycle bundle diagnostic. -/
open SimpleGraph Fin.NatCast
namespace C9BundleProbe
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def pos (x : Fin 9) (s : Fin 8 → Bool) : ℕ → Fin 9
  | 0 => x
  | n+1 => pos x s n + if s (↑n : Fin 8) then 1 else -1

lemma walk_certificate : ∀ (x : Fin 9) (b0 b1 b2 b3 b4 b5 b6 b7 : Bool),
    pos x ![b0,b1,b2,b3,b4,b5,b6,b7] 8 = x →
      ∃ i j : Fin 8, i < j ∧
        (pos x ![b0,b1,b2,b3,b4,b5,b6,b7] i).val % 2 = 0 ∧
        pos x ![b0,b1,b2,b3,b4,b5,b6,b7] i = pos x ![b0,b1,b2,b3,b4,b5,b6,b7] j := by
  decide

#print axioms walk_certificate
end C9BundleProbe
