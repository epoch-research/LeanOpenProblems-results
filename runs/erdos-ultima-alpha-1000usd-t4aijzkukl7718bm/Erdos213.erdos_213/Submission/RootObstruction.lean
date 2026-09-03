import FormalConjecturesUtil

namespace Erdos213.RootObstruction
open Polynomial

lemma monic_no_root_of_mod (P : ℤ[X]) (hP : P.Monic) (p : ℕ)
    (hm : ∀ x : ZMod p, P.eval₂ (Int.castRingHom _) x ≠ 0) (r : ℚ) :
    Polynomial.aeval r P ≠ 0 := by
  intro hr
  obtain ⟨z,hz,_⟩ := exists_integer_of_is_root_of_monic hP hr
  have hZ : P.eval z = 0 := by
    apply IsFractionRing.injective ℤ ℚ
    simpa [hz, Polynomial.aeval_def, Polynomial.eval₂_at_apply] using hr
  apply hm (z : ZMod p)
  change P.eval₂ (Int.castRingHom _) ((Int.castRingHom (ZMod p)) z) = 0
  rw [Polynomial.eval₂_at_apply, hZ, map_zero]

example (r : ℚ) : r^2-3 ≠ 0 := by
  let P : ℤ[X] := X^2-3
  have hp : P.Monic := by dsimp [P]; monicity!
  have hm : ∀ x : ZMod 5, P.eval₂ (Int.castRingHom _) x ≠ 0 := by
    simp only [P, eval₂_sub, eval₂_pow, eval₂_X, eval₂_ofNat]
    decide
  have h := monic_no_root_of_mod P hp 5 hm r
  simpa [P, Polynomial.aeval_def] using h

end Erdos213.RootObstruction
