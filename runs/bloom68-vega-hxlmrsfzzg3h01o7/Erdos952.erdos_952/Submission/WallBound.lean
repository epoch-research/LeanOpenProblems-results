import Submission.WallData
import Submission.WallCurrent
import Submission.WallQuotient
import Submission.WallPrimeBridge

/-!
# A kernel-checked periodic-wall bound for Gaussian-prime walks

The finite black wall, its quotient current, and the discrete stream-function
obstruction together exclude strict squared step bounds `C ≤ 8`.
This is a partial result, not a proof of the arbitrary-bound Gaussian moat
statement in `Submission.Spec`. No declaration from that file is used.
-/

namespace Erdos952

/-- The exact periodic sieve has no injective infinite white king walk. -/
theorem no_injective_white_king_sequence_of_wall :
    ¬ ∃ w : ℕ → GaussianInt, Function.Injective w ∧
      (∀ n, ¬ WallData.Black (w n)) ∧
      ∀ n, WallObstruction.KingAdjacent (w n) (w (n + 1)) := by
  have hpath : Relation.ReflTransGen (WallCurrent.BlackStep WallQuotient.B)
      WallData.start WallData.finish := WallData.wall_path
  have hdispl : WallData.finish - WallData.start = WallQuotient.p :=
    WallData.wall_displacement
  have hres := WallQuotient.residue_eq_of_sub_eq_p hdispl
  obtain ⟨Cx, Cy, hdiv, hx, hy, hwhite⟩ :=
    WallCurrent.exists_divergenceFree_current WallQuotient.r
      WallQuotient.B_residue_invariant hpath hres
  have hflux : (∑ a : WallQuotient.α, Cx a) ≠ 0 ∨
      (∑ a : WallQuotient.α, Cy a) ≠ 0 := by
    left
    rw [hx, hdispl]
    norm_num [WallQuotient.p]
  exact WallObstruction.no_injective_white_king_sequence_of_black_rotation
    WallQuotient.r WallQuotient.r_surjective WallQuotient.p
    WallQuotient.p_ne_zero WallQuotient.r_p WallQuotient.r_I_mul_p
    WallQuotient.kernel_representation WallQuotient.B WallQuotient.B_R
    Cx Cy hdiv hwhite hflux

/-- No injective Gaussian-prime walk has a strict squared step bound at most
8. This theorem still leaves all larger bounds unresolved. -/
theorem no_bounded_step_sequence_of_bound_le_eight {C : ℤ} (hC : C ≤ 8) :
    ¬ ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C := by
  exact WallPrimeBridge.no_bounded_step_sequence_of_bound_le_eight
    no_injective_white_king_sequence_of_wall hC

/-- Any witness to the unrestricted statement must use `C ≥ 9`. -/
theorem nine_le_bound_of_witness {C : ℤ}
    (h : ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) : 9 ≤ C := by
  by_contra hC
  exact no_bounded_step_sequence_of_bound_le_eight (by omega) h

end Erdos952

#print axioms Erdos952.no_injective_white_king_sequence_of_wall
#print axioms Erdos952.no_bounded_step_sequence_of_bound_le_eight
#print axioms Erdos952.nine_le_bound_of_witness
