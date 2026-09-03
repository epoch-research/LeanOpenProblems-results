import Submission.CentralReflectionPairing
import Submission.CentralMetricInverse

/-! Reflection obstruction with assumptions on output distances alone.
These theorems apply only to the central quadratic seven-point construction. -/
namespace Erdos213.CentralOutputReflection
open CentralReflection CentralMetricInverse
noncomputable section
set_option maxHeartbeats 4000000

/-- Six centrally paired outputs force the seventh to be the center, even
when rationality is assumed only after an arbitrary nonzero output scale. -/
theorem paired_singleton_fixed (L t w : ℂ) (hL : L≠0)
    (hi : Function.Injective (points t w))
    (hd : ∀ i j, dist (L*points t w i) (L*points t w j)∈
      Set.range ((↑) : ℚ → ℝ))
    (σ : Equiv.Perm (Fin 7)) (C : ℂ)
    (hp : ∀ k : Fin 3,
      L*points t w (permPair σ k 0)+L*points t w (permPair σ k 1)=C) :
    C-L*points t w (σ 6)=L*points t w (σ 6) := by
  have hs := factors_of_scaled_output_distances L t w hL hi hd
  have hp' (k : Fin 3) :
      points t w (permPair σ k 0)+points t w (permPair σ k 1)=C/L := by
    apply (eq_div_iff hL).mpr
    linear_combination hp k
  have hf := CentralReflection.paired_singleton_fixed t w (hs 1) (hs 4) hi σ (C/L) hp'
  have he := congrArg (fun z : ℂ => L*z) hf
  simpa only [mul_sub,mul_div_cancel₀ C hL] using he

/-- A general-position rational-distance output has no centrally paired
six-point subset. In particular this reflection cannot extend it to eight. -/
theorem nontrilinear_no_paired_six (L t w : ℂ) (hL : L≠0)
    (hi : Function.Injective (points t w))
    (hd : ∀ i j, dist (L*points t w i) (L*points t w j)∈
      Set.range ((↑) : ℚ → ℝ))
    (hgp : EuclideanGeometry.NonTrilinear (Set.range (fun i => L*points t w i)))
    (σ : Equiv.Perm (Fin 7)) (C : ℂ)
    (hp : ∀ k : Fin 3,
      L*points t w (permPair σ k 0)+L*points t w (permPair σ k 1)=C) : False := by
  have hf := paired_singleton_fixed L t w hL hi hd σ C hp
  have h0 := hp 0
  change L*points t w (σ 0)+L*points t w (σ 1)=C at h0
  have he : L*points t w (σ 0)+L*points t w (σ 1)=2*(L*points t w (σ 6)) := by
    linear_combination h0+hf
  have hne (i j : Fin 7) (hij : i≠j) : L*points t w (σ i)≠L*points t w (σ j) :=
    fun hh => hij (σ.injective (hi (mul_left_cancel₀ hL hh)))
  exact hgp (Set.mem_range_self (σ 0)) (Set.mem_range_self (σ 1))
    (Set.mem_range_self (σ 6)) (hne 0 1 (by decide)) (hne 1 6 (by decide))
    (hne 0 6 (by decide)) (collinear_of_pair_sum _ _ _ he)

#print axioms paired_singleton_fixed
#print axioms nontrilinear_no_paired_six
end
end Erdos213.CentralOutputReflection
