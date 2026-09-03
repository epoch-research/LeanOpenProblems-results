import Submission.KernelProjectionEstimates

/-! Exact lifting of monomial recurrence from a primitive functional's kernel.
The rational denominator changes the time n to q*n, and the projection error
retains its inverse-degree scale. -/
namespace Erdos3KernelMonomialLift
open Erdos3KernelProjectionEstimates
set_option maxHeartbeats 3000000

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def adjustedCoefficient (α v : E) (q k : ℕ) (c : ℤ) : E :=
  ((q^(k+1) : ℕ) : ℝ) • α-(((q^k : ℕ) : ℝ)*(c : ℝ)) • v

lemma adjustedCoefficient_evaluate (F : E →L[ℝ] ℝ) (α v : E) (hv : F v = 1)
    (q k : ℕ) (c : ℤ) :
    F (adjustedCoefficient α v q k c) = (q : ℝ)^k*((q : ℝ)*F α-(c : ℝ)) := by
  rw [adjustedCoefficient,map_sub,map_smul,map_smul,hv]
  simp only [smul_eq_mul,Nat.cast_pow,Nat.cast_mul,mul_one,pow_succ]
  ring

/-- A near return of the projected, adjusted coefficient lifts to a near return
of alpha at time q*n. All integer correction terms stay in the original lattice. -/
theorem kernel_monomial_lift (L : Submodule ℤ E) (F : E →L[ℝ] ℝ)
    (α v u : E) (hvL : v ∈ L) (hv : F v = 1)
    (q k n : ℕ) (c : ℤ) {ε η : ℝ}
    (happrox : |(q : ℝ)*F α-(c : ℝ)| ≤ ε)
    (y : E) (hy : y ∈ L)
    (hclose : ‖((n^(k+1) : ℕ) : ℝ) • projectionAlong F u (adjustedCoefficient α v q k c)-y‖ ≤ η) :
    ∃ w : E, w ∈ L ∧ ‖(((q*n)^(k+1) : ℕ) : ℝ) • α-w‖ ≤
      η+(n : ℝ)^(k+1)*(q : ℝ)^k*ε*‖u‖ := by
  let β := adjustedCoefficient α v q k c
  let w : E := ((n^(k+1)*q^k : ℕ) : ℤ) • (c • v)+y
  have hw : w ∈ L := L.add_mem (L.smul_mem _ (L.smul_mem _ hvL)) hy
  have he : (((q*n)^(k+1) : ℕ) : ℝ) • α-w =
      (((n^(k+1) : ℕ) : ℝ) • projectionAlong F u β-y)+
        (((n^(k+1) : ℕ) : ℝ)*F β) • u := by
    rw [projectionAlong_apply]
    dsimp only [w,β,adjustedCoefficient]
    simp only [← Int.cast_smul_eq_zsmul ℝ,Int.cast_natCast,Nat.cast_mul,Nat.cast_pow,mul_pow]
    module
  have hFβ : F β = (q : ℝ)^k*((q : ℝ)*F α-(c : ℝ)) := adjustedCoefficient_evaluate F α v hv q k c
  have herr : ‖(((n^(k+1) : ℕ) : ℝ)*F β) • u‖ ≤ (n : ℝ)^(k+1)*(q : ℝ)^k*ε*‖u‖ := by
    rw [norm_smul,Real.norm_eq_abs,hFβ,Nat.cast_pow,abs_mul,abs_mul,
      abs_of_nonneg (pow_nonneg (Nat.cast_nonneg n) _),
      abs_of_nonneg (pow_nonneg (Nat.cast_nonneg q) _)]
    have hh := mul_le_mul_of_nonneg_left happrox
      (by positivity : 0 ≤ (n : ℝ)^(k+1)*(q : ℝ)^k)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (norm_nonneg u)
  refine ⟨w,hw,?_⟩
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hclose herr)

end Normed

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem kernel_monomial_lift_normal (L : Submodule ℤ E) (F : E →L[ℝ] ℝ) (hF : F ≠ 0)
    (α v : E) (hvL : v ∈ L) (hv : F v = 1)
    (q k n : ℕ) (c : ℤ) {ε η : ℝ}
    (happrox : |(q : ℝ)*F α-(c : ℝ)| ≤ ε)
    (y : E) (hy : y ∈ L)
    (hclose : ‖((n^(k+1) : ℕ) : ℝ) • projectionAlong F (normalVector F)
      (adjustedCoefficient α v q k c)-y‖ ≤ η) :
    ∃ w : E, w ∈ L ∧ ‖(((q*n)^(k+1) : ℕ) : ℝ) • α-w‖ ≤
      η+(n : ℝ)^(k+1)*(q : ℝ)^k*ε/‖F‖ := by
  obtain ⟨w,hw,herr⟩ := kernel_monomial_lift L F α v (normalVector F) hvL hv q k n c happrox y hy hclose
  refine ⟨w,hw,herr.trans_eq ?_⟩
  rw [normalVector_norm F hF]
  ring

#print axioms kernel_monomial_lift_normal
end Hilbert
end Erdos3KernelMonomialLift
