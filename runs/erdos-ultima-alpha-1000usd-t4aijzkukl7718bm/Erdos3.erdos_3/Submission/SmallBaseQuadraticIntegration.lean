import Submission.LocalQuadraticInverse

/-! Approximate quadratic integration with a small doubled base and an arbitrary
large direction. Symmetry is needed across these two sets, not at half-directions. -/
namespace Erdos3SmallBaseQuadraticIntegration
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3LocalQuadraticIntegration
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Only the base u is doubled. The direction h can remain in a polynomially
dense set, avoiding the loss from restricting it to a small Bohr set. -/
theorem quadraticPhase_derivative_small_base {P : Set G} {F : G → AddChar G ℂ}
    (hF : LocallyAdditive P F) (half : G →+ G) (hhalf : ∀ x, half (x+x) = x)
    {u h : G} (hu : u ∈ P) (huu : u+u ∈ P) (hh : h ∈ P) (hsum : (u+u)+h ∈ P)
    {ε : ℝ} (hsym : ‖F u h-F h u‖ ≤ ε) :
    ‖derivative (quadraticPhase F half) h (u+u)-quadraticPhase F half h*F h (u+u)‖ ≤ ε := by
  rw [quadraticPhase_derivative hF half huu hh hsum]
  have hd : half h+half h = h := by rw [← half.map_add,hhalf]
  have hc : crossPhase F half h (u+u) = F h u*F u h := by
    unfold crossPhase
    rw [hhalf,hF u hu u hu huu]
    simp only [AddChar.add_apply]
    rw [← AddChar.map_add_eq_mul,hd]
  rw [hc,AddChar.map_add_eq_mul]
  have he : quadraticPhase F half h*(F h u*F u h)-quadraticPhase F half h*(F h u*F h u) =
      (quadraticPhase F half h*F h u)*(F u h-F h u) := by ring
  rw [he,norm_mul,norm_mul,quadraticPhase_norm,AddChar.norm_apply,one_mul,one_mul]
  exact hsym

#print axioms quadraticPhase_derivative_small_base
end Erdos3SmallBaseQuadraticIntegration
