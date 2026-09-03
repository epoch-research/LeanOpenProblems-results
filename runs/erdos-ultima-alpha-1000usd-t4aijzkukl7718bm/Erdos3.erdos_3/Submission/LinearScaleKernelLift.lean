import Submission.KernelMonomialLift

/-! The natural inverse-degree approximation scale permits a linear loss of
interval length when lifting recurrence from a kernel. -/
namespace Erdos3LinearScaleKernelLift
open Erdos3KernelMonomialLift Erdos3KernelProjectionEstimates
set_option maxHeartbeats 3000000

lemma inverse_degree_lift_budget (k q M n S N : ℕ)
    (hq : 0 < q) (hN : 0 < N) (hn : n ≤ M) (hscale : q*M*S ≤ N)
    {E ρ a : ℝ} (hE : 0 ≤ E) (hρ : 0 ≤ ρ) (ha : 0 < a)
    (hbudget : E ≤ ρ*a*(S : ℝ)^(k+1)) :
    (n : ℝ)^(k+1)*(q : ℝ)^k*(E/(N : ℝ)^(k+1))/a ≤ ρ := by
  have hqn : q*n*S ≤ N := (Nat.mul_le_mul_right S (Nat.mul_le_mul_left q hn)).trans hscale
  have hpow : (n : ℝ)^(k+1)*(q : ℝ)^(k+1)*(S : ℝ)^(k+1) ≤ (N : ℝ)^(k+1) := by
    have hh : ((q : ℝ)*(n : ℝ)*(S : ℝ))^(k+1) ≤ (N : ℝ)^(k+1) :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hqn) _
    simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using hh
  have hqc : (q : ℝ)^k ≤ (q : ℝ)^(k+1) :=
    pow_le_pow_right₀ (by exact_mod_cast hq) (by omega)
  have hnum : (n : ℝ)^(k+1)*(q : ℝ)^k*E ≤ ρ*((N : ℝ)^(k+1)*a) := by
    calc
      _ ≤ (n : ℝ)^(k+1)*(q : ℝ)^(k+1)*E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqc (by positivity)) hE
      _ ≤ (n : ℝ)^(k+1)*(q : ℝ)^(k+1)*(ρ*a*(S : ℝ)^(k+1)) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = (ρ*a)*((n : ℝ)^(k+1)*(q : ℝ)^(k+1)*(S : ℝ)^(k+1)) := by ring
      _ ≤ (ρ*a)*(N : ℝ)^(k+1) := mul_le_mul_of_nonneg_left hpow (mul_nonneg hρ ha.le)
      _ = _ := by ring
  calc
    _ = ((n : ℝ)^(k+1)*(q : ℝ)^k*E)/((N : ℝ)^(k+1)*a) := by ring
    _ ≤ _ := (div_le_iff₀ (mul_pos (pow_pos (Nat.cast_pos.mpr hN) _) ha)).mpr hnum

/-- A kernel return at n<=M lifts to a return in the original interval whenever
q*M*S<=N and S covers the error budget. No root-scale shortening occurs. -/
theorem kernel_lift_at_linear_scale {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (L : Submodule ℤ E) (F : E →L[ℝ] ℝ) (hF : F ≠ 0)
    (α v : E) (hvL : v ∈ L) (hv : F v = 1)
    (q k M n S N : ℕ) (c : ℤ)
    (hq : 0 < q) (hS : 0 < S) (hN : 0 < N) (hn : 0 < n) (hnM : n ≤ M)
    (hscale : q*M*S ≤ N) {A η ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (hbudget : A ≤ ρ*‖F‖*(S : ℝ)^(k+1))
    (happrox : |(q : ℝ)*F α-(c : ℝ)| ≤ A/(N : ℝ)^(k+1))
    (y : E) (hy : y ∈ L)
    (hclose : ‖((n^(k+1) : ℕ) : ℝ) • projectionAlong F (normalVector F)
      (adjustedCoefficient α v q k c)-y‖ ≤ η) :
    ∃ m : ℕ, 0 < m ∧ m ≤ N ∧ ∃ w : E, w ∈ L ∧
      ‖((m^(k+1) : ℕ) : ℝ) • α-w‖ ≤ η+ρ := by
  obtain ⟨w,hw,herr⟩ := kernel_monomial_lift_normal L F hF α v hvL hv q k n c happrox y hy hclose
  have hb := inverse_degree_lift_budget k q M n S N hq hN hnM hscale hA hρ (norm_pos_iff.mpr hF) hbudget
  have htime : q*n ≤ N := by
    have h1 := Nat.mul_le_mul_left (q*M) hS
    have h2 := Nat.mul_le_mul_left q hnM
    nlinarith only [h1,h2,hscale]
  exact ⟨q*n,Nat.mul_pos hq hn,htime,w,hw,herr.trans (add_le_add (le_refl η) hb)⟩

#print axioms kernel_lift_at_linear_scale
end Erdos3LinearScaleKernelLift
