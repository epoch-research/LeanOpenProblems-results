import Submission.QuadraticRecurrenceAverages

/-! Finite collision and pair-energy estimates indexed by arbitrary fibers.
The diagonal mass is controlled by the number of fibers rather than by the
size of the original sample space. -/
namespace Erdos3FiniteFiberEnergy
open Finset Erdos3QuadraticRecurrenceAverages Erdos3FiniteFourier
  Erdos3FiniteSamplingMoments Erdos3LinearFormsUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

lemma fiber_collision_lower {I J : Type*} [Fintype I] [Nonempty I]
    [Fintype J] [Nonempty J] (φ : I → J) :
    1/(Fintype.card J : ℝ) ≤ 𝔼 i, 𝔼 j, (if φ i = φ j then (1 : ℝ) else 0) := by
  let w : J → ℝ := fun a ↦ 𝔼 i, if φ i = a then (1 : ℝ) else 0
  have hsum : ∑ a, w a = 1 := by
    dsimp only [w]
    rw [← expect_sum_comm]
    simp
  have hcollision : (𝔼 i, 𝔼 j, (if φ i = φ j then (1 : ℝ) else 0)) = ∑ a, (w a)^2 := by
    have hpoint (i j : I) : (if φ i = φ j then (1 : ℝ) else 0) =
        ∑ a, (if φ i = a then (1 : ℝ) else 0)*(if φ j = a then (1 : ℝ) else 0) := by
      simp [ite_mul,eq_comm]
    simp_rw [hpoint,expect_sum_comm]
    apply sum_congr rfl
    intro a _
    simp_rw [← mul_expect]
    rw [← expect_mul]
    exact (pow_two _).symm
  have hJ : (0 : ℝ) < Fintype.card J := Nat.cast_pos.mpr Fintype.card_pos
  have hw : (𝔼 a, w a)^2 ≤ 𝔼 a, (w a)^2 := expect_even_pow_le (by decide : Even 2) _
  rw [Fintype.expect_eq_sum_div_card,Fintype.expect_eq_sum_div_card,hsum] at hw
  rw [hcollision]
  have hh := (le_div_iff₀ hJ).mp hw
  have he : (1/(Fintype.card J : ℝ))^2*(Fintype.card J : ℝ) = 1/(Fintype.card J : ℝ) := by
    field_simp
  rwa [he] at hh

/-- Off-fiber small correlations force energy at least the collision mass
minus the correlation bound. -/
lemma fiber_pair_energy_lower {I J X : Type*} [Fintype I] [Nonempty I]
    [Fintype J] [Nonempty J] [Fintype X] [Nonempty X]
    (φ : I → J) (f : X → I → ℂ) (hf : ∀ x i, ‖f x i‖ = 1)
    (hsame : ∀ x i j, φ i = φ j → f x i = f x j)
    {η : ℝ} (hη : 0 ≤ η)
    (hpair : ∀ i j, φ i ≠ φ j → ‖𝔼 x, f x i*conj (f x j)‖ ≤ η) :
    1/(Fintype.card J : ℝ)-η ≤ 𝔼 x, ‖𝔼 i, f x i‖^2 := by
  have he : (𝔼 x, ‖𝔼 i, f x i‖^2) =
      𝔼 i, 𝔼 j, (𝔼 x, f x i*conj (f x j)).re := by
    simp_rw [norm_mean_sq_pair,expect_re]
    rw [expect_comm]
    apply expect_congr rfl
    intro i _
    exact expect_comm _ _ _
  have hlow (i j : I) : (if φ i = φ j then (1 : ℝ) else 0)-η ≤
      (𝔼 x, f x i*conj (f x j)).re := by
    split_ifs with hij
    · have hc : (𝔼 x, f x i*conj (f x j)) = 1 := by
        calc
          _ = 𝔼 _x : X, (1 : ℂ) := by
            apply expect_congr rfl
            intro x _
            rw [hsame x i j hij,Complex.mul_conj,Complex.normSq_eq_norm_sq,hf,one_pow]
            rfl
          _ = _ := Fintype.expect_const _
      rw [hc,Complex.one_re]
      linarith only [hη]
    · have hn := Complex.abs_re_le_norm (𝔼 x, f x i*conj (f x j))
      have hp := hpair i j hij
      have ha := neg_abs_le (𝔼 x, f x i*conj (f x j)).re
      linarith only [hn,hp,ha]
  calc
    _ ≤ (𝔼 i, 𝔼 j, (if φ i = φ j then (1 : ℝ) else 0))-η :=
      sub_le_sub_right (fiber_collision_lower φ) η
    _ = 𝔼 i, 𝔼 j, ((if φ i = φ j then (1 : ℝ) else 0)-η) := by
      simp only [expect_sub_distrib,Fintype.expect_const]
    _ ≤ _ := by
      rw [he]
      exact expect_le_expect (fun i _ ↦ expect_le_expect (fun j _ ↦ hlow i j))

/-- Low energy gives a large correlation between two distinct fibers. -/
theorem low_energy_off_fiber_correlation {I J X : Type*}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    [Fintype X] [Nonempty X] (φ : I → J) (f : X → I → ℂ)
    (hf : ∀ x i, ‖f x i‖ = 1)
    (hsame : ∀ x i j, φ i = φ j → f x i = f x j)
    (hupper : (𝔼 x, ‖𝔼 i, f x i‖^2) ≤ 1/(2*(Fintype.card J : ℝ))) :
    ∃ i j, φ i ≠ φ j ∧ 1/(4*(Fintype.card J : ℝ)) < ‖𝔼 x, f x i*conj (f x j)‖ := by
  by_contra hn
  push_neg at hn
  have hl := fiber_pair_energy_lower φ f hf hsame (by positivity) hn
  have hJ : (0 : ℝ) < Fintype.card J := Nat.cast_pos.mpr Fintype.card_pos
  have hstrict : 1/(2*(Fintype.card J : ℝ)) <
      1/(Fintype.card J : ℝ)-1/(4*(Fintype.card J : ℝ)) := by
    field_simp
    linarith only [hJ]
  linarith only [hl,hupper,hstrict]

#print axioms fiber_collision_lower
#print axioms low_energy_off_fiber_correlation
end Erdos3FiniteFiberEnergy
