import Submission.TensorFejerKernel

/-! A simultaneous avoidance certificate: if a unit-phase tuple never enters
a small neighborhood of the identity, a bounded nonzero integer frequency
has a quantitatively large mean. -/
namespace Erdos3SimultaneousAvoidanceFrequency
open Finset Erdos3TensorFejerKernel Erdos3FiniteFiberEnergy
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

lemma unit_pair_zpow (v : ℂ) (hv : ‖v‖ = 1) (a b : ℕ) :
    v^a*conj (v^b) = v^((a : ℤ)-(b : ℤ)) := by
  have hv0 : v ≠ 0 := by intro he; rw [he,norm_zero] at hv; norm_num at hv
  rw [zpow_sub₀ hv0,zpow_natCast,zpow_natCast,div_eq_mul_inv,
    Complex.inv_eq_conj (by rw [norm_pow,hv,one_pow])]

/-- The frequency bound is mK and the mean threshold is 1/(4(mK)^m).
The kernel scale condition only requires K*epsilon^2>=8m. -/
theorem simultaneous_avoidance_frequency {X : Type*} [Fintype X] [Nonempty X]
    {m K : ℕ} (hm : 0 < m) (hK : 0 < K)
    (v : X → Fin m → ℂ) (hv : ∀ x j, ‖v x j‖ = 1) {ε : ℝ} (hε : 0 < ε)
    (hscale : 8*(m : ℝ) ≤ (K : ℝ)*ε^2)
    (havoid : ∀ x, ∃ j, ε ≤ ‖v x j-1‖) :
    ∃ h : Fin m → ℤ, (∃ j, h j ≠ 0) ∧ (∀ j, |h j| < (m*K : ℕ)) ∧
      1/(4*((m : ℝ)*(K : ℝ))^m) < ‖𝔼 x, ∏ j, (v x j)^(h j)‖ := by
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero K := ⟨by omega⟩
  let I := Fin m → Fin m → Fin K
  let J := Fin m → Fin (m*K)
  let φ : I → J := fun a j ↦ ⟨coordinateSum m K (a j),coordinateSum_lt hm _⟩
  let f : X → I → ℂ := fun x a ↦ kernelAtom m K (v x) a
  have hcard : Fintype.card J = (m*K)^m := by simp only [J,Fintype.card_fun,Fintype.card_fin]
  have hf : ∀ x a, ‖f x a‖ = 1 := fun x a ↦ kernelAtom_norm m K (v x) (hv x) a
  have hsame : ∀ x a b, φ a = φ b → f x a = f x b := by
    intro x a b hab
    apply prod_congr rfl
    intro j _
    have hh := congrArg (fun c : J ↦ (c j).val) hab
    change coordinateSum m K (a j) = coordinateSum m K (b j) at hh
    rw [hh]
  have hupper : (𝔼 x, ‖𝔼 a, f x a‖^2) ≤ 1/(2*(Fintype.card J : ℝ)) := by
    apply expect_le univ_nonempty
    intro x _
    simpa only [hcard,Nat.cast_pow,Nat.cast_mul] using
      kernel_avoidance_bound hm hK (v x) (hv x) hε hscale (havoid x)
  obtain ⟨a,b,hab,hmean⟩ := low_energy_off_fiber_correlation φ f hf hsame hupper
  let h : Fin m → ℤ := fun j ↦ (coordinateSum m K (a j) : ℤ)-(coordinateSum m K (b j) : ℤ)
  have hne : ∃ j, h j ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hab
    funext j
    apply Fin.ext
    have hh := sub_eq_zero.mp (hn j)
    exact_mod_cast hh
  have hbound (j : Fin m) : |h j| < (m*K : ℕ) := by
    have ha := coordinateSum_lt hm (a j)
    have hb := coordinateSum_lt hm (b j)
    apply abs_lt.mpr
    dsimp only [h]
    constructor <;> omega
  have hpair (x : X) : f x a*conj (f x b) = ∏ j, (v x j)^(h j) := by
    dsimp only [f,kernelAtom]
    rw [map_prod,← prod_mul_distrib]
    apply prod_congr rfl
    intro j _
    exact unit_pair_zpow (v x j) (hv x j) _ _
  refine ⟨h,hne,hbound,?_⟩
  simpa only [hpair,hcard,Nat.cast_pow,Nat.cast_mul] using hmean

#print axioms simultaneous_avoidance_frequency
end Erdos3SimultaneousAvoidanceFrequency
