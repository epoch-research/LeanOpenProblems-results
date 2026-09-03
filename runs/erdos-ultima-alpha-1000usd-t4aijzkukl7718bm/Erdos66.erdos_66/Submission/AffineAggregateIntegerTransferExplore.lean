import Submission.AggregateCyclicThickeningExplore

/-! A complete conditional transfer from unsigned and signed scalar coarse
counts to natural representation counts, using individual colored curves.
This does not construct the scalar profiles or change the prime compatibly. -/
namespace Erdos66AffineAggregateIntegerTransfer
open AdditiveCombinatorics Erdos66OriginRepair Erdos66AffineRootAggregate
  Erdos66SharedParameterKernel Erdos66CyclicThickening Erdos66OuterCarryProfile
  Erdos66AggregateCyclicThickening
open scoped Classical
set_option maxHeartbeats 1400000

variable (p K L : ℕ) [Fact p.Prime] [NeZero K] [NeZero L]

/-- There is no requirement that the individual curves, or their individual
mixed convolutions, be flat. All fine targets are controlled by just two
unsigned and two signed scalar convolution constraints. -/
theorem affine_integer_error (hp : p ≠ 2) (D : Finset ℕ) (a : ZMod p) (h q : ℕ)
    (hD : D ⊆ Finset.range h) (hq : 0<q) (hqh : q<h)
    (ha : ∀ i<h, a+(i : ZMod p) ≠ 0)
    (hop : ∀ m, m=q ∨ m=q-1 → 2*a+(m : ZMod p) ≠ 0)
    (μ E₀ E₁ : ℝ)
    (hunsigned : ∀ m, m=q ∨ m=q-1 → |(sumRep (D : Set ℕ) m : ℝ)-μ| ≤ E₀)
    (hsigned : ∀ m, m=q ∨ m=q-1 →
      |labelFiber h (fun i ↦ selectedWeight D i*(quadraticChar (ZMod p) (a+i) : ℝ)) m| ≤ E₁)
    (z : ZMod ((p*K)^2)) (r : Fin L) :
    |(sumRep
      (Erdos66IntegerBlock.blockSet (((p*K)^2)*L)
        (fun i ↦ outerLift ((p*K)^2) L (thickenedSet p K (coloredCurve D a i))))
      (q*(((p*K)^2)*L)+(blockDigit ((p*K)^2) L z r).val) : ℝ)-L*(K : ℝ)^2*μ| ≤
      ((L : ℝ)+1)*((K : ℝ)^2*(E₀+E₁)+2*K*(μ+(E₀+E₁)))+(K : ℝ)^2*μ := by
  have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  have hplane (m : ℕ) (hm : m=q ∨ m=q-1) (t s : ZMod p) :
      |planeAggregate p (coloredCurve D a) m t s-μ| ≤ E₀+E₁ := by
    have hmh : m<h := by rcases hm with rfl | rfl <;> omega
    have he := coloredCurve_plane_error D a h m hD hmh hF ha (hop m hm) t s
    have he' : |planeAggregate p (coloredCurve D a) m t s-(sumRep (D : Set ℕ) m : ℝ)| ≤ E₁ := by
      exact he.trans (hsigned m hm)
    exact (abs_sub_le _ (sumRep (D : Set ℕ) m : ℝ) μ).trans
      (by linarith [hunsigned m hm])
  exact plane_to_integer_aggregate_error p K L (coloredCurve D a) q hq μ (E₀+E₁)
    (hplane q (Or.inl rfl)) (hplane (q-1) (Or.inr rfl)) z r

end Erdos66AffineAggregateIntegerTransfer
