import Submission.RangeIndependentFamilyExplore
import Submission.MixedCyclicThickeningExplore
import Submission.OuterCarryProfileExplore

/-! Cyclic transfer of the range-independent finite-field families. The
spacing and thickness thresholds do not depend on the maximum index. -/
namespace Erdos66RangeIndependentCyclic
open Erdos66RangeIndependentFamily Erdos66QuadraticLevelSelection
  Erdos66MixedCyclicThickening Erdos66CyclicThickening Erdos66OuterCarryProfile
  Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 2200000

 theorem exists_range_independent_cyclic_family (η : ℝ) (hη : 0<η) (hη1 : η ≤ 1) :
    ∃ D g K₀ : ℕ, 0<g ∧ g ≤ D ∧ 0<K₀ ∧
      ∀ J p : ℕ, ∀ hp : p.Prime,
        max (8*level D J+3) (4*g*level D J)<p → ∀ K≥K₀,
          ∃ C : ℕ → Finset (ZMod ((p*K)^2)), Monotone C ∧
            ∀ i≤J, ∀ j≤J, ∀ z,
              |(cyclicCount ((p*K)^2) (C i) (C j) z:ℝ)-
                4*(K:ℝ)^2*(level D i:ℝ)*(level D j:ℝ)| ≤
                η*(4*(K:ℝ)^2*(level D i:ℝ)*(level D j:ℝ)) := by
  obtain ⟨D,g,hg,hgD,hfamily⟩ := exists_range_independent_flat_family (η/2) (by positivity)
  let K₀ : ℕ := ⌈8/η⌉₊+1
  have hK₀ : 0<K₀ := by dsimp [K₀]; omega
  have hthick : ∀ K≥K₀, 8 ≤ η*(K:ℝ) := by
    intro K hK
    have hh := (div_le_iff₀ hη).mp (Nat.le_ceil (8/η))
    have hc : (⌈8/η⌉₊:ℝ) ≤ K := by exact_mod_cast (show ⌈8/η⌉₊ ≤ K by dsimp [K₀] at hK; omega)
    nlinarith only [hh,hc,hη]
  refine ⟨D,g,K₀,hg,hgD,hK₀,?_⟩
  intro J p hp hprime K hK
  letI : Fact p.Prime := ⟨hp⟩
  have hKpos : 0<K := hK₀.trans_le hK
  letI : NeZero K := ⟨hKpos.ne'⟩
  obtain ⟨B,hmono,hB⟩ := hfamily J p hp hprime
  let C := fun i ↦ thickenedSet p K (B i)
  refine ⟨C,fun i j hij ↦ thickenedSet_mono p K (hmono hij),?_⟩
  intro i hi j hj z
  let μ : ℝ := 4*(level D i:ℝ)*(level D j:ℝ)
  have hμ : 0 ≤ μ := by dsimp [μ]; positivity
  have hf : ∀ t s : ZMod p, |((mixedFiber p (B i) (B j) t s).card:ℝ)-μ| ≤ (η/2)*μ := by
    intro t s
    have hh := hB i hi j hj (t,s)
    simpa only [pairCount,mixedFiber,Prod.mk_sub_mk] using hh
  have hh := Erdos66MixedCyclicThickening.thickenedSet_error p K (B i) (B j) μ ((η/2)*μ) hf z
  change |(cyclicCount ((p*K)^2) (C i) (C j) z:ℝ)-(K:ℝ)^2*μ| ≤
    (K:ℝ)^2*((η/2)*μ)+2*K*(μ+(η/2)*μ) at hh
  have hKscale := hthick K hK
  have hrest : 2*(1+η/2) ≤ (η/2)*(K:ℝ) := by linarith
  have hm := mul_le_mul_of_nonneg_left hrest (show (0:ℝ) ≤ (K:ℝ)*μ by positivity)
  have hbound : (K:ℝ)^2*((η/2)*μ)+2*K*(μ+(η/2)*μ) ≤ η*((K:ℝ)^2*μ) := by
    nlinarith only [hm]
  convert hh.trans hbound using 1 <;> dsimp only [μ] <;> ring

end Erdos66RangeIndependentCyclic
