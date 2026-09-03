import Submission.AggregateBlockTransferExplore
import Submission.AffineRootAggregateExplore

/-! Carry transfer preserves collective flatness from a field plane to a
cyclic group, with no loss proportional to the number of color pairs. -/
namespace Erdos66AggregateCyclicThickening
open Erdos66CyclicThickening Erdos66MixedCyclicThickening Erdos66CarryAveraging
  Erdos66OuterCarryProfile Erdos66AggregateBlockTransfer
open scoped Classical
set_option maxHeartbeats 1600000

variable (p K : ℕ) [NeZero p] [NeZero K]

/-- Tags distinguish the fibers of different color pairs, so the original
two-fiber carry bound applies to their collective count. -/
theorem thickened_aggregate_error {ι : Type*} (S : Finset ι)
    (B C : ι → Finset (ZMod p × ZMod p)) (μ E : ℝ)
    (hBC : ∀ t s : ZMod p,
      |(∑ i∈S, ((mixedFiber p (B i) (C i) t s).card : ℝ))-μ| ≤ E)
    (z : ZMod ((p*K)^2)) :
    |(∑ i∈S, (cyclicCount ((p*K)^2) (thickenedSet p K (B i))
      (thickenedSet p K (C i)) z : ℝ))-(K : ℝ)^2*μ| ≤
      (K : ℝ)^2*E+2*K*(μ+E) := by
  obtain ⟨⟨x,s⟩,rfl⟩ := (cyclicDigitEquiv (p*K)).surjective z
  obtain ⟨⟨t,q⟩,rfl⟩ := (blockEquiv p K).surjective x
  let T (u : ZMod p) : Finset (Σ _i : ι, ZMod p × ZMod p) :=
    S.sigma (fun i ↦ mixedFiber p (B i) (C i) t u)
  have hT (u : ZMod p) : |((T u).card : ℝ)-μ| ≤ E := by
    simpa only [T,Finset.card_sigma,Nat.cast_sum] using hBC t u
  have hh := two_fiber_error (T (reduceDigit p K s)) (T (reduceDigit p K s-1))
    (fun iz ↦ smallBorrow p t iz.2.1)
    (fun iz _ ↦ smallBorrow_cases p t iz.2.1)
    (fun iz _ ↦ smallBorrow_cases p t iz.2.1) K q.val q.isLt μ E
    (hT _) (hT _)
  simp only [T,Finset.sum_sigma] at hh
  have hf (i : ι) :
      (cyclicCount ((p*K)^2) (thickenedSet p K (B i)) (thickenedSet p K (C i))
        (cyclicEncode (p*K) (blockDigit p K t q,s)) : ℝ) =
      (K : ℝ)*((∑ z∈mixedFiber p (B i) (C i) t (reduceDigit p K s),
        (triangle K ((q.val : ℤ)-smallBorrow p t z.1) : ℝ))+
      ∑ z∈mixedFiber p (B i) (C i) t (reduceDigit p K s-1),
        (triangle K ((q.val : ℤ)+K-smallBorrow p t z.1) : ℝ)) := by
    change (((thickenedSet p K (B i)).filter (fun a ↦ _-a∈thickenedSet p K (C i))).card : ℝ) = _
    rw [←mixedConv_setWeight,thickenedSet_weight,thickenedSet_weight,Erdos66MixedCyclicThickening.lift_set_convolution_formula]
  change |(∑ i∈S, (cyclicCount ((p*K)^2) (thickenedSet p K (B i)) (thickenedSet p K (C i))
    (cyclicEncode (p*K) (blockDigit p K t q,s)) : ℝ))-(K : ℝ)^2*μ| ≤ _
  simp_rw [hf]
  simpa only [←Finset.mul_sum,Finset.sum_add_distrib] using hh


noncomputable def planeAggregate (B : ℕ → Finset (ZMod p × ZMod p))
    (q : ℕ) (t s : ZMod p) : ℝ :=
  ∑ i∈Finset.range (q+1), ((mixedFiber p (B i) (B (q-i)) t s).card : ℝ)

/-- Collective flatness survives coordinate thickening. -/
theorem thickened_plane_aggregate_error (B : ℕ → Finset (ZMod p × ZMod p))
    (q : ℕ) (μ E : ℝ) (hB : ∀ t s, |planeAggregate p B q t s-μ| ≤ E)
    (z : ZMod ((p*K)^2)) :
    |aggregateCyclic ((p*K)^2) (fun i ↦ thickenedSet p K (B i)) q z-(K : ℝ)^2*μ| ≤
      (K : ℝ)^2*E+2*K*(μ+E) := by
  exact thickened_aggregate_error p K (Finset.range (q+1)) B (fun i ↦ B (q-i)) μ E hB z

/-- Full conditional plane-to-natural transfer. The assumptions concern only
collective counts at two neighboring coarse targets. -/
theorem plane_to_integer_aggregate_error (L : ℕ) [NeZero L]
    (B : ℕ → Finset (ZMod p × ZMod p)) (q : ℕ) (hq : 0<q) (μ E : ℝ)
    (hcur : ∀ t s, |planeAggregate p B q t s-μ| ≤ E)
    (hprev : ∀ t s, |planeAggregate p B (q-1) t s-μ| ≤ E)
    (z : ZMod ((p*K)^2)) (r : Fin L) :
    |(AdditiveCombinatorics.sumRep
      (Erdos66IntegerBlock.blockSet (((p*K)^2)*L)
        (fun i ↦ outerLift ((p*K)^2) L (thickenedSet p K (B i))))
      (q*(((p*K)^2)*L)+(blockDigit ((p*K)^2) L z r).val) : ℝ)-L*(K : ℝ)^2*μ| ≤
      ((L : ℝ)+1)*((K : ℝ)^2*E+2*K*(μ+E))+(K : ℝ)^2*μ := by
  have hh := aggregate_block_error ((p*K)^2) L (fun i ↦ thickenedSet p K (B i)) q hq z r
    ((K : ℝ)^2*μ) ((K : ℝ)^2*E+2*K*(μ+E))
    (thickened_plane_aggregate_error p K B q μ E hcur z)
    (thickened_plane_aggregate_error p K B (q-1) μ E hprev z)
  convert hh using 1 <;> ring_nf

end Erdos66AggregateCyclicThickening
