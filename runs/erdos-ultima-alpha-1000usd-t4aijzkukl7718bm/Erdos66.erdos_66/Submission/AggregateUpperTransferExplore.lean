import Submission.AggregateCyclicThickeningExplore

/-! Global upper bounds for the collective carry transfer, including the
initial coarse block q=0. -/
namespace Erdos66AggregateUpperTransfer
open AdditiveCombinatorics Erdos66IntegerBlock Erdos66AggregateBlockTransfer
  Erdos66OuterCarryProfile Erdos66CyclicThickening Erdos66AggregateCyclicThickening
open scoped Classical
set_option maxHeartbeats 2200000

lemma aggregateCyclic_nonneg (M : ℕ) [NeZero M] (C : ℕ → Finset (ZMod M)) (q : ℕ) (z : ZMod M) :
    0 ≤ aggregateCyclic M C q z := Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)

lemma aggregate_block_upper (M J : ℕ) [NeZero M] [NeZero J] (C : ℕ → Finset (ZMod M))
    (U : ℝ) (hU : 0 ≤ U) (hC : ∀ q z, aggregateCyclic M C q z ≤ U)
    (q : ℕ) (z : ZMod M) (r : Fin J) :
    (sumRep (blockSet (M*J) (fun i ↦ outerLift M J (C i)))
      (q*(M*J)+(blockDigit M J z r).val) : ℝ) ≤ ((J : ℝ)+1)*U := by
  by_cases hq : 0<q
  · have habs (q : ℕ) : |aggregateCyclic M C q z-0| ≤ U := by
      rw [sub_zero,abs_of_nonneg (aggregateCyclic_nonneg M C q z)]
      exact hC q z
    have hh := aggregate_block_error M J C q hq z r 0 U (habs q) (habs (q-1))
    simp only [mul_zero,sub_zero,add_zero,zero_add] at hh
    have hh' := (le_abs_self _).trans hh
    nlinarith only [hh']
  · have hq0 : q=0 := by omega
    subst q
    have hf := block_formula (M*J) (fun i ↦ outerLift M J (C i)) 0
      (blockDigit M J z r).val (ZMod.val_lt _)
    simp only [Nat.zero_mul,zero_add,Finset.sum_range_one,Nat.sub_self,Finset.range_zero,
      Finset.sum_empty,add_zero] at hf
    rw [Nat.zero_mul,zero_add,hf,outer_lower_formula]
    push_cast
    have hc : (cyclicCount M (C 0) (C 0) z : ℝ) ≤ U := by simpa [aggregateCyclic] using hC 0 z
    have hl := (aggregateLower_bounds M C 0 z).2
    simp only [aggregateLower,aggregateCyclic,zero_add,Finset.sum_range_one,Nat.sub_self] at hl
    have hr : (r.val : ℝ) ≤ J := by exact_mod_cast r.isLt.le
    have hprod := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α := ℝ) r.val)
    have hprod' := mul_le_mul_of_nonneg_right hr hU
    nlinarith

lemma plane_to_integer_upper (p K J : ℕ) [NeZero p] [NeZero K] [NeZero J]
    (B : ℕ → Finset (ZMod p×ZMod p)) (U : ℝ) (hU : 0 ≤ U)
    (hB : ∀ q t s, planeAggregate p B q t s ≤ U) (q : ℕ) (z : ZMod ((p*K)^2)) (r : Fin J) :
    (sumRep (blockSet (((p*K)^2)*J) (fun i ↦ outerLift ((p*K)^2) J (thickenedSet p K (B i))))
      (q*(((p*K)^2)*J)+(blockDigit ((p*K)^2) J z r).val) : ℝ) ≤
        ((J : ℝ)+1)*((K : ℝ)^2+2*K)*U := by
  have hcyc (q : ℕ) (z : ZMod ((p*K)^2)) :
      aggregateCyclic ((p*K)^2) (fun i ↦ thickenedSet p K (B i)) q z ≤ ((K : ℝ)^2+2*K)*U := by
    have habs (t s : ZMod p) : |planeAggregate p B q t s-0| ≤ U := by
      have hn : 0 ≤ planeAggregate p B q t s := Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
      rw [sub_zero,abs_of_nonneg hn]
      exact hB q t s
    have hh := thickened_plane_aggregate_error p K B q 0 U habs z
    simp only [mul_zero,sub_zero,zero_add,
      abs_of_nonneg (aggregateCyclic_nonneg ((p*K)^2) _ q z)] at hh
    nlinarith
  have hh := aggregate_block_upper ((p*K)^2) J (fun i ↦ thickenedSet p K (B i))
    (((K : ℝ)^2+2*K)*U) (by positivity) hcyc q z r
  nlinarith only [hh]

lemma blockSet_support (M L : ℕ) [NeZero M] (C : ℕ → Finset (ZMod M))
    (hC : ∀ i, L < i → C i=∅) : blockSet M C ⊆ Set.Iio ((L+1)*M) := by
  intro n hn
  change (n : ZMod M)∈C (n/M) at hn
  have hq : n/M ≤ L := by
    by_contra hh
    rw [hC (n/M) (by omega)] at hn
    exact Finset.notMem_empty _ hn
  change n < (L+1)*M
  have hprod := Nat.mul_le_mul_right M hq
  have hmod := Nat.mod_lt n (NeZero.pos M)
  have he := Nat.div_add_mod n M
  rw [Nat.mul_comm M (n/M)] at he
  rw [Nat.add_mul]
  simp only [Nat.one_mul]
  omega

end Erdos66AggregateUpperTransfer
