import Submission.ColoredBlockTransferExplore

/-! Collective, rather than pairwise, cyclic flatness suffices for the outer
block transfer. No infinite compatible family is constructed here. -/
namespace Erdos66AggregateBlockTransfer
open AdditiveCombinatorics Erdos66IntegerBlock Erdos66CyclicThickening
  Erdos66OuterCarryProfile
open scoped Classical
set_option maxHeartbeats 1800000

variable (M : ℕ) [NeZero M]

noncomputable def aggregateCyclic (C : ℕ → Finset (ZMod M)) (q : ℕ) (t : ZMod M) : ℝ :=
  ∑ i∈Finset.range (q+1), (cyclicCount M (C i) (C (q-i)) t : ℝ)

noncomputable def aggregateLower (C : ℕ → Finset (ZMod M)) (q : ℕ) (t : ZMod M) : ℝ :=
  ∑ i∈Finset.range (q+1), (lower M (C i) (C (q-i)) t.val : ℝ)

lemma aggregateLower_bounds (C : ℕ → Finset (ZMod M)) (q : ℕ) (t : ZMod M) :
    0 ≤ aggregateLower M C q t ∧ aggregateLower M C q t ≤ aggregateCyclic M C q t := by
  constructor
  · exact Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
  · apply Finset.sum_le_sum
    intro i hi
    have hh := lower_add_upper M (C i) (C (q-i)) t.val
    change _ = cyclicCount M (C i) (C (q-i)) (t.val : ZMod M) at hh
    rw [ZMod.natCast_zmod_val] at hh
    exact_mod_cast (show lower M (C i) (C (q-i)) t.val ≤ cyclicCount M (C i) (C (q-i)) t by omega)

lemma aggregate_upper (C : ℕ → Finset (ZMod M)) (q : ℕ) (hq : 0 < q) (t : ZMod M) :
    (∑ i∈Finset.range q, (upper M (C i) (C (q-i-1)) t.val : ℝ)) =
      aggregateCyclic M C (q-1) t-aggregateLower M C (q-1) t := by
  unfold aggregateCyclic aggregateLower
  rw [show q-1+1=q by omega,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show q-i-1=q-1-i by omega]
  have hh := lower_add_upper M (C i) (C (q-1-i)) t.val
  change _ = cyclicCount M (C i) (C (q-1-i)) (t.val : ZMod M) at hh
  rw [ZMod.natCast_zmod_val] at hh
  have hh' : (lower M (C i) (C (q-1-i)) t.val : ℝ)+upper M (C i) (C (q-1-i)) t.val =
      cyclicCount M (C i) (C (q-1-i)) t := by exact_mod_cast hh
  linarith

variable (K : ℕ) [NeZero K]

/-- Exact collective identity. The carry error is a difference of consecutive
lower aggregates, not a sum of absolute pairwise errors. -/
theorem aggregate_block_formula (C : ℕ → Finset (ZMod M)) (q : ℕ) (hq : 0 < q)
    (t : ZMod M) (r : Fin K) :
    (sumRep (blockSet (M*K) (fun i ↦ outerLift M K (C i)))
      (q*(M*K)+(blockDigit M K t r).val) : ℝ) =
      r.val*aggregateCyclic M C q t+((K : ℝ)-r.val)*aggregateCyclic M C (q-1) t+
        aggregateLower M C q t-aggregateLower M C (q-1) t := by
  have hf := block_formula (M*K) (fun i ↦ outerLift M K (C i)) q
    (blockDigit M K t r).val (ZMod.val_lt _)
  have hf' := congrArg (fun n : ℕ ↦ (n : ℝ)) hf
  simp only [Nat.cast_add,Nat.cast_sum] at hf'
  rw [hf']
  simp_rw [outer_lower_formula,outer_upper_formula,Nat.cast_add,Nat.cast_mul]
  have hr : ((K-r.val-1 : ℕ) : ℝ)=(K : ℝ)-r.val-1 := by
    rw [Nat.cast_sub (by have := r.isLt; omega),Nat.cast_sub r.isLt.le,Nat.cast_one]
  rw [hr]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  have hc : (∑ i∈Finset.range q, (cyclicCount M (C i) (C (q-i-1)) t : ℝ)) =
      aggregateCyclic M C (q-1) t := by
    unfold aggregateCyclic
    rw [show q-1+1=q by omega]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show q-i-1=q-1-i by omega]
  rw [hc,aggregate_upper M C q hq t]
  change (r.val : ℝ)*aggregateCyclic M C q t+aggregateLower M C q t+
    (((K : ℝ)-r.val-1)*aggregateCyclic M C (q-1) t+
      (aggregateCyclic M C (q-1) t-aggregateLower M C (q-1) t)) = _
  ring

/-- It is enough for the two consecutive cyclic aggregates to be flat. No
individual mixed-count estimate or nesting hypothesis is assumed. -/
theorem aggregate_block_error (C : ℕ → Finset (ZMod M)) (q : ℕ) (hq : 0 < q)
    (t : ZMod M) (r : Fin K) (μ E : ℝ)
    (hcur : |aggregateCyclic M C q t-μ| ≤ E)
    (hprev : |aggregateCyclic M C (q-1) t-μ| ≤ E) :
    |(sumRep (blockSet (M*K) (fun i ↦ outerLift M K (C i)))
      (q*(M*K)+(blockDigit M K t r).val) : ℝ)-K*μ| ≤ K*E+μ+E := by
  obtain ⟨hl0,hl⟩ := aggregateLower_bounds M C q t
  obtain ⟨hp0,hp⟩ := aggregateLower_bounds M C (q-1) t
  have hcurup := (abs_le.mp hcur).2
  have hprevup := (abs_le.mp hprev).2
  have hdiff : |aggregateLower M C q t-aggregateLower M C (q-1) t| ≤ μ+E := by
    rw [abs_le]
    constructor <;> linarith
  have hr0 : (0 : ℝ) ≤ r.val := Nat.cast_nonneg _
  have hrK : (r.val : ℝ) ≤ K := by exact_mod_cast r.isLt.le
  have hKr : 0 ≤ (K : ℝ)-r.val := sub_nonneg.mpr hrK
  have hinterp : |r.val*(aggregateCyclic M C q t-μ)+
      ((K : ℝ)-r.val)*(aggregateCyclic M C (q-1) t-μ)| ≤ K*E := by
    calc
      _ ≤ |(r.val : ℝ)*(aggregateCyclic M C q t-μ)|+
          |((K : ℝ)-r.val)*(aggregateCyclic M C (q-1) t-μ)| := abs_add_le _ _
      _ = r.val*|aggregateCyclic M C q t-μ|+
          ((K : ℝ)-r.val)*|aggregateCyclic M C (q-1) t-μ| := by
            rw [abs_mul,abs_mul,abs_of_nonneg hr0,abs_of_nonneg hKr]
      _ ≤ r.val*E+((K : ℝ)-r.val)*E :=
        add_le_add (mul_le_mul_of_nonneg_left hcur hr0) (mul_le_mul_of_nonneg_left hprev hKr)
      _ = _ := by ring
  rw [aggregate_block_formula M K C q hq t r]
  have he : (r.val : ℝ)*aggregateCyclic M C q t+
      ((K : ℝ)-r.val)*aggregateCyclic M C (q-1) t+
      aggregateLower M C q t-aggregateLower M C (q-1) t-K*μ =
      (r.val*(aggregateCyclic M C q t-μ)+((K : ℝ)-r.val)*(aggregateCyclic M C (q-1) t-μ))+
      (aggregateLower M C q t-aggregateLower M C (q-1) t) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

end Erdos66AggregateBlockTransfer
