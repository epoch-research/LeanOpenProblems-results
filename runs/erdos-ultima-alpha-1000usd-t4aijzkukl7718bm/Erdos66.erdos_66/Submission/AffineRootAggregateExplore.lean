import Submission.CrossGraphExplore
import Submission.SharedParameterKernelExplore
import Submission.NatPairAlgebraExplore

/-! Collective root counts for affine parameter labels. All fine targets
share one signed scalar convolution at each fixed coarse target. This is
an algebraic reduction, not an infinite integer construction. -/
namespace Erdos66AffineRootAggregate
open Erdos66FiniteField Erdos66CrossGraph Erdos66OriginRepair
  Erdos66SharedParameterKernel
open scoped Classical
set_option maxHeartbeats 1500000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def rootAggregate (h : ℕ) (a : F) (v : ℕ → ℝ) (q : ℕ) (t s : F) : ℝ :=
  ∑ i∈Finset.range h, ∑ j∈Finset.range h,
    if i+j=q then v i*v j*(Fintype.card {x : F // x^2/(a+i)+(t-x)^2/(a+j)=s} : ℝ) else 0

/-- At a fixed coarse sum i+j=q, the target-dependent character is common
to every pair of labels. -/
theorem rootAggregate_identity (h : ℕ) (a : F) (v : ℕ → ℝ) (q : ℕ)
    (hF : ringChar F ≠ 2) (ha : ∀ i<h, a+(i : F) ≠ 0)
    (hq : 2*a+(q : F) ≠ 0) (t s : F) :
    rootAggregate h a v q t s = labelFiber h v q+
      labelFiber h (fun i ↦ v i*(quadraticChar F (a+i) : ℝ)) q*
        (quadraticChar F ((2*a+(q : F))*s-t^2) : ℝ) := by
  unfold rootAggregate labelFiber
  rw [Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i+j=q
  · simp only [hij,if_true]
    have hparam : (a+(i : F))+(a+(j : F))=2*a+(q : F) := by
      rw [←hij,Nat.cast_add]
      ring
    have hc : (Fintype.card {x : F // x^2/(a+i)+(t-x)^2/(a+j)=s} : ℝ) =
        1+(quadraticChar F (a+i) : ℝ)*(quadraticChar F (a+j) : ℝ)*
          (quadraticChar F (((a+i)+(a+j))*s-t^2) : ℝ) := by
      exact_mod_cast parabola_sum_count hF (a+i) (a+j) t s
        (ha i (Finset.mem_range.mp hi)) (ha j (Finset.mem_range.mp hj))
        (by rwa [hparam])
    rw [hc,hparam]
    ring
  · simp [hij]

/-- This bounds all fine targets without summing their number. The only
remaining error is the signed convolution in the coarse label variable. -/
theorem rootAggregate_error (h : ℕ) (a : F) (v : ℕ → ℝ) (q : ℕ)
    (hF : ringChar F ≠ 2) (ha : ∀ i<h, a+(i : F) ≠ 0)
    (hq : 2*a+(q : F) ≠ 0) (t s : F) :
    |rootAggregate h a v q t s-labelFiber h v q| ≤
      |labelFiber h (fun i ↦ v i*(quadraticChar F (a+i) : ℝ)) q| := by
  rw [rootAggregate_identity h a v q hF ha hq,add_sub_cancel_left,abs_mul]
  have hc : |(quadraticChar F ((2*a+(q : F))*s-t^2) : ℝ)| ≤ 1 := by
    have hh := quadraticChar_abs_le_one (F := F) ((2*a+(q : F))*s-t^(2 : ℕ))
    exact_mod_cast hh
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (abs_nonneg _)

lemma singleton_parabola_pair_count (u v t s : F) :
    (pairCount (parabolaSet {u}) (parabolaSet {v}) (t,s) : ℤ) =
      (Fintype.card {x : F // x^2/u+(t-x)^2/v=s} : ℤ) := by
  rw [parabolaSet_crossCount_eq]
  simpa only [finiteConv,graphIndicator,Finset.mem_singleton,exists_eq_left,
    Prod.fst_sub,Prod.snd_sub] using graph_pair_count u v t s

noncomputable def coloredCurve (D : Finset ℕ) (a : F) (i : ℕ) : Finset (F×F) :=
  if i∈D then parabolaSet {a+(i : F)} else ∅

noncomputable def selectedWeight (D : Finset ℕ) (i : ℕ) : ℝ := if i∈D then 1 else 0

/-- The root aggregate is an actual sum of set-pair counts when weights are
zero or one. No parameter-origin multiplicity correction is needed because
the coarse label distinguishes the individual curves. -/
theorem coloredCurve_aggregate (D : Finset ℕ) (a : F) (h q : ℕ) (t s : F) :
    (∑ i∈Finset.range h, ∑ j∈Finset.range h,
      if i+j=q then (pairCount (coloredCurve D a i) (coloredCurve D a j) (t,s) : ℝ) else 0) =
      rootAggregate h a (selectedWeight D) q t s := by
  unfold rootAggregate
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i+j=q
  · simp only [hij,if_true]
    by_cases hiD : i∈D <;> by_cases hjD : j∈D
    · simp only [coloredCurve,selectedWeight,if_pos hiD,if_pos hjD,one_mul]
      exact_mod_cast singleton_parabola_pair_count (a+i) (a+j) t s
    · simp [coloredCurve,selectedWeight,hiD,hjD,pairCount]
    · simp [coloredCurve,selectedWeight,hiD,hjD,pairCount]
    · simp [coloredCurve,selectedWeight,hiD,hjD,pairCount]
  · simp [hij]


lemma selectedWeight_fiber_eq_sumRep (D : Finset ℕ) (h q : ℕ)
    (hD : D ⊆ Finset.range h) :
    labelFiber h (selectedWeight D) q = (AdditiveCombinatorics.sumRep (D : Set ℕ) q : ℝ) := by
  rw [←Erdos66NatPairAlgebra.pairs_self,Erdos66NatPairAlgebra.pairs,
    Finset.product_eq_sprod,Finset.card_filter]
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_product]
  unfold labelFiber
  calc
    _ = ∑ i∈D, ∑ j∈Finset.range h,
        if i+j=q then selectedWeight D i*selectedWeight D j else 0 := by
      symm
      apply Finset.sum_subset hD
      intro i hi hiD
      simp [selectedWeight,hiD]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have he : (∑ j∈Finset.range h,
          if i+j=q then selectedWeight D i*selectedWeight D j else 0) =
          ∑ j∈D, if i+j=q then selectedWeight D i*selectedWeight D j else 0 := by
        symm
        apply Finset.sum_subset hD
        intro j hj hjD
        simp [selectedWeight,hjD]
      rw [he]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [selectedWeight,if_pos hi,if_pos hj,one_mul]

/-- The scalar unsigned main term is precisely the representation function
of the selected coarse indices. The additional condition is a signed one. -/
theorem coloredCurve_aggregate_error (D : Finset ℕ) (a : F) (h q : ℕ)
    (hD : D ⊆ Finset.range h) (hF : ringChar F ≠ 2)
    (ha : ∀ i<h, a+(i : F) ≠ 0) (hq : 2*a+(q : F) ≠ 0) (t s : F) :
    |(∑ i∈Finset.range h, ∑ j∈Finset.range h,
      if i+j=q then (pairCount (coloredCurve D a i) (coloredCurve D a j) (t,s) : ℝ) else 0)-
      (AdditiveCombinatorics.sumRep (D : Set ℕ) q : ℝ)| ≤
      |labelFiber h (fun i ↦ selectedWeight D i*(quadraticChar F (a+i) : ℝ)) q| := by
  rw [coloredCurve_aggregate,←selectedWeight_fiber_eq_sumRep D h q hD]
  exact rootAggregate_error h a (selectedWeight D) q hF ha hq t s


lemma diagonal_sum (h q : ℕ) (hq : q<h) (f : ℕ → ℕ → ℝ) :
    (∑ i∈Finset.range h, ∑ j∈Finset.range h, if i+j=q then f i j else 0) =
      ∑ i∈Finset.range (q+1), f i (q-i) := by
  calc
    _ = ∑ i∈Finset.range (q+1), ∑ j∈Finset.range h, if i+j=q then f i j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hq)
      intro i hi hiq
      have hiq' : q < i := by
        have hh : q+1 ≤ i := by simpa only [Finset.mem_range,not_lt] using hiq
        omega
      apply Finset.sum_eq_zero
      intro j hj
      exact if_neg (by omega)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiq : i ≤ q := by have := Finset.mem_range.mp hi; omega
      have he (j : ℕ) : i+j=q ↔ j=q-i := by omega
      simp_rw [he]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_range,show q-i<h by omega,if_true]

/-- Version indexed in the form used by the actual integer block formula. -/
theorem coloredCurve_plane_error (D : Finset ℕ) (a : F) (h q : ℕ)
    (hD : D ⊆ Finset.range h) (hqh : q<h) (hF : ringChar F ≠ 2)
    (ha : ∀ i<h, a+(i : F) ≠ 0) (hq : 2*a+(q : F) ≠ 0) (t s : F) :
    |(∑ i∈Finset.range (q+1),
      (pairCount (coloredCurve D a i) (coloredCurve D a (q-i)) (t,s) : ℝ))-
      (AdditiveCombinatorics.sumRep (D : Set ℕ) q : ℝ)| ≤
      |labelFiber h (fun i ↦ selectedWeight D i*(quadraticChar F (a+i) : ℝ)) q| := by
  rw [←diagonal_sum h q hqh (fun i j ↦
    (pairCount (coloredCurve D a i) (coloredCurve D a j) (t,s) : ℝ))]
  exact coloredCurve_aggregate_error D a h q hD hF ha hq t s

end Erdos66AffineRootAggregate
