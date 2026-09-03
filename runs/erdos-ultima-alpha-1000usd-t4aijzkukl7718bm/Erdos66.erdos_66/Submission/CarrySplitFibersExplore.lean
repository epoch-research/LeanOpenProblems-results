import Submission.RectangularCarryAverageExplore
import Submission.MixedCyclicThickeningExplore

/-! The two endpoint-restricted mixed plane fibers and their averaged carry
bound. The restrictions are retained until after averaging. -/
namespace Erdos66CarrySplitFibers
open Erdos66MixedCyclicThickening Erdos66CyclicThickening Erdos66RectangularCarryAverage
open scoped Classical
set_option maxHeartbeats 1800000
variable (p : ℕ) [NeZero p]

noncomputable def beforeCount (B C : Finset (ZMod p × ZMod p)) (t s : ZMod p) : ℕ :=
  ((mixedFiber p B C t s).filter (fun a ↦ a.1.val≤t.val)).card
noncomputable def afterCount (B C : Finset (ZMod p × ZMod p)) (t s : ZMod p) : ℕ :=
  ((mixedFiber p B C t s).filter (fun a ↦ t.val<a.1.val)).card

lemma before_add_after (B C : Finset (ZMod p × ZMod p)) (t s : ZMod p) :
    beforeCount p B C t s+afterCount p B C t s=(mixedFiber p B C t s).card := by
  simpa only [beforeCount, afterCount, not_le] using
    Finset.card_filter_add_card_filter_not (s := mixedFiber p B C t s) (fun a ↦ a.1.val≤t.val)

lemma before_sum (B C : Finset (ZMod p × ZMod p)) (t s : ZMod p) :
    beforeCount p B C t s = ∑ x : ZMod p, ∑ u : ZMod p,
      if x.val≤t.val ∧ (x,u)∈B ∧ (t-x,s-u)∈C then 1 else 0 := by
  calc
    _ = ∑ a : ZMod p × ZMod p,
        if a∈B ∧ (t-a.1,s-a.2)∈C ∧ a.1.val≤t.val then 1 else 0 := by
      simp only [beforeCount, mixedFiber, Finset.filter_filter, Finset.card_filter,
        ite_and, Finset.sum_ite_mem, Finset.univ_inter]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro u hu
      congr 1
      apply propext
      dsimp
      tauto

lemma after_sum (B C : Finset (ZMod p × ZMod p)) (t s : ZMod p) :
    afterCount p B C t s = ∑ x : ZMod p, ∑ u : ZMod p,
      if t.val<x.val ∧ (x,u)∈B ∧ (t-x,s-u)∈C then 1 else 0 := by
  calc
    _ = ∑ a : ZMod p × ZMod p,
        if a∈B ∧ (t-a.1,s-a.2)∈C ∧ t.val<a.1.val then 1 else 0 := by
      simp only [afterCount, mixedFiber, Finset.filter_filter, Finset.card_filter,
        ite_and, Finset.sum_ite_mem, Finset.univ_inter]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro u hu
      congr 1
      apply propext
      dsimp
      tauto

lemma carry_split (B C : Finset (ZMod p × ZMod p)) (t s : ZMod p) :
    (∑ x : ZMod p, ∑ u : ZMod p,
      if (x,u)∈B ∧ (t-x,s-(borrow p t x:ZMod p)-u)∈C then 1 else 0) =
      beforeCount p B C t s+afterCount p B C t (s-1) := by
  rw [before_sum, after_sum, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : t.val<x.val
  · simp [borrow, h, Nat.not_le.mpr h]
  · simp [borrow, h, Nat.le_of_not_gt h]

lemma after_bounds (B C : Finset (ZMod p × ZMod p)) (t : ZMod p) (μ E : ℝ)
    (hflat : ∀ s, |((mixedFiber p B C t s).card:ℝ)-μ| ≤ E) (s : ZMod p) :
    0≤(afterCount p B C t s:ℝ) ∧ (afterCount p B C t s:ℝ)≤μ+E := by
  have hh : (beforeCount p B C t s:ℝ)+afterCount p B C t s = (mixedFiber p B C t s).card := by
    exact_mod_cast before_add_after p B C t s
  have h0 : (0:ℝ)≤beforeCount p B C t s := Nat.cast_nonneg _
  exact ⟨Nat.cast_nonneg _, by linarith [(abs_le.mp (hflat s)).2]⟩

lemma sum_zmod_val (M : ℕ) [NeZero M] (f : ℕ → ℝ) :
    (∑ x : ZMod M, f x.val) = ∑ i∈Finset.range M, f i := by
  apply Finset.sum_bij (fun x _ ↦ x.val)
  · intro x hx
    exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro x hx y hy hxy
    exact ZMod.val_injective M hxy
  · intro i hi
    exact ⟨(i:ZMod M), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp hi)⟩
  · intro x hx
    rfl

/-- Mixed full-fiber accuracy controls the two-dimensional carry average,
with a boundary cost min(K,L)*(mu+E). -/
theorem averaged_fiber_error (K L : ℕ) [NeZero K] [NeZero L]
    (B C : Finset (ZMod p × ZMod p)) (t s : ZMod p) (μ E : ℝ)
    (hflat : ∀ z, |((mixedFiber p B C t z).card:ℝ)-μ| ≤ E) :
    |(∑ i : ZMod K, ∑ j : ZMod L,
      ((beforeCount p B C t (s-i.val-j.val):ℝ)+afterCount p B C t (s-i.val-j.val-1)))-
      (K:ℝ)*L*μ| ≤ (K:ℝ)*L*E+(min K L:ℕ)*(μ+E) := by
  have hf : ∀ z, |(beforeCount p B C t z:ℝ)+(afterCount p B C t z:ℝ)-μ| ≤ E := by
    intro z
    have hh : (beforeCount p B C t z:ℝ)+afterCount p B C t z=(mixedFiber p B C t z).card := by
      exact_mod_cast before_add_after p B C t z
    simpa only [hh] using hflat z
  have hh := carriedBox_error K L (fun z ↦ (beforeCount p B C t z:ℝ))
    (fun z ↦ (afterCount p B C t z:ℝ)) s μ E hf (after_bounds p B C t μ E hflat)
  have he : (∑ i : ZMod K, ∑ j : ZMod L,
      ((beforeCount p B C t (s-i.val-j.val):ℝ)+afterCount p B C t (s-i.val-j.val-1))) =
      carriedBox K L (fun z ↦ (beforeCount p B C t z:ℝ))
        (fun z ↦ (afterCount p B C t z:ℝ)) s := by
    rw [Finset.sum_comm]
    have hi (j : ZMod L) :
        (∑ i : ZMod K, ((beforeCount p B C t (s-i.val-j.val):ℝ)+afterCount p B C t (s-i.val-j.val-1))) =
        ∑ i∈Finset.range K, ((beforeCount p B C t (s-i-j.val):ℝ)+afterCount p B C t (s-i-j.val-1)) :=
      sum_zmod_val K (fun i ↦ ((beforeCount p B C t (s-i-j.val):ℝ)+afterCount p B C t (s-i-j.val-1)))
    simp_rw [hi]
    rw [sum_zmod_val L (fun j ↦ ∑ i∈Finset.range K,
      ((beforeCount p B C t (s-i-j):ℝ)+afterCount p B C t (s-i-j-1)))]
    unfold carriedBox carriedRow
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    have he : s-(i:ZMod p)-j=s-j-i := by ring
    rw [he]
  rwa [he]

end Erdos66CarrySplitFibers
