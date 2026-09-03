import Submission.IntervalProgressionPartition

/-! The fibers of the complete-block progression partition are explicitly
equivalent to Fin L. This permits density-preserving refinement of each fiber. -/
namespace Erdos3ProgressionFiberEquivalence
open Finset Erdos3IntervalProgressionPartition Erdos3FinitePartitionIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

lemma mem_cell_iff {V I : Type*} [Fintype V] (c : V → I) (x : V) (i : I) :
    x ∈ cell c i ↔ c x = i := by simp only [cell,mem_filter,mem_univ,true_and]

lemma progressionLabel_coordinate {N d L : ℕ} (hd : 0 < d) (hL : 0 < L)
    (a : Fin N) (ha : (cell (progressionLabel N d L) (some a)).Nonempty)
    {j : ℕ} (hj : j < L) : (a.val+j*d)/d%L = j := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨_,hab⟩ := progressionLabel_some_base ((mem_cell_iff _ _ _).mp hx)
  have hr : x.val%d < d := Nat.mod_lt _ hd
  have he : a.val+j*d = (x.val/d/L*L+j)*d+x.val%d := by rw [hab]; unfold blockBase; ring
  rw [he,encoded_div hd hr,show x.val/d/L*L+j = L*(x.val/d/L)+j by ring,
    Nat.mul_add_mod,Nat.mod_eq_of_lt hj]

noncomputable def progressionFiberEquiv {N d L : ℕ} (hd : 0 < d) (hL : 0 < L)
    (a : Fin N) (ha : (cell (progressionLabel N d L) (some a)).Nonempty) :
    Fin L ≃ cell (progressionLabel N d L) (some a) where
  toFun j := ⟨⟨a.val+j.val*d,(progressionLabel_fiber hd hL a ha).1 j j.isLt⟩,
    (mem_cell_iff _ _ _).mpr ((progressionLabel_fiber hd hL a ha).2 _ |>.mpr ⟨j,rfl⟩)⟩
  invFun x := ⟨x.val.val/d%L,Nat.mod_lt _ hL⟩
  left_inv j := Fin.ext (progressionLabel_coordinate hd hL a ha j.isLt)
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    change a.val+(x.val.val/d%L)*d = x.val.val
    obtain ⟨_,hab⟩ := progressionLabel_some_base ((mem_cell_iff _ _ _).mp x.property)
    rw [hab]
    exact blockBase_add_offset d L x.val.val

lemma progressionFiberEquiv_val {N d L : ℕ} (hd : 0 < d) (hL : 0 < L)
    (a : Fin N) (ha : (cell (progressionLabel N d L) (some a)).Nonempty) (j : Fin L) :
    (progressionFiberEquiv hd hL a ha j).val.val = a.val+j.val*d := rfl

/-- Conditional sums on a complete outer fiber are exactly sums in its local
progression coordinate, with no loss of density. -/
lemma progressionLabel_charge_coordinate {N d L : ℕ} (hd : 0 < d) (hL : 0 < L)
    (a : Fin N) (ha : (cell (progressionLabel N d L) (some a)).Nonempty) (F : Fin L → ℝ) :
    cellCharge (progressionLabel N d L) (fun x ↦ F ⟨x.val/d%L,Nat.mod_lt _ hL⟩) (some a) =
      (∑ j : Fin L, F j)/(N : ℝ) := by
  unfold cellCharge
  rw [Fintype.expect_eq_sum_div_card,Fintype.card_fin]
  congr 1
  let e := progressionFiberEquiv hd hL a ha
  calc
    _ = ∑ x : cell (progressionLabel N d L) (some a), F ⟨x.val.val/d%L,Nat.mod_lt _ hL⟩ := by
      rw [sum_coe_sort (cell (progressionLabel N d L) (some a)) (fun x : Fin N ↦ F ⟨x.val/d%L,Nat.mod_lt _ hL⟩)]
      simp only [cell,sum_filter]
      apply sum_congr rfl
      intro x _
      split_ifs <;> rfl
    _ = ∑ j : Fin L, F j := by
      apply (Fintype.sum_equiv e _ _ ?_).symm
      intro j
      congr 1
      exact (e.left_inv j).symm

lemma progressionLabel_inner_bad_charge {N d L : ℕ} {J : Type*}
    (hd : 0 < d) (hL : 0 < L) (a : Fin N)
    (ha : (cell (progressionLabel N d L) (some a)).Nonempty) (b : Fin L → Option J) :
    cellCharge (progressionLabel N d L)
      (fun x ↦ if b ⟨x.val/d%L,Nat.mod_lt _ hL⟩ = none then 1 else 0) (some a) =
      ((cell b none).card : ℝ)/(N : ℝ) := by
  rw [progressionLabel_charge_coordinate hd hL a ha (fun j ↦ if b j = none then (1 : ℝ) else 0)]
  congr 1
  simp only [cell,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

#print axioms progressionFiberEquiv
#print axioms progressionLabel_inner_bad_charge
end Erdos3ProgressionFiberEquivalence
