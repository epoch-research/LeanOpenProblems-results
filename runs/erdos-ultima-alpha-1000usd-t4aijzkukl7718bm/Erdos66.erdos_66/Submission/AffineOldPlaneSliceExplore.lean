import Submission.FreshCurvePrefixExplore
import Submission.GrowingSubfieldBlockExplore

/-! Off-old-plane cosets contain at most two points of each nonzero parabola.
This supplies a cardinality check for coset-block encodings, not an unrestricted
obstruction to the original conjecture. -/
namespace Erdos66AffineOldPlaneSlice
open Erdos66FreshCurvePrefix Erdos66ParabolaRepair Erdos66OriginRepair
  Erdos66FiniteField Erdos66Coset
open scoped Classical
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

lemma oldPlane_add (k : Subfield K) {a b : K×K}
    (ha : a∈oldPlane k) (hb : b∈oldPlane k) : a+b∈oldPlane k := by
  obtain ⟨ha1,ha2⟩ := (mem_oldPlane k a).mp ha
  obtain ⟨hb1,hb2⟩ := (mem_oldPlane k b).mp hb
  exact (mem_oldPlane k (a+b)).mpr ⟨k.add_mem ha1 hb1,k.add_mem ha2 hb2⟩

lemma off_sub_old (k : Subfield K) {z a : K×K}
    (hz : z∉oldPlane k) (ha : a∈oldPlane k) : z-a∉oldPlane k := by
  intro hh
  exact hz (by simpa only [sub_add_cancel] using oldPlane_add k hh ha)

/-- Removing the old-plane part of the curve changes no intersection with
an off-old-plane translated copy of the old plane. -/
lemma old_curve_count_eq_fresh (k : Subfield K) (A : Finset (K×K))
    (hA : A⊆oldPlane k) (u : K) (z : K×K) (hz : z∉oldPlane k) :
    pairCount A (curve u) z=pairCount A (freshCurve k u) z := by
  unfold pairCount
  congr 1
  apply Finset.filter_congr
  intro a ha
  simp only [freshCurve,Finset.mem_sdiff,off_sub_old k hz (hA ha),not_false_eq_true,and_true]

lemma off_old_curve_cap (k : Subfield K) (hK : ringChar K≠2)
    (u : K) (hu : u≠0) (z : K×K) (hz : z∉oldPlane k) :
    pairCount (curve u) (oldPlane k) z≤2 := by
  rw [pairCount_comm,old_curve_count_eq_fresh k (oldPlane k) (Finset.Subset.refl _) u z hz]
  exact arbitrary_old_fresh_curve_cap k hK (oldPlane k) (Finset.Subset.refl _) u hu z

lemma off_old_parabola_cap (k : Subfield K) (hK : ringChar K≠2)
    (U : Finset K) (hU : ∀ u∈U, u≠0) (z : K×K) (hz : z∉oldPlane k) :
    pairCount (parabolaSet U) (oldPlane k) z≤2*U.card := by
  rw [parabolaSet_eq_biUnion]
  calc
    _ ≤ ∑ u∈U, pairCount (curve u) (oldPlane k) z := pairCount_biUnion_left_le _ _ _ _
    _ ≤ ∑ _u∈U, 2 := Finset.sum_le_sum (fun u hu ↦ off_old_curve_cap k hK u (hU u hu) z hz)
    _ = _ := by simp [mul_comm]

/-- An arbitrary partial origin repair adds at most four points to an
affine old-plane coset outside the old plane. -/
lemma off_old_repaired_cap (k : Subfield K) (hK : ringChar K≠2)
    (U : Finset K) (hU : ∀ u∈U, u≠0) (w : K) (hw : w≠0)
    (T : Finset K) (z : K×K) (hz : z∉oldPlane k) :
    pairCount (parabolaSet U∪repairPoints w T) (oldPlane k) z≤2*U.card+4 := by
  have hsub : parabolaSet U∪repairPoints w T⊆parabolaSet (U∪{w,-w}) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · simp only [parabolaSet,Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
      obtain ⟨u,hu,he⟩ := hx
      exact ⟨u,Finset.mem_union_left _ hu,he⟩
    · have hx' := repairPoints_subset w T hx
      simp only [parabolaSet,Finset.mem_filter,Finset.mem_univ,true_and] at hx' ⊢
      obtain ⟨u,hu,he⟩ := hx'
      exact ⟨u,Finset.mem_union_right _ hu,he⟩
  have hnon : ∀ u∈U∪{w,-w}, u≠0 := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu|hu
    · exact hU u hu
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hu
      rcases hu with rfl|rfl
      · exact hw
      · exact neg_ne_zero.mpr hw
  have hcard : (U∪{w,-w}).card≤U.card+2 :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_le_two _)
  exact (pairCount_mono hsub (Finset.Subset.refl _) z).trans
    ((off_old_parabola_cap k hK _ hnon z hz).trans (by omega))

end Erdos66AffineOldPlaneSlice
