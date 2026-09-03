import Submission.SeparatedParametersExplore

/-! A nested rectangular origin repair distributed over several parabolas.
The required field size is linear, rather than quadratic, in the maximum
family index when the band width is fixed. This does not construct an
infinite set of natural numbers. -/
namespace Erdos66BandedRepairFamily
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66AsymmetricRepair
  Erdos66CrossGraph Erdos66RectangleRepair Erdos66PartitionCurveRepair
  Erdos66GridBandPartition Erdos66SeparatedParameters Erdos66CyclicThickening
open scoped Classical
set_option maxHeartbeats 1000000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Each level i uses at most i/g+1 repair curves. -/
theorem banded_origin_repair (hF : ringChar F ≠ 2) (H g : ℕ) (hg : 0 < g)
    (hband : 4*g*H < Fintype.card F)
    (U : ℕ → Finset F) (hmono : Monotone U)
    (hcard : ∀ i ≤ H, (U i).card=2*i)
    (hU0 : ∀ u∈U H, u ≠ 0)
    (hUopp : ∀ u∈U H, ∀ v∈U H, u+v ≠ 0)
    (hspace : 2*(2*H+(H/g+1))+1 < Fintype.card F) :
    ∃ B : ℕ → Finset (F × F), Monotone B ∧
      ∀ i, 0 < i → i ≤ H → ∀ j, 0 < j → j ≤ H →
        pairCount (B i) (B j) 0=1+4*i*j ∧
        ∀ z : F × F, z ≠ 0 →
          pairCount (parabolaSet (U i)) (parabolaSet (U j)) z ≤ pairCount (B i) (B j) z ∧
          pairCount (B i) (B j) z ≤
            pairCount (parabolaSet (U i)) (parabolaSet (U j)) z+
              8*i*(j/g+1)+8*(i/g+1)*j+8*(i/g+1)*(j/g+1) := by
  obtain ⟨w,hw,hw0,hwU,hwopp⟩ := exists_separated_parameters hF (U H) (H/g+1)
    (by rwa [hcard H le_rfl])
  obtain ⟨f,hf,hf0,hfc⟩ := grid_curve_embedding H g hg hband w hw hw0
  have hfopp := curve_images_no_opposites (bandColor H g) w hw0 hwopp f hf0 hfc
  let R : ℕ → Finset (Fin (2*H) × Fin H) := fun i ↦ gridRows (2*i)
  let S : ℕ → Finset (Fin (2*H) × Fin H) := gridCols
  let D := fun i ↦ pointRepair f (R i) (S i)
  let B := fun i ↦ parabolaSet (U i) ∪ D i
  let W := fun i : ℕ ↦
    ((Finset.univ : Finset (Fin (H/g+1))).filter (fun k ↦ k.val < i/g+1)).image w
  have hW0 : ∀ i, ∀ u∈W i, u ≠ 0 := by
    intro i u hu
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hu
    exact hw0 k
  have hWcard : ∀ i ≤ H, (W i).card ≤ i/g+1 := by
    intro i hi
    apply Finset.card_image_le.trans
    rw [card_fin_below _ _ (by exact Nat.add_le_add_right (Nat.div_le_div_right hi) 1)]
  have hDsub : ∀ i, D i ⊆ parabolaSet (W i ∪ (W i).image Neg.neg) := by
    intro i
    apply pointRepair_parabola_subset
    · intro x hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,w (bandColor H g x),?_,(mem_curve _ _).mp (hfc x)⟩
      exact Finset.mem_image.mpr ⟨bandColor H g x,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,row_band_lt H g i hg x hx⟩,rfl⟩
    · intro x hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,w (bandColor H g x),?_,(mem_curve _ _).mp (hfc x)⟩
      exact Finset.mem_image.mpr ⟨bandColor H g x,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,col_band_lt H g i hg x hx⟩,rfl⟩
  have hfnot : ∀ i ≤ H, ∀ x, f x∉parabolaSet (U i) ∧ -(f x)∉parabolaSet (U i) := by
    intro i hi x
    have hU : ∀ u∈U i, u ≠ 0 := fun u hu ↦ hU0 u (hmono hi hu)
    constructor
    · exact curve_point_not_mem (U i) hU _ (hw0 _) (fun hh ↦ (hwU _).1 (hmono hi hh))
        (f x) (hfc x) (hf0 x)
    · exact curve_point_not_mem (U i) hU _ (neg_ne_zero.mpr (hw0 _))
        (fun hh ↦ (hwU _).2 (hmono hi hh)) (-(f x))
        (neg_mem_curve _ (hfc x)) (neg_ne_zero.mpr (hf0 x))
  have hdis : ∀ i ≤ H, Disjoint (parabolaSet (U i)) (D i) := by
    intro i hi
    exact pointRepair_disjoint_base _ f (fun x ↦ (hfnot i hi x).1)
      (fun x ↦ (hfnot i hi x).2) (R i) (S i)
  have horigin : ∀ i ≤ H, ∀ j, pairCount (D j) (parabolaSet (U i)) 0=0 := by
    intro i hi j
    exact pointRepair_base_origin _ f (fun x ↦ (hfnot i hi x).1)
      (fun x ↦ (hfnot i hi x).2) (R j) (S j)
  refine ⟨B,?_,?_⟩
  · intro i j hij
    exact Finset.union_subset_union (parabolaSet_mono (hmono hij))
      (pointRepair_mono f (gridRows_mono (by omega)) (gridCols_mono hij))
  · intro i hi hiH j hj hjH
    have hUi : ∀ u∈U i, u ≠ 0 := fun u hu ↦ hU0 u (hmono hiH hu)
    have hUj : ∀ u∈U j, u ≠ 0 := fun u hu ↦ hU0 u (hmono hjH hu)
    have hUij : ∀ u∈U i, ∀ v∈U j, u+v ≠ 0 :=
      fun u hu v hv ↦ hUopp u (hmono hiH hu) v (hmono hjH hv)
    have hnei : (U i).Nonempty := Finset.card_pos.mp (by rw [hcard i hiH]; omega)
    have hnej : (U j).Nonempty := Finset.card_pos.mp (by rw [hcard j hjH]; omega)
    constructor
    · change pairCount (parabolaSet (U i) ∪ D i) (parabolaSet (U j) ∪ D j) 0 = _
      rw [pairCount_union_mixed _ _ _ _ _ (hdis i hiH) (hdis j hjH),
        cross_graph_origin hF (U i) (U j) hUi hUj hUij hnei hnej,
        pairCount_comm (parabolaSet (U i)) (D j),horigin i hiH j,horigin j hjH i]
      change 1+0+0+pairCount (pointRepair f (R i) (S i)) (pointRepair f (R j) (S j)) 0 = _
      rw [pointRepair_origin f hf hfopp,Finset.inter_comm (S i) (R j),
        grid_inter_card (2*i) j (by omega) hjH,grid_inter_card (2*j) i (by omega) hiH]
      ring
    · intro z hz
      obtain ⟨hlo,hhi⟩ := multiple_curve_error hF (U i) (U j) (W i) (W j) hUi hUj
        (hW0 i) (hW0 j) (D i) (D j) (hDsub i) (hDsub j) (hdis i hiH) (hdis j hjH) z hz
      refine ⟨hlo,hhi.trans ?_⟩
      rw [hcard i hiH,hcard j hjH]
      have hwi := hWcard i hiH
      have hwj := hWcard j hjH
      have hh := Nat.mul_le_mul hwi hwj
      nlinarith [Nat.mul_le_mul_left (8*i) hwj,Nat.mul_le_mul_right (8*j) hwi]

end Erdos66BandedRepairFamily
