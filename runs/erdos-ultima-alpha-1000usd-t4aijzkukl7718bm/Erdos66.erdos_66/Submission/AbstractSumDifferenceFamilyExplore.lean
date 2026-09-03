import Submission.SumDifferenceFamilyExplore

/-! The origin repair and nonzero difference estimates separated from the
particular method of constructing a parameter family. -/
namespace Erdos66AbstractSumDifferenceFamily
open Erdos66OriginRepair Erdos66FiniteField Erdos66CrossGraph
  Erdos66ParabolaRepair Erdos66AsymmetricRepair Erdos66RectangleRepair
  Erdos66SumDifferenceRepair Erdos66DegenerateCrossGraph
open scoped Classical
set_option maxHeartbeats 1200000

theorem repair_parameter_family (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (H : ℕ)
    (hpg : 2*H^2 < p) (hpu : 4*H+1 < p)
    (U : ℕ → Finset (ZMod p)) (hmono : Monotone U)
    (hcard : ∀ h ≤ 2*H, (U h).card=h)
    (hU : ∀ u∈U (2*H), u ≠ 0)
    (hUV : ∀ u∈U (2*H), ∀ v∈U (2*H), u+v ≠ 0) :
    ∃ B : ℕ → Finset (ZMod p × ZMod p), Monotone B ∧
      ∃ E : ℕ → ℕ → ℤ,
        (∀ i j, E i j = (∑ a : ZMod p, |crossCharFiber (U (2*i)) (U (2*j)) a|) +
          ∑ a : ZMod p, |crossCharFiber (U (2*i)) ((U (2*j)).image Neg.neg) a|) ∧
        ∀ i, 0 < i → i ≤ H → ∀ j, 0 < j → j ≤ H →
          0 ≤ E i j ∧
          (∀ z, |(pairCount (B i) (B j) z : ℤ)-4*i*j| ≤ E i j+12*i+12*j+8) ∧
          ∀ z, z ≠ 0 →
            |(pairCount (B i) ((B j).image Neg.neg) z : ℤ)-4*i*j| ≤ E i j+12*i+12*j+8 := by
  have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  obtain ⟨w,hw,hwU,hnwU⟩ := exists_unused_parameter (U (2*H)) (by
    rw [hcard (2*H) le_rfl,ZMod.card]
    omega)
  let R : ℕ → Finset (ZMod p) := fun i ↦ (gridRows (2*i)).image (gridEmbed H p)
  let S : ℕ → Finset (ZMod p) := fun j ↦ (gridCols j).image (gridEmbed H p)
  have hRm : Monotone R := fun i j hij ↦ Finset.image_subset_image (gridRows_mono (by omega))
  have hSm : Monotone S := fun i j hij ↦ Finset.image_subset_image (gridCols_mono hij)
  have hR0 (i : ℕ) : (0 : ZMod p) ∉ R i := by
    rintro hz
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hz
    exact gridEmbed_ne_zero H p hpg x he
  have hS0 (i : ℕ) : (0 : ZMod p) ∉ S i := by
    rintro hz
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hz
    exact gridEmbed_ne_zero H p hpg x he
  have hRS (i j : ℕ) (hi : i ≤ H) (hj : j ≤ H) :
      (R i ∩ S j).card = 2*i*j :=
    grid_image_inter_card (gridEmbed H p) (gridEmbed_injective H p hpg)
      (2*i) j (by omega) hj
  let D := fun i ↦ asymmetricRepair w (R i) (S i)
  let B := fun i ↦ parabolaSet (U (2*i)) ∪ D i
  let es := fun i j ↦ ∑ a : ZMod p, |crossCharFiber (U (2*i)) (U (2*j)) a|
  let ed := fun i j ↦ ∑ a : ZMod p, |crossCharFiber (U (2*i)) ((U (2*j)).image Neg.neg) a|
  let err := fun i j ↦ es i j+ed i j
  refine ⟨B,?_,err,(fun i j ↦ rfl),?_⟩
  · intro i j hij
    exact Finset.union_subset_union (parabolaSet_mono (hmono (by omega)))
      (asymmetricRepair_mono w (hRm hij) (hSm hij))
  · intro i hi hiH j hj hjH
    have hci := hcard (2*i) (by omega)
    have hcj := hcard (2*j) (by omega)
    have hUi : ∀ u ∈ U (2*i), u ≠ 0 := fun u hu ↦ hU u (hmono (by omega) hu)
    have hUj : ∀ u ∈ U (2*j), u ≠ 0 := fun u hu ↦ hU u (hmono (by omega) hu)
    have hUij : ∀ u ∈ U (2*i), ∀ v ∈ U (2*j), u+v ≠ 0 :=
      fun u hu v hv ↦ hUV u (hmono (by omega) hu) v (hmono (by omega) hv)
    have hnei : (U (2*i)).Nonempty := Finset.card_pos.mp (by omega)
    have hnej : (U (2*j)).Nonempty := Finset.card_pos.mp (by omega)
    have hwUi : w ∉ U (2*i) := fun hh ↦ hwU (hmono (by omega) hh)
    have hnwUi : -w ∉ U (2*i) := fun hh ↦ hnwU (hmono (by omega) hh)
    have hwUj : w ∉ U (2*j) := fun hh ↦ hwU (hmono (by omega) hh)
    have hnwUj : -w ∉ U (2*j) := fun hh ↦ hnwU (hmono (by omega) hh)
    have hes0 : 0 ≤ es i j := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    have hed0 : 0 ≤ ed i j := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    have herr0 : 0 ≤ err i j := add_nonneg hes0 hed0
    refine ⟨herr0,?_,?_⟩
    · intro z
      obtain ⟨hzero,hother⟩ := asymmetricRepair_mixed hF (U (2*i)) (U (2*j))
        hUi hUj hUij hnei hnej w hw hwUi hnwUi hwUj hnwUj
        (R i) (S i) (R j) (S j) (hR0 i) (hS0 i) (hR0 j) (hS0 j)
      by_cases hz : z = 0
      · subst z
        rw [hzero,hRS i j hiH hjH,Finset.inter_comm (S i) (R j),hRS j i hjH hiH]
        push_cast
        have he : (1 : ℤ)+2*i*j+2*j*i-4*i*j = 1 := by ring
        rw [he,abs_one]
        omega
      · have hb := cross_graph_error hF (U (2*i)) (U (2*j)) hUi hUj hUij hnei hnej z hz
        rw [hci,hcj] at hb
        obtain ⟨hlo,hhi⟩ := hother z hz
        rw [hci,hcj] at hhi
        have hlo' : (pairCount (parabolaSet (U (2*i))) (parabolaSet (U (2*j))) z : ℤ) ≤
            pairCount (B i) (B j) z := by exact_mod_cast hlo
        have hhi' : (pairCount (B i) (B j) z : ℤ) ≤
            pairCount (parabolaSet (U (2*i))) (parabolaSet (U (2*j))) z + 8*i+8*j+8 := by
          have hh : pairCount (B i) (B j) z ≤
              pairCount (parabolaSet (U (2*i))) (parabolaSet (U (2*j))) z+8*i+8*j+8 := by
            dsimp [B,D]
            omega
          exact_mod_cast hh
        push_cast at hb
        change |(_ : ℤ)-2*i*(2*j)| ≤ es i j+2*i+2*j at hb
        rw [abs_le] at hb ⊢
        dsimp [err]
        constructor <;> nlinarith
    · intro z hz
      have hUjn : ∀ v ∈ (U (2*j)).image Neg.neg, v ≠ 0 := by
        intro v hv
        obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
        exact neg_ne_zero.mpr (hUj u hu)
      have hnejn : ((U (2*j)).image Neg.neg).Nonempty := hnej.image _
      have hb := cross_graph_error_allow_opposites hF (U (2*i)) ((U (2*j)).image Neg.neg)
        hUi hUjn hnei hnejn z hz
      rw [← parabolaSet_neg,Finset.card_image_of_injective _ neg_injective,hci,hcj] at hb
      have hDi : D i ⊆ parabolaSet {w,-w} :=
        (asymmetricRepair_subset w (R i) (S i)).trans (repairPoints_subset w (R i ∪ S i))
      have hDj : D j ⊆ parabolaSet {w,-w} :=
        (asymmetricRepair_subset w (R j) (S j)).trans (repairPoints_subset w (R j ∪ S j))
      have hdisi := asymmetricRepair_disjoint (U (2*i)) hUi w hw hwUi hnwUi
        (R i) (S i) (hR0 i) (hS0 i)
      have hdisj := asymmetricRepair_disjoint (U (2*j)) hUj w hw hwUj hnwUj
        (R j) (S j) (hR0 j) (hS0 j)
      obtain ⟨hlo,hhi⟩ := reflected_repair_bounds hF (U (2*i)) (U (2*j)) hUi hUj
        w hw (D i) (D j) hDi hDj hdisi hdisj z hz
      rw [hci,hcj] at hhi
      have hlo' : (pairCount (parabolaSet (U (2*i))) ((parabolaSet (U (2*j))).image Neg.neg) z : ℤ) ≤
          pairCount (B i) ((B j).image Neg.neg) z := by exact_mod_cast hlo
      have hhi' : (pairCount (B i) ((B j).image Neg.neg) z : ℤ) ≤
          pairCount (parabolaSet (U (2*i))) ((parabolaSet (U (2*j))).image Neg.neg) z+8*i+8*j+8 := by
        have hh : pairCount (B i) ((B j).image Neg.neg) z ≤
            pairCount (parabolaSet (U (2*i))) ((parabolaSet (U (2*j))).image Neg.neg) z+8*i+8*j+8 := by
          dsimp [B]
          omega
        exact_mod_cast hh
      push_cast at hb
      change |(_ : ℤ)-2*i*(2*j)| ≤ ed i j+2*(2*i)+2*j at hb
      rw [abs_le] at hb ⊢
      dsimp [err]
      constructor <;> nlinarith


end Erdos66AbstractSumDifferenceFamily
