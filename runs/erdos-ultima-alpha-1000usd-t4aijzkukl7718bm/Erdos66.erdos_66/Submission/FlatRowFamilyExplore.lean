import Submission.GraphRowGeometryExplore

/-! The original mixed-flat prime family with its row geometry explicitly
retained. This does not assert compatibility of different prime fields. -/
namespace Erdos66FlatRowFamily
open Erdos66OriginRepair Erdos66FiniteField Erdos66CrossGraph Erdos66ParabolaRepair
  Erdos66MixedPrimeInterval Erdos66AsymmetricRepair Erdos66RectangleRepair Erdos66GraphRowGeometry
open scoped Classical
set_option maxHeartbeats 1500000

/-- A nested family with flat mixed counts, including the exceptional origin.
For indices `i,j` the main term is `4*i*j`; the error is `O(sqrt(i*j*(i+j))+i+j)`.
The maximum index and the lower bound on the prime may be prescribed independently. -/
theorem exists_mixed_flat_prime_family_with_rows (H N : ℕ) :
    ∃ p : ℕ, ∃ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      N < p ∧ p % 8 = 1 ∧ ∃ B : ℕ → Finset (ZMod p × ZMod p), Monotone B ∧
        (∀ i ≤ H, ∀ s, rowCount (B i) s ≤ 4*i+4) ∧
        ∃ E : ℕ → ℕ → ℤ, ∀ i, 0 < i → i ≤ H → ∀ j, 0 < j → j ≤ H →
          0 ≤ E i j ∧ (E i j) ^ 2 ≤ 16 * (i : ℤ) * j * (i + j) ∧
          ∀ z, |(pairCount (B i) (B j) z : ℤ) - 4 * i * j| ≤
            E i j + 10 * i + 10 * j + 8 := by
  obtain ⟨p, hp, hpN, hp8, U, hmono, hcard, hU, hUV, hE⟩ :=
    exists_prime_parameter_family (2 * H) (max N (max (2 * H ^ 2) (4 * H + 1)))
  letI : Fact p.Prime := ⟨hp⟩
  have hpg : 2 * H ^ 2 < p := by omega
  have hpu : 4 * H + 1 < p := by omega
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  obtain ⟨w, hw, hwU, hnwU⟩ := exists_unused_parameter (U (2 * H)) (by
    rw [hcard (2 * H) le_rfl, ZMod.card]
    omega)
  let E : ℕ → Finset (ZMod p) := fun i ↦ (gridRows (2 * i)).image (gridEmbed H p)
  let F' : ℕ → Finset (ZMod p) := fun j ↦ (gridCols j).image (gridEmbed H p)
  have hEm : Monotone E := fun i j hij ↦ Finset.image_subset_image (gridRows_mono (by omega))
  have hFm : Monotone F' := fun i j hij ↦ Finset.image_subset_image (gridCols_mono hij)
  have hE0 (i : ℕ) : (0 : ZMod p) ∉ E i := by
    rintro hz
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hz
    exact gridEmbed_ne_zero H p hpg x he
  have hF0 (j : ℕ) : (0 : ZMod p) ∉ F' j := by
    rintro hz
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hz
    exact gridEmbed_ne_zero H p hpg x he
  have hEF (i j : ℕ) (hi : i ≤ H) (hj : j ≤ H) :
      (E i ∩ F' j).card = 2 * i * j :=
    grid_image_inter_card (gridEmbed H p) (gridEmbed_injective H p hpg)
      (2 * i) j (by omega) hj
  let B := fun i ↦ parabolaSet (U (2 * i)) ∪ asymmetricRepair w (E i) (F' i)
  let err := fun i j ↦ ∑ a : ZMod p, |crossCharFiber (U (2 * i)) (U (2 * j)) a|
  have hrow (i : ℕ) (hi : i ≤ H) (s : ZMod p) : rowCount (B i) s ≤ 4*i+4 := by
    have hUi : ∀ u∈U (2*i), u≠0 := fun u hu ↦ hU u (hmono (by omega) hu)
    have hsub : B i ⊆ parabolaSet (U (2*i))∪repairPoints w (E i∪F' i) :=
      Finset.union_subset_union (Finset.Subset.refl _) (asymmetricRepair_subset w (E i) (F' i))
    have hh := (rowCount_mono hsub s).trans
      (repaired_row_bound (U (2*i)) hUi w hw (E i∪F' i) s)
    rw [hcard (2*i) (by omega)] at hh
    omega
  refine ⟨p, hp, by omega, hp8, B, ?_, hrow, err, ?_⟩
  · intro i j hij
    exact Finset.union_subset_union (parabolaSet_mono (hmono (by omega)))
      (asymmetricRepair_mono w (hEm hij) (hFm hij))
  · intro i hi hiH j hj hjH
    have hci := hcard (2 * i) (by omega)
    have hcj := hcard (2 * j) (by omega)
    have hUi : ∀ u ∈ U (2 * i), u ≠ 0 := fun u hu ↦ hU u (hmono (by omega) hu)
    have hUj : ∀ v ∈ U (2 * j), v ≠ 0 := fun v hv ↦ hU v (hmono (by omega) hv)
    have hUij : ∀ u ∈ U (2 * i), ∀ v ∈ U (2 * j), u + v ≠ 0 :=
      fun u hu v hv ↦ hUV u (hmono (by omega) hu) v (hmono (by omega) hv)
    have hnei : (U (2 * i)).Nonempty := Finset.card_pos.mp (by omega)
    have hnej : (U (2 * j)).Nonempty := Finset.card_pos.mp (by omega)
    have hwUi : w ∉ U (2 * i) := fun hh ↦ hwU (hmono (by omega) hh)
    have hnwUi : -w ∉ U (2 * i) := fun hh ↦ hnwU (hmono (by omega) hh)
    have hwUj : w ∉ U (2 * j) := fun hh ↦ hwU (hmono (by omega) hh)
    have hnwUj : -w ∉ U (2 * j) := fun hh ↦ hnwU (hmono (by omega) hh)
    obtain ⟨hzero, hother⟩ := asymmetricRepair_mixed hF (U (2 * i)) (U (2 * j))
      hUi hUj hUij hnei hnej w hw hwUi hnwUi hwUj hnwUj
      (E i) (F' i) (E j) (F' j) (hE0 i) (hF0 i) (hE0 j) (hF0 j)
    have herr0 : 0 ≤ err i j := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    refine ⟨herr0, ?_, ?_⟩
    · have he := hE (2 * i) (by omega) (2 * j) (by omega)
      push_cast at he
      dsimp [err]
      nlinarith [he]
    · intro z
      by_cases hz : z = 0
      · subst z
        change |(pairCount _ _ 0 : ℤ) - 4 * i * j| ≤ _
        rw [hzero, hEF i j hiH hjH, Finset.inter_comm (F' i) (E j), hEF j i hjH hiH]
        push_cast
        have he : (1 : ℤ) + 2 * i * j + 2 * j * i - 4 * i * j = 1 := by ring
        rw [he, abs_one]
        omega
      · have hb := cross_graph_error hF (U (2 * i)) (U (2 * j))
          hUi hUj hUij hnei hnej z hz
        rw [hci, hcj] at hb
        obtain ⟨hlo, hhi⟩ := hother z hz
        rw [hci, hcj] at hhi
        have hlo' : (pairCount (parabolaSet (U (2 * i))) (parabolaSet (U (2 * j))) z : ℤ) ≤
            pairCount (B i) (B j) z := by exact_mod_cast hlo
        have hhi' : (pairCount (B i) (B j) z : ℤ) ≤
            pairCount (parabolaSet (U (2 * i))) (parabolaSet (U (2 * j))) z + 8 * i + 8 * j + 8 := by
          dsimp [B]
          have hh : pairCount (parabolaSet (U (2 * i)) ∪ asymmetricRepair w (E i) (F' i))
              (parabolaSet (U (2 * j)) ∪ asymmetricRepair w (E j) (F' j)) z ≤
              pairCount (parabolaSet (U (2 * i))) (parabolaSet (U (2 * j))) z + 8 * i + 8 * j + 8 := by omega
          exact_mod_cast hh
        push_cast at hb
        rw [abs_le] at hb ⊢
        dsimp [err] at herr0 ⊢
        constructor <;> nlinarith


end Erdos66FlatRowFamily
