import Submission.PartitionCurveRepairExplore

/-! A rectangular repair grid partitioned into narrow bands of its minimum
coordinate. Every row or column prefix meets only a small initial collection
of bands. This is finite combinatorial infrastructure. -/
namespace Erdos66GridBandPartition
open Erdos66RectangleRepair Erdos66PartitionCurveRepair
open scoped Classical

lemma quotient_fiber_card (R g k : ℕ) (hg : 0 < g) :
    ((Finset.univ : Finset (Fin R)).filter (fun r ↦ r.val/g=k)).card ≤ g := by
  let f : {r : Fin R // r.val/g=k} → Fin g := fun r ↦ ⟨r.val.val%g,Nat.mod_lt _ hg⟩
  have hf : Function.Injective f := by
    intro r s hrs
    have he : r.val.val%g=s.val.val%g := congrArg Fin.val hrs
    have hr := Nat.div_add_mod r.val.val g
    have hs := Nat.div_add_mod s.val.val g
    rw [r.property] at hr
    rw [s.property] at hs
    apply Subtype.ext
    apply Fin.ext
    omega
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_subtype,Fintype.card_fin] using hh

def bandIndex (H g : ℕ) (x : Fin (2*H) × Fin H) : ℕ :=
  min (x.1.val/(2*g)) (x.2.val/g)

lemma bandIndex_lt (H g : ℕ) (x : Fin (2*H) × Fin H) :
    bandIndex H g x < H/g+1 := by
  exact Nat.lt_succ_of_le ((min_le_right _ _).trans
    (Nat.div_le_div_right (Nat.le_of_lt x.2.isLt)))

def bandColor (H g : ℕ) (x : Fin (2*H) × Fin H) : Fin (H/g+1) :=
  ⟨bandIndex H g x,bandIndex_lt H g x⟩

lemma row_band_lt (H g i : ℕ) (hg : 0 < g) (x : Fin (2*H) × Fin H)
    (hx : x ∈ gridRows (2*i)) : (bandColor H g x).val < i/g+1 := by
  have hr : x.1.val < 2*i := by simpa [gridRows] using hx
  have hi := Nat.lt_mul_div_succ i hg
  have hh : x.1.val/(2*g) < i/g+1 :=
    (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by nlinarith)
  exact lt_of_le_of_lt (min_le_left _ _) hh

lemma col_band_lt (H g i : ℕ) (hg : 0 < g) (x : Fin (2*H) × Fin H)
    (hx : x ∈ gridCols i) : (bandColor H g x).val < i/g+1 := by
  have hc : x.2.val < i := by simpa [gridCols] using hx
  have hh : x.2.val/g < i/g+1 := Nat.lt_succ_of_le (Nat.div_le_div_right hc.le)
  exact lt_of_le_of_lt (min_le_right _ _) hh

/-- A band contains at most 4*g*H grid points, rather than 2*H^2. -/
lemma band_fiber_card (H g k : ℕ) (hg : 0 < g) :
    Fintype.card {x : Fin (2*H) × Fin H // bandIndex H g x=k} ≤ 4*g*H := by
  let R := (Finset.univ : Finset (Fin (2*H))).filter (fun r ↦ r.val/(2*g)=k)
  let C := (Finset.univ : Finset (Fin H)).filter (fun c ↦ c.val/g=k)
  have hsub : (Finset.univ.filter (fun x : Fin (2*H) × Fin H ↦ bandIndex H g x=k)) ⊆
      R.product Finset.univ ∪ Finset.univ.product C := by
    intro x hx
    have hh := (Finset.mem_filter.mp hx).2
    have he : x.1.val/(2*g)=k ∨ x.2.val/g=k := by
      dsimp [bandIndex] at hh
      omega
    rcases he with he | he
    · exact Finset.mem_union_left _ (by simp [R,he])
    · exact Finset.mem_union_right _ (by simp [C,he])
  rw [Fintype.card_subtype]
  apply (Finset.card_le_card hsub).trans
  apply (Finset.card_union_le _ _).trans
  simp only [Finset.product_eq_sprod,Finset.card_product,Finset.card_univ,Fintype.card_fin]
  have hr : R.card ≤ 2*g := quotient_fiber_card (2*H) (2*g) k (by positivity)
  have hc : C.card ≤ g := quotient_fiber_card H g k hg
  nlinarith [Nat.mul_le_mul_right H hr,Nat.mul_le_mul_left (2*H) hc]

lemma bandColor_fiber_card (H g : ℕ) (hg : 0 < g) (k : Fin (H/g+1)) :
    Fintype.card {x : Fin (2*H) × Fin H // bandColor H g x=k} ≤ 4*g*H := by
  have he : ∀ x : Fin (2*H) × Fin H, bandColor H g x=k ↔ bandIndex H g x=k.val := by
    intro x
    exact Fin.ext_iff
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  exact band_fiber_card H g k.val hg

/-- The grid can be placed on H/g+1 parabolas whenever each individual band
fits into the nonzero elements of the field. -/
theorem grid_curve_embedding {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (H g : ℕ) (hg : 0 < g) (hp : 4*g*H < Fintype.card F)
    (w : Fin (H/g+1) → F) (hw : Function.Injective w) (hw0 : ∀ i, w i ≠ 0) :
    ∃ f : Fin (2*H) × Fin H → F × F, Function.Injective f ∧
      (∀ x, (f x).1 ≠ 0) ∧ ∀ x, f x ∈ Erdos66ParabolaRepair.curve (w (bandColor H g x)) := by
  apply partition_curve_embedding (bandColor H g) w hw hw0
  intro k
  convert (bandColor_fiber_card H g hg k).trans_lt hp using 1
  congr 1
  exact Subsingleton.elim _ _

end Erdos66GridBandPartition
