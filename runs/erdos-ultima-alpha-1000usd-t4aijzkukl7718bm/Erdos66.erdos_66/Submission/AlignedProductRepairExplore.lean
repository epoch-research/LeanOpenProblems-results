import Submission.ProductProjectionRepairExplore

/-! A symmetric product-parabola repair with injective projections and
exactly 2m points. Both prime fields are larger than m. -/
namespace Erdos66AlignedProductRepair
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66SharedParameterSet
  Erdos66ProductProjectionRepair
open scoped Classical
set_option maxHeartbeats 1000000

def repairInput (p m : ℕ) (i : Fin m) : ZMod p := ((i.val+1 : ℕ) : ZMod p)

lemma repairInput_injective (p m : ℕ) (hm : m<p) : Function.Injective (repairInput p m) := by
  intro i j hij
  have he := congrArg ZMod.val hij
  dsimp [repairInput] at he
  rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_natCast_of_lt (by omega)] at he
  exact Fin.ext (by omega)

lemma repairInput_ne_zero (p m : ℕ) (hm : m<p) (i : Fin m) : repairInput p m i ≠ 0 := by
  intro he
  have hh := congrArg ZMod.val he
  dsimp [repairInput] at hh
  rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at hh
  omega

noncomputable def repairInputs (p m : ℕ) : Finset (ZMod p) :=
  Finset.univ.image (repairInput p m)

lemma repairInputs_zero_notMem (p m : ℕ) (hm : m<p) : (0 : ZMod p)∉repairInputs p m := by
  intro hz
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hz
  exact repairInput_ne_zero p m hm i he

noncomputable def curvePoint (p m : ℕ) [Fact p.Prime] (w : ZMod p) (i : Fin m) : ZMod p × ZMod p :=
  (repairInput p m i,(repairInput p m i)^2/w)

lemma curvePoint_injective (p m : ℕ) [Fact p.Prime] (w : ZMod p) (hm : m<p) :
    Function.Injective (curvePoint p m w) := by
  intro i j he
  exact repairInput_injective p m hm (congrArg Prod.fst he)

lemma curvePoint_mem (p m : ℕ) [Fact p.Prime] (w : ZMod p) (i : Fin m) :
    curvePoint p m w i∈curve w := by simp [mem_curve,curvePoint]

lemma curvePoint_ne_zero (p m : ℕ) [Fact p.Prime] (w : ZMod p) (hm : m<p) (i : Fin m) :
    curvePoint p m w i ≠ 0 := fun he ↦ repairInput_ne_zero p m hm i (congrArg Prod.fst he)

lemma curvePoint_ne_neg (p m : ℕ) [Fact p.Prime] (hp : p ≠ 2) (w : ZMod p)
    (hw : w ≠ 0) (hm : m<p) (i j : Fin m) : curvePoint p m w i ≠ -curvePoint p m w j := by
  intro he
  have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  have hz : curvePoint p m w i∈curve (-w) := he ▸ neg_mem_curve w (curvePoint_mem p m w j)
  exact curvePoint_ne_zero p m w hm i
    (curve_intersection hw (neg_ne_zero.mpr hw) (parameter_ne_neg hF hw)
      (curvePoint_mem p m w i) hz)

noncomputable def signedCurvePoint (p m : ℕ) [Fact p.Prime] (w : ZMod p)
    (bi : Bool × Fin m) : ZMod p × ZMod p :=
  if bi.1 then -curvePoint p m w bi.2 else curvePoint p m w bi.2

lemma signedCurvePoint_injective (p m : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (w : ZMod p) (hw : w ≠ 0) (hm : m<p) : Function.Injective (signedCurvePoint p m w) := by
  rintro ⟨b,i⟩ ⟨c,j⟩ he
  cases b <;> cases c
  · simp only [signedCurvePoint,Bool.false_eq_true,if_false] at he
    exact Prod.ext rfl (curvePoint_injective p m w hm he)
  · simp only [signedCurvePoint,Bool.false_eq_true,if_false,if_true] at he
    exact (curvePoint_ne_neg p m hp w hw hm i j he).elim
  · simp only [signedCurvePoint,Bool.false_eq_true,if_false,if_true] at he
    exact (curvePoint_ne_neg p m hp w hw hm j i he.symm).elim
  · simp only [signedCurvePoint,if_true,neg_inj] at he
    exact Prod.ext rfl (curvePoint_injective p m w hm he)

lemma signedCurvePoint_flip (p m : ℕ) [Fact p.Prime] (w : ZMod p) (bi : Bool × Fin m) :
    signedCurvePoint p m w (!bi.1,bi.2) = -signedCurvePoint p m w bi := by
  obtain ⟨b,i⟩ := bi
  cases b <;> simp [signedCurvePoint]

lemma signedCurvePoint_mem_repair (p m : ℕ) [Fact p.Prime] (w : ZMod p) (bi : Bool × Fin m) :
    signedCurvePoint p m w bi∈repairPoints w (repairInputs p m) := by
  have hi : curvePoint p m w bi.2∈partialCurve w (repairInputs p m) :=
    Finset.mem_image.mpr ⟨repairInput p m bi.2,Finset.mem_image.mpr ⟨bi.2,Finset.mem_univ _,rfl⟩,rfl⟩
  unfold signedCurvePoint
  split_ifs
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨curvePoint p m w bi.2,hi,rfl⟩)
  · exact Finset.mem_union_left _ hi

noncomputable def alignedRepair (p q m : ℕ) [Fact p.Prime] [Fact q.Prime]
    (w : ZMod p) (v : ZMod q) : Finset ((ZMod p × ZMod p) × (ZMod q × ZMod q)) :=
  Finset.univ.image (fun bi : Bool × Fin m ↦ (signedCurvePoint p m w bi,signedCurvePoint q m v bi))

lemma alignedRepair_symmetric (p q m : ℕ) [Fact p.Prime] [Fact q.Prime]
    (w : ZMod p) (v : ZMod q) : ∀ z∈alignedRepair p q m w v, -z∈alignedRepair p q m w v := by
  intro z hz
  obtain ⟨bi,hi,rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨(!bi.1,bi.2),Finset.mem_univ _,
    Prod.ext (signedCurvePoint_flip p m w bi) (signedCurvePoint_flip q m v bi)⟩

lemma alignedRepair_fst_inj (p q m : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (w : ZMod p) (v : ZMod q) (hw : w ≠ 0) (hm : m<p) :
    Set.InjOn Prod.fst ((alignedRepair p q m w v) : Set ((ZMod p × ZMod p) × (ZMod q × ZMod q))) := by
  intro x hx y hy he
  change x∈alignedRepair p q m w v at hx
  change y∈alignedRepair p q m w v at hy
  obtain ⟨bi,hi,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨bj,hj,rfl⟩ := Finset.mem_image.mp hy
  have hij := signedCurvePoint_injective p m hp w hw hm he
  rw [hij]

lemma alignedRepair_snd_inj (p q m : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hq : q ≠ 2) (w : ZMod p) (v : ZMod q) (hv : v ≠ 0) (hm : m<q) :
    Set.InjOn Prod.snd ((alignedRepair p q m w v) : Set ((ZMod p × ZMod p) × (ZMod q × ZMod q))) := by
  intro x hx y hy he
  change x∈alignedRepair p q m w v at hx
  change y∈alignedRepair p q m w v at hy
  obtain ⟨bi,hi,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨bj,hj,rfl⟩ := Finset.mem_image.mp hy
  have hij := signedCurvePoint_injective q m hq v hv hm he
  rw [hij]

lemma alignedRepair_card (p q m : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (w : ZMod p) (v : ZMod q) (hw : w ≠ 0) (hm : m<p) :
    (alignedRepair p q m w v).card = 2*m := by
  unfold alignedRepair
  rw [Finset.card_image_of_injective _ (fun x y he ↦
    signedCurvePoint_injective p m hp w hw hm (congrArg Prod.fst he))]
  simp

lemma alignedRepair_fst_subset (p q m : ℕ) [Fact p.Prime] [Fact q.Prime]
    (w : ZMod p) (v : ZMod q) :
    (alignedRepair p q m w v).image Prod.fst ⊆ repairPoints w (repairInputs p m) := by
  intro x hx
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨bi,hi,rfl⟩ := Finset.mem_image.mp hz
  exact signedCurvePoint_mem_repair p m w bi

lemma alignedRepair_snd_subset (p q m : ℕ) [Fact p.Prime] [Fact q.Prime]
    (w : ZMod p) (v : ZMod q) :
    (alignedRepair p q m w v).image Prod.snd ⊆ repairPoints v (repairInputs q m) := by
  intro x hx
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨bi,hi,rfl⟩ := Finset.mem_image.mp hz
  exact signedCurvePoint_mem_repair q m v bi

lemma alignedRepair_disjoint (p q m h : ℕ) [Fact p.Prime] [Fact q.Prime]
    (u : ℕ → ZMod p) (v : ℕ → ZMod q) (hu : ∀ i<h, u i ≠ 0)
    (w : ZMod p) (w' : ZMod q) (hw : w ≠ 0)
    (hwU : w∉(Finset.range h).image u) (hnwU : -w∉(Finset.range h).image u)
    (hm : m<p) : Disjoint (sharedSet h u v) (alignedRepair p q m w w') := by
  have hU : ∀ a∈(Finset.range h).image u, a ≠ 0 := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact hu i (Finset.mem_range.mp hi)
  have hdis := repairPoints_disjoint ((Finset.range h).image u) hU w hw hwU hnwU
    (repairInputs p m) (repairInputs_zero_notMem p m hm)
  apply Finset.disjoint_left.mpr
  intro z hz hzd
  exact Finset.disjoint_left.mp hdis
    (sharedSet_fst_subset h u v (Finset.mem_image.mpr ⟨z,hz,rfl⟩))
    (alignedRepair_fst_subset p q m w w' (Finset.mem_image.mpr ⟨z,hzd,rfl⟩))

end Erdos66AlignedProductRepair
