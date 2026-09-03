import Submission.IntegerBlockExplore

/-! Multiplicative rows preserve a parameter prefix and have exact row mass.
Their mixed counts are weighted linear counts of the old parameter sets.
These identities do not provide the required asymptotic estimates. -/
namespace Erdos66MultiplicativeRows
open Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 1600000
variable {F : Type*} [Field F]

noncomputable def rowMap (a y u : F) : F := (u+a)/(y+1)-a
noncomputable def rowLabel (a y x : F) : F := (y+1)*(x+a)-a

lemma rowLabel_rowMap (a y u : F) (hy : y+1≠0) :
    rowLabel a y (rowMap a y u)=u := by
  dsimp [rowLabel,rowMap]
  field_simp
  <;> ring

lemma rowMap_rowLabel (a y x : F) (hy : y+1≠0) :
    rowMap a y (rowLabel a y x)=x := by
  dsimp [rowLabel,rowMap]
  field_simp
  <;> ring

lemma rowMap_injective (a y : F) (hy : y+1≠0) : Function.Injective (rowMap a y) := by
  intro u v he
  have hh := congrArg (rowLabel a y) he
  simpa only [rowLabel_rowMap a y _ hy] using hh

noncomputable def row (U : Finset F) (a y : F) : Finset F :=
  if y+1=0 then ∅ else U.image (rowMap a y)

lemma mem_row (U : Finset F) (a y x : F) :
    x∈row U a y ↔ y+1≠0 ∧ rowLabel a y x∈U := by
  by_cases hy : y+1=0
  · simp [row,hy]
  · rw [row,if_neg hy]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨hy,by simpa only [rowLabel_rowMap a y u hy] using hu⟩
    · intro hx
      exact ⟨rowLabel a y x,hx.2,rowMap_rowLabel a y x hy⟩

lemma row_zero (U : Finset F) (a : F) : row U a 0=U := by
  ext x
  simp [mem_row,rowLabel]

lemma row_card (U : Finset F) (a y : F) :
    (row U a y).card=if y+1=0 then 0 else U.card := by
  by_cases hy : y+1=0
  · simp [row,hy]
  · simp only [row,if_neg hy,Finset.card_image_of_injective _ (rowMap_injective a y hy)]

noncomputable def linearTarget (a y z t : F) : F :=
  (y+1)*(z+1)*(t+2*a)-a*((y+1)+(z+1))

noncomputable def linearSolution (a y z t u : F) : F :=
  (linearTarget a y z t-(z+1)*u)/(y+1)

lemma reflected_rowLabel (a y z t u : F) (hy : y+1≠0) :
    rowLabel a z (t-rowMap a y u)=linearSolution a y z t u := by
  dsimp [rowLabel,rowMap,linearSolution,linearTarget]
  field_simp
  <;> ring

/-- The endpoint predicate is retained, not discarded by completing the
field count. It may be any predicate on the first spatial endpoint. -/
theorem filtered_row_count (U V : Finset F) (a y z t : F)
    (hy : y+1≠0) (hz : z+1≠0) (Q : F → Prop) :
    ((row U a y).filter (fun x ↦ Q x ∧ t-x∈row V a z)).card=
      (U.filter (fun u ↦ Q (rowMap a y u) ∧ linearSolution a y z t u∈V)).card := by
  rw [show row U a y=U.image (rowMap a y) by simp only [row,if_neg hy],Finset.filter_image,
    Finset.card_image_of_injective _ (rowMap_injective a y hy)]
  congr 1
  apply Finset.filter_congr
  intro u hu
  rw [mem_row,reflected_rowLabel a y z t u hy]
  constructor
  · rintro ⟨hQ,_,hV⟩
    exact ⟨hQ,hV⟩
  · rintro ⟨hQ,hV⟩
    exact ⟨hQ,hz,hV⟩

theorem row_pairCount (U V : Finset F) (a y z t : F)
    (hy : y+1≠0) (hz : z+1≠0) :
    pairCount (row U a y) (row V a z) t=
      (U.filter (fun u ↦ linearSolution a y z t u∈V)).card := by
  simpa only [pairCount,true_and] using filtered_row_count U V a y z t hy hz (fun _ ↦ True)

lemma linearSolution_eq_iff (a y z t u v : F) (hy : y+1≠0) :
    linearSolution a y z t u=v ↔
      (z+1)*u+(y+1)*v=linearTarget a y z t := by
  rw [linearSolution,div_eq_iff hy]
  constructor <;> intro h <;> linear_combination -h

/-- Equal spatial row heights reduce the weighted equation to an ordinary
old-parameter sum, with no quadratic root-location issue. -/
lemma same_row_pairCount (U V : Finset F) (a y t : F) (hy : y+1≠0) :
    pairCount (row U a y) (row V a y) t=
      pairCount U V ((y+1)*(t+2*a)-2*a) := by
  rw [row_pairCount U V a y y t hy hy]
  unfold pairCount
  congr 1
  apply Finset.filter_congr
  intro u hu
  have he : linearSolution a y y t u=(y+1)*(t+2*a)-2*a-u := by
    dsimp [linearSolution,linearTarget]
    field_simp
    <;> ring
  rw [he]

end Erdos66MultiplicativeRows
