import Submission.GrowingParameterTranslateExplore

/-! Enlarging a finite-field parabola parameter set while retaining its exact
old plane slice. Ordinary natural-number carries and intermediate prefixes
are not asserted here. -/
namespace Erdos66GrowingFieldSlice
open Erdos66GrowingParameterTranslate Erdos66OddFieldExtension
  Erdos66OddExtensionFlatSet Erdos66OddExtensionCharacterFiber
  Erdos66FiniteField Erdos66OriginRepair Erdos66ParabolaRepair Erdos66Coset
open scoped Classical
set_option maxHeartbeats 2600000

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]

noncomputable def scalarRange : Finset K := Finset.univ.image (algebraMap F K)

omit [DecidableEq F] [Fintype K] in
lemma mem_scalarRange (x : K) :
    x∈scalarRange (F:=F) ↔ x∈Set.range (algebraMap F K) := by
  simp [scalarRange]

omit [DecidableEq F] [Fintype K] in
lemma scalarRange_card : (scalarRange (F:=F) (K:=K)).card=Fintype.card F := by
  simp [scalarRange,Finset.card_image_of_injective _ (algebraMap F K).injective]

omit [DecidableEq F] [Fintype K] in
lemma zero_mem_scalarRange : (0:K)∈scalarRange (F:=F) := by
  exact (mem_scalarRange 0).mpr ⟨0,map_zero _⟩

omit [DecidableEq F] [Fintype K] in
lemma neg_mem_scalarRange {x : K} (hx : x∈scalarRange (F:=F)) :
    -x∈scalarRange (F:=F) := by
  obtain ⟨a,rfl⟩ := (mem_scalarRange x).mp hx
  exact (mem_scalarRange _).mpr ⟨-a,map_neg _ _⟩

omit [DecidableEq F] [Fintype K] in
lemma image_mem_scalarRange (U : Finset F) {x : K}
    (hx : x∈U.image (algebraMap F K)) : x∈scalarRange (F:=F) := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  exact (mem_scalarRange _).mpr ⟨a,rfl⟩

omit [DecidableEq F] [Fintype K] in
lemma enlarged_admissible (U : Finset F) (V : Finset K)
    (hU : ∀ u∈U, u≠0) (hUU : ∀ u∈U, ∀ v∈U, u+v≠0)
    (hV : Disjoint V (scalarRange (F:=F)))
    (hVV : ∀ u∈V, ∀ v∈V, u+v≠0) :
    (∀ u∈U.image (algebraMap F K)∪V, u≠0) ∧
      ∀ u∈U.image (algebraMap F K)∪V,
        ∀ v∈U.image (algebraMap F K)∪V, u+v≠0 := by
  have hdis := Finset.disjoint_left.mp hV
  have hv0 : ∀ v∈V, v≠0 := by
    intro v hv he
    exact hdis hv (he ▸ zero_mem_scalarRange)
  have huv : ∀ u∈U.image (algebraMap F K), ∀ v∈V, u+v≠0 := by
    intro u hu v hv he
    apply hdis hv
    have hvu : v = -u := by linear_combination he
    rw [hvu]
    exact neg_mem_scalarRange (image_mem_scalarRange U hu)
  constructor
  · intro u hu
    rcases Finset.mem_union.mp hu with hu|hu
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
      exact (map_ne_zero (algebraMap F K)).mpr (hU a ha)
    · exact hv0 u hu
  · intro u hu v hv
    rcases Finset.mem_union.mp hu with hu|hu <;>
      rcases Finset.mem_union.mp hv with hv|hv
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
      rw [←map_add]
      exact (map_ne_zero (algebraMap F K)).mpr (hUU a ha b hb)
    · exact huv u hu v hv
    · simpa only [add_comm] using huv v hv u hu
    · exact hVV u hu v hv

lemma enlarged_old_slice (U : Finset F) (hU : U.Nonempty) (V : Finset K)
    (hV : Disjoint V (scalarRange (F:=F))) (z : F×F) :
    planeMap z∈parabolaSet (U.image (algebraMap F K)∪V) ↔ z∈parabolaSet U := by
  have hmem (Z : Finset K) : planeMap z∈parabolaSet Z ↔
      ∃ u∈Z, planeMap z∈curve u := by simp [parabolaSet,mem_curve]
  constructor
  · intro hz
    obtain ⟨u,hu,hzu⟩ := (hmem _).mp hz
    rcases Finset.mem_union.mp hu with hu|hu
    · apply (parabolaSet_old_slice (K:=K) U z).mp
      exact (hmem _).mpr ⟨u,hu,hzu⟩
    · have hout : u∉Set.range (algebraMap F K) := by
        intro hr
        exact Finset.disjoint_left.mp hV hu ((mem_scalarRange u).mpr hr)
      have hz0 := (outside_parameter_old_slice u hout z.1 z.2).mp hzu
      have he : z=0 := Prod.ext hz0.1 hz0.2
      obtain ⟨a,ha⟩ := hU
      subst z
      simp only [parabolaSet,Finset.mem_filter,Finset.mem_univ,true_and,
        Prod.snd_zero,Prod.fst_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_div]
      exact ⟨a,ha,True.intro⟩
  · intro hz
    have hz' := (parabolaSet_old_slice (K:=K) U z).mpr hz
    obtain ⟨u,hu,hzu⟩ := (hmem _).mp hz'
    exact (hmem _).mpr ⟨u,Finset.mem_union_left _ hu,hzu⟩

/-- A genuinely enlarged parameter family. Its mean is the square of the NEW
cardinality. Old character error is retained under an odd extension, while
the explicit cross cost can be made small relative to the new mean by using
a sufficiently large new block. -/
theorem exists_growing_slice_parameters (hd : Odd (Module.finrank F K))
    (hK : ringChar K≠2) (U : Finset F) (hne : U.Nonempty)
    (hU : ∀ u∈U, u≠0) (hUU : ∀ u∈U, ∀ v∈U, u+v≠0)
    (W S : Finset K) (hS : ∀ x∈W, ∀ y∈W, x+y∈S)
    (hsize : 2*(Fintype.card F*W.card+S.card)<Fintype.card K) :
    ∃ (Z : Finset K) (E : ℝ), U.image (algebraMap F K)⊆Z ∧
      Z.card=U.card+W.card ∧
      (∀ u : F, algebraMap F K u∈Z ↔ u∈U) ∧ (∀ u∈Z, u≠0) ∧
      (∀ u∈Z, ∀ v∈Z, u+v≠0) ∧
      (∀ z : F×F, planeMap z∈parabolaSet Z ↔ z∈parabolaSet U) ∧
      0≤E ∧ E^2≤8*S.card*(W.card:ℝ)^2 ∧
      (∑ z : K, |(charFiber Z z:ℝ)|) ≤
        (∑ z : F, |(charFiber U z:ℝ)|)+E+2*(U.card:ℝ)*W.card ∧
      ∀ z : K×K, z≠0 → |(pairCount (parabolaSet Z) (parabolaSet Z) z:ℝ)-
        ((U.card:ℝ)+W.card)^2| ≤
          (∑ z : F, |(charFiber U z:ℝ)|)+E+2*(U.card:ℝ)*W.card+
            2*((U.card:ℝ)+W.card) := by
  obtain ⟨V,hcard,hV,hVV,henergy⟩ := exists_avoiding_parameter_block hK
    (scalarRange (F:=F)) W S hS (by simpa only [scalarRange_card] using hsize)
  let U' := U.image (algebraMap F K)
  let Z := U'∪V
  let E : ℝ := ∑ z : K, |(charFiber V z:ℝ)|
  have hUV : Disjoint U' V := by
    apply Finset.disjoint_left.mpr
    intro x hx hVx
    exact Finset.disjoint_left.mp hV hVx (image_mem_scalarRange U hx)
  have hcU : U'.card=U.card := Finset.card_image_of_injective _ (algebraMap F K).injective
  have hcZ : Z.card=U.card+W.card := by
    dsimp only [Z]
    rw [Finset.card_union_of_disjoint hUV,hcU,hcard]
  obtain ⟨hZ0,hZZ⟩ := enlarged_admissible U V hU hUU hV hVV
  have hl1 : (∑ z : K, |(charFiber Z z:ℝ)|) ≤
      (∑ z : F, |(charFiber U z:ℝ)|)+E+2*(U.card:ℝ)*W.card := by
    have hh := charFiber_union_l1 U' V hUV
    rw [hcU,hcard,sum_abs_charFiber_map hd U] at hh
    dsimp only [Z,E]
    exact_mod_cast hh
  have hscalar : ∀ u : F, algebraMap F K u∈Z ↔ u∈U := by
    intro u
    have hn : algebraMap F K u∉V := fun hv ↦ Finset.disjoint_left.mp hV hv
      ((mem_scalarRange _).mpr ⟨u,rfl⟩)
    simp only [Z,Finset.mem_union,hn,or_false]
    exact Finset.mem_image.trans ⟨fun ⟨v,hv,he⟩ ↦
      (algebraMap F K).injective he ▸ hv,fun hu ↦ ⟨u,hu,rfl⟩⟩
  refine ⟨Z,E,Finset.subset_union_left,hcZ,hscalar,hZ0,hZZ,
    enlarged_old_slice U hne V hV,Finset.sum_nonneg (fun z _ ↦ abs_nonneg _),
    henergy,hl1,?_⟩
  intro z hz
  have hneZ : Z.Nonempty := (hne.image (algebraMap F K)).mono Finset.subset_union_left
  have hh := graph_set_error_bound hK Z hZ0 hZZ hneZ z.1 z.2
    (by simpa only [Prod.mk.eta] using hz)
  rw [←parabolaSet_pairCount_eq Z z,hcZ] at hh
  have hr : |(pairCount (parabolaSet Z) (parabolaSet Z) z:ℝ)-
      ((U.card:ℝ)+W.card)^2| ≤ (∑ a : K, |(charFiber Z a:ℝ)|)+
        2*((U.card:ℝ)+W.card) := by exact_mod_cast hh
  linarith

end Erdos66GrowingFieldSlice
