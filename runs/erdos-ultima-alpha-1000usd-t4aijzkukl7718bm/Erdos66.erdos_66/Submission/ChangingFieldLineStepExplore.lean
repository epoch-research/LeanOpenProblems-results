import Submission.LineRecoloringIterationExplore

/-! Line recoloring with an injective change of color alphabet and field.
These are finite-product-group statements, not natural carry statements. -/
namespace Erdos66ChangingFieldLineStep
open Erdos66LineRecoloring Erdos66LineRecoloringPeaks Erdos66LineRecoloringIteration
  Erdos66OriginRepair Erdos66ParabolaRepair
open scoped Classical
set_option maxHeartbeats 3000000
variable {ι G F E : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup G] [DecidableEq G]
  [Field F] [Fintype F] [DecidableEq F]
  [Field E] [Fintype E] [DecidableEq E]

noncomputable def extend (e : ι ↪ F) (A : ι → Finset G) (u : F) : Finset G :=
  Finset.univ.biUnion (fun i ↦ if e i=u then A i else ∅)

lemma mem_extend (e : ι ↪ F) (A : ι → Finset G) (u : F) (a : G) :
    a∈extend e A u ↔ ∃ i, e i=u ∧ a∈A i := by
  simp only [extend,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    by_cases h : e i=u
    · exact ⟨i,h,by simpa only [h,if_true] using hi⟩
    · simp [h] at hi
  · rintro ⟨i,hi,ha⟩
    exact ⟨i,by simpa only [hi,if_true] using ha⟩

lemma extend_apply (e : ι ↪ F) (A : ι → Finset G) (u : ι) : extend e A (e u)=A u := by
  ext a
  rw [mem_extend]
  constructor
  · rintro ⟨i,hi,ha⟩
    rwa [e.injective hi] at ha
  · intro ha
    exact ⟨u,rfl,ha⟩

lemma extend_mono (e : ι ↪ F) {A B : ι → Finset G} (hAB : ∀ u, A u⊆B u) :
    ∀ v, extend e A v⊆extend e B v := by
  intro v a ha
  rw [mem_extend] at ha ⊢
  obtain ⟨u,hu,ha⟩ := ha
  exact ⟨u,hu,hAB u ha⟩

noncomputable def step (e : ι ↪ F) (A : ι → Finset G) (τ α v : F) : Finset (G×(F×F)) :=
  recolored (extend e A) τ α v

lemma step_mono (e : ι ↪ F) {A B : ι → Finset G} (hAB : ∀ u, A u⊆B u)
    (τ α v : F) : step e A τ α v⊆step e B τ α v :=
  recolored_mono (extend_mono e hAB) τ α v

lemma step_mixed_dominates (e : ι ↪ F) (A : ι → Finset G) (τ α : F) (hα : α≠0)
    (u t : ι) (v w : F) (z : G) :
    pairCount (A u) (A t) z≤pairCount (step e A τ α v) (step e A τ α w)
      (z,oldPoint τ α v (e u)+oldPoint τ α w (e t)) := by
  simpa only [extend_apply,step] using recolored_mixed_dominates (extend e A) τ α hα
    (e u) (e t) v w z

lemma step_self_dominates_twice (e : ι ↪ F) (A : ι → Finset G) (τ α : F) (hα : α≠0)
    (u t : ι) (hut : u≠t) (v : F) (z : G) :
    2*pairCount (A u) (A t) z≤pairCount (step e A τ α v) (step e A τ α v)
      (z,oldPoint τ α v (e u)+oldPoint τ α v (e t)) := by
  simpa only [extend_apply,step] using recolored_self_dominates_twice (extend e A) τ α hα
    (e u) (e t) (fun h ↦ hut (e.injective h)) v z

/-- The two successive fields, and their cardinalities, may differ. -/
theorem two_step_amplification (e : ι ↪ F) (d : F ↪ E) (A : ι → Finset G)
    (τ α : F) (σ β : E) (hα : α≠0) (hβ : β≠0) (u : ι) (v : E) (z : G) :
    ∃ z' : (G×(F×F))×(E×E),
      2*pairCount (A u) (A u) z≤
        pairCount (step d (step e A τ α) σ β v) (step d (step e A τ α) σ β v) z' := by
  let z₁ := (z,oldPoint τ α 0 (e u)+oldPoint τ α 1 (e u))
  refine ⟨(z₁,oldPoint σ β v (d 0)+oldPoint σ β v (d 1)),?_⟩
  have hfirst := step_mixed_dominates e A τ α hα u u 0 1 z
  have hsecond := step_self_dominates_twice d (step e A τ α) σ β hβ 0 1 zero_ne_one v z₁
  exact (Nat.mul_le_mul_left 2 hfirst).trans hsecond

lemma step_nonempty (e : ι ↪ F) (A : ι → Finset G) (τ α : F) (hα : α≠0)
    (u : ι) (hA : (A u).Nonempty) (v : F) : (step e A τ α v).Nonempty := by
  obtain ⟨a,ha⟩ := hA
  refine ⟨(a,oldPoint τ α v (e u)),?_⟩
  rw [step,oldPoint,mem_recolored,label_oldRow α v (e u) hα,extend_apply]
  exact ⟨ha,rfl⟩

lemma union_step_membership (e : ι ↪ F) (A : ι → Finset G) (τ α x y : F) (a : G) :
    (a,(x,y))∈Finset.univ.biUnion (step e A τ α) ↔
      ∃ u : ι, a∈A u ∧ y=e u*x+τ*(e u)^2 := by
  change (a,(x,y))∈Finset.univ.biUnion (recolored (extend e A) τ α) ↔ _
  rw [union_recolored_membership]
  simp only [mem_extend]
  constructor
  · rintro ⟨v,⟨u,hu,ha⟩,hy⟩
    exact ⟨u,ha,by rwa [hu]⟩
  · rintro ⟨u,hu,hy⟩
    exact ⟨e u,⟨u,rfl,hu⟩,hy⟩

/-- One retained old point supplies an entire affine line. Its opposite-row
pairs give a peak at least as large as the NEW field, without disjointness
or any restriction on added points. -/
theorem field_size_peak (e : ι ↪ F) (A : ι → Finset G) (τ α : F)
    (u : ι) (hA : (A u).Nonempty) :
    ∃ z : G×(F×F), Fintype.card F≤
      pairCount (Finset.univ.biUnion (step e A τ α))
        (Finset.univ.biUnion (step e A τ α)) z := by
  obtain ⟨a,ha⟩ := hA
  let S := Finset.univ.biUnion (step e A τ α)
  let f (x : F) : G×(F×F) := (a,(x,e u*x+τ*(e u)^2))
  refine ⟨(a+a,((0:F),2*τ*(e u)^2)),?_⟩
  have hinj : Function.Injective f := by
    intro x y h
    exact congrArg (fun z : G×(F×F) ↦ z.2.1) h
  have hsub : Finset.univ.image f⊆S.filter (fun b ↦ (a+a,((0:F),2*τ*(e u)^2))-b∈S) := by
    intro b hb
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb
    apply Finset.mem_filter.mpr
    constructor
    · exact (union_step_membership e A τ α x _ a).mpr ⟨u,ha,rfl⟩
    · change (a+a-a,(0-x,2*τ*(e u)^2-(e u*x+τ*(e u)^2)))∈S
      rw [add_sub_cancel_right]
      apply (union_step_membership e A τ α _ _ a).mpr
      refine ⟨u,ha,?_⟩
      ring
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj,Finset.card_univ] at hc
  exact hc

end Erdos66ChangingFieldLineStep
