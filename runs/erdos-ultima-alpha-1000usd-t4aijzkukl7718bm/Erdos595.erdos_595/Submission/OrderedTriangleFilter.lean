import Submission.TriangleFilterCoupling

/-!
The canonical filter on increasing triangles has all three ordered edge
marginals equal to the canonical filter on ascending edges. This is a finite
coupling identity, not a four-clique coupling or an infinite-limit theorem.
-/
set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595OrderedTriangleFilter
open Erdos595Work Erdos595CountableBadEdge
variable {V : Type*} [LinearOrder V] (G : SimpleGraph V)

abbrev Edge := {e : Erdos595ArcAdjoint.Arc G // e.val.1 < e.val.2}

def edgeGenerators : Set (Set (Edge G)) :=
  {s | ∃ H : SimpleGraph V, H.CliqueFree 3 ∧ s = {e | ¬H.Adj e.val.val.1 e.val.val.2}}

def edgeFilter : Filter (Edge G) := Filter.countableGenerate (edgeGenerators G)

instance : CountableInterFilter (edgeFilter G) :=
  inferInstanceAs (CountableInterFilter (Filter.countableGenerate _))

lemma edge_avoids (H : SimpleGraph V) (hH : H.CliqueFree 3) :
    ∀ᶠ e : Edge G in edgeFilter G, ¬H.Adj e.val.val.1 e.val.val.2 :=
  Filter.CountableGenerateSets.basic ⟨H,hH,rfl⟩

/-- This is exactly the restriction of the existing canonical edge filter
along the inclusion of ascending orientations. -/
theorem comap_inclusion :
    Filter.comap (Subtype.val : Edge G → Erdos595ArcAdjoint.Arc G) (coveringFilter G) =
      edgeFilter G := by
  apply le_antisymm
  · apply Filter.le_countableGenerate_iff_of_countableInterFilter.mpr
    rintro s ⟨H,hH,rfl⟩
    exact Filter.preimage_mem_comap (coveringFilter_avoids G H hH)
  · apply Filter.map_le_iff_le_comap.mp
    apply le_coveringFilter G
    intro H hH
    exact edge_avoids G H hH

structure Triangle where
  a : V
  b : V
  c : V
  ab : G.Adj a b
  ac : G.Adj a c
  bc : G.Adj b c
  altb : a < b
  bltc : b < c

def side (i : Fin 3) (t : Triangle G) : Edge G :=
  if i = 0 then ⟨⟨(t.a,t.b),t.ab⟩,t.altb⟩
  else if i = 1 then ⟨⟨(t.a,t.c),t.ac⟩,t.altb.trans t.bltc⟩
  else ⟨⟨(t.b,t.c),t.bc⟩,t.bltc⟩

def avoidTriangle (H : SimpleGraph V) : Set (Triangle G) :=
  {t | ¬H.Adj t.a t.b ∧ ¬H.Adj t.a t.c ∧ ¬H.Adj t.b t.c}

def triangleGenerators : Set (Set (Triangle G)) :=
  {s | ∃ H : SimpleGraph V, H.CliqueFree 3 ∧ s = avoidTriangle G H}

def triangleFilter : Filter (Triangle G) :=
  Filter.countableGenerate (triangleGenerators G)

instance : CountableInterFilter (triangleFilter G) :=
  inferInstanceAs (CountableInterFilter (Filter.countableGenerate _))

lemma avoidTriangle_mem (H : SimpleGraph V) (hH : H.CliqueFree 3) :
    avoidTriangle G H ∈ triangleFilter G :=
  Filter.CountableGenerateSets.basic ⟨H,hH,rfl⟩

lemma side_avoids (H : SimpleGraph V) (i : Fin 3) (t : Triangle G)
    (ht : t ∈ avoidTriangle G H) :
    ¬H.Adj (side G i t).val.val.1 (side G i t).val.val.2 := by
  fin_cases i
  · exact ht.1
  · exact ht.2.1
  · exact ht.2.2

lemma map_side_le (i : Fin 3) :
    Filter.map (side G i) (triangleFilter G) ≤ edgeFilter G := by
  apply Filter.le_countableGenerate_iff_of_countableInterFilter.mpr
  rintro s ⟨H,hH,rfl⟩
  change {t | ¬H.Adj (side G i t).val.val.1 (side G i t).val.val.2} ∈ triangleFilter G
  exact Filter.mem_of_superset (avoidTriangle_mem G H hH) (side_avoids G H i)

/-- Sorting does not try to preserve the role of any one old edge. -/
private lemma sorted (R : SimpleGraph V) {a b c : V}
    (hab : R.Adj a b) (hac : R.Adj a c) (hbc : R.Adj b c) :
    ∃ x y z, x < y ∧ y < z ∧ R.Adj x y ∧ R.Adj x z ∧ R.Adj y z := by
  rcases lt_or_gt_of_ne hab.ne with h₁ | h₁
  · rcases lt_or_gt_of_ne hbc.ne with h₂ | h₂
    · exact ⟨a,b,c,h₁,h₂,hab,hac,hbc⟩
    · rcases lt_or_gt_of_ne hac.ne with h₃ | h₃
      · exact ⟨a,c,b,h₃,h₂, hac,hab,hbc.symm⟩
      · exact ⟨c,a,b,h₃,h₁,hac.symm,hbc.symm,hab⟩
  · rcases lt_or_gt_of_ne hac.ne with h₂ | h₂
    · exact ⟨b,a,c,h₁,h₂,hab.symm,hbc,hac⟩
    · rcases lt_or_gt_of_ne hbc.ne with h₃ | h₃
      · exact ⟨b,c,a,h₃,h₂,hbc,hab.symm,hac.symm⟩
      · exact ⟨c,b,a,h₃,h₁,hbc.symm,hac.symm,hab.symm⟩

lemma le_map_side (i : Fin 3) :
    edgeFilter G ≤ Filter.map (side G i) (triangleFilter G) := by
  classical
  intro S hS
  change (side G i) ⁻¹' S ∈ triangleFilter G at hS
  obtain ⟨T,hT,hTc,hsub⟩ := Filter.mem_countableGenerate_iff.mp hS
  letI : Countable T := hTc.to_subtype
  choose H hH hEq using fun t : T => hT t.property
  have htri : ∀ t : Triangle G, (∀ j : T, t ∈ avoidTriangle G (H j)) → side G i t ∈ S := by
    intro t ht
    apply hsub
    intro s hs
    have he := hEq ⟨s,hs⟩
    change s = _ at he
    rw [he]
    exact ht ⟨s,hs⟩
  let bad (a b : V) : Prop := ∃ h : G.Adj a b, ∃ hl : a < b,
    (⟨⟨(a,b),h⟩,hl⟩ : Edge G) ∉ S
  let R : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ (∀ j : T, ¬(H j).Adj a b) ∧ (bad a b ∨ bad b a)
      symm := fun a b h => ⟨h.1.symm,fun j hj => h.2.1 j hj.symm,h.2.2.symm⟩
      loopless := fun a h => G.loopless a h.1 }
  have hbad {a b : V} (h : R.Adj a b) (hl : a < b) :
      (⟨⟨(a,b),h.1⟩,hl⟩ : Edge G) ∉ S := by
    rcases h.2.2 with ⟨_,_,hn⟩ | ⟨_,hr,_⟩
    · exact hn
    · exact (lt_asymm hl hr).elim
  have hR : R.CliqueFree 3 := by
    intro s hs
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
    obtain ⟨x,y,z,hxy,hyz,h₁,h₂,h₃⟩ := sorted R hab hac hbc
    let t : Triangle G := ⟨x,y,z,h₁.1,h₂.1,h₃.1,hxy,hyz⟩
    have ht : side G i t ∈ S := htri t (fun j => ⟨h₁.2.1 j,h₂.2.1 j,h₃.2.1 j⟩)
    fin_cases i
    · exact hbad h₁ hxy ht
    · exact hbad h₂ (hxy.trans hyz) ht
    · exact hbad h₃ hyz ht
  have hall : ∀ᶠ e : Edge G in edgeFilter G, ∀ j : T, ¬(H j).Adj e.val.val.1 e.val.val.2 :=
    eventually_countable_forall.mpr (fun j => edge_avoids G (H j) (hH j))
  filter_upwards [hall,edge_avoids G R hR] with e he hn
  by_contra hnot
  exact hn ⟨e.val.property,he,Or.inl ⟨e.val.property,e.property,hnot⟩⟩

/-- All ordered sides have exactly the same canonical marginal. -/
theorem map_side (i : Fin 3) :
    Filter.map (side G i) (triangleFilter G) = edgeFilter G :=
  le_antisymm (map_side_le G i) (le_map_side G i)

theorem edgeFilter_neBot_iff :
    (edgeFilter G).NeBot ↔ ¬IsCountableUnionOfTriangleFree G := by
  classical
  constructor
  · intro hF hG
    letI := hF
    obtain ⟨H,hH,hcov⟩ := hG
    have hall : ∀ᶠ e : Edge G in edgeFilter G, ∀ n, ¬(H n).Adj e.val.val.1 e.val.val.2 :=
      eventually_countable_forall.mpr (fun n => edge_avoids G (H n) (hH n))
    obtain ⟨e,he⟩ := hall.exists
    have hadj := e.val.property
    simp only [hcov,SimpleGraph.iSup_adj] at hadj
    obtain ⟨n,hn⟩ := hadj
    exact he n hn
  · intro hG
    refine ⟨fun hb => ?_⟩
    have hempty : (∅ : Set (Edge G)) ∈ edgeFilter G := by rw [hb]; simp
    obtain ⟨S,hS,hSc,hint⟩ := Filter.mem_countableGenerate_iff.mp hempty
    letI : Countable S := hSc.to_subtype
    choose H hH hEq using fun s : S => hS s.property
    apply hG (cover_of_countable_family G H hH ?_)
    intro a b hab
    by_contra hn
    push_neg at hn
    have hnot (e : Edge G) (he : ∀ j, ¬(H j).Adj e.val.val.1 e.val.val.2) : False := by
      apply hint
      intro s hs
      have heq := hEq ⟨s,hs⟩
      change s = _ at heq
      rw [heq]
      exact he ⟨s,hs⟩
    rcases lt_or_gt_of_ne hab.ne with hl | hl
    · exact hnot ⟨⟨(a,b),hab⟩,hl⟩ hn
    · exact hnot ⟨⟨(b,a),hab.symm⟩,hl⟩ (fun j h => hn j h.symm)

/-- Properness is still precisely the unresolved covering obstruction. -/
theorem triangleFilter_neBot_iff :
    (triangleFilter G).NeBot ↔ ¬IsCountableUnionOfTriangleFree G := by
  rw [← edgeFilter_neBot_iff G,← map_side G 0]
  exact (Filter.map_neBot_iff (side G 0)).symm

#print axioms comap_inclusion
#print axioms map_side
#print axioms edgeFilter_neBot_iff
#print axioms triangleFilter_neBot_iff
end Erdos595OrderedTriangleFilter
