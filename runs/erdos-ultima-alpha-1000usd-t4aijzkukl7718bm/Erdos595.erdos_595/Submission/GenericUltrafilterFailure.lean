import Submission.CountableExtensionGraph

/-!
The mutual-ultrafilter extension of an explicit countable K4-free graph with
all finite allowable extensions need not retain even the common-neighbor
property. The failure persists after removing all isolated vertices.
This is not a proof or disproof of Erdős 595.
-/

open SimpleGraph Set Filter
open Erdos595Work Erdos595CountableExtension
namespace Erdos595GenericUltrafilterFailure

private lemma leaf_exists (v : Vertex) (F : Finset Vertex) :
    ∃ x, x ∉ F ∧ G.Adj v x ∧ ∀ w ∈ F, w ≠ v → ¬G.Adj w x := by
  classical
  obtain ⟨x,hx,hp,hn⟩ := finite_extension {v,v} (F.erase v)
    (pair_triangleFree v v) (by simp)
  refine ⟨x,?_,(hp v (by simp)).symm,?_⟩
  · intro h
    apply hx
    by_cases he : x = v
    · exact Finset.mem_union_left _ (by simp [he])
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨he,h⟩)
  · intro w hw hwv h
    exact hn w (Finset.mem_erase.mpr ⟨hwv,hw⟩) h.symm

noncomputable def leaf (v : Vertex) (F : Finset Vertex) : Vertex :=
  (leaf_exists v F).choose

lemma leaf_spec (v : Vertex) (F : Finset Vertex) :
    leaf v F ∉ F ∧ G.Adj v (leaf v F) ∧
      ∀ w ∈ F, w ≠ v → ¬G.Adj w (leaf v F) := (leaf_exists v F).choose_spec

noncomputable def fine : Ultrafilter (Finset Vertex) := Ultrafilter.of atTop

lemma eventually_mem (v : Vertex) : {F : Finset Vertex | v ∈ F} ∈ fine := by
  classical
  apply Ultrafilter.of_le (atTop : Filter (Finset Vertex))
  exact Filter.eventually_atTop.mpr ⟨{v},fun F hF => hF (by simp)⟩

noncomputable def point (v : Vertex) : Ultrafilter Vertex := Ultrafilter.map (leaf v) fine

lemma trace_eq (v : Vertex) : {w | G.neighborSet w ∈ point v} = {v} := by
  ext w
  change G.neighborSet w ∈ point v ↔ w = v
  constructor
  · intro hm
    by_contra hwv
    rw [point,Ultrafilter.mem_map] at hm
    obtain ⟨F,hF,hFm⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (eventually_mem w) hm)
    exact (leaf_spec v F).2.2 w hF hwv hFm
  · rintro rfl
    rw [point,Ultrafilter.mem_map]
    exact Filter.Eventually.of_forall (fun F => (leaf_spec w F).2.1)

lemma no_singleton (v w : Vertex) : {w} ∉ point v := by
  intro hm
  rw [point,Ultrafilter.mem_map] at hm
  obtain ⟨F,hF,he⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (eventually_mem w) hm)
  exact (leaf_spec v F).1 (by simpa using he ▸ hF)

lemma eq_pure_of_singleton {A : Type*} (q : Ultrafilter A) (a : A) (ha : {a} ∈ q) : q = pure a := by
  apply Ultrafilter.ext
  intro S
  rw [Ultrafilter.mem_pure]
  constructor
  · intro hS
    obtain ⟨x,hx,hxS⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem ha hS)
    exact hx ▸ hxS
  · intro hS
    exact Filter.mem_of_superset ha (fun x hx => hx ▸ hS)

abbrev G₁ := ultrafilterGraph G G_cliqueFree

lemma point_pure (v : Vertex) : G₁.Adj (point v) (pure v) := by
  constructor
  · change {w | G.neighborSet w ∈ (pure v : Ultrafilter Vertex)} ∈ point v
    have he : {w | G.neighborSet w ∈ (pure v : Ultrafilter Vertex)} = G.neighborSet v := by
      ext w
      simp only [Ultrafilter.mem_pure,Set.mem_setOf_eq,SimpleGraph.mem_neighborSet]
      exact G.adj_comm w v
    rw [he]
    have h := Set.mem_singleton v
    rw [← trace_eq v] at h
    exact h
  · change {w | G.neighborSet w ∈ point v} ∈ (pure v : Ultrafilter Vertex)
    rw [trace_eq,Ultrafilter.mem_pure]
    rfl

/-- Each new ultrafilter point is a genuine degree-one vertex at its original vertex. -/
theorem point_neighbors (v : Vertex) (q : Ultrafilter Vertex) :
    G₁.Adj (point v) q ↔ q = pure v := by
  constructor
  · intro h
    have hm := h.2
    change {w | G.neighborSet w ∈ point v} ∈ q at hm
    rw [trace_eq] at hm
    exact eq_pure_of_singleton q v hm
  · rintro rfl
    exact point_pure v

lemma point_not_pure (v w : Vertex) : point v ≠ pure w := by
  intro h
  have hm : {w} ∈ point v := by rw [h,Ultrafilter.mem_pure]; rfl
  exact no_singleton v w hm

lemma point_independent (v w : Vertex) : ¬G₁.Adj (point v) (point w) := by
  rw [point_neighbors]
  exact point_not_pure w v

lemma no_common (v w : Vertex) (hvw : v ≠ w) (q : Ultrafilter Vertex) :
    ¬(G₁.Adj (point v) q ∧ G₁.Adj (point w) q) := by
  rintro ⟨h1,h2⟩
  have hp : (pure v : Ultrafilter Vertex) = pure w :=
    ((point_neighbors v q).mp h1).symm.trans ((point_neighbors w q).mp h2)
  have hm : {v} ∈ (pure w : Ultrafilter Vertex) := by rw [← hp,Ultrafilter.mem_pure]; rfl
  exact hvw ((Ultrafilter.mem_pure.mp hm).symm)

def Active : Set (Ultrafilter Vertex) := {p | ∃ q, G₁.Adj p q}
def Core : SimpleGraph Active := G₁.induce Active

/-- Removing isolated vertices does not restore even common neighbors for pairs. -/
theorem core_pair_failure :
    ∃ p q : Active, p ≠ q ∧ ¬Core.Adj p q ∧ ¬∃ r, Core.Adj p r ∧ Core.Adj q r := by
  classical
  let v := seed 0
  let w := seed 1
  have hvw : v ≠ w := fun h => (by decide : (0 : ℕ) ≠ 1) (seed_injective h)
  let p : Active := ⟨point v,⟨pure v,point_pure v⟩⟩
  let q : Active := ⟨point w,⟨pure w,point_pure w⟩⟩
  refine ⟨p,q,?_,point_independent v w,?_⟩
  · intro he
    have he' : point v = point w := congrArg Subtype.val he
    exact no_common v w hvw (pure v) ⟨point_pure v,by rw [← he']; exact point_pure v⟩
  · rintro ⟨r,hpr,hqr⟩
    exact no_common v w hvw r.val ⟨hpr,hqr⟩

/-- This explicit failure is compatible with the known countable edge cover of the extension. -/
theorem extension_cover : IsCountableUnionOfTriangleFree G₁ :=
  countable_union_ultrafilterGraph_of_countable G G_cliqueFree

#print axioms point_neighbors
#print axioms core_pair_failure
#print axioms extension_cover
end Erdos595GenericUltrafilterFailure
