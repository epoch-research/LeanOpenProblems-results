import Submission.BadEdgeUltrafilter

/-!
An exact countably complete filter formulation of failure of countable
triangle-free edge covering. Unlike the earlier avoiding ULTRAFILTER criterion,
which detects failure of finite covering, this criterion is equivalent to the
countable covering obstruction. It does not construct such a filter for a
K4-free graph and therefore does not settle Erdős 595.
-/

open SimpleGraph Set Filter
namespace Erdos595CountableBadEdge
open Erdos595Work Erdos595ArcAdjoint

variable {V : Type*}

/-- A countably indexed family covering all G-edges can be reindexed by N
and intersected with G to give equality with its supremum. -/
theorem cover_of_countable_family {C : Type*} [Countable C]
    (G : SimpleGraph V) (H : C → SimpleGraph V) (hH : ∀ i, (H i).CliqueFree 3)
    (hcov : ∀ a b, G.Adj a b → ∃ i, (H i).Adj a b) :
    IsCountableUnionOfTriangleFree G := by
  classical
  letI : Encodable C := Encodable.ofCountable C
  let K : ℕ → SimpleGraph V := fun n => match Encodable.decode (α := C) n with
    | none => ⊥
    | some i => G ⊓ H i
  refine ⟨K, ?_, ?_⟩
  · intro n
    cases hn : Encodable.decode (α := C) n with
    | none => simpa only [K, hn] using (SimpleGraph.cliqueFree_bot (α := V) (n := 3) (by omega))
    | some i => simpa only [K, hn] using ((hH i).anti (show G ⊓ H i ≤ H i from inf_le_right))
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      obtain ⟨i, hi⟩ := hcov a b hab
      exact ⟨Encodable.encode i, by simpa only [K, Encodable.encodek] using
        (show (G ⊓ H i).Adj a b from ⟨hab,hi⟩)⟩
    · rintro ⟨n, hn⟩
      cases hd : Encodable.decode (α := C) n with
      | none => simp only [K, hd, SimpleGraph.bot_adj] at hn
      | some i =>
        have hh : (G ⊓ H i).Adj a b := by simpa only [K, hd] using hn
        exact hh.1

/-- The filter contains the complement of each triangle-free edge set.
This is a membership assertion, stronger than merely not containing that set. -/
def Avoids (G : SimpleGraph V) (F : Filter (Arc G)) : Prop :=
  ∀ H : SimpleGraph V, H.CliqueFree 3 → ∀ᶠ e in F, ¬H.Adj e.val.1 e.val.2

/-- Complements of triangle-free edge sets, on the directed edge carrier. -/
def generators (G : SimpleGraph V) : Set (Set (Arc G)) :=
  {s | ∃ H : SimpleGraph V, H.CliqueFree 3 ∧ s = {e | ¬H.Adj e.val.1 e.val.2}}

/-- Close the generators under COUNTABLE intersections, not merely finite
intersections. Properness of this filter is the unresolved issue. -/
def coveringFilter (G : SimpleGraph V) : Filter (Arc G) :=
  Filter.countableGenerate (generators G)

instance (G : SimpleGraph V) : CountableInterFilter (coveringFilter G) :=
  inferInstanceAs (CountableInterFilter (Filter.countableGenerate _))

theorem coveringFilter_avoids (G : SimpleGraph V) : Avoids G (coveringFilter G) := by
  intro H hH
  exact Filter.CountableGenerateSets.basic ⟨H,hH,rfl⟩

/-- Every countably complete avoiding filter contains all members of the
canonical filter (the order on filters is reverse inclusion of their sets). -/
theorem le_coveringFilter (G : SimpleGraph V) (F : Filter (Arc G))
    [CountableInterFilter F] (hF : Avoids G F) : F ≤ coveringFilter G := by
  apply Filter.le_countableGenerate_iff_of_countableInterFilter.mpr
  rintro s ⟨H,hH,rfl⟩
  exact hF H hH

/-- Countable completeness upgrades rejection of triangle-free pieces to
rejection of every countably coverable edge graph. -/
theorem avoids_coverable (G : SimpleGraph V) (F : Filter (Arc G))
    [CountableInterFilter F] (hF : Avoids G F)
    (H : SimpleGraph V) (hH : IsCountableUnionOfTriangleFree H) :
    ∀ᶠ e in F, ¬H.Adj e.val.1 e.val.2 := by
  obtain ⟨K,hK,hcov⟩ := hH
  have hall : ∀ᶠ e in F, ∀ n, ¬(K n).Adj e.val.1 e.val.2 :=
    eventually_countable_forall.mpr (fun n => hF (K n) (hK n))
  apply hall.mono
  intro e he h
  rw [hcov, SimpleGraph.iSup_adj] at h
  obtain ⟨n,hn⟩ := h
  exact he n hn

/-- A proper countably complete avoiding filter really does obstruct the
COUNTABLE covering in the original conjecture. -/
theorem no_cover_of_filter (G : SimpleGraph V) (F : Filter (Arc G))
    [F.NeBot] [CountableInterFilter F] (hF : Avoids G F) :
    ¬IsCountableUnionOfTriangleFree G := by
  intro hG
  obtain ⟨e,he⟩ := (avoids_coverable G F hF G hG).exists
  exact he e.property

/-- Exact properness criterion for the canonical countably complete filter. -/
theorem coveringFilter_neBot_iff (G : SimpleGraph V) :
    (coveringFilter G).NeBot ↔ ¬IsCountableUnionOfTriangleFree G := by
  classical
  constructor
  · intro h
    letI := h
    exact no_cover_of_filter G _ (coveringFilter_avoids G)
  · intro hG
    refine ⟨?_⟩
    intro hb
    have hempty : (∅ : Set (Arc G)) ∈ coveringFilter G := by rw [hb]; simp
    obtain ⟨S,hS,hSc,hint⟩ := Filter.mem_countableGenerate_iff.mp hempty
    letI : Countable S := hSc.to_subtype
    choose H hH hEq using fun s : S => hS s.property
    apply hG (cover_of_countable_family G H hH ?_)
    intro a b hab
    by_contra hn
    push_neg at hn
    have he : (⟨(a,b),hab⟩ : Arc G) ∈ ⋂₀ S := by
      intro s hs
      have heq := hEq ⟨s,hs⟩
      change s = _ at heq
      rw [heq]
      exact hn ⟨s,hs⟩
    exact hint he

/-- An exact filter reformulation, requiring no extra set-theoretic axioms.
The filter is NOT claimed to be an ultrafilter. -/
theorem no_cover_iff_exists_filter (G : SimpleGraph V) :
    ¬IsCountableUnionOfTriangleFree G ↔
      ∃ F : Filter (Arc G), F.NeBot ∧ CountableInterFilter F ∧ Avoids G F := by
  constructor
  · intro h
    exact ⟨coveringFilter G,(coveringFilter_neBot_iff G).mpr h,inferInstance,
      coveringFilter_avoids G⟩
  · rintro ⟨F,hF,hc,hA⟩
    letI := hF
    letI := hc
    exact no_cover_of_filter G F hA

/-- Every bipartite cut is rejected, so the two endpoints agree on
membership in every fixed vertex subset, eventually in F. -/
theorem endpoint_agreement (G : SimpleGraph V) (F : Filter (Arc G))
    (hF : Avoids G F) (S : Set V) :
    ∀ᶠ e in F, (e.val.1 ∈ S ↔ e.val.2 ∈ S) := by
  classical
  let cut : SimpleGraph V := (⊤ : SimpleGraph Bool).comap (fun v => decide (v ∈ S))
  have hc : cut.CliqueFree 3 :=
    (SimpleGraph.Coloring.mk (G := cut) (fun v => decide (v ∈ S))
      (fun h => h)).colorable.cliqueFree (by decide)
  simpa only [cut, SimpleGraph.comap_adj, SimpleGraph.top_adj, not_not,
    decide_eq_decide] using hF cut hc

/-- The endpoint marginals are equal as filters. -/
theorem marginals_equal (G : SimpleGraph V) (F : Filter (Arc G))
    (hF : Avoids G F) :
    Filter.map (fun e => e.val.1) F = Filter.map (fun e => e.val.2) F := by
  apply Filter.ext
  intro S
  simp only [Filter.mem_map]
  have he := endpoint_agreement G F hF S
  constructor
  · intro h
    exact Filter.mem_of_superset (Filter.inter_mem h he) (fun e he => he.2.mp he.1)
  · intro h
    exact Filter.mem_of_superset (Filter.inter_mem h he) (fun e he => he.2.mpr he.1)

/-- Countable completeness makes agreement simultaneous for all fibers of
a countable vertex label. -/
theorem countable_labels_agree {C : Type*} [Countable C]
    (G : SimpleGraph V) (F : Filter (Arc G)) [CountableInterFilter F]
    (hF : Avoids G F) (f : V → C) :
    ∀ᶠ e in F, f e.val.1 = f e.val.2 := by
  have hall : ∀ᶠ e in F, ∀ c, (f e.val.1 = c ↔ f e.val.2 = c) :=
    eventually_countable_forall.mpr (fun c => endpoint_agreement G F hF {v | f v = c})
  exact hall.mono (fun e he => ((he (f e.val.1)).mp rfl).symm)

/-- In fact every fixed binary-sequence vertex label has equal endpoint
values eventually; arbitrary countably many cuts can be intersected. -/
theorem binary_labels_agree (G : SimpleGraph V) (F : Filter (Arc G))
    [CountableInterFilter F] (hF : Avoids G F) (f : V → ℕ → Fin 2) :
    ∀ᶠ e in F, f e.val.1 = f e.val.2 := by
  have hall : ∀ᶠ e in F, ∀ n, f e.val.1 n = f e.val.2 n :=
    eventually_countable_forall.mpr (fun n => countable_labels_agree G F hF (fun v => f v n))
  exact hall.mono (fun _ h => funext h)

/-- In a K4-free graph, both endpoints eventually avoid each fixed original
neighborhood. This uses the triangle-free neighborhood-induced piece. -/
theorem avoids_neighborhood (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (F : Filter (Arc G)) (hF : Avoids G F) (v : V) :
    ∀ᶠ e in F, ¬G.Adj v e.val.1 ∧ ¬G.Adj v e.val.2 := by
  have hn := hF (Erdos595BadEdge.neighborhoodPiece G v)
    (Erdos595BadEdge.neighborhoodPiece_cliqueFree G hG v)
  have he := endpoint_agreement G F hF (G.neighborSet v)
  filter_upwards [hn,he] with e hn he
  constructor
  · intro h
    exact hn ⟨e.property,h,he.mp h⟩
  · intro h
    exact hn ⟨e.property,he.mpr h,h⟩

/-- Such a filter is incompatible with an ordinary vertex coloring by
binary sequences, recovering the necessary chromatic lower bound. -/
theorem no_binary_coloring (G : SimpleGraph V) (F : Filter (Arc G))
    [F.NeBot] [CountableInterFilter F] (hF : Avoids G F) :
    IsEmpty (G.Coloring (ℕ → Fin 2)) := by
  constructor
  intro c
  obtain ⟨e,he⟩ := (binary_labels_agree G F hF c).exists
  exact c.valid e.property he

/-- Countable completeness allows simultaneous avoidance of the
neighborhoods of an arbitrary fixed countable set of vertices. -/
theorem avoids_countable_neighborhoods (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (F : Filter (Arc G)) [CountableInterFilter F] (hF : Avoids G F)
    (S : Set V) (hS : S.Countable) :
    ∀ᶠ e in F, ∀ v ∈ S, ¬G.Adj v e.val.1 ∧ ¬G.Adj v e.val.2 :=
  (eventually_countable_ball hS).mpr (fun v _ => avoids_neighborhood G hG F hF v)

/-- Any graph containing an F-large set of original edges must itself
fail countable covering. This does not assert that every positive set is large. -/
theorem large_graph_no_cover (G : SimpleGraph V) (F : Filter (Arc G))
    [F.NeBot] [CountableInterFilter F] (hF : Avoids G F)
    (H : SimpleGraph V) (hH : ∀ᶠ e in F, H.Adj e.val.1 e.val.2) :
    ¬IsCountableUnionOfTriangleFree H := by
  intro hc
  obtain ⟨e,ha,hn⟩ := (hH.and (avoids_coverable G F hF H hc)).exists
  exact hn ha

#print axioms le_coveringFilter
#print axioms no_binary_coloring
#print axioms avoids_countable_neighborhoods
#print axioms large_graph_no_cover
#print axioms coveringFilter_neBot_iff
#print axioms no_cover_iff_exists_filter
#print axioms marginals_equal
#print axioms binary_labels_agree
#print axioms avoids_neighborhood
end Erdos595CountableBadEdge
