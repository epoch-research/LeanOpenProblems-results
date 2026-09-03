import Submission.GenericUltrafilterFailure
import Submission.CountableGenericUniversality

/-!
Every triangle-free subset of the original generic graph is exactly the
original trace of a nonprincipal ultrafilter. Disjoint traces obstruct
common neighbors even for points on triangles with infinite neighborhoods.
No countable-cover obstruction or solution of Erdős 595 is asserted.
-/
set_option autoImplicit false
open SimpleGraph Set Filter
open Erdos595Work Erdos595CountableExtension
namespace Erdos595GenericTrace
open Erdos595GenericUltrafilterFailure (fine eventually_mem)

abbrev U := ultrafilterGraph G G_cliqueFree

def trace (p : Ultrafilter Vertex) : Set Vertex := {v | G.neighborSet v ∈ p}

private lemma witness_exists (S : Set Vertex) (hS : (G.induce S).CliqueFree 3)
    (F : Finset Vertex) : ∃ x, x ∉ F ∧ ∀ w ∈ F, G.Adj w x ↔ w ∈ S := by
  classical
  let A := F.filter (· ∈ S)
  let B := F.filter (· ∉ S)
  have hab : Disjoint A B := by simp [A,B,Finset.disjoint_filter]
  let e : G.induce (A : Set Vertex) ↪g G.induce S :=
    { toFun := fun x => ⟨x.val,(Finset.mem_filter.mp x.property).2⟩
      inj' := fun _ _ h => Subtype.ext (congrArg (fun x : S => x.val) h)
      map_rel_iff' := Iff.rfl }
  have hA : (G.induce (A : Set Vertex)).CliqueFree 3 := hS.comap e
  obtain ⟨x,hx,hp,hn⟩ := finite_extension A B hA hab
  have hAB : A ∪ B = F := by ext w; simp [A,B]; tauto
  refine ⟨x,hAB ▸ hx,?_⟩
  intro w hw
  constructor
  · intro h
    by_contra hws
    exact hn w (Finset.mem_filter.mpr ⟨hw,hws⟩) h.symm
  · intro hws
    exact (hp w (Finset.mem_filter.mpr ⟨hw,hws⟩)).symm

noncomputable def witness (S : Set Vertex) (hS : (G.induce S).CliqueFree 3)
    (F : Finset Vertex) : Vertex := (witness_exists S hS F).choose

lemma witness_spec (S : Set Vertex) (hS : (G.induce S).CliqueFree 3) (F : Finset Vertex) :
    witness S hS F ∉ F ∧ ∀ w ∈ F, G.Adj w (witness S hS F) ↔ w ∈ S :=
  (witness_exists S hS F).choose_spec

noncomputable def point (S : Set Vertex) (hS : (G.induce S).CliqueFree 3) :
    Ultrafilter Vertex := Ultrafilter.map (witness S hS) fine

theorem trace_point (S : Set Vertex) (hS : (G.induce S).CliqueFree 3) :
    trace (point S hS) = S := by
  ext w
  change G.neighborSet w ∈ point S hS ↔ w ∈ S
  rw [point,Ultrafilter.mem_map]
  constructor
  · intro hm
    obtain ⟨F,hF,hFm⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (eventually_mem w) hm)
    exact ((witness_spec S hS F).2 w hF).mp hFm
  · intro hw
    exact Filter.mem_of_superset (eventually_mem w)
      (fun F hF => ((witness_spec S hS F).2 w hF).mpr hw)

lemma point_no_singleton (S : Set Vertex) (hS : (G.induce S).CliqueFree 3) (v : Vertex) :
    {v} ∉ point S hS := by
  intro hm
  rw [point,Ultrafilter.mem_map] at hm
  obtain ⟨F,hF,he⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (eventually_mem v) hm)
  exact (witness_spec S hS F).1 (by simpa using he ▸ hF)

lemma point_not_pure (S : Set Vertex) (hS : (G.induce S).CliqueFree 3) (v : Vertex) :
    point S hS ≠ pure v := by
  intro h
  apply point_no_singleton S hS v
  rw [h,Ultrafilter.mem_pure]
  rfl

/-- The complete range of traces, including the empty trace, is identified. -/
theorem trace_exists_iff (S : Set Vertex) :
    (∃ p : Ultrafilter Vertex, trace p = S) ↔ (G.induce S).CliqueFree 3 := by
  constructor
  · rintro ⟨p,rfl⟩
    exact ultrafilter_trace_cliqueFree G G_cliqueFree p
  · intro hS
    exact ⟨point S hS,trace_point S hS⟩

lemma adj_pure (p : Ultrafilter Vertex) (v : Vertex) : U.Adj p (pure v) ↔ v ∈ trace p := by
  change ({w | G.neighborSet w ∈ (pure v : Ultrafilter Vertex)} ∈ p ∧
    {w | G.neighborSet w ∈ p} ∈ (pure v : Ultrafilter Vertex)) ↔ _
  have he : {w | G.neighborSet w ∈ (pure v : Ultrafilter Vertex)} = G.neighborSet v := by
    ext w
    simp only [Ultrafilter.mem_pure,Set.mem_setOf_eq,SimpleGraph.mem_neighborSet]
    exact G.adj_comm w v
  rw [he,Ultrafilter.mem_pure]
  exact ⟨And.left,fun h => ⟨h,h⟩⟩

lemma pure_adj_pure (v w : Vertex) :
    U.Adj (pure v) (pure w) ↔ G.Adj v w := by
  rw [adj_pure]
  change G.neighborSet w ∈ (pure v : Ultrafilter Vertex) ↔ _
  simp only [Ultrafilter.mem_pure,SimpleGraph.mem_neighborSet,G.adj_comm]

lemma point_adj_pure (S : Set Vertex) (hS : (G.induce S).CliqueFree 3) (v : Vertex) :
    U.Adj (point S hS) (pure v) ↔ v ∈ S := by rw [adj_pure,trace_point]

/-- Any common neighbor must contain both traces as ultrafilter members. -/
theorem no_common_of_disjoint_trace (p q : Ultrafilter Vertex)
    (h : Disjoint (trace p) (trace q)) : ¬∃ r, U.Adj p r ∧ U.Adj q r := by
  rintro ⟨r,hpr,hqr⟩
  have hp : trace p ∈ r := hpr.2
  have hq : trace q ∈ r := hqr.2
  obtain ⟨v,hvp,hvq⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hp hq)
  exact Set.disjoint_left.mp h hvp hvq

def InTriangle (p : Ultrafilter Vertex) : Prop :=
  ∃ q r, U.Adj p q ∧ U.Adj p r ∧ U.Adj q r

theorem point_in_triangle (S : Set Vertex) (hS : (G.induce S).CliqueFree 3)
    {a b : Vertex} (ha : a ∈ S) (hb : b ∈ S) (hab : G.Adj a b) :
    InTriangle (point S hS) :=
  ⟨pure a,pure b,(point_adj_pure S hS a).mpr ha,
    (point_adj_pure S hS b).mpr hb,(pure_adj_pure a b).mpr hab⟩

theorem point_infinite_neighbors (S : Set Vertex) (hS : (G.induce S).CliqueFree 3)
    (hInf : S.Infinite) : (U.neighborSet (point S hS)).Infinite := by
  apply (hInf.image Ultrafilter.pure_injective.injOn).mono
  rintro _ ⟨v,hv,rfl⟩
  exact (point_adj_pure S hS v).mpr hv

/-- The remaining vertices after deleting all finite-degree vertices and
all vertices that do not lie on a triangle. -/
def Rich : Set (Ultrafilter Vertex) :=
  {p | InTriangle p ∧ (U.neighborSet p).Infinite}
abbrev RichGraph := U.induce Rich

private abbrev ModelVertex := Bool × Bool × ℕ
private def model : SimpleGraph ModelVertex where
  Adj x y := x.1 = y.1 ∧ x.2.1 ≠ y.2.1
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => h.2 rfl

private theorem model_triangleFree : model.CliqueFree 3 := by
  have hc : model.Colorable 2 := (SimpleGraph.Coloring.mk (G := model)
    (fun x => x.2.1) (fun h => h.2)).colorable
  exact hc.cliqueFree (by decide)

/-- Even the infinite-degree triangle core fails the pair extension
property. The chosen pair has no common neighbor in the FULL extension. -/
theorem rich_pair_failure :
    ∃ p q : Rich, p ≠ q ∧
      (RichGraph.neighborSet p).Infinite ∧ (RichGraph.neighborSet q).Infinite ∧
      (∃ r t : Rich, RichGraph.Adj p r ∧ RichGraph.Adj p t ∧ RichGraph.Adj r t) ∧
      (∃ r t : Rich, RichGraph.Adj q r ∧ RichGraph.Adj q t ∧ RichGraph.Adj r t) ∧
      ¬∃ r : Ultrafilter Vertex, U.Adj p.val r ∧ U.Adj q.val r := by
  classical
  obtain ⟨e⟩ := Erdos595CountableGenericUniversality.universal_countable model
    (model_triangleFree.mono (by decide))
  let S : Bool → Set Vertex := fun b => Set.range (fun x : Bool × ℕ => e (b,x))
  have hS (b : Bool) : (G.induce (S b)).CliqueFree 3 := by
    let f : G.induce (S b) ↪g model :=
      { toFun := fun x => (b,x.property.choose)
        inj' := by
          intro x y h
          apply Subtype.ext
          exact x.property.choose_spec.symm.trans
            ((congrArg e h).trans y.property.choose_spec)
        map_rel_iff' := by
          intro x y
          rw [← e.map_rel_iff]
          exact iff_of_eq (congrArg₂ G.Adj x.property.choose_spec y.property.choose_spec) }
    exact model_triangleFree.comap f
  have hdis : Disjoint (S false) (S true) := by
    apply Set.disjoint_left.mpr
    rintro v ⟨x,hx⟩ ⟨y,hy⟩
    have hh := congrArg Prod.fst (e.injective (hx.trans hy.symm))
    exact Bool.false_ne_true hh
  have hInf (b : Bool) : (S b).Infinite := by
    have hi : Function.Injective (fun n : ℕ => e (b,false,n)) := by
      intro n m h
      exact congrArg (fun x : ModelVertex => x.2.2) (e.injective h)
    apply (Set.infinite_range_of_injective hi).mono
    rintro _ ⟨n,rfl⟩
    exact ⟨(false,n),rfl⟩
  let P (b : Bool) : Ultrafilter Vertex := point (S b) (hS b)
  have hP (b : Bool) (k : Bool) (n : ℕ) : U.Adj (P b) (pure (e (b,k,n))) :=
    (point_adj_pure (S b) (hS b) _).mpr ⟨(k,n),rfl⟩
  have hedge (b k : Bool) (n m : ℕ) :
      U.Adj (pure (e (b,k,n))) (pure (e (b,!k,m))) := by
    apply (pure_adj_pure _ _).mpr
    apply e.map_rel_iff.mpr
    exact ⟨rfl,by cases k <;> simp⟩
  have hpure (b k : Bool) (n : ℕ) : (pure (e (b,k,n)) : Ultrafilter Vertex) ∈ Rich := by
    constructor
    · exact ⟨P b,pure (e (b,!k,0)),(hP b k n).symm,hedge b k n 0,hP b (!k) 0⟩
    · have hi : Function.Injective (fun m : ℕ => (pure (e (b,!k,m)) : Ultrafilter Vertex)) := by
        intro m l h
        exact congrArg (fun x : ModelVertex => x.2.2)
          (e.injective (Ultrafilter.pure_injective h))
      apply (Set.infinite_range_of_injective hi).mono
      rintro _ ⟨m,rfl⟩
      exact hedge b k n m
  have hPrich (b : Bool) : P b ∈ Rich := by
    constructor
    · exact ⟨pure (e (b,false,0)),pure (e (b,true,0)),hP b false 0,hP b true 0,
        hedge b false 0 0⟩
    · exact point_infinite_neighbors (S b) (hS b) (hInf b)
  let Q (b : Bool) : Rich := ⟨P b,hPrich b⟩
  let R (b k : Bool) (n : ℕ) : Rich := ⟨pure (e (b,k,n)),hpure b k n⟩
  have hQInf (b : Bool) : (RichGraph.neighborSet (Q b)).Infinite := by
    have hi : Function.Injective (R b false) := by
      intro n m h
      exact congrArg (fun x : ModelVertex => x.2.2)
        (e.injective (Ultrafilter.pure_injective (congrArg Subtype.val h)))
    apply (Set.infinite_range_of_injective hi).mono
    rintro _ ⟨n,rfl⟩
    exact hP b false n
  have hQT (b : Bool) : ∃ r t : Rich,
      RichGraph.Adj (Q b) r ∧ RichGraph.Adj (Q b) t ∧ RichGraph.Adj r t :=
    ⟨R b false 0,R b true 0,hP b false 0,hP b true 0,hedge b false 0 0⟩
  have hnone : ¬∃ r, U.Adj (P false) r ∧ U.Adj (P true) r := by
    apply no_common_of_disjoint_trace
    simpa only [P,trace_point] using hdis
  refine ⟨Q false,Q true,?_,hQInf false,hQInf true,hQT false,hQT true,hnone⟩
  intro he
  have he' : P false = P true := congrArg Subtype.val he
  exact hnone ⟨pure (e (false,false,0)),hP false false 0,
    by rw [← he']; exact hP false false 0⟩

#print axioms trace_exists_iff
#print axioms point_not_pure
#print axioms no_common_of_disjoint_trace
#print axioms point_infinite_neighbors
#print axioms rich_pair_failure
end Erdos595GenericTrace
