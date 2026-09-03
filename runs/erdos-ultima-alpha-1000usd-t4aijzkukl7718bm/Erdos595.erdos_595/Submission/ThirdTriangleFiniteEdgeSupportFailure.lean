import Submission.ThirdFiniteEdgeSupportFailure

/-!
The finite-edge-cover support failure persists for a vertex lying in a
triangle. The original base remains countable and K4-free. This is not
itself a non-coverability theorem.
-/

open SimpleGraph Set Filter
open Erdos595Work Erdos595FinitePalette Erdos595FiniteEdgeCoverIdeal
open Erdos595FiniteEdgeSupportFailure
namespace Erdos595ThirdTriangleFiniteEdgeSupportFailure

def extraSet (M : ℕ) : Set Vertex :=
  {v | match v with | .inl b => b ∈ Cutoff M | .inr _ => True}

lemma extraSet_triangleFree (M : ℕ) : (G.induce (extraSet M)).CliqueFree 3 := by
  let c : extraSet M → Fin 2 := fun v => match v.val with | .inl _ => 0 | .inr _ => 1
  have hc : (G.induce (extraSet M)).Coloring (Fin 2) := SimpleGraph.Coloring.mk c (by
    rintro ⟨x,hx⟩ ⟨y,hy⟩ hab he
    cases x with
    | inl x =>
      cases y with
      | inl y => exact cutoff_independent M hx hy hab
      | inr y => exact (by decide : (0 : Fin 2) ≠ 1) he
    | inr x =>
      cases y with
      | inl y => exact (by decide : (1 : Fin 2) ≠ 0) he
      | inr y => exact hab)
  exact hc.colorable.cliqueFree (by decide)

def admissible₂ (M : ℕ) : Erdos595Extension.Admissible G :=
  ⟨extraSet M,extraSet_triangleFree M⟩

abbrev NewVertex := Vertex ⊕ ℕ

def K : SimpleGraph NewVertex :=
  (Erdos595Extension.apexFamilyGraph G).comap (Sum.map id admissible₂)

lemma K_cliqueFree : K.CliqueFree 4 := by
  have hh := Erdos595Extension.apexFamilyGraph_cliqueFree G G_cliqueFree
  classical
  by_contra hn
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have he : ∀ i j : Fin 4, i ≠ j →
      (Erdos595Extension.apexFamilyGraph G).Adj
        (Sum.map id admissible₂ (f i)) (Sum.map id admissible₂ (f j)) :=
    fun i j h => f.map_rel_iff.mpr h
  exact no_adj_common_neighbors hh (he 0 1 (by decide)) (he 0 2 (by decide))
    (he 1 2 (by decide)) (he 0 3 (by decide)) (he 1 3 (by decide)) (he 2 3 (by decide))

def oldEmbedding : G ↪g K where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

noncomputable def pointK (z : Label) : Ultrafilter NewVertex := Ultrafilter.map Sum.inl (point z)

abbrev K₁ := ultrafilterGraph K K_cliqueFree
abbrev K₂ := ultrafilterGraph K₁ (ultrafilterGraph_cliqueFree K K_cliqueFree)
abbrev K₃ := ultrafilterGraph K₂ (ultrafilterGraph_cliqueFree K₁ (ultrafilterGraph_cliqueFree K K_cliqueFree))

noncomputable def Q₀ : Ultrafilter (Ultrafilter NewVertex) :=
  Ultrafilter.map (fun M => (pure (Sum.inl (Sum.inr M)) : Ultrafilter NewVertex)) Erdos595SuffixSupportTemplate.U
noncomputable def Q₁ : Ultrafilter (Ultrafilter NewVertex) :=
  Ultrafilter.map (fun M => (pure (Sum.inr M) : Ultrafilter NewVertex)) Erdos595SuffixSupportTemplate.U

lemma point_trace_zero (z : Label) : K₁.neighborSet (pointK z) ∈ Q₀ := by
  rw [Q₀,Ultrafilter.mem_map]
  apply Filter.mem_of_superset (Erdos595SuffixSupportTemplate.tail z.2.2)
  intro M hM
  change K₁.Adj (pointK z) (pure (Sum.inl (Sum.inr M)))
  rw [adj_pure,pointK,Ultrafilter.mem_map,point,Ultrafilter.mem_map]
  exact Erdos595SuffixSupportTemplate.cutoff_mem_point z.2.1 z.2.2 M (Nat.le_of_lt hM)

lemma point_trace_one (z : Label) : K₁.neighborSet (pointK z) ∈ Q₁ := by
  rw [Q₁,Ultrafilter.mem_map]
  apply Filter.mem_of_superset (Erdos595SuffixSupportTemplate.tail z.2.2)
  intro M hM
  change K₁.Adj (pointK z) (pure (Sum.inr M))
  rw [adj_pure,pointK,Ultrafilter.mem_map,point,Ultrafilter.mem_map]
  exact Erdos595SuffixSupportTemplate.cutoff_mem_point z.2.1 z.2.2 M (Nat.le_of_lt hM)

lemma Q_adj : K₂.Adj Q₀ Q₁ := by
  have h : ∀ M N : ℕ,
      K₁.Adj (pure (Sum.inl (Sum.inr M))) (pure (Sum.inr N)) := by
    intro M N
    rw [adj_pure,Ultrafilter.mem_pure]
    trivial
  constructor
  · change {M : ℕ | {N : ℕ | K₁.Adj (pure (Sum.inl (Sum.inr M))) (pure (Sum.inr N))}
      ∈ Erdos595SuffixSupportTemplate.U} ∈ Erdos595SuffixSupportTemplate.U
    exact Filter.Eventually.of_forall (fun M => Filter.Eventually.of_forall (h M))
  · change {N : ℕ | {M : ℕ | K₁.Adj (pure (Sum.inr N)) (pure (Sum.inl (Sum.inr M)))}
      ∈ Erdos595SuffixSupportTemplate.U} ∈ Erdos595SuffixSupportTemplate.U
    exact Filter.Eventually.of_forall (fun N => Filter.Eventually.of_forall (fun M => (h M N).symm))

noncomputable def P : Ultrafilter (Ultrafilter (Ultrafilter NewVertex)) :=
  Ultrafilter.map (fun z => (pure (pointK z) : Ultrafilter (Ultrafilter NewVertex)))
    Erdos595ThirdFiniteEdgeSupportFailure.U

lemma P_zero : K₃.Adj P (pure Q₀) := by
  rw [adj_pure,P,Ultrafilter.mem_map]
  apply Filter.Eventually.of_forall
  intro z
  change K₂.Adj Q₀ (pure (pointK z))
  rw [adj_pure]
  exact point_trace_zero z

lemma P_one : K₃.Adj P (pure Q₁) := by
  rw [adj_pure,P,Ultrafilter.mem_map]
  apply Filter.Eventually.of_forall
  intro z
  change K₂.Adj Q₁ (pure (pointK z))
  rw [adj_pure]
  exact point_trace_one z

/-- The unsupported point really belongs to a triangle, not just to an edge. -/
theorem third_triangle : K₃.Adj P (pure Q₀) ∧ K₃.Adj P (pure Q₁) ∧
    K₃.Adj (pure Q₀) (pure Q₁) := by
  refine ⟨P_zero,P_one,?_⟩
  rw [adj_pure,Ultrafilter.mem_pure]
  exact Q_adj.symm

def lift₃ (S : Set NewVertex) : Set (Ultrafilter (Ultrafilter NewVertex)) :=
  {R | {p | S ∈ p} ∈ R}

lemma preimage_finiteOn (S : Set NewVertex) (hS : FiniteOn K S) :
    FiniteOn G (Sum.inl ⁻¹' S) := by
  obtain ⟨C,hC,hc⟩ := hS
  let f : G.induce (Sum.inl ⁻¹' S) →g K.induce S :=
    ⟨fun x => ⟨Sum.inl x.val,x.property⟩,fun h => h⟩
  exact ⟨C,hC,hc.comap f⟩

/-- Even triangle-bearing third-stage points need not have an original
support with a finite triangle-free EDGE cover. -/
theorem no_finite_edge_support (S : Set NewVertex) (hS : FiniteOn K S) : lift₃ S ∉ P := by
  intro hm
  rw [P,Ultrafilter.mem_map] at hm
  change {z | S ∈ pointK z} ∈ Erdos595ThirdFiniteEdgeSupportFailure.U at hm
  have he : {z | S ∈ pointK z} = {z | Sum.inl ⁻¹' S ∈ point z} := rfl
  rw [he] at hm

  obtain ⟨z,hno,hy⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem
    (Erdos595ThirdFiniteEdgeSupportFailure.U_avoids _ (preimage_finiteOn S hS)) hm)
  exact hno hy

/-- Even an intersection of traces of ADJACENT second-stage points need not
have a common original support with a finite triangle-free edge cover. -/
theorem adjacent_trace_no_finite_support :
    K₂.Adj Q₀ Q₁ ∧ ¬∃ S : Set NewVertex, FiniteOn K S ∧
      ∀ p : Ultrafilter NewVertex,
        K₁.neighborSet p ∈ Q₀ → K₁.neighborSet p ∈ Q₁ → S ∈ p := by
  refine ⟨Q_adj, ?_⟩
  rintro ⟨S, hS, hs⟩
  apply no_finite_edge_support S hS
  rw [P, Ultrafilter.mem_map]
  exact Filter.Eventually.of_forall
    (fun z => hs (pointK z) (point_trace_zero z) (point_trace_one z))

/-- The intersection in the preceding counterexample really is independent
at the first stage. Independence does not supply the missing compression. -/
theorem common_trace_independent {p q : Ultrafilter NewVertex}
    (hp₀ : K₁.neighborSet p ∈ Q₀) (hp₁ : K₁.neighborSet p ∈ Q₁)
    (hq₀ : K₁.neighborSet q ∈ Q₀) (hq₁ : K₁.neighborSet q ∈ Q₁) :
    ¬K₁.Adj p q := by
  intro hpq
  have hp₀' : K₂.Adj Q₀ (pure p) := (adj_pure _ _ _ _).mpr hp₀
  have hp₁' : K₂.Adj Q₁ (pure p) := (adj_pure _ _ _ _).mpr hp₁
  have hq₀' : K₂.Adj Q₀ (pure q) := (adj_pure _ _ _ _).mpr hq₀
  have hq₁' : K₂.Adj Q₁ (pure q) := (adj_pure _ _ _ _).mpr hq₁
  have hpq' : K₂.Adj (pure p) (pure q) := by
    rw [adj_pure, Ultrafilter.mem_pure]
    exact hpq.symm
  exact no_adj_common_neighbors
    (ultrafilterGraph_cliqueFree K₁ (ultrafilterGraph_cliqueFree K K_cliqueFree))
    Q_adj hp₀' hp₁' hq₀' hq₁' hpq'

#print axioms adjacent_trace_no_finite_support
#print axioms common_trace_independent

example : Countable NewVertex := inferInstance
#print axioms K_cliqueFree
#print axioms third_triangle
#print axioms no_finite_edge_support
end Erdos595ThirdTriangleFiniteEdgeSupportFailure
