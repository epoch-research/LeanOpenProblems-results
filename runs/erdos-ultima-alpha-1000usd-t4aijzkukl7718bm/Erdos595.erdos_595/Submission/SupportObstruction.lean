import Submission.Work

/-!
A counterexample to a proposed support-compression step for iterated ultrafilters.
This does NOT settle Erdős Problem 595: the example is a cone and has a
triangle-free two-piece edge cover.
-/

open SimpleGraph Set
open Erdos595Work

namespace Erdos595Support

inductive BaseVertex
  | va : ℕ → BaseVertex
  | vb : ℕ → BaseVertex
  | vx : ℕ → BaseVertex
  deriving DecidableEq, Countable

open BaseVertex

def baseGraph : SimpleGraph BaseVertex where
  Adj
    | va i, vb j => i = j
    | vb i, va j => i = j
    | va i, vx n => i < n
    | vx n, va i => i < n
    | vb i, vx n => n ≤ i
    | vx n, vb i => n ≤ i
    | _, _ => False
  symm := by
    intro v w
    cases v <;> cases w <;> simp_all
  loopless := by intro v; cases v <;> simp

theorem baseGraph_cliqueFree : baseGraph.CliqueFree 3 := by
  intro t ht
  obtain ⟨v, w, z, hvw, hvz, hwz, _⟩ := SimpleGraph.is3Clique_iff.mp ht
  cases v <;> cases w <;> cases z <;> simp_all [baseGraph] <;> omega

abbrev Vertex := Option BaseVertex

def G : SimpleGraph Vertex := coneGraph baseGraph

theorem G_cliqueFree : G.CliqueFree 4 :=
  coneGraph_cliqueFree baseGraph baseGraph_cliqueFree

theorem G_cover : IsCountableUnionOfTriangleFree G :=
  countable_union_coneGraph baseGraph baseGraph_cliqueFree

abbrev G₁ := ultrafilterGraph G G_cliqueFree

noncomputable def q : Ultrafilter Vertex :=
  Ultrafilter.map (fun i => some (vb i)) (Filter.hyperfilter ℕ)

noncomputable def P : Ultrafilter (Ultrafilter Vertex) :=
  Ultrafilter.map (fun n => (pure (some (vx n)) : Ultrafilter Vertex))
    (Filter.hyperfilter ℕ)

/-- The trace of the second-stage ultrafilter on first-stage vertices. -/
def trace : Set (Ultrafilter Vertex) := {p | G₁.neighborSet p ∈ P}

private theorem adj_pure_right {W : Type*} (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (p : Ultrafilter W) (v : W) :
    (ultrafilterGraph H hH).Adj p (pure v) ↔ H.neighborSet v ∈ p := by
  change ({w | H.neighborSet w ∈ (pure v : Ultrafilter W)} ∈ p ∧
    {w | H.neighborSet w ∈ p} ∈ (pure v : Ultrafilter W)) ↔ _
  simp only [Ultrafilter.mem_pure, mem_setOf_eq, SimpleGraph.mem_neighborSet]
  have he : {w | H.Adj w v} = H.neighborSet v := by
    ext w
    exact H.adj_comm w v
  rw [he]
  exact ⟨And.left, fun h => ⟨h, h⟩⟩

private theorem adj_pure_pure {W : Type*} (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (v w : W) :
    (ultrafilterGraph H hH).Adj (pure v) (pure w) ↔ H.Adj v w := by
  rw [adj_pure_right]
  simp only [Ultrafilter.mem_pure, SimpleGraph.mem_neighborSet]
  exact H.adj_comm w v

private theorem tail_mem (i : ℕ) : {n : ℕ | i < n} ∈ Filter.hyperfilter ℕ := by
  exact Nat.hyperfilter_le_atTop (Filter.eventually_gt_atTop i)

private theorem tail_mem_le (i : ℕ) : {n : ℕ | i ≤ n} ∈ Filter.hyperfilter ℕ := by
  exact Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop i)

theorem apex_mem_trace : (pure none : Ultrafilter Vertex) ∈ trace := by
  change G₁.neighborSet (pure none) ∈ P
  rw [P, Ultrafilter.mem_map]
  have he : (fun n => (pure (some (vx n)) : Ultrafilter Vertex)) ⁻¹'
      G₁.neighborSet (pure none) = univ := by
    ext n
    simp [adj_pure_pure, G, coneGraph]
  rw [he]
  exact Filter.univ_mem

theorem a_mem_trace (i : ℕ) : (pure (some (va i)) : Ultrafilter Vertex) ∈ trace := by
  change G₁.neighborSet (pure (some (va i))) ∈ P
  rw [P, Ultrafilter.mem_map]
  have he : (fun n => (pure (some (vx n)) : Ultrafilter Vertex)) ⁻¹'
      G₁.neighborSet (pure (some (va i))) = {n | i < n} := by
    ext n
    simp [adj_pure_pure, G, coneGraph, baseGraph]
  rw [he]
  exact tail_mem i

theorem q_mem_trace : q ∈ trace := by
  change G₁.neighborSet q ∈ P
  rw [P, Ultrafilter.mem_map]
  have h : ∀ n, G₁.Adj q (pure (some (vx n))) := by
    intro n
    rw [adj_pure_right, q, Ultrafilter.mem_map]
    change {i | n ≤ i} ∈ Filter.hyperfilter ℕ
    exact tail_mem_le n
  have he : (fun n => (pure (some (vx n)) : Ultrafilter Vertex)) ⁻¹'
      G₁.neighborSet q = univ := by
    ext n
    simp only [mem_preimage, SimpleGraph.mem_neighborSet, mem_univ, iff_true]
    exact h n
  rw [he]
  exact Filter.univ_mem

/-- Even though the second-stage trace is triangle-free, it need not be contained
in the lift of any single original triangle-free set. -/
theorem no_single_triangleFree_support :
    ¬ ∃ S : Set Vertex, (G.induce S).CliqueFree 3 ∧ ∀ p ∈ trace, S ∈ p := by
  rintro ⟨S, hS, h⟩
  have hz : none ∈ S := (Ultrafilter.mem_pure).mp (h _ apex_mem_trace)
  have ha : ∀ i, some (va i) ∈ S := fun i =>
    (Ultrafilter.mem_pure).mp (h _ (a_mem_trace i))
  have hb := h _ q_mem_trace
  rw [q, Ultrafilter.mem_map] at hb
  obtain ⟨i, hi⟩ := Ultrafilter.nonempty_of_mem hb
  apply hS _
  exact SimpleGraph.is3Clique_triple_iff.mpr
    (show (G.induce S).Adj ⟨none, hz⟩ ⟨some (va i), ha i⟩ ∧
      (G.induce S).Adj ⟨none, hz⟩ ⟨some (vb i), hi⟩ ∧
      (G.induce S).Adj ⟨some (va i), ha i⟩ ⟨some (vb i), hi⟩ from
        ⟨True.intro, True.intro, rfl⟩)

theorem trace_cliqueFree : (G₁.induce trace).CliqueFree 3 :=
  ultrafilter_trace_cliqueFree G₁ (ultrafilterGraph_cliqueFree G G_cliqueFree) P

/-- Every finite part of a second-stage trace has a common original
triangle-free support. The example above shows that passing from finite parts
to the whole trace is not a valid compactness argument. -/
theorem finite_trace_support {W : Type*} (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (R : Ultrafilter (Ultrafilter W)) (T : Finset (Ultrafilter W))
    (hT : ∀ p ∈ T, (ultrafilterGraph H hH).neighborSet p ∈ R) :
    ∃ S : Set W, (H.induce S).CliqueFree 3 ∧ ∀ p ∈ T, S ∈ p := by
  have hh : {q | ∀ p ∈ T, (ultrafilterGraph H hH).Adj p q} ∈ R :=
    (Filter.eventually_all_finset T).mpr hT
  obtain ⟨q, hq⟩ := Ultrafilter.nonempty_of_mem hh
  refine ⟨{w | H.neighborSet w ∈ q}, ultrafilter_trace_cliqueFree H hH q, ?_⟩
  intro p hp
  exact (hq p hp).1

theorem finite_support_but_no_global_support :
    (∀ T : Finset (Ultrafilter Vertex), (∀ p ∈ T, p ∈ trace) →
      ∃ S : Set Vertex, (G.induce S).CliqueFree 3 ∧ ∀ p ∈ T, S ∈ p) ∧
    ¬ (∃ S : Set Vertex, (G.induce S).CliqueFree 3 ∧ ∀ p ∈ trace, S ∈ p) := by
  refine ⟨?_, no_single_triangleFree_support⟩
  intro T hT
  exact finite_trace_support G G_cliqueFree P T hT

#print axioms G_cliqueFree
#print axioms G_cover
#print axioms no_single_triangleFree_support
#print axioms trace_cliqueFree
#print axioms finite_support_but_no_global_support

end Erdos595Support
