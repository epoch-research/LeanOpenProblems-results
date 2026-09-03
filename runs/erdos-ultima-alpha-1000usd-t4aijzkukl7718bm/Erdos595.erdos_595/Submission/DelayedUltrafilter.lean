import Submission.Work

/-!
A delayed ultrafilter construction. Any K4-free graph maps into a second
mutual-ultrafilter extension, with EVERY image vertex having empty original
neighborhood trace after flattening. Thus such trace fibers cannot be assumed
triangle-free. Countable input graphs give countable bases. This is an
obstruction to a compression argument, not a settlement of Erdős 595.
-/

set_option autoImplicit false
open Set Filter SimpleGraph
namespace Erdos595DelayedUltrafilter
open Erdos595Work

variable {V : Type*}
abbrev Carrier (V : Type*) := (V × ℕ) × ℕ

/-- Delay each cross-level edge until both inner coordinates exceed the
opposite outer coordinate. -/
def delayed (G : SimpleGraph V) : SimpleGraph (Carrier V) where
  Adj x y := G.Adj x.1.1 y.1.1 ∧ x.1.2 ≠ y.1.2 ∧ y.1.2 < x.2 ∧ x.1.2 < y.2
  symm := fun _ _ h => ⟨h.1.symm,h.2.1.symm,h.2.2.2,h.2.2.1⟩
  loopless := fun _ h => h.2.1 rfl

def projection (G : SimpleGraph V) : delayed G →g G :=
  ⟨fun x => x.1.1,fun h => h.1⟩

def levelColoring (G : SimpleGraph V) : (delayed G).Coloring ℕ :=
  SimpleGraph.Coloring.mk (fun x => x.1.2) (fun h => h.2.1)

theorem delayed_cliqueFree (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    (delayed G).CliqueFree 4 := by
  classical
  by_contra h
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree h
  have he (i j : Fin 4) (hij : i ≠ j) : G.Adj (e i).1.1 (e j).1.1 :=
    (e.map_rel_iff.mpr hij).1
  exact no_adj_common_neighbors hG (he 0 1 (by decide)) (he 0 2 (by decide))
    (he 1 2 (by decide)) (he 0 3 (by decide)) (he 1 3 (by decide)) (he 2 3 (by decide))

private noncomputable def U : Ultrafilter ℕ := Filter.hyperfilter ℕ
private theorem tail (n : ℕ) : ∀ᶠ m in (U : Filter ℕ), n < m :=
  Nat.hyperfilter_le_atTop (Filter.eventually_gt_atTop n)

noncomputable def first (x : V × ℕ) : Ultrafilter (Carrier V) :=
  Ultrafilter.map (fun i => (x,i)) U

lemma first_fubini (G : SimpleGraph V) (x y : V × ℕ) :
    fubiniAdj (delayed G) (first x) (first y) ↔ (levelGraph G).Adj x y := by
  change {i | {j | G.Adj x.1 y.1 ∧ x.2 ≠ y.2 ∧ y.2 < i ∧ x.2 < j} ∈ U} ∈ U ↔ _
  constructor
  · intro h
    obtain ⟨i,hi⟩ := Ultrafilter.nonempty_of_mem h
    obtain ⟨j,hj⟩ := Ultrafilter.nonempty_of_mem hi
    exact ⟨hj.1,hj.2.1⟩
  · intro h
    apply Filter.mem_of_superset (tail y.2)
    intro i hi
    exact Filter.mem_of_superset (tail x.2) (fun j hj => ⟨h.1,h.2,hi,hj⟩)

lemma first_adj (G : SimpleGraph V) (hG : G.CliqueFree 4) (x y : V × ℕ) :
    (ultrafilterGraph (delayed G) (delayed_cliqueFree G hG)).Adj (first x) (first y) ↔
      (levelGraph G).Adj x y := by
  change (fubiniAdj (delayed G) (first x) (first y) ∧
    fubiniAdj (delayed G) (first y) (first x)) ↔ _
  rw [first_fubini,first_fubini]
  exact ⟨And.left,fun h => ⟨h,h.symm⟩⟩

noncomputable def firstHom (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    levelGraph G →g ultrafilterGraph (delayed G) (delayed_cliqueFree G hG) :=
  ⟨first,fun h => (first_adj G hG _ _).mpr h⟩

noncomputable def second (v : V) : Ultrafilter (Ultrafilter (Carrier V)) :=
  Ultrafilter.map (fun n => first (v,n)) U

abbrev twice (G : SimpleGraph V) (hG : G.CliqueFree 4) :=
  ultrafilterGraph (ultrafilterGraph (delayed G) (delayed_cliqueFree G hG))
    (ultrafilterGraph_cliqueFree _ _)

lemma second_fubini (G : SimpleGraph V) (hG : G.CliqueFree 4) (v w : V) :
    fubiniAdj (ultrafilterGraph (delayed G) (delayed_cliqueFree G hG))
      (second v) (second w) ↔ G.Adj v w := by
  change {n | {m | (ultrafilterGraph (delayed G) (delayed_cliqueFree G hG)).Adj
    (first (v,n)) (first (w,m))} ∈ U} ∈ U ↔ _
  have hi (n m : ℕ) : (ultrafilterGraph (delayed G) (delayed_cliqueFree G hG)).Adj
      (first (v,n)) (first (w,m)) ↔ G.Adj v w ∧ n ≠ m := first_adj G hG _ _
  simp only [hi]
  exact fubiniAdj_fiberUltrafilter G v w

/-- The delayed second extension recovers the input graph. -/
noncomputable def secondHom (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    G →g twice G hG where
  toFun := second
  map_rel' h := ⟨(second_fubini G hG _ _).mpr h,(second_fubini G hG _ _).mpr h.symm⟩

/-- Ultrafilter multiplication, without any claim that it is a graph map. -/
def flatten {A : Type*} (P : Ultrafilter (Ultrafilter A)) : Ultrafilter A := P.bind id

lemma mem_flatten {A : Type*} (P : Ultrafilter (Ultrafilter A)) (S : Set A) :
    S ∈ flatten P ↔ {p | S ∈ p} ∈ P := by
  change S ∈ Filter.bind (P : Filter (Ultrafilter A)) (fun p => (p : Filter A)) ↔ _
  rw [Filter.mem_bind']
  rfl

/-- Every fixed original neighborhood disappears under the double limit. -/
theorem flattened_neighborhood_empty (G : SimpleGraph V) (v : V) (x : Carrier V) :
    (delayed G).neighborSet x ∉ flatten (second v) := by
  rw [mem_flatten]
  change {n | {i | G.Adj x.1.1 v ∧ x.1.2 ≠ n ∧ n < x.2 ∧ x.1.2 < i} ∈ U} ∉ U
  intro h
  obtain ⟨n,hn,hm⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (tail x.2) h)
  obtain ⟨i,hi⟩ := Ultrafilter.nonempty_of_mem hm
  exact (Nat.not_lt_of_ge (Nat.le_of_lt hn)) hi.2.2.1

/-- Flattening separates adjacent second-stage vertices, although it need
not preserve adjacency in the first-stage graph. -/
theorem flatten_ne_of_adj (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (P Q : Ultrafilter (Ultrafilter V))
    (hPQ : (ultrafilterGraph (ultrafilterGraph G hG)
      (ultrafilterGraph_cliqueFree G hG)).Adj P Q) : flatten P ≠ flatten Q := by
  intro he
  have hE : {p : Ultrafilter V | {q | fubiniAdj G q p} ∈ P} ∈ P := by
    apply Filter.mem_of_superset hPQ.1
    intro p hp
    have hq : {q | fubiniAdj G q p} ∈ Q :=
      Filter.mem_of_superset hp (fun q h => h.2)
    have hh : {v | G.neighborSet v ∈ p} ∈ flatten Q := (mem_flatten Q _).mpr hq
    rw [← he] at hh
    exact (mem_flatten P _).mp hh
  obtain ⟨p₀,h₀⟩ := Ultrafilter.nonempty_of_mem hE
  obtain ⟨p₁,h₁,h₁₀⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hE h₀)
  obtain ⟨p₂,h₂,h₂₀,h₂₁⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hE (Filter.inter_mem h₀ h₁))
  obtain ⟨p₃,h₃₀,h₃₁,h₃₂⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem h₀ (Filter.inter_mem h₁ h₂))
  exact no_four_fubini G hG p₃ p₂ p₁ p₀ h₃₂ h₃₁ h₃₀ h₂₁ h₂₀ h₁₀

lemma second_injective : Function.Injective (second : V → _) := by
  intro v w he
  have hv : {p : Ultrafilter (Carrier V) | {x | x.1.1 = v} ∈ p} ∈ second v := by
    change {n : ℕ | {i : ℕ | v = v} ∈ U} ∈ U
    exact Filter.Eventually.of_forall (fun _ => Filter.Eventually.of_forall (fun _ => rfl))
  rw [he] at hv
  change {n : ℕ | {i : ℕ | w = v} ∈ U} ∈ U at hv
  obtain ⟨n,hn⟩ := Ultrafilter.nonempty_of_mem hv
  obtain ⟨i,hi⟩ := Ultrafilter.nonempty_of_mem hn
  exact hi.symm

noncomputable def secondEmbedding (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    G ↪g twice G hG where
  toFun := second
  inj' := second_injective
  map_rel_iff' := by
    intro v w
    exact ⟨fun h => (second_fubini G hG v w).mp h.1,
      fun h => (secondHom G hG).map_adj h⟩


theorem flattened_trace (G : SimpleGraph V) (v : V) :
    {x | (delayed G).neighborSet x ∈ flatten (second v)} = ∅ := by
  ext x
  simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
  exact flattened_neighborhood_empty G v x

/-- A hypothetical coverability proof for this entire empty-trace fiber
would already imply coverability of the arbitrary original graph. -/
theorem cover_of_empty_trace_fiber (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (hcov : IsCountableUnionOfTriangleFree
      ((twice G hG).induce {P | ∀ x, (delayed G).neighborSet x ∉ flatten P})) :
    IsCountableUnionOfTriangleFree G := by
  let f : G →g (twice G hG).induce {P | ∀ x, (delayed G).neighborSet x ∉ flatten P} :=
    ⟨fun v => ⟨second v,flattened_neighborhood_empty G v⟩,fun h => (secondHom G hG).map_adj h⟩
  exact countable_union_of_hom f hcov

/-- Even for a countable delayed base, the empty flattened-trace fiber
can contain a triangle. The base used here is countably vertex-colorable. -/
theorem empty_trace_fiber_can_contain_triangle :
    ∃ (G : SimpleGraph (Fin 3)) (hG : G.CliqueFree 4),
      ¬((twice G hG).induce
        {P | ∀ x, (delayed G).neighborSet x ∉ flatten P}).CliqueFree 3 := by
  classical
  let G : SimpleGraph (Fin 3) := ⊤
  let c : G.Coloring (Fin 3) := SimpleGraph.Coloring.mk id (fun h => h)
  have hG : G.CliqueFree 4 := c.colorable.cliqueFree (by decide)
  let f (v : Fin 3) : {P : Ultrafilter (Ultrafilter (Carrier (Fin 3))) |
      ∀ x, (delayed G).neighborSet x ∉ flatten P} :=
    ⟨second v,flattened_neighborhood_empty G v⟩
  refine ⟨G,hG,?_⟩
  intro h
  exact h _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show ((twice G hG).induce _).Adj (f 0) (f 1) ∧
      ((twice G hG).induce _).Adj (f 0) (f 2) ∧
      ((twice G hG).induce _).Adj (f 1) (f 2) from
        ⟨(secondHom G hG).map_adj (by decide : G.Adj 0 1),
         (secondHom G hG).map_adj (by decide : G.Adj 0 2),
         (secondHom G hG).map_adj (by decide : G.Adj 1 2)⟩))

#print axioms empty_trace_fiber_can_contain_triangle
#print axioms flatten_ne_of_adj
#print axioms secondEmbedding
#print axioms delayed_cliqueFree
#print axioms secondHom
#print axioms flattened_trace
#print axioms cover_of_empty_trace_fiber
end Erdos595DelayedUltrafilter
