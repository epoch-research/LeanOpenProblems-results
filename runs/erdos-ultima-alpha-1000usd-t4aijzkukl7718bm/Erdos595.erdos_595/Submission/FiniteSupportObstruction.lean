import Submission.MiddleCornerObstruction
import Submission.ExtensionObstruction

/-!
A second-stage trace need not admit even a finite cover by lifted original
triangle-free vertex sets. This is an obstruction to support compression, NOT
a settlement of Erdős 595. The base graph below has a finite edge cover.
-/

open SimpleGraph Set Filter
open Erdos595Work Erdos595MiddleCorner

namespace Erdos595FiniteSupport

abbrev Vertex := Triple ℕ ⊕ ℕ

instance : Countable (Triple ℕ) := by
  apply Function.Injective.countable (f := fun x : Triple ℕ => (x.a, x.b, x.c))
  intro x y h
  cases x
  cases y
  simpa using h

instance : Countable Vertex := inferInstanceAs (Countable (Triple ℕ ⊕ ℕ))

private theorem cutoff_independent (n : ℕ) (x y : Triple ℕ)
    (hx : x.a ≤ n ∧ n < x.b) (hy : y.a ≤ n ∧ n < y.b) :
    ¬ (graph ℕ).Adj x y := by
  intro h
  rcases h with h | h
  · rcases first_of_forward h with h | h
    all_goals have := x.bc; omega
  · rcases first_of_forward h with h | h
    all_goals have := y.bc; omega

private def cutoff (n : ℕ) : Erdos595Extension.Admissible (graph ℕ) :=
  ⟨{x | x.a ≤ n ∧ n < x.b}, by
    classical
    intro t ht
    obtain ⟨x, y, z, hxy, _, _, _⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact cutoff_independent n x y x.2 y.2 hxy⟩

def G : SimpleGraph Vertex :=
  (Erdos595Extension.apexFamilyGraph (graph ℕ)).comap
    (Sum.map id cutoff)

theorem G_cliqueFree : G.CliqueFree 4 := by
  classical
  by_contra h
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree h
  have he : ∀ i j : Fin 4, i ≠ j →
      (Erdos595Extension.apexFamilyGraph (graph ℕ)).Adj
        (Sum.map id cutoff (e i)) (Sum.map id cutoff (e j)) :=
    fun i j hij => e.map_rel_iff.mpr hij
  exact no_adj_common_neighbors
    (Erdos595Extension.apexFamilyGraph_cliqueFree _ (graph_cliqueFree ℕ))
    (he 0 1 (by decide)) (he 0 2 (by decide)) (he 1 2 (by decide))
    (he 0 3 (by decide)) (he 1 3 (by decide)) (he 2 3 (by decide))

theorem G_cover : IsCountableUnionOfTriangleFree G := by
  apply Erdos595Extension.countable_cover_independent_extension
  · exact graph_cover ℕ
  · intro a b h
    exact h

abbrev G₁ := ultrafilterGraph G G_cliqueFree

private noncomputable def U : Ultrafilter ℕ := Filter.hyperfilter ℕ

private theorem tail (n : ℕ) : {m : ℕ | n < m} ∈ U :=
  Nat.hyperfilter_le_atTop (Filter.eventually_gt_atTop n)

/-- A total choice of an increasing triple, agreeing with the specified
coordinates whenever they are increasing. -/
def triple (a b c : ℕ) : Triple ℕ :=
  ⟨a, max (a + 1) b, max (max (a + 1) b + 1) c, by omega, by omega⟩

@[simp] private theorem triple_a (a b c : ℕ) : (triple a b c).a = a := rfl

private theorem triple_eq (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    triple a b c = ⟨a, b, c, hab, hbc⟩ := by
  simp [triple, Nat.max_eq_right (by omega : a + 1 ≤ b),
    Nat.max_eq_right (by omega : b + 1 ≤ c)]

noncomputable def p (a : ℕ) : Ultrafilter Vertex :=
  U.bind fun b => Ultrafilter.map (fun c => Sum.inl (triple a b c)) U

private theorem mem_p (S : Set Vertex) (a : ℕ) :
    S ∈ p a ↔ {b | {c | Sum.inl (triple a b c) ∈ S} ∈ U} ∈ U := by
  change S ∈ Filter.bind (U : Filter ℕ)
    (fun b => (Ultrafilter.map (fun c => (Sum.inl (triple a b c) : Vertex)) U).toFilter) ↔ _
  rw [Filter.mem_bind']
  rfl

noncomputable def P : Ultrafilter (Ultrafilter Vertex) :=
  Ultrafilter.map (fun n => (pure (Sum.inr n) : Ultrafilter Vertex)) U

def trace : Set (Ultrafilter Vertex) := {q | G₁.neighborSet q ∈ P}

private theorem adj_pure_right {W : Type*} (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (q : Ultrafilter W) (v : W) :
    (ultrafilterGraph H hH).Adj q (pure v) ↔ H.neighborSet v ∈ q := by
  change ({w | H.neighborSet w ∈ (pure v : Ultrafilter W)} ∈ q ∧
    {w | H.neighborSet w ∈ q} ∈ (pure v : Ultrafilter W)) ↔ _
  simp only [Ultrafilter.mem_pure, mem_setOf_eq, SimpleGraph.mem_neighborSet]
  have he : {w | H.Adj w v} = H.neighborSet v := by
    ext w
    exact H.adj_comm w v
  rw [he]
  exact ⟨And.left, fun h => ⟨h, h⟩⟩

theorem p_mem_trace (a : ℕ) : p a ∈ trace := by
  change G₁.neighborSet (p a) ∈ P
  rw [P, Ultrafilter.mem_map]
  apply Filter.mem_of_superset (tail a)
  intro n hn
  have han : a < n := hn
  change G₁.Adj (p a) (pure (Sum.inr n))
  rw [adj_pure_right, mem_p]
  apply Filter.mem_of_superset (tail n)
  intro b hb
  have hnb : n < b := hb
  apply Filter.mem_of_superset (tail b)
  intro c hc
  change (triple a b c).a ≤ n ∧ n < (triple a b c).b
  rw [triple_eq a b c (by omega) hc]
  exact ⟨Nat.le_of_lt han, hnb⟩

/-- A triangle-free original set cannot support an outer-ultrafilter-large
set of the `p a`. Five successive coordinates would give a shift triangle. -/
theorem not_large_support (S : Set Vertex) (hS : (G.induce S).CliqueFree 3) :
    {a | S ∈ p a} ∉ U := by
  classical
  intro h
  let B : ℕ → Set ℕ := fun a => {b | {c | Sum.inl (triple a b c) ∈ S} ∈ U}
  have hB : {a | B a ∈ U} ∈ U := by
    simpa only [mem_p] using h
  obtain ⟨a, ha⟩ := Ultrafilter.nonempty_of_mem hB
  obtain ⟨b, hb, hab, hbA⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hB (Filter.inter_mem (tail a) ha))
  obtain ⟨c, hc, hbc, hcA, hcB⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hB (Filter.inter_mem (tail b) (Filter.inter_mem hbA hb)))
  obtain ⟨d, hcd, hdB, hdC⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem (tail c) (Filter.inter_mem hcB hc))
  obtain ⟨e, hde, heC⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem (tail d) hdC)
  have hx : Sum.inl (triple a b c) ∈ S := hcA
  have hy : Sum.inl (triple b c d) ∈ S := hdB
  have hz : Sum.inl (triple c d e) ∈ S := heC
  apply hS _
  apply SimpleGraph.is3Clique_triple_iff.mpr
  change (G.induce S).Adj ⟨Sum.inl (triple a b c), hx⟩ ⟨Sum.inl (triple b c d), hy⟩ ∧
    (G.induce S).Adj ⟨Sum.inl (triple a b c), hx⟩ ⟨Sum.inl (triple c d e), hz⟩ ∧
    (G.induce S).Adj ⟨Sum.inl (triple b c d), hy⟩ ⟨Sum.inl (triple c d e), hz⟩
  change (graph ℕ).Adj (triple a b c) (triple b c d) ∧
    (graph ℕ).Adj (triple a b c) (triple c d e) ∧
    (graph ℕ).Adj (triple b c d) (triple c d e)
  rw [triple_eq a b c hab hbc, triple_eq b c d hbc hcd,
    triple_eq c d e hcd hde]
  exact ⟨Or.inl (Or.inl ⟨rfl, rfl⟩), Or.inl (Or.inr rfl),
    Or.inl (Or.inl ⟨rfl, rfl⟩)⟩

/-- Finite support compression fails, not just single-support compression. -/
theorem no_finite_triangleFree_support :
    ¬ ∃ T : Finset (Set Vertex),
      (∀ S ∈ T, (G.induce S).CliqueFree 3) ∧
      ∀ q ∈ trace, ∃ S ∈ T, S ∈ q := by
  rintro ⟨T, hT, hcov⟩
  have hh : ∀ᶠ a in (U : Filter ℕ), ∃ S ∈ (T : Set (Set Vertex)), S ∈ p a :=
    Filter.Eventually.of_forall fun a => hcov (p a) (p_mem_trace a)
  obtain ⟨S, hST, hS⟩ := (Ultrafilter.eventually_exists_mem_iff T.finite_toSet).mp hh
  exact not_large_support S (hT S hST) hS

abbrev G₂ := ultrafilterGraph G₁ (ultrafilterGraph_cliqueFree G G_cliqueFree)
abbrev G₃ := ultrafilterGraph G₂
  (ultrafilterGraph_cliqueFree G₁ (ultrafilterGraph_cliqueFree G G_cliqueFree))

noncomputable def X : Ultrafilter (Ultrafilter (Ultrafilter Vertex)) :=
  Ultrafilter.map (fun a => (pure (p a) : Ultrafilter (Ultrafilter Vertex))) U

/-- The third extension has a concrete nonisolated vertex not supported on the
threefold lift of any original triangle-free set. -/
theorem third_stage_edge : G₃.Adj X (pure P) := by
  rw [adj_pure_right, X, Ultrafilter.mem_map]
  apply Filter.Eventually.of_forall
  intro a
  change G₂.Adj P (pure (p a))
  rw [adj_pure_right]
  exact p_mem_trace a

theorem third_stage_no_original_support (S : Set Vertex)
    (hS : (G.induce S).CliqueFree 3) :
    {R : Ultrafilter (Ultrafilter Vertex) | {q : Ultrafilter Vertex | S ∈ q} ∈ R}
      ∉ X := by
  intro h
  rw [X, Ultrafilter.mem_map] at h
  apply not_large_support S hS
  simpa only [mem_preimage, mem_setOf_eq, Ultrafilter.mem_pure] using h

/-- In contrast, the concrete base still admits a three-piece edge cover. -/
def piece (i : Fin 3) : SimpleGraph Vertex where
  Adj x y := match x, y with
    | .inl x, .inl y =>
        (i = 0 ∧ (oneGraph ℕ).Adj x y) ∨ (i = 1 ∧ (twoGraph ℕ).Adj x y)
    | .inl x, .inr n => i = 2 ∧ x.a ≤ n ∧ n < x.b
    | .inr n, .inl x => i = 2 ∧ x.a ≤ n ∧ n < x.b
    | .inr _, .inr _ => False
  symm := by
    intro x y h
    cases x <;> cases y
    · exact h.imp (fun h => ⟨h.1, h.2.symm⟩) (fun h => ⟨h.1, h.2.symm⟩)
    · exact h
    · exact h
    · exact h
  loopless := by
    intro x
    cases x <;> simp

theorem piece_cliqueFree (i : Fin 3) : (piece i).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := SimpleGraph.is3Clique_iff.mp ht
  cases x <;> cases y <;> cases z <;> simp only [piece] at hxy hxz hyz
  all_goals first
    | contradiction
    | (have := hxy; have := hxz; have := hyz; omega)
    | skip
  fin_cases i
  · simp at hxy hxz hyz
    exact oneGraph_cliqueFree ℕ _
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)
  · simp at hxy hxz hyz
    exact twoGraph_cliqueFree ℕ _
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)
  · simp at hxy

theorem three_piece_cover : G = ⨆ i : Fin 3, piece i := by
  ext x y
  rw [SimpleGraph.iSup_adj]
  cases x <;> cases y <;>
    simp only [G, SimpleGraph.comap_adj, Sum.map,
      Erdos595Extension.apexFamilyGraph, piece]
  · constructor
    · rintro (h | h)
      · rcases h with h | h
        · exact ⟨0, Or.inl ⟨rfl, Or.inl h⟩⟩
        · exact ⟨1, Or.inr ⟨rfl, Or.inl h⟩⟩
      · rcases h with h | h
        · exact ⟨0, Or.inl ⟨rfl, Or.inr h⟩⟩
        · exact ⟨1, Or.inr ⟨rfl, Or.inr h⟩⟩
    · rintro ⟨i, (⟨_, h⟩ | ⟨_, h⟩)⟩
      · exact h.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inl h))
      · exact h.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h))
  · exact ⟨fun h => ⟨2, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  · exact ⟨fun h => ⟨2, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  · simp

/-- Thus the support obstruction does not give a non-coverable third extension:
it still has a three-piece triangle-free edge cover. -/
theorem third_stage_three_piece_cover :
    ∃ H : Fin 3 → SimpleGraph (Ultrafilter (Ultrafilter (Ultrafilter Vertex))),
      (∀ i, (H i).CliqueFree 3) ∧ G₃ = ⨆ i, H i := by
  obtain ⟨H₁, hH₁, he₁⟩ := ultrafilterGraph_finite_cover G G_cliqueFree
    piece piece_cliqueFree three_piece_cover
  obtain ⟨H₂, hH₂, he₂⟩ := ultrafilterGraph_finite_cover G₁
    (ultrafilterGraph_cliqueFree G G_cliqueFree) H₁ hH₁ he₁
  exact ultrafilterGraph_finite_cover G₂
    (ultrafilterGraph_cliqueFree G₁ (ultrafilterGraph_cliqueFree G G_cliqueFree))
    H₂ hH₂ he₂

#print axioms third_stage_three_piece_cover

#print axioms G_cliqueFree
#print axioms third_stage_edge
#print axioms third_stage_no_original_support
#print axioms piece_cliqueFree
#print axioms three_piece_cover

#print axioms G_cover
#print axioms p_mem_trace
#print axioms not_large_support
#print axioms no_finite_triangleFree_support

end Erdos595FiniteSupport
