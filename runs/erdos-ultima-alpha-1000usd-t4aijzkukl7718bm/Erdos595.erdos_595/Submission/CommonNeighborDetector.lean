import Submission.Work

/-!
A countable family detecting common neighbors gives a countable proper
vertex coloring of a K4-free graph. Application: the FIRST mutual ultrafilter
extension of a countable K4-free graph is countably vertex-colorable.
This does not assert the analogous result for higher towers.
-/

open SimpleGraph Set
namespace Erdos595CommonNeighborDetector
open Erdos595Work

variable {V : Type*} (G : SimpleGraph V) (d : ℕ → V)

noncomputable def first (v : V) : ℕ := by
  classical
  exact if h : ∃ n, G.Adj v (d n) then h.choose else 0

lemma first_spec {v : V} (h : ∃ n, G.Adj v (d n)) :
    G.Adj v (d (first G d v)) := by
  classical
  simp only [first,dif_pos h]
  exact h.choose_spec

noncomputable def tag (v : V) : Option ℕ := by
  classical
  exact if h : ∃ n, G.Adj v (d n) ∧ G.Adj (d (first G d v)) (d n)
    then some h.choose else none

lemma tag_spec {v : V} {n : ℕ} (h : tag G d v = some n) :
    G.Adj v (d n) ∧ G.Adj (d (first G d v)) (d n) := by
  classical
  unfold tag at h
  split_ifs at h with he
  · have hn := Option.some.inj h
    exact hn ▸ he.choose_spec

/-- Repetitions a=b are allowed in the detector condition, so it also
ensures that every nonisolated vertex has a neighbor in the family d. -/
theorem countable_coloring (hG : G.CliqueFree 4)
    (hD : ∀ a b, (∃ x, G.Adj a x ∧ G.Adj b x) →
      ∃ n, G.Adj a (d n) ∧ G.Adj b (d n)) :
    Nonempty (G.Coloring ℕ) := by
  classical
  obtain ⟨enc,henc⟩ := exists_injective_nat (ℕ × Option ℕ)
  refine ⟨SimpleGraph.Coloring.mk (fun v => enc (first G d v,tag G d v)) ?_⟩
  intro v w hvw he
  have hc := henc he
  have hi : first G d v = first G d w := congrArg Prod.fst hc
  have ht : tag G d v = tag G d w := congrArg Prod.snd hc
  have hv : G.Adj v (d (first G d v)) :=
    first_spec G d (by obtain ⟨n,hn,_⟩ := hD v v ⟨w,hvw,hvw⟩; exact ⟨n,hn⟩)
  have hw : G.Adj w (d (first G d v)) := by
    rw [hi]
    exact first_spec G d (by
      obtain ⟨n,hn,_⟩ := hD w w ⟨v,hvw.symm,hvw.symm⟩
      exact ⟨n,hn⟩)
  have hex : ∃ n, G.Adj v (d n) ∧ G.Adj (d (first G d v)) (d n) :=
    hD v (d (first G d v)) ⟨w,hvw,hw.symm⟩
  have hvtag : tag G d v = some hex.choose := by simp only [tag,dif_pos hex]
  have hwtag : tag G d w = some hex.choose := ht.symm.trans hvtag
  have hvs := tag_spec G d hvtag
  have hws := tag_spec G d hwtag
  exact no_adj_common_neighbors hG hvw hv hw hvs.1 hws.1 hvs.2

/-- For a principal endpoint, mutual adjacency is ordinary neighborhood
membership in the other ultrafilter. -/
lemma adj_pure {A : Type*} (H : SimpleGraph A) (hH : H.CliqueFree 4)
    (p : Ultrafilter A) (a : A) :
    (ultrafilterGraph H hH).Adj p (pure a) ↔ H.neighborSet a ∈ p := by
  have hs : {v | H.Adj v a} = H.neighborSet a := by
    ext v
    exact H.adj_comm v a
  simp only [ultrafilterGraph,fubiniAdj,Ultrafilter.mem_pure,Set.mem_setOf_eq,
    SimpleGraph.mem_neighborSet,hs,and_self]

/-- Every finite pair of ultrafilter vertices having a common neighbor
already has a PRINCIPAL common neighbor. -/
theorem principal_detector {A : Type*} (H : SimpleGraph A) (hH : H.CliqueFree 4)
    (p q : Ultrafilter A)
    (h : ∃ r, (ultrafilterGraph H hH).Adj p r ∧ (ultrafilterGraph H hH).Adj q r) :
    ∃ a : A, (ultrafilterGraph H hH).Adj p (pure a) ∧
      (ultrafilterGraph H hH).Adj q (pure a) := by
  obtain ⟨r,hpr,hqr⟩ := h
  obtain ⟨a,ha,hb⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hpr.2 hqr.2)
  exact ⟨a,(adj_pure H hH p a).mpr ha,(adj_pure H hH q a).mpr hb⟩

/-- A strengthening of the previously established first-extension cover:
the first extension has a COUNTABLE PROPER VERTEX coloring. -/
theorem first_extension_countable_coloring {A : Type*} [Countable A]
    (H : SimpleGraph A) (hH : H.CliqueFree 4) :
    Nonempty ((ultrafilterGraph H hH).Coloring ℕ) := by
  classical
  cases isEmpty_or_nonempty A with
  | inl h =>
    refine ⟨SimpleGraph.Coloring.mk (fun _ => 0) ?_⟩
    intro p q hpq _
    obtain ⟨a,_⟩ := Ultrafilter.nonempty_of_mem hpq.1
    exact isEmptyElim a
  | inr h =>
    obtain ⟨e,he⟩ := exists_surjective_nat A
    apply countable_coloring (ultrafilterGraph H hH) (fun n => pure (e n))
      (ultrafilterGraph_cliqueFree H hH)
    intro p q h
    obtain ⟨a,hpa,hqa⟩ := principal_detector H hH p q h
    obtain ⟨n,rfl⟩ := he a
    exact ⟨n,hpa,hqa⟩

#print axioms countable_coloring
#print axioms principal_detector
#print axioms first_extension_countable_coloring
end Erdos595CommonNeighborDetector
