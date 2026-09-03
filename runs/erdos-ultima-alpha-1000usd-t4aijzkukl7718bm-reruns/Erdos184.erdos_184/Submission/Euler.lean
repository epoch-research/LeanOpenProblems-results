import Submission.Cycles

/-! Euler-tour existence for connected finite even graphs. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma longest_trail_start_saturated {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : p.IsTrail)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsTrail → q.length ≤ p.length) :
    ∀ x, G.Adj u x → s(u, x) ∈ p.edges := by
  intro x hux
  by_contra hn
  have ht : (p.cons hux.symm).IsTrail := hp.cons hux.symm (by simpa [Sym2.eq_swap] using hn)
  have hh := hmax x v (p.cons hux.symm) ht
  simp only [Walk.length_cons] at hh
  omega

lemma saturated_trail_count_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v x : V} (p : G.Walk u v) (hp : p.IsTrail)
    (hs : ∀ y, G.Adj x y → s(x, y) ∈ p.edges) :
    p.edges.countP (fun e => x ∈ e) = G.degree x := by
  have heq : hp.edgesFinset.filter (fun e => x ∈ e) = G.incidenceFinset x := by
    ext e
    simp only [Finset.mem_filter, Walk.IsTrail.edgesFinset, Finset.mem_mk,
      Multiset.mem_coe, SimpleGraph.mem_incidenceFinset]
    constructor
    · rintro ⟨he, hx⟩
      exact ⟨p.edges_subset_edgeSet he, hx⟩
    · rintro ⟨he, hx⟩
      refine ⟨?_, hx⟩
      induction e using Sym2.ind with
      | h a b =>
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact hs b he
        · simpa only [Sym2.eq_swap] using hs a he.symm
  rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
  change (hp.edgesFinset.filter (fun e => x ∈ e)).card = _
  rw [heq, SimpleGraph.card_incidenceFinset_eq_degree]

lemma longest_trail_closed {V : Type*} [Fintype V] {G : SimpleGraph V}
    (he : ∀ x, Even (G.degree x)) {u v : V} (p : G.Walk u v) (hp : p.IsTrail)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsTrail → q.length ≤ p.length) : u = v := by
  have hcount := saturated_trail_count_degree p hp (longest_trail_start_saturated p hp hmax)
  have he' : Even (p.edges.countP (fun e => u ∈ e)) := by
    rw [hcount]
    exact he u
  have hh := (hp.even_countP_edges_iff u).mp he'
  by_contra huv
  exact (hh huv).1 rfl

lemma longest_closed_trail_eulerian {V : Type*} {G : SimpleGraph V}
    (hc : G.Connected) {u : V} (p : G.Walk u u) (hp : p.IsTrail)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsTrail → q.length ≤ p.length) :
    p.IsEulerian := by
  have hs : ∀ x ∈ p.support, ∀ y, G.Adj x y → s(x, y) ∈ p.edges := by
    intro x hx y hxy
    have hr := hp.rotate hx
    have hl : (p.rotate hx).length = p.length := by
      simpa only [Walk.length_edges] using (p.rotate_edges hx).perm.length_eq
    have hm : ∀ (a b : V) (q : G.Walk a b), q.IsTrail → q.length ≤ (p.rotate hx).length := by
      intro a b q hq
      rw [hl]
      exact hmax a b q hq
    have hh := longest_trail_start_saturated (p.rotate hx) hr hm y hxy
    exact (p.rotate_edges hx).mem_iff.mp hh
  have hwalk : ∀ {x y : V} (q : G.Walk x y), x ∈ p.support → y ∈ p.support := by
    intro x y q
    induction q with
    | nil => exact id
    | @cons x y z hxy q ih =>
      intro hx
      exact ih (p.snd_mem_support_of_mem_edges (hs x hx y hxy))
  have hall : ∀ x, x ∈ p.support := by
    intro x
    obtain ⟨q⟩ := hc u x
    exact hwalk q p.start_mem_support
  apply hp.isEulerian_of_forall_mem
  intro e he
  induction e using Sym2.ind with
  | h x y => exact hs x (hall x) y he

/-- Euler's sufficiency theorem, including the one-vertex graph with no edges. -/
lemma exists_eulerian_closed_walk {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected) (he : ∀ x, Even (G.degree x)) :
    ∃ u, ∃ p : G.Walk u u, p.IsEulerian := by
  haveI := hc.nonempty
  obtain ⟨u, v, p, hp, hm⟩ := Walk.exists_isTrail_forall_isTrail_length_le_length G
  have huv := longest_trail_closed he p hp hm
  subst v
  exact ⟨u, p, longest_closed_trail_eulerian hc p hp hm⟩

end Erdos184
