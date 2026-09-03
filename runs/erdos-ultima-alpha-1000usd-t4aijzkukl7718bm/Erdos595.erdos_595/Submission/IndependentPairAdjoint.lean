import Submission.ThreePointMatchingApex

/-!
A pair-graph candidate with a K4-free full right adjoint. Its vertices are
independent pairs in a triangle-free graph, with two orientations. Same-side
adjacency is mutual domination; opposite-side adjacency is intersection.
No non-coverability assertion is made.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595IndependentPair
open Erdos595ArcAdjoint
variable {V : Type*} (B : SimpleGraph V)

/-- Repeated entries, and hence singleton supports, are allowed. -/
abbrev Pair := {p : V × V // ¬B.Adj p.1 p.2}

def support (p : Pair B) : Set V := {p.val.1,p.val.2}

lemma independent (p : Pair B) {a b : V} (ha : a ∈ support B p)
    (hb : b ∈ support B p) : ¬B.Adj a b := by
  simp only [support,Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact B.loopless _
  · exact p.property
  · exact fun h => p.property h.symm
  · exact B.loopless _

lemma support_at (p : Pair B) {x : V} (hx : x ∈ support B p) :
    ∃ a, support B p = {x,a} := by
  simp only [support,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact ⟨p.val.2,rfl⟩
  · refine ⟨p.val.1,?_⟩
    ext z
    simp only [support,Set.mem_insert_iff,Set.mem_singleton_iff]
    exact or_comm

def Dominates (p q : Pair B) : Prop :=
  ∃ a ∈ support B p, ∀ b ∈ support B q, B.Adj a b

def Near (p q : Pair B) : Prop := Dominates B p q ∧ Dominates B q p

lemma near_irrefl (p : Pair B) : ¬Near B p p := by
  rintro ⟨⟨a,ha,h⟩,_⟩
  exact B.loopless a (h a ha)

lemma near_disjoint {p q : Pair B} (h : Near B p q) :
    Disjoint (support B p) (support B q) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨a,ha,hp⟩ := h.1
  exact independent B p ha hz (hp z hz')

abbrev Vertex := Pair B × Bool

def graph : SimpleGraph (Vertex B) where
  Adj p q := if p.2 = q.2 then Near B p.1 q.1 else
    (support B p.1 ∩ support B q.1).Nonempty
  symm := by
    classical
    intro p q h
    by_cases he : p.2 = q.2
    · simpa only [if_pos he,if_pos he.symm,Near,and_comm] using h
    · have he' : q.2 ≠ p.2 := Ne.symm he
      simpa only [if_neg he,if_neg he',Set.inter_comm] using h
  loopless := by
    intro p h
    exact near_irrefl B p.1 (by simpa only [if_pos rfl] using h)

/-- Each apex has a distinguished point nonadjacent to its other two
neighbors. Thus its neighborhood induces at most one edge. -/
abbrev Apex := {t : V × V × V // ¬B.Adj t.1 t.2.1 ∧ ¬B.Adj t.1 t.2.2}

def neighborhood (e : Apex B) : Set V := {e.val.2.1,e.val.2.2,e.val.1}

abbrev extension := Erdos595BipartiteNeighborhoodApex.graph B (neighborhood B)

lemma extension_cliqueFree (hB : B.CliqueFree 3) :
    (right (right (extension B))).CliqueFree 4 :=
  Erdos595ThreePointMatchingApex.second_right_cliqueFree_of_one_edge
    B (neighborhood B) hB (fun e => e.val.2.1) (fun e => e.val.2.2)
    (fun e => e.val.1) (fun _ => Set.Subset.rfl)
    (fun e => e.property.1) (fun e => e.property.2)

def oldSupport (p : Pair B) : Set (V ⊕ Apex B) := Sum.inl '' support B p

def common (p : Pair B) : Set (V ⊕ Apex B) :=
  {z | ∀ a ∈ support B p, (extension B).Adj (Sum.inl a) z}

def forward (p : Pair B) : Biclique (extension B) :=
  ⟨(oldSupport B p,common B p),by
    rintro _ ⟨a,ha,rfl⟩ z hz
    exact hz a ha⟩

def reverse (p : Pair B) : Biclique (extension B) :=
  ⟨(common B p,oldSupport B p),by
    rintro z hz _ ⟨a,ha,rfl⟩
    exact (hz a ha).symm⟩

lemma common_old {p q : Pair B} (h : Dominates B q p) :
    (common B p ∩ oldSupport B q).Nonempty := by
  obtain ⟨a,ha,hp⟩ := h
  refine ⟨Sum.inl a,?_,⟨a,ha,rfl⟩⟩
  intro b hb
  exact (hp b hb).symm

lemma overlap_common {p q : Pair B}
    (h : (support B p ∩ support B q).Nonempty) :
    (common B p ∩ common B q).Nonempty := by
  classical
  obtain ⟨x,hxp,hxq⟩ := h
  obtain ⟨a,ha⟩ := support_at B p hxp
  obtain ⟨b,hb⟩ := support_at B q hxq
  have hxa : ¬B.Adj x a := independent B p hxp (by simp [ha])
  have hxb : ¬B.Adj x b := independent B q hxq (by simp [hb])
  let e : Apex B := ⟨(x,a,b),hxa,hxb⟩
  refine ⟨Sum.inr e,?_,?_⟩
  · intro z hz
    change z ∈ neighborhood B e
    simp only [ha,Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> simp [neighborhood,e]
  · intro z hz
    change z ∈ neighborhood B e
    simp only [hb,Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> simp [neighborhood,e]

lemma forward_near {p q : Pair B} (h : Near B p q) :
    (right (extension B)).Adj (forward B p) (forward B q) :=
  ⟨common_old B h.2,common_old B h.1⟩

lemma reverse_near {p q : Pair B} (h : Near B p q) :
    (right (extension B)).Adj (reverse B p) (reverse B q) := by
  have hp := common_old B h.1
  have hq := common_old B h.2
  exact ⟨by simpa only [reverse,Set.inter_comm] using hp,
    by simpa only [reverse,Set.inter_comm] using hq⟩

lemma forward_reverse {p q : Pair B}
    (h : (support B p ∩ support B q).Nonempty) :
    (right (extension B)).Adj (forward B p) (reverse B q) := by
  refine ⟨overlap_common B h,?_⟩
  obtain ⟨x,hxp,hxq⟩ := h
  exact ⟨Sum.inl x,⟨x,hxq,rfl⟩,⟨x,hxp,rfl⟩⟩

def intoFirst : graph B →g right (extension B) where
  toFun p := if p.2 then reverse B p.1 else forward B p.1
  map_rel' := by
    rintro ⟨p,i⟩ ⟨q,j⟩ h
    cases i <;> cases j
    · exact forward_near B h
    · exact forward_reverse B h
    · apply SimpleGraph.Adj.symm
      apply forward_reverse B
      simpa only [graph,Bool.true_eq_false,if_false,Set.inter_comm] using h
    · exact reverse_near B h

/-- Covariance of the biclique right adjoint. -/
def rightMap {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) : right G →g right H where
  toFun p := ⟨(f '' p.val.1,f '' p.val.2),by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    exact f.map_adj (p.property a ha b hb)⟩
  map_rel' := by
    intro p q h
    obtain ⟨a,hap,haq⟩ := h.1
    obtain ⟨b,hbq,hbp⟩ := h.2
    exact ⟨⟨f a,⟨a,hap,rfl⟩,⟨a,haq,rfl⟩⟩,
      ⟨f b,⟨b,hbq,rfl⟩,⟨b,hbp,rfl⟩⟩⟩

/-- The full right adjoint of the pair graph is K4-free. -/
theorem right_cliqueFree (hB : B.CliqueFree 3) : (right (graph B)).CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  let f := (rightMap (intoFirst B)).comp e.toHom
  have h (i j : Fin 4) (hij : i ≠ j) :
      (right (right (extension B))).Adj (f i) (f j) := f.map_adj hij
  exact Erdos595Work.no_adj_common_neighbors (extension_cliqueFree B hB)
    (h 0 1 (by decide)) (h 0 2 (by decide)) (h 1 2 (by decide))
    (h 0 3 (by decide)) (h 1 3 (by decide)) (h 2 3 (by decide))

#print axioms intoFirst
#print axioms right_cliqueFree
end Erdos595IndependentPair
