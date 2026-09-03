import Submission.ChordalIncidence

/-! Lifting paths and cycles through an internally disjoint family of paths.
This is infrastructure for cycle-junction recombination, not a proof of the conjecture. -/

open SimpleGraph
namespace Erdos184Work.PathSubstitution

variable {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}

structure Model (H : SimpleGraph W) (G : SimpleGraph V) where
  vertex : W → V
  injective : Function.Injective vertex
  path {a b : W} : H.Adj a b → G.Walk (vertex a) (vertex b)
  isPath {a b : W} (h : H.Adj a b) : (path h).IsPath
  vertex_mem {a b : W} (h : H.Adj a b) (x : W) :
    vertex x ∈ (path h).support ↔ x = a ∨ x = b
  edge_disjoint {a b c d : W} (h : H.Adj a b) (h' : H.Adj c d)
    (hne : s(a,b) ≠ s(c,d)) : (path h).edges.Disjoint (path h').edges
  support_inter {a b c d : W} (h : H.Adj a b) (h' : H.Adj c d)
    (hne : s(a,b) ≠ s(c,d)) (x : V) :
    x ∈ (path h).support → x ∈ (path h').support → x = vertex a ∨ x = vertex b

namespace Model
variable (M : Model H G)

def bind (M : Model H G) {a b : W} : H.Walk a b → G.Walk (M.vertex a) (M.vertex b)
  | .nil => .nil
  | .cons h p => (M.path h).append (bind M p)

lemma vertex_mem_bind {a b x : W} (p : H.Walk a b) :
    M.vertex x ∈ (M.bind p).support ↔ x ∈ p.support := by
  induction p with
  | nil => simp [bind,M.injective.eq_iff]
  | @cons a b c h p ih =>
    simp only [bind,Walk.mem_support_append_iff,M.vertex_mem,ih,
      Walk.support_cons,List.mem_cons]
    have hb : b ∈ p.support := p.start_mem_support
    aesop

lemma mem_edges_bind {a b : W} (p : H.Walk a b) (e : Sym2 V) :
    e ∈ (M.bind p).edges ↔ ∃ d ∈ p.darts, e ∈ (M.path d.adj).edges := by
  induction p with
  | nil => simp [bind]
  | @cons a b c h p ih =>
    simp [bind,ih]

lemma path_bind_edges_disjoint {a b c d : W} (h : H.Adj a b) (p : H.Walk c d)
    (hne : s(a,b) ∉ p.edges) : (M.path h).edges.Disjoint (M.bind p).edges := by
  apply List.disjoint_left.mpr
  intro e he hp
  obtain ⟨d,hd,hed⟩ := (M.mem_edges_bind p e).mp hp
  have hdiff : s(a,b) ≠ d.edge := by
    intro heq
    apply hne
    rw [heq]
    exact List.mem_map_of_mem hd
  exact List.disjoint_left.mp (M.edge_disjoint h d.adj hdiff) he hed

lemma path_bind_support_inter {a b c d : W} (h : H.Adj a b) (p : H.Walk c d)
    (hne : s(a,b) ∉ p.edges) (x : V)
    (hx : x ∈ (M.path h).support) (hxp : x ∈ (M.bind p).support) :
    x = M.vertex a ∨ x = M.vertex b := by
  induction p with
  | @nil c =>
    have hxc : x = M.vertex c := by simpa only [bind,Walk.support_nil,List.mem_singleton] using hxp
    rw [hxc] at hx ⊢
    exact ((M.vertex_mem h c).mp hx).imp (congrArg M.vertex) (congrArg M.vertex)
  | @cons c d e h' p ih =>
    simp only [Walk.edges_cons,List.mem_cons,not_or] at hne
    rcases (Walk.mem_support_append_iff _ _).mp hxp with hx' | hxp
    · exact M.support_inter h h' hne.1 x hx hx'
    · exact ih hne.2 hxp

lemma bind_isPath {a b : W} {p : H.Walk a b} (hp : p.IsPath) : (M.bind p).IsPath := by
  induction p with
  | nil => exact Walk.IsPath.nil
  | @cons a b c h p ih =>
    have hp' := Walk.cons_isPath_iff h p |>.mp hp
    apply append_isPath_of_support_inter (M.isPath h) (ih hp'.1)
    intro x hx hxq
    have hne : s(a,b) ∉ p.edges := by
      intro he
      exact hp'.2 (p.fst_mem_support_of_mem_edges he)
    rcases M.path_bind_support_inter h p hne x hx hxq with hx | hx
    · exact (hp'.2 ((M.vertex_mem_bind p).mp (hx ▸ hxq))).elim
    · exact hx

lemma bind_isCycle {a : W} {p : H.Walk a a} (hp : p.IsCycle) : (M.bind p).IsCycle := by
  cases p with
  | nil => exact (hp.not_nil Walk.Nil.nil).elim
  | @cons a b c h p =>
    have hp' := (Walk.cons_isCycle_iff p h).mp hp
    apply append_isCycle_of_support_inter (M.isPath h) (M.bind_isPath hp'.1)
      (fun he => h.ne (M.injective he)) (M.path_bind_edges_disjoint h p hp'.2)
    exact M.path_bind_support_inter h p hp'.2

#print axioms bind_isPath
#print axioms bind_isCycle
end Model

/-- A labelled multigraph whose edges are realized by internally disjoint paths.
The labels allow two different paths to have the same pair of endpoints. -/
structure Family (J W : Type*) (G : SimpleGraph V) where
  vertex : W → V
  injective : Function.Injective vertex
  src : J → W
  dst : J → W
  ne : ∀ j, src j ≠ dst j
  path (j : J) : G.Walk (vertex (src j)) (vertex (dst j))
  isPath : ∀ j, (path j).IsPath
  vertex_mem : ∀ j x, vertex x ∈ (path j).support ↔ x = src j ∨ x = dst j
  edge_disjoint : ∀ i j, i ≠ j → (path i).edges.Disjoint (path j).edges
  support_inter : ∀ i j, i ≠ j → ∀ x,
    x ∈ (path i).support → x ∈ (path j).support → x = vertex (src i) ∨ x = vertex (dst i)

namespace Family
variable {J : Type*} (F : Family J W G)

lemma endpoint_of_src {j : J} {a b : W} (he : s(F.src j,F.dst j) = s(a,b))
    (ha : F.src j = a) : F.dst j = b := by
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact h2
  · exact h2.trans (ha.symm.trans h1)

lemma endpoints_of_not_src {j : J} {a b : W} (he : s(F.src j,F.dst j) = s(a,b))
    (ha : F.src j ≠ a) : F.dst j = a ∧ F.src j = b := by
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact (ha h1).elim
  · exact ⟨h2,h1⟩

noncomputable def oriented (j : J) (a b : W) (he : s(F.src j,F.dst j) = s(a,b)) :
    G.Walk (F.vertex a) (F.vertex b) := by
  classical
  exact if ha : F.src j = a then
    (F.path j).copy (congrArg F.vertex ha) (congrArg F.vertex (F.endpoint_of_src he ha))
  else
    (F.path j).reverse.copy (congrArg F.vertex (F.endpoints_of_not_src he ha).1)
      (congrArg F.vertex (F.endpoints_of_not_src he ha).2)

lemma oriented_isPath (j : J) (a b : W) (he : s(F.src j,F.dst j) = s(a,b)) :
    (F.oriented j a b he).IsPath := by
  classical
  unfold oriented
  split_ifs <;> simp only [Walk.isPath_copy]
  · exact F.isPath j
  · exact (F.isPath j).reverse

lemma mem_oriented_support (j : J) (a b : W) (he : s(F.src j,F.dst j) = s(a,b)) (x : V) :
    x ∈ (F.oriented j a b he).support ↔ x ∈ (F.path j).support := by
  classical
  unfold oriented
  split_ifs <;> simp

lemma mem_oriented_edges (j : J) (a b : W) (he : s(F.src j,F.dst j) = s(a,b)) (e : Sym2 V) :
    e ∈ (F.oriented j a b he).edges ↔ e ∈ (F.path j).edges := by
  classical
  unfold oriented
  split_ifs <;> simp

noncomputable def model (H : SimpleGraph W) (route : H.Dart → J)
    (ends : ∀ d, s(F.src (route d),F.dst (route d)) = d.edge) : Model H G where
  vertex := F.vertex
  injective := F.injective
  path {a b} h := F.oriented (route ⟨(a,b),h⟩) a b (ends _)
  isPath h := F.oriented_isPath _ _ _ _
  vertex_mem {a b} h x := by
    rw [F.mem_oriented_support,F.vertex_mem]
    have he := congrArg (fun e : Sym2 W => x ∈ e) (ends ⟨(a,b),h⟩)
    simpa only [Dart.edge,Sym2.mem_iff] using iff_of_eq he
  edge_disjoint {a b c d} h h' hne := by
    have hr : route ⟨(a,b),h⟩ ≠ route ⟨(c,d),h'⟩ := by
      intro he
      apply hne
      exact (ends ⟨(a,b),h⟩).symm.trans ((congrArg (fun j => s(F.src j,F.dst j)) he).trans (ends ⟨(c,d),h'⟩))
    apply List.disjoint_left.mpr
    intro e he1 he2
    exact List.disjoint_left.mp (F.edge_disjoint _ _ hr)
      ((F.mem_oriented_edges _ _ _ _ _).mp he1) ((F.mem_oriented_edges _ _ _ _ _).mp he2)
  support_inter {a b c d} h h' hne x hx hx' := by
    have hr : route ⟨(a,b),h⟩ ≠ route ⟨(c,d),h'⟩ := by
      intro he
      apply hne
      exact (ends ⟨(a,b),h⟩).symm.trans ((congrArg (fun j => s(F.src j,F.dst j)) he).trans (ends ⟨(c,d),h'⟩))
    have hm := F.support_inter _ _ hr x ((F.mem_oriented_support _ _ _ _ _).mp hx)
      ((F.mem_oriented_support _ _ _ _ _).mp hx')
    rcases Sym2.eq_iff.mp (ends ⟨(a,b),h⟩) with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · simpa only [h1,h2] using hm
    · simpa only [h1,h2,or_comm] using hm

lemma mem_model_bind_edges (H : SimpleGraph W) (route : H.Dart → J)
    (ends : ∀ d, s(F.src (route d),F.dst (route d)) = d.edge)
    {a b : W} (p : H.Walk a b) (e : Sym2 V) :
    e ∈ ((F.model H route ends).bind p).edges ↔
      ∃ j ∈ p.darts.map route, e ∈ (F.path j).edges := by
  rw [Model.mem_edges_bind]
  simp only [model,F.mem_oriented_edges,List.mem_map]
  constructor
  · rintro ⟨d,hd,he⟩
    exact ⟨route d,⟨d,hd,rfl⟩,he⟩
  · rintro ⟨j,⟨d,hd,rfl⟩,he⟩
    exact ⟨d,hd,he⟩

lemma model_binds_disjoint (H₁ H₂ : SimpleGraph W) (r₁ : H₁.Dart → J) (r₂ : H₂.Dart → J)
    (he₁ : ∀ d, s(F.src (r₁ d),F.dst (r₁ d)) = d.edge)
    (he₂ : ∀ d, s(F.src (r₂ d),F.dst (r₂ d)) = d.edge)
    {a b c d : W} (p : H₁.Walk a b) (q : H₂.Walk c d)
    (hdis : (p.darts.map r₁).Disjoint (q.darts.map r₂)) :
    ((F.model H₁ r₁ he₁).bind p).edges.Disjoint ((F.model H₂ r₂ he₂).bind q).edges := by
  apply List.disjoint_left.mpr
  intro e hep heq
  obtain ⟨i,hi,hei⟩ := (F.mem_model_bind_edges _ _ _ _ _).mp hep
  obtain ⟨j,hj,hej⟩ := (F.mem_model_bind_edges _ _ _ _ _).mp heq
  have hij : i ≠ j := by rintro rfl; exact List.disjoint_left.mp hdis hi hj
  exact List.disjoint_left.mp (F.edge_disjoint i j hij) hei hej

lemma number_le_two_lifted_cycles [Fintype V]
    (H₁ H₂ : SimpleGraph W) (r₁ : H₁.Dart → J) (r₂ : H₂.Dart → J)
    (he₁ : ∀ d, s(F.src (r₁ d),F.dst (r₁ d)) = d.edge)
    (he₂ : ∀ d, s(F.src (r₂ d),F.dst (r₂ d)) = d.edge)
    {a b : W} (p : H₁.Walk a a) (q : H₂.Walk b b) (hp : p.IsCycle) (hq : q.IsCycle)
    (hdis : (p.darts.map r₁).Disjoint (q.darts.map r₂))
    (hroutes : ∀ j, j ∈ p.darts.map r₁ ∨ j ∈ q.darts.map r₂)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply LocalObstruction.number_le_two_cycles
    ((F.model H₁ r₁ he₁).bind p) ((F.model H₂ r₂ he₂).bind q)
    ((F.model H₁ r₁ he₁).bind_isCycle hp) ((F.model H₂ r₂ he₂).bind_isCycle hq)
    (F.model_binds_disjoint H₁ H₂ r₁ r₂ he₁ he₂ p q hdis)
  intro x y
  constructor
  · intro hxy
    obtain ⟨j,hj⟩ := hcover x y hxy
    rcases hroutes j with hr | hr
    · exact Or.inl ((F.mem_model_bind_edges _ _ _ _ _).mpr ⟨j,hr,hj⟩)
    · exact Or.inr ((F.mem_model_bind_edges _ _ _ _ _).mpr ⟨j,hr,hj⟩)
  · rintro (he | he)
    · exact Walk.adj_of_mem_edges _ he
    · exact Walk.adj_of_mem_edges _ he

#print axioms number_le_two_lifted_cycles
#print axioms model
#print axioms model_binds_disjoint
end Family
end Erdos184Work.PathSubstitution
