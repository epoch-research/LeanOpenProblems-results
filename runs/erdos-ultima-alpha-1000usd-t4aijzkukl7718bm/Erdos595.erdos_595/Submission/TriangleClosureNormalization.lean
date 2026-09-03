import Submission.TriangleRadius

/-!
Every graph embeds in a graph generated under triangle completion by one
edge over a bipartite triangle-closed spanning subgraph. The enlargement
preserves K4-freeness. This rules out a proposed closure-growth shortcut;
it does not prove or disprove Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595TriangleClosure
open Erdos595TriangleRadius

universe u
variable {V : Type u}

/-- Two sides already present force the third, when it is an ambient edge. -/
def Closed {A : Type*} (F K : SimpleGraph A) : Prop :=
  ∀ x y z, K.Adj x y → K.Adj x z → F.Adj y z → K.Adj y z

def OldRel : Vertex V → Vertex V → Prop
  | .b,.port _ | .port _,.b => True
  | .a,.pair _ | .pair _,.a => True
  | .port v,.orig w | .orig w,.port v => v = w
  | _,_ => False

def old : SimpleGraph (Vertex V) where
  Adj := OldRel
  symm := by intro x y h; cases x <;> cases y <;> simp_all [OldRel]
  loopless := by intro x; cases x <;> simp [OldRel]

def side : Vertex V → Bool
  | .port _ | .pair _ => true
  | _ => false

/-- The old graph is genuinely bipartite, with an explicit two-coloring. -/
def oldColoring : (old (V := V)).Coloring Bool := SimpleGraph.Coloring.mk side (by
  intro x y h
  cases x <;> cases y <;> simp_all [old,OldRel,side])

lemma old_le (G : SimpleGraph V) : old ≤ graph G := by
  intro x y h
  cases x <;> cases y <;> simp_all [old,OldRel,adj_iff,Erdos595TriangleRadius.Rel]

/-- No ambient triangle contains even two old edges. -/
lemma no_two_old (G : SimpleGraph V) (x y z : Vertex V)
    (hxy : old.Adj x y) (hxz : old.Adj x z) (hyz : (graph G).Adj y z) : False := by
  cases x <;> cases y <;> cases z <;>
    simp_all [old,OldRel,adj_iff,Erdos595TriangleRadius.Rel]

lemma old_closed (G : SimpleGraph V) : Closed (graph G) old :=
  fun x y z hxy hxz hyz => (no_two_old G x y z hxy hxz hyz).elim

lemma seed_not_old : ¬(old (V := V)).Adj .a .b := id

/-- Closing the old graph plus the ONE distinguished edge generates the
entire enlarged graph. In particular it generates the arbitrary original G. -/
theorem generates (G : SimpleGraph V) (K : SimpleGraph (Vertex V))
    (hOld : old ≤ K) (hSeed : K.Adj .a .b) (hClosed : Closed (graph G) K) :
    graph G ≤ K := by
  have hp (v : V) : K.Adj .a (.port v) :=
    hClosed .b .a (.port v) hSeed.symm (hOld (show old.Adj .b (.port v) from trivial)) trivial
  have hq (v : V) (e : Sym2 V) (hv : v ∈ e) : K.Adj (.port v) (.pair e) :=
    hClosed .a (.port v) (.pair e) (hp v)
      (hOld (show old.Adj .a (.pair e) from trivial)) hv
  have hr (v : V) (e : Sym2 V) (hv : v ∈ e) : K.Adj (.pair e) (.orig v) :=
    hClosed (.port v) (.pair e) (.orig v) (hq v e hv)
      (hOld (show old.Adj (.port v) (.orig v) from rfl)) hv
  have ho (v w : V) (hvw : G.Adj v w) : K.Adj (.orig v) (.orig w) :=
    hClosed (.pair s(v,w)) (.orig v) (.orig w)
      (hr v s(v,w) (Sym2.mem_mk_left v w))
      (hr w s(v,w) (Sym2.mem_mk_right v w)) hvw
  intro x y hxy
  cases x with
  | a =>
    cases y with
    | a => exact hxy.elim
    | b => exact hSeed
    | port v => exact hp v
    | pair e => exact hOld (show old.Adj .a (.pair e) from trivial)
    | orig v => exact hxy.elim
  | b =>
    cases y with
    | a => exact hSeed.symm
    | b => exact hxy.elim
    | port v => exact hOld (show old.Adj .b (.port v) from trivial)
    | pair e => exact hxy.elim
    | orig v => exact hxy.elim
  | port v =>
    cases y with
    | a => exact (hp v).symm
    | b => exact (hOld (show old.Adj .b (.port v) from trivial)).symm
    | port w => exact hxy.elim
    | pair e => exact hq v e hxy
    | orig w => exact hOld (show old.Adj (.port v) (.orig w) from (show w = v from hxy).symm)
  | pair e =>
    cases y with
    | a => exact (hOld (show old.Adj .a (.pair e) from trivial)).symm
    | b => exact hxy.elim
    | port v => exact (hq v e hxy).symm
    | pair f => exact hxy.elim
    | orig v => exact hr v e hxy
  | orig v =>
    cases y with
    | a => exact hxy.elim
    | b => exact hxy.elim
    | port w => exact hOld (show old.Adj (.orig v) (.port w) from (show v = w from hxy).symm)
    | pair e => exact (hr v e hxy).symm
    | orig w => exact ho v w hxy

/-- There is no proper triangle-closed intermediate graph containing the
bipartite base and the distinguished edge. -/
theorem closed_eq (G : SimpleGraph V) (K : SimpleGraph (Vertex V))
    (hK : K ≤ graph G) (hOld : old ≤ K) (hSeed : K.Adj .a .b)
    (hClosed : Closed (graph G) K) : K = graph G :=
  le_antisymm hK (generates G K hOld hSeed hClosed)

/-- The closure normal form retains the K4 restriction and an induced copy
of the original graph. There is no hidden coverability premise. -/
theorem normal_form (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    ∃ (A : Type u) (F M : SimpleGraph A) (a b : A),
      F.CliqueFree 4 ∧ Nonempty (G ↪g F) ∧ Nonempty (M.Coloring Bool) ∧ M ≤ F ∧
      Closed F M ∧ F.Adj a b ∧ ¬M.Adj a b ∧
      ∀ K : SimpleGraph A, K ≤ F → M ≤ K → K.Adj a b → Closed F K → K = F := by
  refine ⟨Vertex V,graph G,old,.a,.b,cliqueFree G hG,⟨embedding G⟩,
    ⟨oldColoring⟩,old_le G,old_closed G,trivial,seed_not_old,?_⟩
  exact fun K hK hM hs hc => closed_eq G K hK hM hs hc

/-- The arbitrary original graph lies entirely among the NEW edges, not
merely among the edges of the full enlargement. -/
def newEmbedding (G : SimpleGraph V) : G ↪g (graph G \ old) where
  toFun := Vertex.orig
  inj' := fun _ _ h => Vertex.orig.inj h
  map_rel_iff' := by
    intro v w
    simp only [SimpleGraph.sdiff_adj,adj_iff,Erdos595TriangleRadius.Rel,old,OldRel,
      not_false_eq_true,and_true]

theorem no_cover_new (G : SimpleGraph V)
    (hG : ¬Erdos595Work.IsCountableUnionOfTriangleFree G) :
    ¬Erdos595Work.IsCountableUnionOfTriangleFree (graph G \ old) := by
  intro h
  exact hG (Erdos595Work.countable_union_of_hom (newEmbedding G).toHom h)

#print axioms old_closed
#print axioms generates
#print axioms normal_form
#print axioms newEmbedding
#print axioms no_cover_new
end Erdos595TriangleClosure
