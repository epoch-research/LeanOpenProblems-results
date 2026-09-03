import Submission.PathKernelTransport

/-! Every loopless labelled multigraph has a simple bipartite subdivision
realization, using one new private vertex per edge label. -/
open SimpleGraph
namespace Erdos184Work.LabelKernel.Realization
open PathSubstitution
variable {E W : Type*} [DecidableEq E] [DecidableEq W]
variable (src dst : E → W)

def graph : SimpleGraph (W ⊕ E) where
  Adj
    | .inl w, .inr e => w = src e ∨ w = dst e
    | .inr e, .inl w => w = src e ∨ w = dst e
    | _, _ => False
  symm := by intro x y h; cases x <;> cases y <;> exact h
  loopless := by intro x; cases x <;> exact id

instance : DecidableRel (graph src dst).Adj := by
  intro x y
  cases x <;> cases y <;> unfold graph <;> infer_instance

def path (e : E) : (graph src dst).Walk (.inl (src e)) (.inl (dst e)) :=
  .cons (v := Sum.inr e) (Or.inl rfl)
    (.cons (v := Sum.inl (dst e)) (Or.inr rfl) .nil)

lemma path_isPath (hloop : ∀ e, src e ≠ dst e) (e : E) : (path src dst e).IsPath := by
  rw [Walk.isPath_def]
  simp [path,Walk.support_cons,hloop e]

lemma vertex_mem (e : E) (w : W) :
    Sum.inl w ∈ (path src dst e).support ↔ w = src e ∨ w = dst e := by
  simp [path,Walk.support_cons]

lemma edges_disjoint (e f : E) (hef : e ≠ f) :
    (path src dst e).edges.Disjoint (path src dst f).edges := by
  apply List.disjoint_left.mpr
  intro x hx hy
  simp only [path,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with hy | hy
  all_goals simp only [Sym2.eq_iff,Sum.inl.injEq,Sum.inr.injEq,
    Sum.inl_ne_inr,Sum.inr_ne_inl,false_and,and_false,or_false,false_or] at hy
  all_goals first | exact hef hy.2 | exact hef hy.1

lemma support_inter (e f : E) (hef : e ≠ f) (x : W ⊕ E)
    (hx : x ∈ (path src dst e).support) (hy : x ∈ (path src dst f).support) :
    x = .inl (src e) ∨ x = .inl (dst e) := by
  cases x with
  | inl w => simpa only [Sum.inl.injEq] using (vertex_mem src dst e w).mp hx
  | inr j =>
    have he : j = e := by simpa [path,Walk.support_cons] using hx
    have hf : j = f := by simpa [path,Walk.support_cons] using hy
    exact (hef (he.symm.trans hf)).elim

def family (hloop : ∀ e, src e ≠ dst e) : Family E W (graph src dst) where
  vertex := Sum.inl
  injective := Sum.inl_injective
  src := src
  dst := dst
  ne := hloop
  path := path src dst
  isPath := path_isPath src dst hloop
  vertex_mem := vertex_mem src dst
  edge_disjoint := edges_disjoint src dst
  support_inter := support_inter src dst

lemma cover (hloop : ∀ e, src e ≠ dst e) (x y : W ⊕ E)
    (hxy : (graph src dst).Adj x y) : ∃ e, s(x,y) ∈ ((family src dst hloop).path e).edges := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact hxy.elim
    | inr e =>
      refine ⟨e,?_⟩
      rcases hxy with rfl | rfl
      · simp [family,path]
      · simp [family,path,Sym2.eq_swap]
  | inr e =>
    cases y with
    | inl y =>
      refine ⟨e,?_⟩
      rcases hxy with rfl | rfl
      · simp [family,path,Sym2.eq_swap]
      · simp [family,path]
    | inr f => exact hxy.elim

#print axioms family
#print axioms cover
end Erdos184Work.LabelKernel.Realization
