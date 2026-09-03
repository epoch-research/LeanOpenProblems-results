import Submission.InfiniteTriangleRamsey

/-!
A bounded number of positive predecessors in the Erdős--Rado tree does not
control edges between different branches. Attaching private leaves, ordered
before the old vertices, makes every positive-predecessor set have size at
most one, for an ARBITRARY graph. Clique exclusions and countable triangle-free
edge coverability are unchanged. This is not a settlement of Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595ErdosRadoLeaf
open Erdos595InfiniteTriangleRamsey Erdos595Work

variable {V : Type*}
abbrev Vertex (V : Type*) := V ⊕ₗ V

def leaf (v : V) : Vertex V := toLex (.inl v)
def old (v : V) : Vertex V := toLex (.inr v)

def graph (G : SimpleGraph V) : SimpleGraph (Vertex V) where
  Adj x y := match ofLex x, ofLex y with
    | .inl _, .inl _ => False
    | .inl a, .inr b => a = b
    | .inr a, .inl b => a = b
    | .inr a, .inr b => G.Adj a b
  symm := by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h.symm
    · exact h.symm
    · exact h.symm
  loopless := by
    intro x h
    cases x
    · exact h
    · exact G.loopless _ h

def embedding (G : SimpleGraph V) : G ↪g graph G where
  toFun := old
  inj' := fun _ _ h => Sum.inr_injective h
  map_rel_iff' := Iff.rfl

lemma triangle_old (G : SimpleGraph V) {a b c : Vertex V}
    (hab : (graph G).Adj a b) (hac : (graph G).Adj a c)
    (hbc : (graph G).Adj b c) :
    ∃ x y z, a = old x ∧ b = old y ∧ c = old z := by
  cases a with
  | inl x =>
    cases b with
    | inl y => exact hab.elim
    | inr y =>
      cases c with
      | inl z => exact hac.elim
      | inr z =>
        change x = y at hab
        change x = z at hac
        exact ((show G.Adj y z from hbc).ne (hab.symm.trans hac)).elim
  | inr x =>
    cases b with
    | inl y =>
      cases c with
      | inl z => exact hbc.elim
      | inr z =>
        change x = y at hab
        change y = z at hbc
        exact ((show G.Adj x z from hac).ne (hab.trans hbc)).elim
    | inr y =>
      cases c with
      | inl z =>
        change x = z at hac
        change y = z at hbc
        exact ((show G.Adj x y from hab).ne (hac.trans hbc.symm)).elim
      | inr z => exact ⟨x,y,z,rfl,rfl,rfl⟩

theorem cliqueFree (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    (graph G).CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have ha : ∀ i j : Fin 4, i ≠ j → (graph G).Adj (e i) (e j) :=
    fun _ _ h => e.map_rel_iff.mpr h
  obtain ⟨a,b,c,h0,h1,h2⟩ := triangle_old G
    (ha 0 1 (by decide)) (ha 0 2 (by decide)) (ha 1 2 (by decide))
  obtain ⟨_,_,d,_,_,h3⟩ := triangle_old G
    (ha 0 1 (by decide)) (ha 0 3 (by decide)) (ha 1 3 (by decide))
  have h01 := ha 0 1 (by decide)
  have h02 := ha 0 2 (by decide)
  have h03 := ha 0 3 (by decide)
  have h12 := ha 1 2 (by decide)
  have h13 := ha 1 3 (by decide)
  have h23 := ha 2 3 (by decide)
  rw [h0,h1] at h01
  rw [h0,h2] at h02
  rw [h0,h3] at h03
  rw [h1,h2] at h12
  rw [h1,h3] at h13
  rw [h2,h3] at h23
  exact no_adj_common_neighbors hG h01 h02 h12 h03 h13 h23

def project : Vertex V → V := fun x => (ofLex x).elim id id

theorem cover_iff (G : SimpleGraph V) :
    IsCountableUnionOfTriangleFree (graph G) ↔ IsCountableUnionOfTriangleFree G := by
  constructor
  · exact countable_union_of_hom (embedding G).toHom
  · intro hG
    obtain ⟨c,hc⟩ := (countable_union_iff_edge_coloring G).mp hG
    apply (countable_union_iff_edge_coloring (graph G)).mpr
    refine ⟨fun e => c (e.map project),?_⟩
    intro a b d hab had hbd he
    obtain ⟨x,y,z,rfl,rfl,rfl⟩ := triangle_old G hab had hbd
    exact hc x y z hab had hbd he

section Tree
variable [LinearOrder V] [WellFoundedLT V]

instance : WellFoundedLT (Vertex V) :=
  ⟨Sum.lex_wf (wellFounded_lt (α := V)) (wellFounded_lt (α := V))⟩

noncomputable def color (G : SimpleGraph V) (x y : Vertex V) : Bool :=
  by classical exact decide ((graph G).Adj x y)

lemma pred_leaf (G : SimpleGraph V) (v : V) (x : Vertex V) :
    x ∈ pred (color G) (leaf v) ↔ ∃ u, u < v ∧ x = leaf u := by
  constructor
  · intro hx
    have hl := pred_lt (color G) hx
    cases x with
    | inl u => exact ⟨u,Sum.Lex.inl_lt_inl_iff.mp hl,rfl⟩
    | inr u => exact (Sum.Lex.not_inr_lt_inl hl).elim
  · rintro ⟨u,hu,rfl⟩
    apply (mem_pred (color G)).mpr
    refine ⟨Sum.Lex.inl_lt_inl_iff.mpr hu,?_⟩
    intro w hw
    have hl := pred_lt (color G) hw
    cases w with
    | inl t => rfl
    | inr t => exact (Sum.Lex.not_inr_lt_inl hl).elim

lemma leaf_pred_old (G : SimpleGraph V) (u v : V) :
    leaf u ∈ pred (color G) (old v) ↔ u ≤ v := by
  classical
  constructor
  · intro h
    by_contra hn
    have hvu : v < u := lt_of_not_ge hn
    have hv : leaf v ∈ pred (color G) (leaf u) :=
      (pred_leaf G u (leaf v)).mpr ⟨v,hvu,rfl⟩
    have he := pred_agree (color G) h hv
    simp [color,graph,leaf,old] at he
  · intro huv
    apply (mem_pred (color G)).mpr
    refine ⟨Sum.Lex.inl_lt_inr u v,?_⟩
    intro w hw
    obtain ⟨t,htu,rfl⟩ := (pred_leaf G u w).mp hw
    have htv : t ≠ v := (htu.trans_le huv).ne
    simp [color,graph,leaf,old,htv]

lemma old_not_pred_old (G : SimpleGraph V) (u v : V) :
    old u ∉ pred (color G) (old v) := by
  classical
  intro h
  have huv : u < v := Sum.Lex.inr_lt_inr_iff.mp (pred_lt (color G) h)
  have hu := (leaf_pred_old G u u).mpr le_rfl
  have he := pred_agree (color G) h hu
  simp [color,graph,leaf,old,huv.ne] at he

/-- All predecessors of an original vertex are on the independent leaf spine. -/
theorem pred_old (G : SimpleGraph V) (v : V) (x : Vertex V) :
    x ∈ pred (color G) (old v) ↔ ∃ u, u ≤ v ∧ x = leaf u := by
  constructor
  · intro hx
    cases x with
    | inl u => exact ⟨u,(leaf_pred_old G u v).mp hx,rfl⟩
    | inr u => exact (old_not_pred_old G u v hx).elim
  · rintro ⟨u,hu,rfl⟩
    exact (leaf_pred_old G u v).mpr hu

/-- The positive predecessor set is EMPTY at each private leaf. -/
theorem positive_leaf (G : SimpleGraph V) (v : V) :
    {x | x ∈ pred (color G) (leaf v) ∧ (graph G).Adj x (leaf v)} = ∅ := by
  ext x
  apply iff_false_intro
  rintro ⟨hp,hx⟩
  obtain ⟨u,_,rfl⟩ := (pred_leaf G v x).mp hp
  exact hx

/-- The positive predecessor set is a SINGLETON at each original vertex,
regardless of the adjacency relation on the original graph. -/
theorem positive_old (G : SimpleGraph V) (v : V) :
    {x | x ∈ pred (color G) (old v) ∧ (graph G).Adj x (old v)} = {leaf v} := by
  ext x
  constructor
  · rintro ⟨hp,ha⟩
    obtain ⟨u,_,rfl⟩ := (pred_old G v x).mp hp
    change u = v at ha
    exact congrArg leaf ha
  · intro hx
    have he : x = leaf v := hx
    subst x
    exact ⟨(leaf_pred_old G v v).mpr le_rfl,rfl⟩

/-- Every graph has a private-leaf enlargement with at most one positive
predecessor per vertex in its actual Erdős--Rado tree. -/
theorem at_most_one_positive (G : SimpleGraph V) (v a b : Vertex V)
    (ha : a ∈ pred (color G) v) (hb : b ∈ pred (color G) v)
    (hav : (graph G).Adj a v) (hbv : (graph G).Adj b v) : a = b := by
  cases v with
  | inl v =>
    have he := Set.ext_iff.mp (positive_leaf G v) a
    exact (he.mp ⟨ha,hav⟩).elim
  | inr v =>
    have he := Set.ext_iff.mp (positive_old G v) a
    have hf := Set.ext_iff.mp (positive_old G v) b
    exact (he.mp ⟨ha,hav⟩).trans (hf.mp ⟨hb,hbv⟩).symm

end Tree
#print axioms cliqueFree
#print axioms cover_iff
#print axioms pred_old
#print axioms at_most_one_positive
end Erdos595ErdosRadoLeaf
