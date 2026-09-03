import Submission.Work

/-!
Successively removing maximal triangle-free subgraphs can leave a triangle
after all countably many stages, even in a countable three-colorable graph.
This refutes a greedy proof strategy, not Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595MaximalDecompositionFailure

inductive Node where
  | leaf : Fin 3 → Node
  | fork : ℕ → Node → Node → Node
  deriving DecidableEq, Countable

open Node

def height : Node → ℕ
  | leaf _ => 0
  | fork _ a b => max (height a) (height b) + 1

def Child (a : Node) : Node → Prop
  | leaf _ => False
  | fork _ b c => a = b ∨ a = c

lemma child_height {a b : Node} (h : Child a b) : height a < height b := by
  cases b with
  | leaf i => exact h.elim
  | fork n b c =>
    rcases h with rfl | rfl <;> simp only [height] <;> omega

def Adj (a b : Node) : Prop :=
  (∃ i j : Fin 3, a = leaf i ∧ b = leaf j ∧ i ≠ j) ∨ Child a b ∨ Child b a

lemma adj_symm {a b : Node} (h : Adj a b) : Adj b a := by
  rcases h with ⟨i,j,rfl,rfl,h⟩ | h | h
  · exact Or.inl ⟨j,i,rfl,rfl,h.symm⟩
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

def tag : Node → WithTop ℕ
  | leaf _ => ⊤
  | fork n _ _ => n

def label (a b : Node) : WithTop ℕ :=
  if height a < height b then tag b else tag a

lemma label_symm {a b : Node} (h : Adj a b) : label a b = label b a := by
  rcases h with ⟨i,j,rfl,rfl,_⟩ | h | h
  · rfl
  · have hh := child_height h
    simp only [label, if_pos hh, if_neg (not_lt_of_gt hh)]
  · have hh := child_height h
    simp only [label, if_pos hh, if_neg (not_lt_of_gt hh)]

lemma label_child {a : Node} {n : ℕ} {b c : Node} (h : Child a (fork n b c)) :
    label a (fork n b c) = n := by
  simp only [label, if_pos (child_height h), tag]

def Valid : Node → Prop
  | leaf _ => True
  | fork n a b => Valid a ∧ Valid b ∧ Adj a b ∧ (n : WithTop ℕ) < label a b

abbrev Vertex := {a : Node // Valid a}

private def missing (a b : Fin 3) : Fin 3 :=
  if a ≠ 0 ∧ b ≠ 0 then 0 else if a ≠ 1 ∧ b ≠ 1 then 1 else 2

private lemma missing_ne (a b : Fin 3) : missing a b ≠ a ∧ missing a b ≠ b := by
  fin_cases a <;> fin_cases b <;> decide +kernel

def color : Node → Fin 3
  | leaf i => i
  | fork _ a b => missing (color a) (color b)

lemma color_child {a b : Node} (h : Child a b) : color a ≠ color b := by
  cases b with
  | leaf i => exact h.elim
  | fork n b c =>
    have hb := (missing_ne (color b) (color c)).1.symm
    have hc := (missing_ne (color b) (color c)).2.symm
    rcases h with rfl | rfl
    · exact hb
    · exact hc

lemma color_ne {a b : Node} (h : Adj a b) : color a ≠ color b := by
  rcases h with ⟨i,j,rfl,rfl,h⟩ | h | h
  · exact h
  · exact color_child h
  · exact (color_child h).symm

def G : SimpleGraph Vertex where
  Adj a b := Adj a.val b.val
  symm := fun _ _ h => adj_symm h
  loopless := fun _ h => color_ne h rfl

def coloring : G.Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk (fun a => color a.val) (fun h => color_ne h)

lemma cliqueFree : G.CliqueFree 4 := coloring.colorable.cliqueFree (by decide)

lemma countable_cover : Erdos595Work.IsCountableUnionOfTriangleFree G := by
  apply Erdos595Work.countable_union_of_coloring G
  refine SimpleGraph.Coloring.mk (fun v n => if (coloring v).val = n then 1 else 0) ?_
  intro v w hvw he
  have hh := congrFun he (coloring v).val
  have hn : (coloring w).val ≠ (coloring v).val :=
    fun h => coloring.valid hvw (Fin.ext h.symm)
  simp only [if_neg hn] at hh
  exact (by decide : (1 : Fin 2) ≠ 0) hh

/-- Every still-unremoved edge has a fresh common neighbor in every lower
color. The two new edges have exactly that lower color. -/
lemma lower_witness {a b : Vertex} (hab : G.Adj a b) (n : ℕ)
    (hn : (n : WithTop ℕ) < label a.val b.val) :
    ∃ w : Vertex, G.Adj a w ∧ G.Adj b w ∧
      label a.val w.val = n ∧ label b.val w.val = n := by
  let w : Vertex := ⟨fork n a.val b.val, a.property, b.property, hab, hn⟩
  refine ⟨w, Or.inr (Or.inl (Or.inl rfl)), Or.inr (Or.inl (Or.inr rfl)), ?_, ?_⟩
  · exact label_child (Or.inl rfl)
  · exact label_child (Or.inr rfl)

lemma child_of_le {a b : Node} (h : Adj a b) (hab : height a ≤ height b)
    (hb : 0 < height b) : Child a b := by
  rcases h with ⟨i,j,rfl,rfl,_⟩ | h | h
  · exact (Nat.lt_irrefl 0 hb).elim
  · exact h
  · have hh := child_height h
    omega

/-- A triangle whose highest vertex is a fork has two equal lower-colored
edges and one strictly higher-colored edge. -/
lemma triangle_not_same (n : ℕ) {a b c : Vertex}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (ha : height a.val ≤ height c.val) (hb : height b.val ≤ height c.val)
    (h₁ : label a.val b.val = n) (h₂ : label a.val c.val = n) : False := by
  cases hc : c.val with
  | leaf i =>
    have haz : height a.val = 0 := by simp only [hc, height] at ha; omega
    have hbz : height b.val = 0 := by simp only [hc, height] at hb; omega
    have al : ∃ j, a.val = leaf j := by
      cases he : a.val with
      | leaf j => exact ⟨j,rfl⟩
      | fork k x y => simp only [he, height] at haz; omega
    have bl : ∃ j, b.val = leaf j := by
      cases he : b.val with
      | leaf j => exact ⟨j,rfl⟩
      | fork k x y => simp only [he, height] at hbz; omega
    obtain ⟨j,hj⟩ := al
    obtain ⟨k,hk⟩ := bl
    simp only [hj,hk,label,height,lt_self_iff_false,if_false,tag] at h₁
    exact WithTop.top_ne_coe h₁
  | fork k x y =>
    have hcpos : 0 < height c.val := by simp only [hc,height]; omega
    have hach : Child a.val c.val := child_of_le hac ha hcpos
    have hbch : Child b.val c.val := child_of_le hbc hb hcpos
    have hlab : label a.val c.val = k := by rw [hc] at hach ⊢; exact label_child hach
    have hnk : (k : WithTop ℕ) = n := hlab.symm.trans h₂
    have hv := c.property
    rw [hc] at hv hach hbch
    change Valid x ∧ Valid y ∧ Adj x y ∧ (k : WithTop ℕ) < label x y at hv
    rcases hach with hax | hay <;> rcases hbch with hbx | hby
    · exact (color_ne hab) (congrArg color (hax.trans hbx.symm))
    · rw [← hax, ← hby, h₁, hnk] at hv
      exact lt_irrefl _ hv.2.2.2
    · have hl : label x y = label a.val b.val := by
        rw [← hbx, ← hay]
        exact (label_symm hab).symm
      rw [hl,h₁,hnk] at hv
      exact lt_irrefl _ hv.2.2.2
    · exact (color_ne hab) (congrArg color (hay.trans hby.symm))

def piece (n : ℕ) : SimpleGraph Vertex where
  Adj a b := G.Adj a b ∧ label a.val b.val = n
  symm := fun _ _ h => ⟨h.1.symm, (label_symm h.1).symm.trans h.2⟩
  loopless := fun _ h => G.loopless _ h.1

lemma piece_triangleFree (n : ℕ) : (piece n).CliqueFree 3 := by
  intro t ht
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp ht
  by_cases ha : height a.val ≤ height c.val
  · by_cases hb : height b.val ≤ height c.val
    · exact triangle_not_same n hab.1 hac.1 hbc.1 ha hb hab.2 hac.2
    · exact triangle_not_same n hac.1 hab.1 hbc.1.symm
        (ha.trans (le_of_not_ge hb)) (le_of_not_ge hb) hac.2 hab.2
  · by_cases hb : height b.val ≤ height a.val
    · exact triangle_not_same n hbc.1 hab.1.symm hac.1.symm hb
        (le_of_not_ge ha) hbc.2 ((label_symm hab.1).symm.trans hab.2)
    · exact triangle_not_same n hac.1 hab.1 hbc.1.symm (le_of_not_ge hb)
        ((le_of_not_ge ha).trans (le_of_not_ge hb)) hac.2 hab.2

/-- The graph remaining just before removing color n. -/
def remaining (n : ℕ) : SimpleGraph Vertex where
  Adj a b := G.Adj a b ∧ (n : WithTop ℕ) ≤ label a.val b.val
  symm := fun _ _ h => ⟨h.1.symm, (label_symm h.1) ▸ h.2⟩
  loopless := fun _ h => G.loopless _ h.1

lemma remaining_zero : remaining 0 = G := by
  ext a b
  change (G.Adj a b ∧ (0 : WithTop ℕ) ≤ label a.val b.val) ↔ G.Adj a b
  simp

/-- These really are successive removals, rather than unrelated maximal
subgraphs of G. -/
lemma remaining_succ (n : ℕ) : remaining (n+1) = remaining n \ piece n := by
  ext a b
  rw [SimpleGraph.sdiff_adj]
  change (G.Adj a b ∧ ((n+1 : ℕ) : WithTop ℕ) ≤ label a.val b.val) ↔
    (G.Adj a b ∧ (n : WithTop ℕ) ≤ label a.val b.val) ∧
      ¬(G.Adj a b ∧ label a.val b.val = n)
  by_cases h : G.Adj a b
  · simp only [h,true_and]
    generalize label a.val b.val = l
    induction l using WithTop.recTopCoe with
    | top => simp
    | coe k =>
      simp only [← WithTop.coe_natCast, Nat.cast_id, WithTop.coe_le_coe, WithTop.coe_inj]
      omega
  · simp only [h,false_and,not_false_eq_true]

lemma piece_le_remaining (n : ℕ) : piece n ≤ remaining n := by
  intro a b h
  exact ⟨h.1,le_of_eq h.2.symm⟩

/-- The chosen piece is genuinely maximal in the remaining graph. -/
theorem piece_maximal (n : ℕ) (J : SimpleGraph Vertex) (hJ : J.CliqueFree 3)
    (hlo : piece n ≤ J) (hhi : J ≤ remaining n) : J = piece n := by
  apply le_antisymm ?_ hlo
  intro a b hab
  have hh := hhi hab
  refine ⟨hh.1, ?_⟩
  by_contra hn
  have hlt : (n : WithTop ℕ) < label a.val b.val := lt_of_le_of_ne hh.2 (Ne.symm hn)
  obtain ⟨w,haw,hbw,ha,hb⟩ := lower_witness hh.1 n hlt
  exact hJ _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hlo ⟨haw,ha⟩,hlo ⟨hbw,hb⟩⟩)

def root (i : Fin 3) : Vertex := ⟨leaf i,trivial⟩

lemma root_adj {i j : Fin 3} (h : i ≠ j) : G.Adj (root i) (root j) :=
  Or.inl ⟨i,j,rfl,rfl,h⟩

lemma root_not_piece (i j : Fin 3) (n : ℕ) : ¬(piece n).Adj (root i) (root j) := by
  intro h
  exact WithTop.top_ne_coe h.2

/-- All three edges of the original triangle survive EVERY finite stage. -/
theorem remaining_triangle (n : ℕ) : ¬(remaining n).CliqueFree 3 := by
  intro h
  apply h _
  exact SimpleGraph.is3Clique_triple_iff.mpr
    ⟨⟨root_adj (by decide : (0 : Fin 3) ≠ 1),le_top⟩,
      ⟨root_adj (by decide : (0 : Fin 3) ≠ 2),le_top⟩,
      ⟨root_adj (by decide : (1 : Fin 3) ≠ 2),le_top⟩⟩

/-- Consequently their countable supremum is not G, despite maximality at
all stages and countable three-colorability of the original graph. -/
theorem not_cover : G ≠ ⨆ n, piece n := by
  intro h
  have hh := root_adj (by decide : (0 : Fin 3) ≠ 1)
  rw [h,SimpleGraph.iSup_adj] at hh
  obtain ⟨n,hn⟩ := hh
  exact root_not_piece 0 1 n hn

/-- The actual residual graph after the union of all removed layers still
contains a triangle, not merely one leftover edge. -/
theorem residual_triangle : ¬(G \ ⨆ n, piece n).CliqueFree 3 := by
  intro h
  have hadj {i j : Fin 3} (hij : i ≠ j) :
      (G \ ⨆ n, piece n).Adj (root i) (root j) := by
    rw [SimpleGraph.sdiff_adj,SimpleGraph.iSup_adj]
    exact ⟨root_adj hij,fun ⟨n,hn⟩ => root_not_piece i j n hn⟩
  exact h _ (SimpleGraph.is3Clique_triple_iff.mpr
    ⟨hadj (by decide : (0 : Fin 3) ≠ 1),hadj (by decide : (0 : Fin 3) ≠ 2),
      hadj (by decide : (1 : Fin 3) ≠ 2)⟩)

#print axioms remaining_succ
#print axioms residual_triangle
example : Countable Vertex := inferInstance
#print axioms cliqueFree
#print axioms piece_triangleFree
#print axioms piece_maximal
#print axioms not_cover
end Erdos595MaximalDecompositionFailure
