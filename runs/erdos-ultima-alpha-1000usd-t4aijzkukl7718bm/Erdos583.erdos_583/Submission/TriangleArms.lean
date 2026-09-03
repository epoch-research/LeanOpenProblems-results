import Submission.ButterflyRestoration

/-! Splitting a triangle and a path into two rooted arms, with a controlled avoided vertex. -/
namespace Erdos583TriangleArmsDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma triangle_arms_at_split {V : Type*} {G : SimpleGraph V} {r x y a b : V}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (A : G.Walk a x) (B : G.Walk x b) (hP : (A.append B).IsPath)
    (hr : r ∉ (A.append B).support) (hyA : y ∉ A.support) :
    ∃ X : G.Walk r a, ∃ Y : G.Walk r b,
      X.IsPath ∧ Y.IsPath ∧
      X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=
        (A.append B).toSubgraph.edgeSet ∪ {s(r,x),s(x,y),s(r,y)} ∧
      X.length+Y.length=(A.append B).length+3 ∧
      (∀ t, t ∈ X.support ↔ t=r ∨ t=y ∨ t ∈ A.support) ∧
      (∀ t, t ∈ Y.support ↔ t=r ∨ t ∈ B.support) := by
  let X := Walk.cons hry (Walk.cons hxy.symm A.reverse)
  let Y := Walk.cons hrx B
  have hrA : r ∉ A.support := fun hh ↦ hr ((Walk.mem_support_append_iff A B).mpr (Or.inl hh))
  have hrB : r ∉ B.support := fun hh ↦ hr ((Walk.mem_support_append_iff A B).mpr (Or.inr hh))
  have hX : X.IsPath := by
    simp only [X,Walk.cons_isPath_iff,Walk.support_cons,Walk.support_reverse,List.mem_reverse,List.mem_cons,not_or]
    exact ⟨⟨hP.of_append_left.reverse,hyA⟩,hry.ne,hrA⟩
  have hY : Y.IsPath := (Walk.cons_isPath_iff hrx B).mpr ⟨hP.of_append_right,hrB⟩
  refine ⟨X,Y,hX,hY,?_,?_,?_,?_⟩
  · ext e
    simp only [X,Y,Set.mem_union,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_reverse,
      Walk.edges_append,List.mem_cons,List.mem_reverse,List.mem_append,Set.mem_insert_iff,
      Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := x)]
    tauto
  · simp only [X,Y,Walk.length_cons,Walk.length_reverse,Walk.length_append]; omega
  · intro t; simp only [X,Walk.support_cons,Walk.support_reverse,List.mem_cons,List.mem_reverse]
  · intro t; simp only [Y,Walk.support_cons,List.mem_cons]

/-- The first arm avoids z; the second avoids the extra triangle tip y whenever
that tip was not on the old path. Endpoints may be exchanged. -/
def ControlledArms {V : Type*} {G : SimpleGraph V} {a b : V}
    (P : G.Walk a b) (r x y z : V) : Prop :=
  ∃ u v, ∃ X : G.Walk r u, ∃ Y : G.Walk r v,
    X.IsPath ∧ Y.IsPath ∧
    X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=P.toSubgraph.edgeSet ∪ {s(r,x),s(x,y),s(r,y)} ∧
    X.length+Y.length=P.length+3 ∧
    (∀ t, t ∈ X.support ∨ t ∈ Y.support → t=r ∨ t=y ∨ t ∈ P.support) ∧
    z ∉ X.support ∧ (y ∉ P.support → y ∉ Y.support)

lemma triangle_arms_first_side {V : Type*} {G : SimpleGraph V} {r x y z a b : V}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (A : G.Walk a x) (B : G.Walk x b) (hP : (A.append B).IsPath)
    (hr : r ∉ (A.append B).support) (hzr : z ≠ r) (hzy : z ≠ y)
    (hzA : z ∉ A.support) : ControlledArms (A.append B) r x y z := by
  classical
  by_cases hyA : y ∈ A.support
  · have hyB : y ∉ B.support := fun hh ↦
      hP.ne_of_mem_support_of_append hxy.ne.symm hyA hh rfl
    have hrev : (B.reverse.append A.reverse).IsPath := by
      simpa only [Walk.reverse_append] using hP.reverse
    have hrrev : r ∉ (B.reverse.append A.reverse).support := by
      simpa only [←Walk.reverse_append,Walk.support_reverse,List.mem_reverse] using hr
    obtain ⟨X,Y,hX,hY,he,hl,hXs,hYs⟩ := triangle_arms_at_split hrx hxy hry B.reverse A.reverse hrev
      hrrev (by simpa using hyB)
    refine ⟨a,b,Y,X,hY,hX,?_,?_,?_,?_,?_⟩
    · rw [Set.union_comm]
      simpa only [←Walk.reverse_append,Walk.edgeSet_toSubgraph,Walk.edges_reverse,List.mem_reverse] using he
    · simp only [←Walk.reverse_append,Walk.length_reverse] at hl
      omega
    · intro t ht
      rcases ht with ht | ht
      · rcases (hYs t).mp ht with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr ((Walk.mem_support_append_iff A B).mpr (Or.inl (by simpa using h))))
      · rcases (hXs t).mp ht with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ((Walk.mem_support_append_iff A B).mpr (Or.inr (by simpa using h))))
    · intro hz
      rcases (hYs z).mp hz with h | h
      · exact hzr h
      · exact hzA (by simpa using h)
    · intro hn
      exact (hn ((Walk.mem_support_append_iff A B).mpr (Or.inl hyA))).elim
  · obtain ⟨X,Y,hX,hY,he,hl,hXs,hYs⟩ := triangle_arms_at_split hrx hxy hry A B hP hr hyA
    refine ⟨a,b,X,Y,hX,hY,he,hl,?_,?_,?_⟩
    · intro t ht
      rcases ht with ht | ht
      · rcases (hXs t).mp ht with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ((Walk.mem_support_append_iff A B).mpr (Or.inl h)))
      · rcases (hYs t).mp ht with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr ((Walk.mem_support_append_iff A B).mpr (Or.inr h)))
    · intro hz
      rcases (hXs z).mp hz with h | h | h
      · exact hzr h
      · exact hzy h
      · exact hzA h
    · intro hn hy
      rcases (hYs y).mp hy with h | h
      · exact hry.ne h.symm
      · exact hn ((Walk.mem_support_append_iff A B).mpr (Or.inr h))

lemma triangle_arms_avoiding {V : Type*} {G : SimpleGraph V} {r x y z a b : V}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (P : G.Walk a b) (hP : P.IsPath) (hr : r ∉ P.support) (hx : x ∈ P.support)
    (hzr : z ≠ r) (hzx : z ≠ x) (hzy : z ≠ y) : ControlledArms P r x y z := by
  classical
  obtain ⟨A,B,_,_,hform⟩ := hP.mem_support_iff_exists_append.mp hx
  subst P
  by_cases hzA : z ∈ A.support
  · have hzB : z ∉ B.support := fun hh ↦ hP.ne_of_mem_support_of_append hzx hzA hh rfl
    have hrev : (B.reverse.append A.reverse).IsPath := by
      simpa only [Walk.reverse_append] using hP.reverse
    have hrrev : r ∉ (B.reverse.append A.reverse).support := by
      simpa only [←Walk.reverse_append,Walk.support_reverse,List.mem_reverse] using hr
    have hh := triangle_arms_first_side hrx hxy hry B.reverse A.reverse hrev hrrev hzr hzy
      (by simpa using hzB)
    simpa only [ControlledArms,←Walk.reverse_append,Walk.length_reverse,Walk.edgeSet_toSubgraph,
      Walk.edges_reverse,Walk.support_reverse,List.mem_reverse] using hh
  · exact triangle_arms_first_side hrx hxy hry A B hP hr hzr hzy hzA

end Erdos583TriangleArmsDevelopment
