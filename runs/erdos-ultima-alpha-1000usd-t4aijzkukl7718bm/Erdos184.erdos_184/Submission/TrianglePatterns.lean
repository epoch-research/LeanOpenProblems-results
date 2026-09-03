import Submission.TriangleContacts

/-! Exhaustive classification by the three pair-contact multiplicities, each one or two. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.TriangleContacts
open CycleSegments ThreeCycleKernels
set_option maxHeartbeats 1500000
set_option linter.unusedVariables false
lemma pattern_000 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 = p 0 1)
    (h1 : p 1 0 = p 1 1)
    (h2 : p 2 0 = p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![0,1,2] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 3 → V := ![p 0 0,p 1 0,p 2 0]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · rfl
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨0,rfl⟩
    · exact ⟨0,h0⟩
    · exact ⟨1,rfl⟩
    · exact ⟨1,h1⟩
    · exact ⟨2,rfl⟩
    · exact ⟨2,h2⟩
  have L : ContactLayout DoubleTriangle.sizes DoubleTriangle.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, DoubleTriangle.place 0 j = 0
        rw [hi]
        decide
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, DoubleTriangle.place 0 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, DoubleTriangle.place 0 j = 2
        rw [hi]
        decide
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, DoubleTriangle.place 1 j = 0
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, DoubleTriangle.place 1 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, DoubleTriangle.place 1 j = 2
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, DoubleTriangle.place 2 j = 0
        rw [hi]
        decide
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, DoubleTriangle.place 2 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, DoubleTriangle.place 2 j = 2
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply DoubleTriangle.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_000

lemma pattern_001 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 = p 0 1)
    (h1 : p 1 0 = p 1 1)
    (h2 : p 2 0 ≠ p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![1,2,0] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 4 → V := ![p 2 0,p 2 1,p 0 0,p 1 0]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 2 0 = p 2 1 at he
      exact (h2 he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 1 = p 2 0 at he
      exact (h2 he.symm).elim
    · rfl
    · change p 2 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · rfl
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨2,rfl⟩
    · exact ⟨2,h0⟩
    · exact ⟨3,rfl⟩
    · exact ⟨3,h1⟩
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
  have L : ContactLayout MatchedFour.sizes MatchedFour.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 0 j = 0
        rw [hi]
        decide
      · change p 2 1 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 0 j = 1
        rw [hi]
        decide
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 0 j = 2
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 0 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 0
        rw [hi]
        decide
      · change p 2 1 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 1
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 2
        rw [hi]
        decide
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 2 j = 0
        rw [hi]
        decide
      · change p 2 1 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 2 j = 1
        rw [hi]
        decide
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 2 j = 2
        rw [hi]
        decide
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 2 j = 3
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply MatchedFour.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_001

lemma pattern_010 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 = p 0 1)
    (h1 : p 1 0 ≠ p 1 1)
    (h2 : p 2 0 = p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![0,2,1] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 4 → V := ![p 1 0,p 1 1,p 0 0,p 2 0]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 1 0 = p 1 1 at he
      exact (h1 he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 1 = p 1 0 at he
      exact (h1 he.symm).elim
    · rfl
    · change p 1 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · rfl
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨2,rfl⟩
    · exact ⟨2,h0⟩
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨3,h2⟩
  have L : ContactLayout MatchedFour.sizes MatchedFour.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 0
        rw [hi]
        decide
      · change p 1 1 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 1
        rw [hi]
        decide
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 2
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 3
        rw [hi]
        decide
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 0
        rw [hi]
        decide
      · change p 1 1 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 1
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 2
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 1 j = 3
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 2 j = 0
        rw [hi]
        decide
      · change p 1 1 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 2 j = 1
        rw [hi]
        decide
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 2 j = 2
        rw [hi]
        decide
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 2 j = 3
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply MatchedFour.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_010

lemma pattern_011 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 = p 0 1)
    (h1 : p 1 0 ≠ p 1 1)
    (h2 : p 2 0 ≠ p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![2,0,1] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 5 → V := ![p 1 0,p 1 1,p 2 0,p 2 1,p 0 0]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 1 0 = p 1 1 at he
      exact (h1 he).elim
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 1 = p 1 0 at he
      exact (h1 he.symm).elim
    · rfl
    · change p 1 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 1 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · rfl
    · change p 2 0 = p 2 1 at he
      exact (h2 he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 1 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 1 = p 2 0 at he
      exact (h2 he.symm).elim
    · rfl
    · change p 2 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨4,rfl⟩
    · exact ⟨4,h0⟩
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
  have L : ContactLayout CompleteFive.sizes CompleteFive.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 0 j = 0
        rw [hi]
        decide
      · change p 1 1 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 0 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 0 j = 2
        rw [hi]
        decide
      · change p 2 1 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 0 j = 3
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 0 j = 4
        rw [hi]
        decide
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 0
        rw [hi]
        decide
      · change p 1 1 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 2
        rw [hi]
        decide
      · change p 2 1 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 3
        rw [hi]
        decide
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 4
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 2 j = 0
        rw [hi]
        decide
      · change p 1 1 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 2 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 2 j = 2
        rw [hi]
        decide
      · change p 2 1 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 2 j = 3
        rw [hi]
        decide
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 2 j = 4
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply CompleteFive.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_011

lemma pattern_100 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 ≠ p 0 1)
    (h1 : p 1 0 = p 1 1)
    (h2 : p 2 0 = p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![0,1,2] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 4 → V := ![p 0 0,p 0 1,p 1 0,p 2 0]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 0 0 = p 0 1 at he
      exact (h0 he).elim
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 1 = p 0 0 at he
      exact (h0 he.symm).elim
    · rfl
    · change p 0 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · rfl
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨2,h1⟩
    · exact ⟨3,rfl⟩
    · exact ⟨3,h2⟩
  have L : ContactLayout MatchedFour.sizes MatchedFour.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 2
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, MatchedFour.place 0 j = 3
        rw [hi]
        decide
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 1 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 1 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 1 j = 2
        rw [hi]
        decide
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, MatchedFour.place 1 j = 3
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 2 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 2 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 2 j = 2
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, MatchedFour.place 2 j = 3
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply MatchedFour.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_100

lemma pattern_101 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 ≠ p 0 1)
    (h1 : p 1 0 = p 1 1)
    (h2 : p 2 0 ≠ p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![1,0,2] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 5 → V := ![p 0 0,p 0 1,p 2 0,p 2 1,p 1 0]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 0 0 = p 0 1 at he
      exact (h0 he).elim
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 1 = p 0 0 at he
      exact (h0 he.symm).elim
    · rfl
    · change p 0 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 1 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · rfl
    · change p 2 0 = p 2 1 at he
      exact (h2 he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 1 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 1 = p 2 0 at he
      exact (h2 he.symm).elim
    · rfl
    · change p 2 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨4,rfl⟩
    · exact ⟨4,h1⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
  have L : ContactLayout CompleteFive.sizes CompleteFive.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 0 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 0 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 0 j = 2
        rw [hi]
        decide
      · change p 2 1 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 0 j = 3
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 0 j = 4
        rw [hi]
        decide
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 2
        rw [hi]
        decide
      · change p 2 1 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 3
        rw [hi]
        decide
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 1 j = 4
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 1
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 2
        rw [hi]
        decide
      · change p 2 1 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 3
        rw [hi]
        decide
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 4
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply CompleteFive.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_101

lemma pattern_110 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 ≠ p 0 1)
    (h1 : p 1 0 ≠ p 1 1)
    (h2 : p 2 0 = p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![0,1,2] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 5 → V := ![p 0 0,p 0 1,p 1 0,p 1 1,p 2 0]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 0 0 = p 0 1 at he
      exact (h0 he).elim
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 1 = p 0 0 at he
      exact (h0 he.symm).elim
    · rfl
    · change p 0 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 1 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · rfl
    · change p 1 0 = p 1 1 at he
      exact (h1 he).elim
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 1 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 1 = p 1 0 at he
      exact (h1 he.symm).elim
    · rfl
    · change p 1 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
    · exact ⟨4,h2⟩
  have L : ContactLayout CompleteFive.sizes CompleteFive.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 0 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 0 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 0 j = 2
        rw [hi]
        decide
      · change p 1 1 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 0 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, CompleteFive.place 0 j = 4
        rw [hi]
        decide
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 1 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 1 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 1 j = 2
        rw [hi]
        decide
      · change p 1 1 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 1 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, CompleteFive.place 1 j = 4
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 2
        rw [hi]
        decide
      · change p 1 1 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, CompleteFive.place 2 j = 4
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply CompleteFive.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_110

lemma pattern_111 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    (h0 : p 0 0 ≠ p 0 1)
    (h1 : p 1 0 ≠ p 1 1)
    (h2 : p 2 0 ≠ p 2 1)
    : Critical.number G ≤ 2 := by
  let perm : Fin 3 ≃ Fin 3 := Equiv.ofBijective ![0,1,2] (by decide)
  let C' : ∀ k, G.Walk (root (perm k)) (root (perm k)) := fun k => C (perm k)
  let vertex : Fin 6 → V := ![p 0 0,p 0 1,p 1 0,p 1 1,p 2 0,p 2 1]
  have hinj : Function.Injective vertex := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · change p 0 0 = p 0 1 at he
      exact (h0 he).elim
    · change p 0 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 1 = p 0 0 at he
      exact (h0 he.symm).elim
    · rfl
    · change p 0 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 1 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 1) he).elim
    · change p 0 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 0 1 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (0 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · rfl
    · change p 1 0 = p 1 1 at he
      exact (h1 he).elim
    · change p 1 0 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 0 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 1 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 0) he).elim
    · change p 1 1 = p 1 0 at he
      exact (h1 he.symm).elim
    · rfl
    · change p 1 1 = p 2 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 1 1 = p 2 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (1 : Fin 3) ≠ 2) he).elim
    · change p 2 0 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 0 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 0 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · rfl
    · change p 2 0 = p 2 1 at he
      exact (h2 he).elim
    · change p 2 1 = p 0 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 1 = p 0 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 0) he).elim
    · change p 2 1 = p 1 0 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 1 = p 1 1 at he
      exact (point_ne_of_group_ne root C p hi (by decide : (2 : Fin 3) ≠ 1) he).elim
    · change p 2 1 = p 2 0 at he
      exact (h2 he.symm).elim
    · rfl
  have hsur : ∀ g i, ∃ w, vertex w = p g i := by
    intro g i
    fin_cases g <;> fin_cases i
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
    · exact ⟨5,rfl⟩
  have L : ContactLayout Octahedron.sizes Octahedron.place vertex (root ∘ perm) C' := by
    refine ⟨hinj,?_,?_⟩
    · intro k w
      fin_cases k <;> fin_cases w
      · change p 0 0 ∈ (C 0).support ↔ ∃ j, Octahedron.place 0 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 0).support ↔ ∃ j, Octahedron.place 0 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 0).support ↔ ∃ j, Octahedron.place 0 j = 2
        rw [hi]
        decide
      · change p 1 1 ∈ (C 0).support ↔ ∃ j, Octahedron.place 0 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 0).support ↔ ∃ j, Octahedron.place 0 j = 4
        rw [hi]
        decide
      · change p 2 1 ∈ (C 0).support ↔ ∃ j, Octahedron.place 0 j = 5
        rw [hi]
        decide
      · change p 0 0 ∈ (C 1).support ↔ ∃ j, Octahedron.place 1 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 1).support ↔ ∃ j, Octahedron.place 1 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 1).support ↔ ∃ j, Octahedron.place 1 j = 2
        rw [hi]
        decide
      · change p 1 1 ∈ (C 1).support ↔ ∃ j, Octahedron.place 1 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 1).support ↔ ∃ j, Octahedron.place 1 j = 4
        rw [hi]
        decide
      · change p 2 1 ∈ (C 1).support ↔ ∃ j, Octahedron.place 1 j = 5
        rw [hi]
        decide
      · change p 0 0 ∈ (C 2).support ↔ ∃ j, Octahedron.place 2 j = 0
        rw [hi]
        decide
      · change p 0 1 ∈ (C 2).support ↔ ∃ j, Octahedron.place 2 j = 1
        rw [hi]
        decide
      · change p 1 0 ∈ (C 2).support ↔ ∃ j, Octahedron.place 2 j = 2
        rw [hi]
        decide
      · change p 1 1 ∈ (C 2).support ↔ ∃ j, Octahedron.place 2 j = 3
        rw [hi]
        decide
      · change p 2 0 ∈ (C 2).support ↔ ∃ j, Octahedron.place 2 j = 4
        rw [hi]
        decide
      · change p 2 1 ∈ (C 2).support ↔ ∃ j, Octahedron.place 2 j = 5
        rw [hi]
        decide
    · intro k l hkl x hx hy
      obtain ⟨g,i,he⟩ := hm (perm k) (perm l) (fun h => hkl (perm.injective h)) x hx hy
      obtain ⟨w,hw⟩ := hsur g i
      exact ⟨w,hw.trans he⟩
  apply Octahedron.contact_number_le_two hrig heven vertex (root ∘ perm) C' (fun k => hC (perm k)) L
  · intro k l hkl
    exact hd (perm k) (perm l) (fun h => hkl (perm.injective h))
  · intro x y hxy
    obtain ⟨k,hk⟩ := hcover x y hxy
    obtain ⟨j,rfl⟩ := perm.surjective k
    exact ⟨j,hk⟩
#print axioms pattern_111

lemma patterns_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (hd : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges)
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    (hm : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x)
    : Critical.number G ≤ 2 := by
  by_cases h0 : p 0 0 = p 0 1
  · by_cases h1 : p 1 0 = p 1 1
    · by_cases h2 : p 2 0 = p 2 1
      · exact pattern_000 hrig heven root C hC hd hcover p hi hm h0 h1 h2
      · exact pattern_001 hrig heven root C hC hd hcover p hi hm h0 h1 h2
    · by_cases h2 : p 2 0 = p 2 1
      · exact pattern_010 hrig heven root C hC hd hcover p hi hm h0 h1 h2
      · exact pattern_011 hrig heven root C hC hd hcover p hi hm h0 h1 h2
  · by_cases h1 : p 1 0 = p 1 1
    · by_cases h2 : p 2 0 = p 2 1
      · exact pattern_100 hrig heven root C hC hd hcover p hi hm h0 h1 h2
      · exact pattern_101 hrig heven root C hC hd hcover p hi hm h0 h1 h2
    · by_cases h2 : p 2 0 = p 2 1
      · exact pattern_110 hrig heven root C hC hd hcover p hi hm h0 h1 h2
      · exact pattern_111 hrig heven root C hC hd hcover p hi hm h0 h1 h2
#print axioms patterns_bound
end Erdos184Work.TriangleContacts
