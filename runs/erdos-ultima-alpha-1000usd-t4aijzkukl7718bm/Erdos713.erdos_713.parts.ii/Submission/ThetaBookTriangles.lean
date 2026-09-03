import FormalConjecturesUtil
import Submission.ThetaRigidBookMass

/-! Triangles in the graph of double row intersections come from a single
anchor pair. This is a finite structural consequence of theta exclusion
and triple-intersection rigidity, not the missing density-gap theorem. -/
open Finset SimpleGraph
open scoped Classical
namespace Erdos713ThetaBookTriangles
open Erdos713ThetaGram Erdos713ThetaHeavyShadow Erdos713ThetaPrivatePetals
variable {A B : Type*} [Fintype B]
set_option maxHeartbeats 2000000

/-- If three distinct rows meet pairwise in two columns, all three
intersections coincide. -/
theorem intersection_triangle {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hrigid : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab2 : 2 ≤ (row R a ∩ row R b).card)
    (hac2 : 2 ≤ (row R a ∩ row R c).card)
    (hbc2 : 2 ≤ (row R b ∩ row R c).card) :
    row R a ∩ row R c = row R a ∩ row R b ∧
      row R b ∩ row R c = row R a ∩ row R b := by
  have habC : (row R a ∩ row R b).card = 2 := Nat.le_antisymm (hrigid a b hab) hab2
  have hacC : (row R a ∩ row R c).card = 2 := Nat.le_antisymm (hrigid a c hac) hac2
  have hbcC : (row R b ∩ row R c).card = 2 := Nat.le_antisymm (hrigid b c hbc) hbc2
  obtain ⟨z,w,hzw,he⟩ := card_eq_two.mp habC
  have hz : R a z ∧ R b z := by
    have hh : z ∈ row R a ∩ row R b := by rw [he]; simp
    simpa only [mem_inter,mem_row] using hh
  have hw : R a w ∧ R b w := by
    have hh : w ∈ row R a ∩ row R b := by rw [he]; simp
    simpa only [mem_inter,mem_row] using hh
  have hsub : row R a ∩ row R c ⊆ row R a ∩ row R b := by
    intro x hx
    have hax := (mem_row R a x).mp (mem_inter.mp hx).1
    have hcx := (mem_row R c x).mp (mem_inter.mp hx).2
    apply mem_inter.mpr
    refine ⟨(mem_inter.mp hx).1,?_⟩
    by_contra hxb
    have hxnot : ¬ R b x := by simpa only [mem_row] using hxb
    have hxz : x ≠ z := by intro hh; exact hxnot (hh ▸ hz.2)
    have hxw : x ≠ w := by intro hh; exact hxnot (hh ▸ hw.2)
    have hsub' : row R b ∩ row R c ⊆ row R a ∩ row R c := by
      intro y hy
      have hby := (mem_row R b y).mp (mem_inter.mp hy).1
      have hcy := (mem_row R c y).mp (mem_inter.mp hy).2
      apply mem_inter.mpr
      refine ⟨?_,(mem_inter.mp hy).2⟩
      by_contra hya
      have hynot : ¬ R a y := by simpa only [mem_row] using hya
      have hyz : y ≠ z := by intro hh; exact hynot (hh ▸ hz.1)
      have hyw : y ≠ w := by intro hh; exact hynot (hh ▸ hw.1)
      have hxy : x ≠ y := by intro hh; exact hxnot (hh ▸ hby)
      exact hf (theta_of_rows hab hac.symm hbc.symm hzw hxz hxw hyz hyw hxy
        hz.1 hw.1 hz.2 hw.2 hax hby hcx hcy)
    have heq : row R b ∩ row R c = row R a ∩ row R c :=
      eq_of_subset_of_card_le hsub' (by rw [hacC,hbcC])
    have hxb' : x ∈ row R b := (mem_inter.mp (heq.symm ▸ hx)).1
    exact hxb hxb'
  have hacEq : row R a ∩ row R c = row R a ∩ row R b :=
    eq_of_subset_of_card_le hsub (by rw [habC,hacC])
  refine ⟨hacEq,?_⟩
  have hh : row R a ∩ row R b ⊆ row R b ∩ row R c := by
    intro x hx
    exact mem_inter.mpr ⟨(mem_inter.mp hx).2,(mem_inter.mp (hacEq.symm ▸ hx)).2⟩
  exact (eq_of_subset_of_card_le hh (by rw [hbcC,habC])).symm

/-- The auxiliary graph joins distinct rows sharing two columns. -/
noncomputable def overlapGraph (R : A → B → Prop) : SimpleGraph A where
  Adj a b := a ≠ b ∧ 2 ≤ (row R a ∩ row R b).card
  symm := by intro a b h; exact ⟨h.1.symm,by simpa only [inter_comm] using h.2⟩
  loopless := by intro a h; exact h.1 rfl

/-- Common neighbours of an edge form a clique: there is no induced
four-vertex diamond in this auxiliary graph. -/
theorem common_neighbors_adj {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hrigid : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    {a b c d : A} (hab : (overlapGraph R).Adj a b)
    (hac : (overlapGraph R).Adj a c) (hbc : (overlapGraph R).Adj b c)
    (had : (overlapGraph R).Adj a d) (hbd : (overlapGraph R).Adj b d)
    (hcd : c ≠ d) : (overlapGraph R).Adj c d := by
  have hc := intersection_triangle hf hrigid hab.1 hac.1 hbc.1 hab.2 hac.2 hbc.2
  have hd := intersection_triangle hf hrigid hab.1 had.1 hbd.1 hab.2 had.2 hbd.2
  refine ⟨hcd,hab.2.trans (card_le_card ?_)⟩
  intro x hx
  exact mem_inter.mpr ⟨(mem_inter.mp (hc.1.symm ▸ hx)).2,
    (mem_inter.mp (hd.1.symm ▸ hx)).2⟩

/-- An adjacent triple has a unique unordered two-column anchor. -/
theorem triangle_anchor {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hrigid : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    {a b c : A} (hab : (overlapGraph R).Adj a b)
    (hac : (overlapGraph R).Adj a c) (hbc : (overlapGraph R).Adj b c) :
    ∃! P : Finset B, P.card = 2 ∧ P ⊆ row R a ∧ P ⊆ row R b ∧ P ⊆ row R c := by
  have hc := intersection_triangle hf hrigid hab.1 hac.1 hbc.1 hab.2 hac.2 hbc.2
  have hcard : (row R a ∩ row R b).card = 2 := Nat.le_antisymm (hrigid a b hab.1) hab.2
  refine ⟨row R a ∩ row R b,⟨hcard,inter_subset_left,inter_subset_right,?_⟩,?_⟩
  · rw [← hc.1]
    exact inter_subset_right
  · intro Q hQ
    exact eq_of_subset_of_card_le (subset_inter hQ.2.1 hQ.2.2.1) (by rw [hcard,hQ.1])

#print axioms intersection_triangle
#print axioms common_neighbors_adj
#print axioms triangle_anchor
end Erdos713ThetaBookTriangles
