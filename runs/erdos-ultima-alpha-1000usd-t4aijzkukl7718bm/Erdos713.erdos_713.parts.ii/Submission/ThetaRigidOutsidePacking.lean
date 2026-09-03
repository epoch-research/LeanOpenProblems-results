import FormalConjecturesUtil
import Submission.ThetaBookTriangles

/-! Under triple-intersection rigidity, outside petals at a fixed row are
fully disjoint, not merely bounded in multiplicity. The bound remains a
fixed-root bound and does not remove global degree weights. -/
open Finset SimpleGraph
open scoped Classical
namespace Erdos713ThetaRigidOutsidePacking
open Erdos713ThetaGram Erdos713ThetaHeavyShadow Erdos713ThetaPrivatePetals
open Erdos713ThetaBookTriangles
variable {A B : Type*} [Fintype B]
set_option maxHeartbeats 2000000

theorem outside_unique {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hrigid : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    {a b c : A} {x : B} (hbx : ¬ R b x) (hax : R a x) (hcx : R c x)
    (hab2 : 2 ≤ (row R a ∩ row R b).card)
    (hcb2 : 2 ≤ (row R c ∩ row R b).card) : a = c := by
  by_contra hac
  have hab : a ≠ b := by intro he; exact hbx (he ▸ hax)
  have hcb : c ≠ b := by intro he; exact hbx (he ▸ hcx)
  have habC : (row R a ∩ row R b).card = 2 := Nat.le_antisymm (hrigid a b hab) hab2
  have hcbC : (row R c ∩ row R b).card = 2 := Nat.le_antisymm (hrigid c b hcb) hcb2
  obtain ⟨z,w,hzw,he⟩ := card_eq_two.mp habC
  have hz : R a z ∧ R b z := by
    have hh : z ∈ row R a ∩ row R b := by rw [he]; simp
    simpa only [mem_inter,mem_row] using hh
  have hw : R a w ∧ R b w := by
    have hh : w ∈ row R a ∩ row R b := by rw [he]; simp
    simpa only [mem_inter,mem_row] using hh
  have hxz : x ≠ z := by intro hh; exact hbx (hh ▸ hz.2)
  have hxw : x ≠ w := by intro hh; exact hbx (hh ▸ hw.2)
  have hsub : row R c ∩ row R b ⊆ row R a ∩ row R b := by
    intro y hy
    have hcy := (mem_row R c y).mp (mem_inter.mp hy).1
    have hby := (mem_row R b y).mp (mem_inter.mp hy).2
    apply mem_inter.mpr
    refine ⟨?_,(mem_inter.mp hy).2⟩
    by_contra hya
    have hynot : ¬ R a y := by simpa only [mem_row] using hya
    have hyz : y ≠ z := by intro hh; exact hynot (hh ▸ hz.1)
    have hyw : y ≠ w := by intro hh; exact hynot (hh ▸ hw.1)
    have hxy : x ≠ y := by intro hh; exact hbx (hh ▸ hby)
    exact hf (theta_of_rows hab (fun he => hac he.symm) hcb hzw hxz hxw hyz hyw hxy
      hz.1 hw.1 hz.2 hw.2 hax hby hcx hcy)
  have heq : row R c ∩ row R b = row R a ∩ row R b :=
    eq_of_subset_of_card_le hsub (by rw [habC,hcbC])
  have hcz : R c z := by
    have hh : z ∈ row R c ∩ row R b := by rw [heq,he]; simp
    exact (mem_row R c z).mp (mem_inter.mp hh).1
  have hcw : R c w := by
    have hh : w ∈ row R c ∩ row R b := by rw [heq,he]; simp
    exact (mem_row R c w).mp (mem_inter.mp hh).1
  have hs : ({x,z,w} : Finset B) ⊆ row R a ∩ row R c := by
    intro y hy
    simp only [mem_insert,mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> simp [mem_row,hax,hcx,hz.1,hw.1,hcz,hcw]
  have hcard : ({x,z,w} : Finset B).card = 3 := by simp [hxz,hxw,hzw]
  have hle := (card_le_card hs).trans (hrigid a c hac)
  omega

/-- Private parts of distinct double-overlap neighbours of b are disjoint. -/
theorem petals_disjoint {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hrigid : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    {a b c : A} (hac : a ≠ c)
    (hab : (overlapGraph R).Adj a b) (hcb : (overlapGraph R).Adj c b) :
    Disjoint (row R a \ row R b) (row R c \ row R b) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact hac (outside_unique hf hrigid
    (by simpa only [mem_row] using (mem_sdiff.mp hx).2)
    ((mem_row R a x).mp (mem_sdiff.mp hx).1)
    ((mem_row R c x).mp (mem_sdiff.mp hy).1) hab.2 hcb.2)

/-- Exact private-petal packing at one row. No minimum degree is needed. -/
theorem outside_sum [Fintype A] {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hrigid : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2) (b : A) :
    (∑ a ∈ (overlapGraph R).neighborFinset b, ((row R a).card-2)) ≤
      Fintype.card B-(row R b).card := by
  let S := (overlapGraph R).neighborFinset b
  let P : A → Finset B := fun a => row R a \ row R b
  have hp : (S : Set A).PairwiseDisjoint P := by
    intro a ha c hc hac
    exact petals_disjoint hf hrigid hac
      ((overlapGraph R).adj_symm (((overlapGraph R).mem_neighborFinset b a).mp ha))
      ((overlapGraph R).adj_symm (((overlapGraph R).mem_neighborFinset b c).mp hc))
  have hcard (a : A) (ha : a ∈ S) : (P a).card = (row R a).card-2 := by
    have hadj := (overlapGraph R).adj_symm (((overlapGraph R).mem_neighborFinset b a).mp ha)
    have hh : (row R a ∩ row R b).card = 2 :=
      Nat.le_antisymm (hrigid a b hadj.1) hadj.2
    simp only [P,card_sdiff,inter_comm (row R b),hh]
  have hsub : S.biUnion P ⊆ univ \ row R b := by
    intro x hx
    obtain ⟨a,ha,hxa⟩ := mem_biUnion.mp hx
    exact mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp hxa).2⟩
  have hh := card_le_card hsub
  rw [card_biUnion hp] at hh
  simp only [card_sdiff_of_subset (subset_univ _),card_univ] at hh
  have he : (∑ a ∈ S, (P a).card) = ∑ a ∈ S, ((row R a).card-2) :=
    sum_congr rfl hcard
  rw [he] at hh
  exact hh

#print axioms outside_unique
#print axioms petals_disjoint
#print axioms outside_sum
end Erdos713ThetaRigidOutsidePacking
