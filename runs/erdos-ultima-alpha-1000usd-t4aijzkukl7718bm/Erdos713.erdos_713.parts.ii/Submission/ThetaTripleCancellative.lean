import FormalConjecturesUtil
import Submission.ThetaRigidRefinement
import Submission.ThetaPrivatePetals

/-! Oriented-theta exclusion for a simple triple system is precisely the
cancellation law for unions of its triples. This gives a representation
of rigid linear triple refinements, not the missing density estimate. -/
open Finset
open scoped Classical
namespace Erdos713ThetaTripleCancellative
open Erdos713ThetaGram Erdos713ThetaHeavyShadow Erdos713ThetaPrivatePetals
open Erdos713ThetaRigidRefinement
variable {A B I : Type*}
set_option maxHeartbeats 2000000

def Cancellative [Fintype B] (R : A → B → Prop) : Prop :=
  ∀ a b c, row R a ∪ row R b = row R a ∪ row R c → b = c

lemma refinement_tripleUnique {R : A → B → Prop} {Q : I → B → Prop} (f : I → A)
    (hsub : ∀ i x, Q i x → R (f i) x) (hlin : FiberLinear f Q)
    (hrigid : TripleUnique R) : TripleUnique Q := by
  intro i j x y z hxy hxz hyz hix hiy hiz hjx hjy hjz
  have he := hrigid (f i) (f j) x y z hxy hxz hyz
    (hsub _ _ hix) (hsub _ _ hiy) (hsub _ _ hiz)
    (hsub _ _ hjx) (hsub _ _ hjy) (hsub _ _ hjz)
  exact hlin i j x y he hxy hix hiy hjx hjy

lemma row_injective_of_triples [Fintype B] {R : A → B → Prop}
    (hrigid : TripleUnique R) (hthree : ∀ a, (row R a).card = 3) :
    Function.Injective (row R) := by
  intro a b he
  have hh : (row R a ∩ row R b).card = 3 := by rw [he,inter_self,hthree]
  have hn : 2 < (row R a ∩ row R b).card := by omega
  obtain ⟨s,hs,hsc⟩ := exists_subset_card_eq (show 3 ≤ (row R a ∩ row R b).card by omega)
  obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := card_eq_three.mp hsc
  have hx := hs (show x ∈ ({x,y,z} : Finset B) by simp)
  have hy := hs (show y ∈ ({x,y,z} : Finset B) by simp)
  have hz := hs (show z ∈ ({x,y,z} : Finset B) by simp)
  simp only [mem_inter,mem_row] at hx hy hz
  exact hrigid a b x y z hxy hxz hyz hx.1 hy.1 hz.1 hx.2 hy.2 hz.2

/-- Distinct triples with the same union with a third triple give theta. -/
theorem cancellative_of_no_theta [Fintype B] {R : A → B → Prop}
    (hthree : ∀ a, (row R a).card = 3) (hinj : Function.Injective (row R))
    (hf : ¬ HasTheta R) : Cancellative R := by
  intro a b c he
  by_contra hbc
  have hsets : row R b ≠ row R c := fun hh => hbc (hinj hh)
  have hsub : (row R b \ row R c) ∪ (row R c \ row R b) ⊆ row R a := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · have hu : x ∈ row R a ∪ row R c := he ▸ mem_union_right _ (mem_sdiff.mp hx).1
      exact (mem_union.mp hu).resolve_right (mem_sdiff.mp hx).2
    · have hu : x ∈ row R a ∪ row R b := he.symm ▸ mem_union_right _ (mem_sdiff.mp hx).1
      exact (mem_union.mp hu).resolve_right (mem_sdiff.mp hx).2
  have hd : Disjoint (row R b \ row R c) (row R c \ row R b) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).1
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint hd,hthree] at hcard
  have hb := card_sdiff_add_card_inter (row R b) (row R c)
  have hc := card_sdiff_add_card_inter (row R c) (row R b)
  rw [hthree] at hb hc
  rw [inter_comm (row R c)] at hc
  have hbig : 1 < (row R b ∩ row R c).card := by omega
  obtain ⟨z,hz,w,hw,hzw⟩ := one_lt_card.mp hbig
  have hbcsub : ¬ row R b ⊆ row R c := by
    intro hs
    exact hsets (eq_of_subset_of_card_le hs (by rw [hthree,hthree]))
  have hcbsub : ¬ row R c ⊆ row R b := by
    intro hs
    exact hsets (eq_of_subset_of_card_le hs (by rw [hthree,hthree])).symm
  obtain ⟨x,hxb,hxc⟩ := not_subset.mp hbcsub
  obtain ⟨y,hyc,hyb⟩ := not_subset.mp hcbsub
  have hxa := hsub (mem_union_left _ (mem_sdiff.mpr ⟨hxb,hxc⟩))
  have hya := hsub (mem_union_right _ (mem_sdiff.mpr ⟨hyc,hyb⟩))
  have hab : a ≠ b := by intro hh; exact hyb (hh ▸ hya)
  have hac : a ≠ c := by intro hh; exact hxc (hh ▸ hxa)
  have hxz : x ≠ z := by intro hh; exact hxc (hh ▸ (mem_inter.mp hz).2)
  have hxw : x ≠ w := by intro hh; exact hxc (hh ▸ (mem_inter.mp hw).2)
  have hyz : y ≠ z := by intro hh; exact hyb (hh ▸ (mem_inter.mp hz).1)
  have hyw : y ≠ w := by intro hh; exact hyb (hh ▸ (mem_inter.mp hw).1)
  have hxy : x ≠ y := by intro hh; exact hyb (hh ▸ hxb)
  simp only [mem_inter,mem_row] at hz hw hxb hyc hxa hya
  exact hf (theta_of_rows hbc hab hac hzw hxz hxw hyz hyw hxy
    hz.1 hw.1 hz.2 hw.2 hxb hyc hxa hya)

/-- Conversely, the two branch triples of a theta differ only in their
petals, which are both contained in the closing triple. -/
theorem no_theta_of_cancellative [Fintype B] {R : A → B → Prop}
    (hthree : ∀ a, (row R a).card = 3) (hc : Cancellative R) : ¬ HasTheta R := by
  rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hne {i j : Fin 4} (h : i ≠ j) : b i ≠ b j := fun he => h (hb he)
  have hrow (i : Fin 3) (j : Fin 4) (hj0 : j ≠ 0) (hj1 : j ≠ 1)
      (h0 : R (a i) (b 0)) (h1 : R (a i) (b 1)) (hj : R (a i) (b j)) :
      row R (a i) = {b 0,b 1,b j} := by
    have hs : ({b 0,b 1,b j} : Finset B) ⊆ row R (a i) := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simpa only [mem_row] using (by assumption)
    exact (eq_of_subset_of_card_le hs (by
      rw [hthree]
      simp [hne (by decide : (0 : Fin 4) ≠ 1),
        Ne.symm (hne hj0),Ne.symm (hne hj1)])).symm
  have h0 := hrow 0 2 (by decide) (by decide) h00 h01 h02
  have h1 := hrow 1 3 (by decide) (by decide) h10 h11 h13
  have hu : row R (a 2) ∪ row R (a 0) = row R (a 2) ∪ row R (a 1) := by
    ext x
    rw [h0,h1]
    simp only [mem_union,mem_insert,mem_singleton,mem_row]
    have hx2 : x = b 2 → R (a 2) x := fun hh => hh ▸ h22
    have hx3 : x = b 3 → R (a 2) x := fun hh => hh ▸ h23
    tauto
  exact (by decide : (0 : Fin 3) ≠ 1) (ha (hc _ _ _ hu))

theorem no_theta_iff_cancellative [Fintype B] {R : A → B → Prop}
    (hthree : ∀ a, (row R a).card = 3) (hinj : Function.Injective (row R)) :
    ¬ HasTheta R ↔ Cancellative R :=
  ⟨cancellative_of_no_theta hthree hinj,no_theta_of_cancellative hthree⟩

/-- A linear pair-covering triple refinement of a rigid theta-free relation
is a simple cancellative triple system. No bound on its row count is hidden. -/
theorem refinement_cancellative [Fintype B]
    {R : A → B → Prop} {Q : I → B → Prop} (f : I → A)
    (hsub : ∀ i x, Q i x → R (f i) x) (hlin : FiberLinear f Q)
    (hrigid : TripleUnique R) (hf : ¬ HasTheta R) (hthree : ∀ i, (row Q i).card = 3) :
    Function.Injective (row Q) ∧ Cancellative Q := by
  have hi := row_injective_of_triples (refinement_tripleUnique f hsub hlin hrigid) hthree
  exact ⟨hi,cancellative_of_no_theta hthree hi (no_theta_of_refinement f hsub hlin hrigid hf)⟩

#print axioms cancellative_of_no_theta
#print axioms no_theta_of_cancellative
#print axioms no_theta_iff_cancellative
#print axioms refinement_cancellative
end Erdos713ThetaTripleCancellative
