import Submission.PrivateShellPressure

/-!
Joint resource accounting for all prime-adic shells around one private point.
An eligible class can serve only one coordinate and one shell depth. This
supplies weighted necessary inequalities, not a resolution of Erdős 7.
-/
namespace Erdos7JointPrivateShellPressure
open scoped BigOperators
open Erdos7PrivateShellPressure
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

section Unique
variable {P I : Type*} (p : P → ℕ) (e d : P → I → ℕ) (a : I → ℤ) (x : ℤ)

/-- For distinct prime coordinates, the entire second coordinate is included
in the cofactor of the first. This is the only cross-coordinate premise. -/
def CrossCofactors : Prop := ∀ q r, q ≠ r → ∀ j, p r ^ e r j ∣ d q j

lemma different_coordinates (hcross : CrossCofactors p e d)
    (q r : P) (hqr : q ≠ r) (s t : ℕ) (j : I) :
    ¬ (Eligible (p q) s (e q) (d q) a x j ∧ Eligible (p r) t (e r) (d r) a x j) := by
  rintro ⟨hq,hr⟩
  have ht : t+1 ≤ e r j := by have := hr.1; omega
  have hd : p r ^ (t+1) ∣ d q j :=
    (pow_dvd_pow (p r) ht).trans (hcross q r hqr j)
  have hd' : ((p r ^ (t+1) : ℕ) : ℤ) ∣ (d q j : ℤ) := by exact_mod_cast hd
  exact hr.2.2.2 (hd'.trans hq.2.1)

abbrev Slot (i : I) := Σ q : P, Fin (e q i)

def SlotEligible (i : I) (s : Slot e i) (j : I) : Prop :=
  Eligible (p s.1) s.2.val (e s.1) (d s.1) a x j

lemma eligible_slot_unique (hcross : CrossCofactors p e d) (i j : I)
    (s t : Slot e i) (hs : SlotEligible p e d a x i s j)
    (ht : SlotEligible p e d a x i t j) : s=t := by
  rcases s with ⟨q,s⟩
  rcases t with ⟨r,t⟩
  by_cases hqr : q=r
  · subst r
    have hv : s.val=t.val := by
      have hn₁ : ¬ s.val < t.val := fun h =>
        eligible_disjoint_depths (p q) (e q) (d q) a x s.val t.val h j ⟨hs,ht⟩
      have hn₂ : ¬ t.val < s.val := fun h =>
        eligible_disjoint_depths (p q) (e q) (d q) a x t.val s.val h j ⟨ht,hs⟩
      omega
    congr 1
    exact Fin.ext hv
  · exact (different_coordinates p e d a x hcross q r hqr _ _ j ⟨hs,ht⟩).elim
end Unique

section Packing
variable {S I : Type*} [Fintype S] [Fintype I]

/-- A label cannot be spent on two different demands. Nonnegativity of B is
needed even for a label eligible nowhere. The costs themselves may be signed. -/
theorem unique_resource_bound (A : S → I → Prop) (c : S → I → ℚ) (B : I → ℚ)
    (hunique : ∀ j s t, A s j → A t j → s=t)
    (hB : ∀ j, 0 ≤ B j) (hc : ∀ s j, A s j → c s j ≤ B j) :
    (∑ s, ∑ j, if A s j then c s j else 0) ≤ ∑ j, B j := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  by_cases hex : ∃ s, A s j
  · obtain ⟨s,hs⟩ := hex
    calc
      (∑ t, if A t j then c t j else 0) = c s j := by
        rw [Finset.sum_eq_single s]
        · simp only [if_pos hs]
        · intro t _ hts
          exact if_neg (fun ht => hts (hunique j t s ht hs))
        · simp
      _ ≤ B j := hc s j hs
  · have hn : ∀ s, ¬ A s j := fun s hs => hex ⟨s,hs⟩
    simpa only [if_neg (hn _),Finset.sum_const_zero] using hB j

/-- Weighted joint pressure from separate shell inequalities and a genuinely
shared per-class budget. It does not identify different classes or shells. -/
theorem weighted_joint_bound (A : S → I → Prop) (demand w : S → ℚ)
    (cost : S → I → ℚ) (B : I → ℚ)
    (hw : ∀ s, 0 ≤ w s)
    (hp : ∀ s, demand s ≤ ∑ j, if A s j then cost s j else 0)
    (hunique : ∀ j s t, A s j → A t j → s=t)
    (hB : ∀ j, 0 ≤ B j)
    (hcost : ∀ s j, A s j → w s * cost s j ≤ B j) :
    (∑ s, w s * demand s) ≤ ∑ j, B j := by
  classical
  calc
    (∑ s, w s*demand s) ≤ ∑ s, w s*(∑ j, if A s j then cost s j else 0) :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hp s) (hw s))
    _ = ∑ s, ∑ j, if A s j then w s*cost s j else 0 := by
      simp_rw [Finset.mul_sum,mul_ite,mul_zero]
    _ ≤ ∑ j, B j := unique_resource_bound A (fun s j => w s*cost s j) B hunique hB hcost
end Packing

section Arithmetic
variable {P I : Type*} [Fintype P] [Fintype I]

/-- All shell depths at all prime coordinates simultaneously require this
much distinct-class capacity. Each other class contributes at most one unit. -/
theorem joint_depth_pressure
    (p E M : P → ℕ) (hp : ∀ q, 2 ≤ p q)
    (e d : P → I → ℕ) (a : I → ℤ) (m : I → ℕ)
    (hfac : ∀ q j, m j=p q ^ e q j * d q j)
    (hcop : ∀ q, (p q ^ E q).Coprime (M q))
    (he : ∀ q j, e q j ≤ E q) (hd : ∀ q j, d q j ∣ M q)
    (hcross : CrossCofactors p e d)
    (hc : ∀ z : ℤ, ∃ j, (m j : ℤ) ∣ z-a j)
    (i : I) (x : ℤ) (hpriv : ∀ j, (m j : ℤ) ∣ x-a j ↔ j=i) :
    (∑ s : Slot e i, ((p s.1 : ℚ)-1)) ≤ (Fintype.card I : ℚ)-1 := by
  classical
  let A := SlotEligible p e d a x i
  let cost (s : Slot e i) (j : I) : ℚ :=
    ((p s.1 : ℚ)⁻¹)^(e s.1 j-s.2.val-1)
  let B (j : I) : ℚ := if j=i then 0 else 1
  have hpressure (s : Slot e i) : ((p s.1 : ℚ)-1) ≤
      ∑ j, if A s j then cost s j else 0 := by
    letI : NeZero (p s.1) := ⟨by have := hp s.1; omega⟩
    have hcf : ∀ z : ℤ, ∃ j, ((p s.1 ^ e s.1 j * d s.1 j : ℕ) : ℤ) ∣ z-a j := by
      intro z
      obtain ⟨j,hj⟩ := hc z
      exact ⟨j,by simpa only [← hfac s.1 j] using hj⟩
    have hpv : ∀ j, ((p s.1 ^ e s.1 j * d s.1 j : ℕ) : ℤ) ∣ x-a j ↔ j=i := by
      intro j
      simpa only [← hfac s.1 j] using hpriv j
    have H := shell_depth_pressure (p s.1) (E s.1) (M s.1) (hcop s.1)
      (e s.1) (d s.1) a (he s.1) (hd s.1) hcf i x hpv s.2.val s.2.isLt
    simpa only [A,SlotEligible,cost] using H
  have hcost (s : Slot e i) (j : I) (hj : A s j) : cost s j ≤ B j := by
    have hji : j ≠ i := by
      intro heq
      subst j
      exact eligible_not_private (p s.1) s.2.val (e s.1) (d s.1) a x i
        (by simpa only [← hfac s.1 i] using (hpriv i).mpr rfl) hj
    simp only [B,if_neg hji]
    have hq : (1 : ℚ) ≤ p s.1 := by exact_mod_cast (by have := hp s.1; omega : 1 ≤ p s.1)
    exact pow_le_one₀ (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq)
  have hb := unique_resource_bound A cost B
    (fun j s t hs ht => eligible_slot_unique p e d a x hcross i j s t hs ht)
    (fun j => by dsimp [B]; split_ifs <;> norm_num) hcost
  have hsum : (∑ j, B j) = (Fintype.card I : ℚ)-1 := by
    have hB (j : I) : B j=1-(if j=i then 1 else 0) := by
      dsimp [B]; split_ifs <;> norm_num
    simp_rw [hB]
    simp
  rw [hsum] at hb
  exact (Finset.sum_le_sum (fun s _ => hpressure s)).trans hb

end Arithmetic
#print axioms different_coordinates
#print axioms eligible_slot_unique
#print axioms unique_resource_bound
#print axioms weighted_joint_bound
#print axioms joint_depth_pressure
end Erdos7JointPrivateShellPressure
