import Submission.UnequalFullFibers
import Submission.FullResidueFiberBound

/-!
A uniform two-thirds ceiling for the nonuniform alteration expression from
individually Sidon full unit-residue fibers, even with arbitrary unequal
lengths. This is a ceiling for the certificate only, not for actual Sidon
subsets or arbitrary partial-fiber selections.
-/
namespace Erdos773.AllLengthFullFiberCeiling
open Finset PartialResidueFibers PartialFiberSelection MatchedResidueLifting UnequalFullFibers
set_option maxHeartbeats 3000000

lemma fiber_length_bound (q r H : ℕ) (hq : 0 < q) (hr : r < q)
    (hS : IsSidon (fiberValues q r (Icc 0 H) : Set ℕ)) : H < 15*q := by
  have he : (roots q H {r}).image (fun n => n^2)=fiberValues q r (Icc 0 H) := by
    ext a
    simp [roots,fiberValues]
  apply FullResidueFiberBound.full_fiber_length_bound q H {r} hq
    (fun s hs => by simpa only [mem_singleton.mp hs] using hr) (by simp)
  rw [he]
  exact hS

lemma cost_div_three (R : Finset ℕ) (V : ℕ → Finset ℕ) (p : ℕ → ℝ) :
    cost R V (fun r => p r/3)=cost R V p/81 := by
  unfold cost
  rw [sum_div]
  apply sum_congr rfl
  intro k hk
  ring

/-- No common-length bound is assumed. Individual Sidonness bounds every
full fiber's length; truncation and rescaled probabilities then reduce to the
unequal short-fiber result. -/
theorem expression_height_bound (q Hmax : ℕ) (R : Finset ℕ) (H : ℕ → ℕ)
    (hq : q.Prime) (hH : ∀ r ∈ R, H r ≤ Hmax)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R)
    (hS : ∀ r ∈ R, IsSidon (fiberValues q r (Icc 0 (H r)) : Set ℕ))
    (p : ℕ → ℝ) (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    (∑ r ∈ R, p r*((H r+1 : ℕ) : ℝ)) -
      cost R (fun r => fiberValues q r (Icc 0 (H r))) p ≤
        38880*((q*(Hmax+1) : ℕ) : ℝ)^(2/3 : ℝ) := by
  let H' := fun r => min (H r) q
  let V := fun r => fiberValues q r (Icc 0 (H r))
  let V' := fun r => fiberValues q r (Icc 0 (H' r))
  let M : ℝ := ∑ r ∈ R, p r*((H r+1 : ℕ) : ℝ)
  let M' : ℝ := ∑ r ∈ R, p r*((H' r+1 : ℕ) : ℝ)
  have hM' : 0 ≤ M' := sum_nonneg (fun r hr => mul_nonneg (hp r hr) (Nat.cast_nonneg _))
  have hsize (r : ℕ) (hr : r ∈ R) : H r+1 ≤ 15*(H' r+1) := by
    have hh := fiber_length_bound q r (H r) hq.pos (hR r hr) (hS r hr)
    dsimp [H']
    by_cases hle : H r ≤ q
    · rw [Nat.min_eq_left hle]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega
  have hm : M ≤ 15*M' := by
    dsimp [M,M']
    rw [mul_sum]
    apply sum_le_sum
    intro r hr
    have hh : ((H r+1 : ℕ) : ℝ) ≤ 15*((H' r+1 : ℕ) : ℝ) := by exact_mod_cast hsize r hr
    have hm := mul_le_mul_of_nonneg_left hh (hp r hr)
    nlinarith only [hm]
  have hc : cost R V' p ≤ cost R V p := by
    apply cost_mono p (Subset.refl R)
    intro r hr
    apply image_subset_image
    intro k hk
    have hh := (mem_Icc.mp hk).2
    exact mem_Icc.mpr ⟨Nat.zero_le _,hh.trans (Nat.min_le_left _ _)⟩
  have hsmall : ∀ r ∈ R, H' r ≤ min Hmax q := by
    intro r hr
    exact min_le_min (hH r hr) (Nat.le_refl q)
  have hp' : ∀ r ∈ R, 0 ≤ p r/3 := by intro r hr; exact div_nonneg (hp r hr) (by norm_num)
  have hp1' : ∀ r ∈ R, p r/3 ≤ 1 := by intro r hr; linarith only [hp1 r hr]
  have hh := UnequalFullFibers.expression_height_bound q (min Hmax q) R H' hq
    (Nat.min_le_right _ _) hsmall hR hunit hM (fun r => p r/3) hp' hp1'
  have hmass : (∑ r ∈ R, p r/3*((H' r+1 : ℕ) : ℝ))=M'/3 := by
    dsimp [M']
    rw [sum_div]
    apply sum_congr rfl
    intro r hr
    ring
  rw [hmass,cost_div_three] at hh
  change M'/3-cost R V' p/81 ≤ _ at hh
  have htop : ((q*(min Hmax q+1) : ℕ) : ℝ)^(2/3 : ℝ) ≤
      ((q*(Hmax+1) : ℕ) : ℝ)^(2/3 : ℝ) := by
    apply Real.rpow_le_rpow (Nat.cast_nonneg _)
    · exact_mod_cast Nat.mul_le_mul_left q (Nat.add_le_add_right (Nat.min_le_left Hmax q) 1)
    · norm_num
  change M-cost R V p ≤ _
  nlinarith only [hm,hc,hM',hh,htop]

/-- This is precisely the nonuniform overlap-cost expression on the actual
full value fibers, not a reformulation of the conjecture's maximum. -/
theorem actual_expression_height_bound (q Hmax : ℕ) (R : Finset ℕ) (H : ℕ → ℕ)
    (hq : q.Prime) (hH : ∀ r ∈ R, H r ≤ Hmax)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R)
    (hS : ∀ r ∈ R, IsSidon (fiberValues q r (Icc 0 (H r)) : Set ℕ))
    (p : ℕ → ℝ) (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    (∑ r ∈ R, p r*(fiberValues q r (Icc 0 (H r))).card) -
      cost R (fun r => fiberValues q r (Icc 0 (H r))) p ≤
        38880*((q*(Hmax+1) : ℕ) : ℝ)^(2/3 : ℝ) := by
  have hc (r : ℕ) : (fiberValues q r (Icc 0 (H r))).card=H r+1 := by
    rw [fiberValues,card_image_of_injective]
    · simp
    · intro a b he
      have hh := Nat.pow_left_injective (by decide : (2:ℕ) ≠ 0) he
      nlinarith only [hh,hq.pos]
  simp_rw [hc]
  exact expression_height_bound q Hmax R H hq hH hR hunit hM hS p hp hp1

lemma cost_eq_zero_of_compatible (R : Finset ℕ) (V : ℕ → Finset ℕ) (p : ℕ → ℝ)
    (hC : Compatible R V) : cost R V p=0 := by
  have he : crossKeys R V=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro k hk
    obtain ⟨hr,hD⟩ := mem_sigma.mp hk
    obtain ⟨hr,hlt⟩ := mem_filter.mp hr
    obtain ⟨hr,hs⟩ := mem_product.mp hr
    exact disjoint_left.mp (hC _ hr _ hs (ne_of_lt hlt)) (mem_inter.mp hD).1 (mem_inter.mp hD).2
  simp [cost,he]

/-- A genuine size ceiling for a Sidon union of full fibers under these
prime-modulus, unit, and matching hypotheses. It is NOT an upper bound for
arbitrary Sidon subsets of squares. -/
theorem sidon_full_union_card_bound (q Hmax : ℕ) (R : Finset ℕ) (H : ℕ → ℕ)
    (hq : q.Prime) (hH : ∀ r ∈ R, H r ≤ Hmax)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R)
    (hS : IsSidon ((R.biUnion (fun r => fiberValues q r (Icc 0 (H r)))) : Set ℕ)) :
    ((R.biUnion (fun r => fiberValues q r (Icc 0 (H r)))).card : ℝ) ≤
      38880*((q*(Hmax+1) : ℕ) : ℝ)^(2/3 : ℝ) := by
  have hs := (sidon_iff_compatible q R (fun r => fiberValues q r (Icc 0 (H r))) hM
    (fun r _ _ ha => fiberValues_residue q r (Icc 0 (H r)) ha)).mp hS
  have hh := actual_expression_height_bound q Hmax R H hq hH hR hunit hM hs.1
    (fun _ => 1) (by intros; norm_num) (by intros; norm_num)
  rw [cost_eq_zero_of_compatible _ _ _ hs.2] at hh
  simp only [one_mul,sub_zero] at hh
  have hcard : (R.biUnion (fun r => fiberValues q r (Icc 0 (H r)))).card =
      ∑ r ∈ R, (fiberValues q r (Icc 0 (H r))).card := by
    apply card_biUnion
    intro r hr s hs hne
    exact fibers_disjoint hM (fun r _ _ ha => fiberValues_residue q r (Icc 0 (H r)) ha) hr hs hne
  rw [hcard,Nat.cast_sum]
  exact hh

#print axioms fiber_length_bound
#print axioms expression_height_bound
#print axioms actual_expression_height_bound
#print axioms sidon_full_union_card_bound
end Erdos773.AllLengthFullFiberCeiling
