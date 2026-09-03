import Submission.ShortFullFiberWeightedCeiling

/-!
Nonuniform alteration certificates for full fibers of unequal lengths bounded
by q. Grouping lengths by powers of eight gives a uniform two-thirds ceiling
without a logarithmic loss. This does not bound the actual Sidon maximum or
arbitrary partial-fiber constructions.
-/
namespace Erdos773.UnequalFullFibers
open Finset PartialResidueFibers PartialFiberSelection MatchedResidueLifting
set_option maxHeartbeats 3000000

noncomputable def cost (R : Finset ℕ) (V : ℕ → Finset ℕ) (p : ℕ → ℝ) : ℝ :=
  ∑ k ∈ crossKeys R V, p k.1.1^2*p k.1.2^2

lemma cost_nonneg (R : Finset ℕ) (V : ℕ → Finset ℕ) (p : ℕ → ℝ) : 0 ≤ cost R V p :=
  sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

lemma cost_mono {R S : Finset ℕ} {V W : ℕ → Finset ℕ} (p : ℕ → ℝ)
    (hRS : R ⊆ S) (hVW : ∀ r ∈ R, V r ⊆ W r) : cost R V p ≤ cost S W p := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨hr,hD⟩ := mem_sigma.mp hk
    obtain ⟨hr,hlt⟩ := mem_filter.mp hr
    obtain ⟨hr,hs⟩ := mem_product.mp hr
    exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hRS hr,hRS hs⟩,hlt⟩,
      mem_inter.mpr ⟨differences_mono (hVW _ hr) (mem_inter.mp hD).1,
        differences_mono (hVW _ hs) (mem_inter.mp hD).2⟩⟩
  · intro k _ _
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

lemma cost_partition_le (R I : Finset ℕ) (V : ℕ → Finset ℕ) (p : ℕ → ℝ) (b : ℕ → ℕ) :
    (∑ j ∈ I, cost (R.filter (fun r => b r=j)) V p) ≤ cost R V p := by
  classical
  let K (j : ℕ) := crossKeys (R.filter (fun r => b r=j)) V
  have hd : (I : Set ℕ).PairwiseDisjoint K := by
    intro j hj k hk hjk
    apply disjoint_left.mpr
    intro e he he'
    have hr := (mem_product.mp (mem_filter.mp (mem_sigma.mp he).1).1).1
    have hr' := (mem_product.mp (mem_filter.mp (mem_sigma.mp he').1).1).1
    exact hjk ((mem_filter.mp hr).2.symm.trans (mem_filter.mp hr').2)
  have hsub : I.biUnion K ⊆ crossKeys R V := by
    intro k hk
    obtain ⟨j,hj,hk⟩ := mem_biUnion.mp hk
    exact WeightedPartialFibers.crossKeys_mono (filter_subset _ _) V hk
  have hh := sum_le_sum_of_subset_of_nonneg
    (f := fun k : Σ _ : ℕ × ℕ, ℕ => p k.1.1^2*p k.1.2^2) hsub
    (fun _ _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [sum_biUnion hd] at hh
  exact hh

lemma pairMatching_subset {q : ℕ} {R S : Finset ℕ} (hM : PairMatching q R) (hS : S ⊆ R) :
    PairMatching q S := by
  intro r hr s hs t ht u hu he
  exact hM r (hS hr) s (hS hs) t (hS ht) u (hS hu) he

/-- A length bin, measured by the number H(r)+1 of root indices. -/
def bin (R : Finset ℕ) (H : ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  R.filter (fun r => Nat.log 8 (H r+1)=j)

lemma bin_length {R : Finset ℕ} {H : ℕ → ℕ} {j r : ℕ} (hr : r ∈ bin R H j) :
    8^j ≤ H r+1 ∧ H r+1 < 8^(j+1) := by
  have he := (mem_filter.mp hr).2
  have hlo := Nat.pow_log_le_self 8 (show H r+1 ≠ 0 by omega)
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < (8:ℕ)) (H r+1)
  rw [he] at hlo hhi
  exact ⟨hlo,hhi⟩

lemma octadic_rpow (q j : ℕ) :
    ((q*8^j : ℕ) : ℝ)^(2/3 : ℝ)=(q : ℝ)^(2/3 : ℝ)*4^j := by
  have h8 : (8:ℝ)^(2/3 : ℝ)=4 := by norm_num
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg _) (by positivity)]
  have hh : ((8:ℝ)^j)^(2/3 : ℝ)=4^j := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm (j : ℝ),Real.rpow_mul_natCast (by norm_num),h8]
  rw [hh]

lemma geometric_four_bound (J : ℕ) : (∑ j ∈ range (J+1), (4:ℝ)^j) ≤ (3/2)*4^J := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [sum_range_succ,pow_succ]
    have hh : 0 ≤ (4:ℝ)^J := by positivity
    nlinarith only [ih,hh]

/-- All full fibers have lengths at most q and at most the claimed Hmax.
Only the certificate is bounded; the actual Sidon maximum can be larger. -/
theorem expression_height_bound (q Hmax : ℕ) (R : Finset ℕ) (H : ℕ → ℕ)
    (hq : q.Prime) (hmaxq : Hmax ≤ q) (hH : ∀ r ∈ R, H r ≤ Hmax)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R) (p : ℕ → ℝ)
    (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    (∑ r ∈ R, p r*((H r+1 : ℕ) : ℝ)) -
      cost R (fun r => fiberValues q r (Icc 0 (H r))) p ≤
        480*((q*(Hmax+1) : ℕ) : ℝ)^(2/3 : ℝ) := by
  classical
  let J := Nat.log 8 (Hmax+1)
  let V := fun r => fiberValues q r (Icc 0 (H r))
  let mass (r : ℕ) : ℝ := p r*((H r+1 : ℕ) : ℝ)
  have hJ : 8^J ≤ Hmax+1 := Nat.pow_log_le_self 8 (by omega)
  have hidx : ∀ r ∈ R, Nat.log 8 (H r+1) ∈ range (J+1) := by
    intro r hr
    have hh := Nat.log_mono_right (show H r+1 ≤ Hmax+1 by have := hH r hr; omega) (b := 8)
    exact mem_range.mpr (Nat.lt_succ_of_le hh)
  have hmass : (∑ j ∈ range (J+1), ∑ r ∈ bin R H j, mass r)=∑ r ∈ R, mass r :=
    sum_fiberwise_of_maps_to hidx mass
  have hcost := cost_partition_le R (range (J+1)) V p (fun r => Nat.log 8 (H r+1))
  have hbin (j : ℕ) (hj : j ∈ range (J+1)) :
      (∑ r ∈ bin R H j, mass r)-cost (bin R H j) V p ≤
        320*((q*8^j : ℕ) : ℝ)^(2/3 : ℝ) := by
    have hjJ : j ≤ J := by simpa using mem_range.mp hj
    have hp8 : 0 < (8:ℕ)^j := pow_pos (by decide) j
    have hlowq : 8^j-1 ≤ q := by
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (8:ℕ)) hjJ
      omega
    have hsub : bin R H j ⊆ R := filter_subset _ _
    have hprefix : ∀ r ∈ bin R H j,
        fiberValues q r (Icc 0 (8^j-1)) ⊆ V r := by
      intro r hr
      apply image_subset_image
      intro k hk
      have hlen := (bin_length hr).1
      have hk' := (mem_Icc.mp hk).2
      exact mem_Icc.mpr ⟨Nat.zero_le _,by omega⟩
    have hc := cost_mono p (Subset.refl (bin R H j)) hprefix
    have hm : (∑ r ∈ bin R H j, mass r) ≤
        8*((8^j : ℕ) : ℝ)*(∑ r ∈ bin R H j, p r) := by
      rw [mul_sum]
      apply sum_le_sum
      intro r hr
      have hl := (bin_length hr).2
      rw [pow_succ] at hl
      have hlR : ((H r+1 : ℕ) : ℝ) ≤ 8*((8^j : ℕ) : ℝ) := by exact_mod_cast (show H r+1 ≤ 8*8^j by nlinarith only [hl])
      have hh := mul_le_mul_of_nonneg_left hlR (hp r (hsub hr))
      dsimp [mass]
      nlinarith only [hh]
    have hh := ShortFullFiberWeightedCeiling.eightfold_height_bound q (8^j-1) (bin R H j)
      hq hlowq (fun r hr => hR r (hsub hr)) (fun r hr => hunit r (hsub hr))
      (pairMatching_subset hM hsub) p (fun r hr => hp r (hsub hr)) (fun r hr => hp1 r (hsub hr))
    have he : 8^j-1+1=8^j := by omega
    rw [he] at hh
    change 8*((8^j : ℕ) : ℝ)*(∑ r ∈ bin R H j, p r) -
      cost (bin R H j) (fun r => fiberValues q r (Icc 0 (8^j-1))) p ≤ _ at hh
    linarith only [hm,hc,hh]
  have hsum := sum_le_sum hbin
  rw [sum_sub_distrib,hmass] at hsum
  have hs : (∑ r ∈ R, mass r)-cost R V p ≤
      ∑ j ∈ range (J+1), 320*((q*8^j : ℕ) : ℝ)^(2/3 : ℝ) := by
    change (∑ j ∈ range (J+1), cost (bin R H j) V p) ≤ cost R V p at hcost
    linarith only [hsum,hcost]
  have hgeo := geometric_four_bound J
  have hgeo' := mul_le_mul_of_nonneg_left hgeo (show (0:ℝ) ≤ 320*(q : ℝ)^(2/3 : ℝ) by positivity)
  have htop : ((q*8^J : ℕ) : ℝ)^(2/3 : ℝ) ≤ ((q*(Hmax+1) : ℕ) : ℝ)^(2/3 : ℝ) := by
    apply Real.rpow_le_rpow (Nat.cast_nonneg _)
    · exact_mod_cast Nat.mul_le_mul_left q hJ
    · norm_num
  rw [octadic_rpow] at htop
  simp_rw [octadic_rpow] at hs
  have heq : (∑ j ∈ range (J+1), 320*((q : ℝ)^(2/3 : ℝ)*4^j)) =
      (320*(q : ℝ)^(2/3 : ℝ))*(∑ j ∈ range (J+1), (4:ℝ)^j) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
  rw [heq] at hs
  change (∑ r ∈ R, mass r)-cost R V p ≤ _
  nlinarith only [hs,hgeo',htop]

/-- The mass is the sum of the actual square-value fiber cardinalities. -/
theorem actual_expression_height_bound (q Hmax : ℕ) (R : Finset ℕ) (H : ℕ → ℕ)
    (hq : q.Prime) (hmaxq : Hmax ≤ q) (hH : ∀ r ∈ R, H r ≤ Hmax)
    (hR : ∀ r ∈ R, r < q) (hunit : ∀ r ∈ R, q.Coprime (2*r))
    (hM : PairMatching q R) (p : ℕ → ℝ)
    (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    (∑ r ∈ R, p r*(fiberValues q r (Icc 0 (H r))).card) -
      cost R (fun r => fiberValues q r (Icc 0 (H r))) p ≤
        480*((q*(Hmax+1) : ℕ) : ℝ)^(2/3 : ℝ) := by
  have hc (r : ℕ) : (fiberValues q r (Icc 0 (H r))).card=H r+1 := by
    rw [fiberValues,card_image_of_injective]
    · simp
    · intro a b he
      have hh := Nat.pow_left_injective (by decide : (2:ℕ) ≠ 0) he
      nlinarith only [hh,hq.pos]
  simp_rw [hc]
  exact expression_height_bound q Hmax R H hq hmaxq hH hR hunit hM p hp hp1

#print axioms cost_partition_le
#print axioms expression_height_bound
#print axioms actual_expression_height_bound
end Erdos773.UnequalFullFibers
