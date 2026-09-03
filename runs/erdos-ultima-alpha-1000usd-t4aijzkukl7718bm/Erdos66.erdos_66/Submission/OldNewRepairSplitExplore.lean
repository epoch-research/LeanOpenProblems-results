import Submission.UnrestrictedRepairIncidenceExplore

/-! Separating the old/new and new/new mechanisms of a shared repair.
These necessary conditions do not construct a repair or negate Erdős 66. -/
namespace Erdos66OldNewRepairSplit
open Filter AdditiveCombinatorics Erdos66NatPairAlgebra
  Erdos66AdditiveDeficitMass Erdos66UnrestrictedRepairIncidence
open scoped Classical Topology
set_option maxHeartbeats 1600000

noncomputable def selfMass (F T : Finset ℕ) : ℝ :=
  ∑ n∈T, (pairs F F n:ℝ)

lemma selfMass_nonneg (F T : Finset ℕ) : 0 ≤ selfMass F T := by
  unfold selfMass
  positivity

lemma selfMass_le_card_sq (F T : Finset ℕ) : selfMass F T ≤ (F.card:ℝ)^2 := by
  unfold selfMass
  exact_mod_cast (show (∑ n∈T, pairs F F n) ≤ F.card^2 by
    simpa only [pow_two] using pairs_sum_le F F T)

lemma increment_old_new_identity (A F T : Finset ℕ) (h : Disjoint A F) :
    incrementMass A F T = 2*∑ x∈F, (targetDegree A T x:ℝ)+selfMass F T := by
  have he : (∑ n∈T, (pairs F A n:ℝ))=∑ x∈F, (targetDegree A T x:ℝ) := by
    exact_mod_cast sum_pairs_eq_degrees F A T
  unfold incrementMass selfMass
  simp_rw [increment_eq A F h,pairs_comm A F]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,he]

lemma uniform_gain_old_new_bound (A F T : Finset ℕ) (h : Disjoint A F) (d : ℝ)
    (hgain : ∀ n∈T, (sumRep (A:Set ℕ) n:ℝ)+d ≤ sumRep (A∪F:Finset ℕ) n) :
    d*T.card ≤ 2*∑ x∈F, (targetDegree A T x:ℝ)+selfMass F T := by
  rw [←increment_old_new_identity A F T h]
  have hs : (∑ _n∈T, d) ≤ incrementMass A F T := by
    apply Finset.sum_le_sum
    intro n hn
    exact le_sub_iff_add_le.mpr (by simpa only [add_comm] using hgain n hn)
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hs

/-- An upper bound on OLD-set degrees leaves a quantified new/new obligation.
Unlike a degree bound for the completed set, this does not hide new/new pairs. -/
theorem old_degree_forces_self_mass (A F T : Finset ℕ) (h : Disjoint A F)
    (δ L R H : ℝ) (hR : 0<R)
    (hgain : ∀ n∈T, (sumRep (A:Set ℕ) n:ℝ)+δ*L ≤ sumRep (A∪F:Finset ℕ) n)
    (hdegree : ∀ x∈F, R*(targetDegree A T x:ℝ) ≤ H*T.card*L) :
    (δ-2*H*((F.card:ℝ)/R))*T.card*L ≤ selfMass F T := by
  have hg := uniform_gain_old_new_bound A F T h (δ*L) hgain
  have hd : (∑ x∈F, (targetDegree A T x:ℝ)) ≤ (H*T.card*L/R)*F.card := by
    calc
      _  ≤  ∑ _x∈F, H*T.card*L/R := Finset.sum_le_sum (fun x hx ↦
        (le_div_iff₀ hR).mpr (by simpa only [mul_comm] using hdegree x hx))
      _ = _ := by simp [mul_comm]
  have he : 2*((H*T.card*L/R)*F.card)=(2*H*((F.card:ℝ)/R))*T.card*L := by ring
  linarith [show 2*(∑ x∈F, (targetDegree A T x:ℝ)) ≤ 
    (2*H*((F.card:ℝ)/R))*T.card*L by rw [←he]; linarith]

/-- With negligible added counting mass, bounded normalized old-set degrees
force essentially the entire prescribed deficit mass into new/new pairs. -/
theorem negligible_old_incidence_forces_self_mass (A F T : ℕ → Finset ℕ)
    (R L : ℕ → ℝ) (δ H d : ℝ) (hd : d<δ)
    (hsmall : Tendsto (fun k ↦ ((F k).card:ℝ)/R k) atTop (𝓝 0))
    (hdata : ∀ᶠ k in atTop, Disjoint (A k) (F k) ∧ 0 ≤ L k ∧ 0<R k ∧
      (∀ n∈T k, (sumRep (A k:Set ℕ) n:ℝ)+δ*L k ≤ sumRep ((A k)∪(F k):Finset ℕ) n) ∧
      (∀ x∈F k, R k*(targetDegree (A k) (T k) x:ℝ) ≤ H*(T k).card*L k)) :
    ∀ᶠ k in atTop, d*(T k).card*L k ≤ selfMass (F k) (T k) := by
  have hlim : Tendsto (fun k ↦ 2*H*(((F k).card:ℝ)/R k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsmall.const_mul (2*H)
  filter_upwards [hdata,hlim.eventually (gt_mem_nhds (show 0<δ-d by linarith))] with k hk hlt
  obtain ⟨hj,hL,hR,hg,hdeg⟩ := hk
  have hb := old_degree_forces_self_mass (A k) (F k) (T k) hj δ (L k) (R k) H hR hg hdeg
  have hm := mul_le_mul_of_nonneg_right (show d ≤ δ-2*H*(((F k).card:ℝ)/R k) by linarith)
    (show 0 ≤ ((T k).card:ℝ)*L k by positivity)
  have hstep : d*(T k).card*L k ≤ (δ-2*H*(((F k).card:ℝ)/R k))*(T k).card*L k := by
    simpa only [mul_assoc] using hm
  exact hstep.trans hb

/-- The resulting lower bound on the addition is a square root of the total
remaining target deficit, rather than a separate packet cost per target. -/
theorem negligible_old_incidence_card_lower (A F T : ℕ → Finset ℕ)
    (R L : ℕ → ℝ) (δ H d : ℝ) (hd : d<δ)
    (hsmall : Tendsto (fun k ↦ ((F k).card:ℝ)/R k) atTop (𝓝 0))
    (hdata : ∀ᶠ k in atTop, Disjoint (A k) (F k) ∧ 0 ≤ L k ∧ 0<R k ∧
      (∀ n∈T k, (sumRep (A k:Set ℕ) n:ℝ)+δ*L k ≤ sumRep ((A k)∪(F k):Finset ℕ) n) ∧
      (∀ x∈F k, R k*(targetDegree (A k) (T k) x:ℝ) ≤ H*(T k).card*L k)) :
    ∀ᶠ k in atTop, Real.sqrt (d*(T k).card*L k) ≤ (F k).card := by
  filter_upwards [negligible_old_incidence_forces_self_mass A F T R L δ H d hd hsmall hdata]
    with k hk
  exact Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _,hk.trans (selfMass_le_card_sq (F k) (T k))⟩

/-- In particular, a scheme keeping its new/new contribution uniformly
subscale cannot also have bounded old-set degrees and negligible added mass. -/
theorem negligible_old_incidence_and_self_forces_empty (A F T : ℕ → Finset ℕ)
    (R L ε : ℕ → ℝ) (δ H : ℝ) (hδ : 0<δ)
    (hsmall : Tendsto (fun k ↦ ((F k).card:ℝ)/R k) atTop (𝓝 0))
    (hε : Tendsto ε atTop (𝓝 0))
    (hdata : ∀ᶠ k in atTop, Disjoint (A k) (F k) ∧ 0<L k ∧ 0<R k ∧
      (∀ n∈T k, (sumRep (A k:Set ℕ) n:ℝ)+δ*L k ≤ sumRep ((A k)∪(F k):Finset ℕ) n) ∧
      (∀ x∈F k, R k*(targetDegree (A k) (T k) x:ℝ) ≤ H*(T k).card*L k) ∧
      (∀ n∈T k, (pairs (F k) (F k) n:ℝ) ≤ ε k*L k)) :
    ∀ᶠ k in atTop, T k=∅ := by
  have hb := negligible_old_incidence_forces_self_mass A F T R L δ H (δ/2) (by linarith)
    hsmall (by
      filter_upwards [hdata] with k hk
      exact ⟨hk.1,hk.2.1.le,hk.2.2.1,hk.2.2.2.1,hk.2.2.2.2.1⟩)
  filter_upwards [hdata,hb,hε.eventually (gt_mem_nhds (show 0<δ/2 by linarith))]
    with k hk hbound heps
  by_contra hne
  have hT : (0:ℝ)<(T k).card := by exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  have hself : selfMass (F k) (T k) ≤ ε k*(T k).card*L k := by
    calc
      _  ≤  ∑ _n∈T k, ε k*L k := Finset.sum_le_sum hk.2.2.2.2.2
      _ = _ := by simp [mul_comm,mul_left_comm,mul_assoc]
  have hlt := mul_lt_mul_of_pos_right heps (mul_pos hT hk.2.1)
  nlinarith only [hself,hbound,hlt]

end Erdos66OldNewRepairSplit
