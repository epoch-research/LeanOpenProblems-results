import Submission.PopulationLowCountBennett
import Submission.SymmetricExposureTail

/-! A soft ordered-exposure tree. At each step, its weight is the fraction of
remaining positions hit by the next residue class. No independence between
positions is assumed. -/
namespace Erdos970.SoftExposure
open Finset Real

noncomputable def avoid (U : Finset ℕ) (p : ℕ) (r : ℕ → ℕ) : Finset ℕ :=
  U.filter (fun x => ¬x ≡ r p [MOD p])

noncomputable def survivors (U P : Finset ℕ) (r : ℕ → ℕ) : Finset ℕ :=
  U.filter (fun x => ∀ p ∈ P, ¬x ≡ r p [MOD p])

noncomputable def hitFraction (U : Finset ℕ) (p : ℕ) (r : ℕ → ℕ) : ℝ :=
  (((U.filter (fun x => x ≡ r p [MOD p])).card : ℝ)) / U.card

noncomputable def tree : ℕ → Finset ℕ → Finset ℕ → (ℕ → ℕ) → ℝ
  | 0, _, _, _ => 1
  | j + 1, U, P, r => ∑ p ∈ P, hitFraction U p r * tree j (avoid U p r) (P.erase p) r

noncomputable def budget : ℕ → Finset ℕ → ℝ
  | 0, _ => 1
  | j + 1, P => ∑ p ∈ P, (p : ℝ)⁻¹ * budget j (P.erase p)

lemma hitFraction_nonneg (U : Finset ℕ) (p : ℕ) (r : ℕ → ℕ) :
    0 ≤ hitFraction U p r := by unfold hitFraction; positivity

lemma tree_nonneg (j : ℕ) (U P : Finset ℕ) (r : ℕ → ℕ) : 0 ≤ tree j U P r := by
  induction j generalizing U P with
  | zero => norm_num [tree]
  | succ j ih => exact sum_nonneg (fun p hp => mul_nonneg (hitFraction_nonneg U p r) (ih _ _))

lemma budget_nonneg (j : ℕ) (P : Finset ℕ) : 0 ≤ budget j P := by
  induction j generalizing P with
  | zero => norm_num [budget]
  | succ j ih => exact sum_nonneg (fun p hp => mul_nonneg (by positivity) (ih _))

lemma tree_congr (j : ℕ) (U P : Finset ℕ) (r s : ℕ → ℕ)
    (hrs : ∀ p ∈ P, r p = s p) : tree j U P r = tree j U P s := by
  induction j generalizing U P with
  | zero => rfl
  | succ j ih =>
    apply sum_congr rfl
    intro p hp
    have ha : avoid U p r = avoid U p s := by simp only [avoid, hrs p hp]
    have hh : hitFraction U p r = hitFraction U p s := by simp only [hitFraction, hrs p hp]
    rw [ha, hh, ih _ _ (fun q hq => hrs q (mem_of_mem_erase hq))]

lemma survivors_empty (U : Finset ℕ) (r : ℕ → ℕ) : survivors U ∅ r = U := by
  simp [survivors]

lemma survivors_insert (U Q : Finset ℕ) (p : ℕ) (r : ℕ → ℕ) :
    survivors U (insert p Q) r = survivors (avoid U p r) Q r := by
  ext x
  simp only [survivors, avoid, mem_filter, forall_mem_insert]
  tauto

lemma survivors_erase_avoid (U P : Finset ℕ) (p : ℕ) (hp : p ∈ P) (r : ℕ → ℕ) :
    survivors (avoid U p r) (P.erase p) r = survivors U P r := by
  rw [← survivors_insert, insert_erase hp]

lemma hits_cover_complement (U P : Finset ℕ) (r : ℕ → ℕ) :
    (U.card : ℝ) - (survivors U P r).card ≤
      ∑ p ∈ P, (((U.filter (fun x => x ≡ r p [MOD p])).card : ℝ)) := by
  classical
  have hsub : U \ survivors U P r ⊆ P.biUnion (fun p => U.filter (fun x => x ≡ r p [MOD p])) := by
    intro x hx
    obtain ⟨hxU, hnot⟩ := mem_sdiff.mp hx
    have hh : ∃ p ∈ P, x ≡ r p [MOD p] := by
      by_contra hn
      push_neg at hn
      exact hnot (mem_filter.mpr ⟨hxU, hn⟩)
    obtain ⟨p, hp, hxp⟩ := hh
    exact mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨hxU, hxp⟩⟩
  have hc := (card_le_card hsub).trans (card_biUnion_le)
  rw [card_sdiff_of_subset (show survivors U P r ⊆ U from filter_subset _ _)] at hc
  have hh := (Nat.cast_le (α := ℝ)).mpr hc
  rw [Nat.cast_sub (card_le_card (show survivors U P r ⊆ U from filter_subset _ _)),
    Nat.cast_sum] at hh
  exact hh

lemma hitFraction_sum_lower (U P : Finset ℕ) (r : ℕ → ℕ)
    (A b : ℝ) (hA : 0 < A) (hAU : A ≤ U.card) (hb : 0 ≤ b)
    (hcount : (survivors U P r).card ≤ b) :
    1 - b / A ≤ ∑ p ∈ P, hitFraction U p r := by
  have hU : (0 : ℝ) < U.card := hA.trans_le hAU
  have hbdiv : b / U.card ≤ b / A := div_le_div_of_nonneg_left hb hA hAU
  have hh := div_le_div_of_nonneg_right (hits_cover_complement U P r) hU.le
  have hc := div_le_div_of_nonneg_right hcount hU.le
  simp only [hitFraction, ← sum_div]
  rw [sub_div, div_self hU.ne'] at hh
  linarith only [hh, hc, hbdiv]

/-- A lower population bound for every partial set of fewer than j classes. -/
def PartialLower (j : ℕ) (U P : Finset ℕ) (r : ℕ → ℕ) (A : ℝ) : Prop :=
  ∀ Q ⊆ P, Q.card < j → A ≤ (survivors U Q r).card

lemma PartialLower.step {j : ℕ} {U P : Finset ℕ} {r : ℕ → ℕ} {A : ℝ}
    (h : PartialLower (j + 1) U P r A) (p : ℕ) (hp : p ∈ P) :
    PartialLower j (avoid U p r) (P.erase p) r A := by
  intro Q hQ hj
  have hpQ : p ∉ Q := fun hh => (mem_erase.mp (hQ hh)).1 rfl
  have hs : insert p Q ⊆ P := insert_subset hp (hQ.trans (erase_subset _ _))
  have hh := h (insert p Q) hs (by rw [card_insert_of_notMem hpQ]; omega)
  rwa [survivors_insert] at hh

/-- A low-count phase has substantial soft-exposure mass. The sum can count
multiple covering primes for a point; only a lower bound is needed here. -/
theorem tree_lower (j : ℕ) (U P : Finset ℕ) (r : ℕ → ℕ)
    (A b : ℝ) (hA : 0 < A) (hb : 0 ≤ b) (hbA : b ≤ A)
    (hpartial : PartialLower j U P r A) (hcount : (survivors U P r).card ≤ b) :
    (1 - b / A) ^ j ≤ tree j U P r := by
  have hbase : 0 ≤ 1 - b / A := sub_nonneg.mpr ((div_le_one hA).mpr hbA)
  induction j generalizing U P with
  | zero => rfl
  | succ j ih =>
    have hAU : A ≤ U.card := by
      simpa only [survivors_empty] using hpartial ∅ (empty_subset _) (by simp)
    have hs := hitFraction_sum_lower U P r A b hA hAU hb hcount
    calc
      (1 - b / A) ^ (j + 1) = (1 - b / A) * (1 - b / A) ^ j := by ring
      _ ≤ (∑ p ∈ P, hitFraction U p r) * (1 - b / A) ^ j :=
        mul_le_mul_of_nonneg_right hs (pow_nonneg hbase j)
      _ = ∑ p ∈ P, hitFraction U p r * (1 - b / A) ^ j := sum_mul _ _ _
      _ ≤ _ := by
        apply sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_left _ (hitFraction_nonneg U p r)
        apply ih _ _ (hpartial.step p hp)
        rwa [survivors_erase_avoid U P p hp]

#print axioms tree_lower
end Erdos970.SoftExposure
