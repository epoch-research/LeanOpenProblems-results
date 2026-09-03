import FormalConjecturesUtil
import Submission.SubcriticalPrimePairCancellation
import Submission.ProductSignTransport
import Submission.RadicalLogMean

/-! Negative off-diagonal correlation inside large-divisor subgroups.
This controls a divisor-restricted signed energy, not the unrestricted
winning-prime energy required for Erdős 371. -/

namespace Erdos371LargeDivisorSignedEnergy

open Finset Erdos371PrimeDiscrepancy Erdos371ProductSignTransport
open Erdos371SubcriticalPrimePairCancellation (count)

lemma count_le_one_of_large_product {a b N : ℕ} (hprod : N < a*b) : count a b N ≤ 1 := by
  have ha : 0 < a := by nlinarith
  have hb : 0 < b := by nlinarith
  by_cases hcop : a.Coprime b
  · have he := Erdos371SubcriticalPrimePairCancellation.count_error ha hb hcop N
    have hr : (N : ℝ)/(a*b : ℕ) < 1 := by
      apply (div_lt_one (Nat.cast_pos.mpr (Nat.mul_pos ha hb))).mpr
      exact_mod_cast hprod
    have hc : (count a b N : ℝ) < 2 := by linarith [(abs_le.mp he).2]
    have hc' : count a b N < 2 := by exact_mod_cast hc
    omega
  · have he : (range N).filter (fun n => a ∣ n ∧ b ∣ n+1) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro n hn hab
      exact hcop (Nat.Coprime.of_dvd hab.1 hab.2 (by simp))
    simp [count,he]

def members (p d N : ℕ) : Finset ℕ :=
  (range N).filter (fun n => winner n=p ∧ d ∣ lower n)

def up (p d N : ℕ) : Finset ℕ := (members p d N).filter (fun n => P n < P (n+1))
def down (p d N : ℕ) : Finset ℕ := (members p d N).filter (fun n => ¬P n < P (n+1))

lemma up_card_le_one {p d N : ℕ} (hprod : N < p*d) : (up p d N).card ≤ 1 := by
  have hs : up p d N ⊆ (range N).filter (fun n => d ∣ n ∧ p ∣ n+1) := by
    intro n hn
    obtain ⟨hn, hcmp⟩ := mem_filter.mp hn
    obtain ⟨hnN,hwin,hdiv⟩ := mem_filter.mp hn
    have hp : P (n+1)=p := by simpa [winner,max_eq_right hcmp.le] using hwin
    refine mem_filter.mpr ⟨hnN,?_,hp ▸ Nat.maxPrimeFac_dvd⟩
    simpa [lower,if_pos hcmp] using hdiv
  exact (card_le_card hs).trans (count_le_one_of_large_product (by simpa [Nat.mul_comm] using hprod))

lemma down_card_le_one {p d N : ℕ} (hprod : N < p*d) : (down p d N).card ≤ 1 := by
  have hs : down p d N ⊆ (range N).filter (fun n => p ∣ n ∧ d ∣ n+1) := by
    intro n hn
    obtain ⟨hn, hcmp⟩ := mem_filter.mp hn
    obtain ⟨hnN,hwin,hdiv⟩ := mem_filter.mp hn
    have hp : P n=p := by simpa [winner,max_eq_left (le_of_not_gt hcmp)] using hwin
    refine mem_filter.mpr ⟨hnN,hp ▸ Nat.maxPrimeFac_dvd,?_⟩
    simpa [lower,if_neg hcmp] using hdiv
  exact (card_le_card hs).trans (count_le_one_of_large_product hprod)

lemma members_card_split (p d N : ℕ) :
    (members p d N).card = (up p d N).card+(down p d N).card :=
  (card_filter_add_card_filter_not (s := members p d N) (fun n => P n < P (n+1))).symm

noncomputable def restrictedGroup (p d N : ℕ) : ℝ :=
  ∑ n ∈ members p d N, (sign n : ℝ)

lemma restrictedGroup_eq_counts (p d N : ℕ) :
    restrictedGroup p d N = ((up p d N).card : ℝ)-(down p d N).card := by
  have he (n : ℕ) : (sign n : ℝ) =
      (if P n < P (n+1) then 1 else 0) - (if ¬P n < P (n+1) then 1 else 0) := by
    unfold sign
    split_ifs <;> norm_num at *
  simp only [restrictedGroup,he,sum_sub_distrib,sum_boole,up,down]

/-- A restricted signed sum lies in [-1,1], rather than being bounded only
by its unsigned cardinality. -/
theorem restrictedGroup_abs_le_one {p d N : ℕ} (hprod : N < p*d) :
    |restrictedGroup p d N| ≤ 1 := by
  have hu : ((up p d N).card : ℝ) ≤ 1 := by exact_mod_cast up_card_le_one hprod
  have hd : ((down p d N).card : ℝ) ≤ 1 := by exact_mod_cast down_card_le_one hprod
  rw [restrictedGroup_eq_counts]
  apply abs_le.mpr
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (up p d N).card,
    Nat.cast_nonneg (α := ℝ) (down p d N).card]

/-- Only the diagonal can contribute positively to this restricted energy. -/
theorem restrictedGroup_square_le_card {p d N : ℕ} (hprod : N < p*d) :
    (restrictedGroup p d N)^2 ≤ (members p d N).card := by
  have hu : ((up p d N).card : ℝ) ≤ 1 := by exact_mod_cast up_card_le_one hprod
  have hd : ((down p d N).card : ℝ) ≤ 1 := by exact_mod_cast down_card_le_one hprod
  have hu0 := Nat.cast_nonneg (α := ℝ) (up p d N).card
  have hd0 := Nat.cast_nonneg (α := ℝ) (down p d N).card
  rw [restrictedGroup_eq_counts,members_card_split,Nat.cast_add]
  have hup : ((up p d N).card : ℝ)^2 ≤ (up p d N).card := by nlinarith
  have hdp : ((down p d N).card : ℝ)^2 ≤ (down p d N).card := by nlinarith
  have hp := mul_nonneg hu0 hd0
  nlinarith

/-- Distinct comparisons in one such subgroup have opposite signs. -/
theorem distinct_members_opposite {p d N n m : ℕ} (hprod : N < p*d)
    (hn : n ∈ members p d N) (hm : m ∈ members p d N) (hne : n ≠ m) : sign n ≠ sign m := by
  intro hs
  by_cases hcmp : P n < P (n+1)
  · have hcmp' : P m < P (m+1) := by
      by_contra hh
      simp [sign,hcmp,hh] at hs
    have hn' : n ∈ up p d N := mem_filter.mpr ⟨hn,hcmp⟩
    have hm' : m ∈ up p d N := mem_filter.mpr ⟨hm,hcmp'⟩
    exact hne ((card_le_one.mp (up_card_le_one hprod)) n hn' m hm')
  · have hcmp' : ¬P m < P (m+1) := by
      intro hh
      simp [sign,hcmp,hh] at hs
    have hn' : n ∈ down p d N := mem_filter.mpr ⟨hn,hcmp⟩
    have hm' : m ∈ down p d N := mem_filter.mpr ⟨hm,hcmp'⟩
    exact hne ((card_le_one.mp (down_card_le_one hprod)) n hn' m hm')

/-- The GCD version describes exactly where this negative-correlation argument
applies. It makes no assertion about the remaining, small-GCD pairs. -/
theorem large_gcd_opposite {N n m : ℕ} (hn : n < N) (hm : m < N)
    (hwin : winner n=winner m) (hne : n ≠ m)
    (hg : N < winner n * Nat.gcd (lower n) (lower m)) : sign n ≠ sign m := by
  apply distinct_members_opposite hg (hne := hne)
  · exact mem_filter.mpr ⟨mem_range.mpr hn,rfl,Nat.gcd_dvd_left _ _⟩
  · exact mem_filter.mpr ⟨mem_range.mpr hm,hwin.symm,Nat.gcd_dvd_right _ _⟩

end Erdos371LargeDivisorSignedEnergy

#print axioms Erdos371LargeDivisorSignedEnergy.restrictedGroup_square_le_card
#print axioms Erdos371LargeDivisorSignedEnergy.large_gcd_opposite
