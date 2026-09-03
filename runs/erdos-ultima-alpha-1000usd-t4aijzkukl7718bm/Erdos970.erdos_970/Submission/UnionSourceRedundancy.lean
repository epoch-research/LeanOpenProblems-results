import Submission.UnionReferenceSource
import Submission.RecursivePositiveScaling

/-! The sharpened overlap-aware source is still redundant if the same plain
numerical envelope certified its source length, in the stated large-missing-prime
range. No claim about all arithmetic sources is made. -/
namespace Erdos970.MixedPattern
open Finset GapAverages

/-- An elementary product bound, with the actual number of adjoined primes. -/
lemma density_card_lower (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) (a : ℝ) (ha : 0 < a)
    (hlarge : ∀ p ∈ R, a ≤ (p : ℝ)) :
    a-(R.card : ℝ) ≤ a*density R := by
  induction R using Finset.induction_on with
  | empty => simp [density]
  | @insert p R hp ih =>
    have hRp : ∀ q ∈ R, q.Prime := fun q hq => hR q (mem_insert_of_mem hq)
    have hh := ih hRp (fun q hq => hlarge q (mem_insert_of_mem hq))
    have hd : density R ≤ 1 := by
      have hh := density_subset_le ∅ R hRp (empty_subset R)
      simpa only [density,prod_empty] using hh
    have hdn := (density_pos R hRp).le
    have hpp : (0 : ℝ) < p := by exact_mod_cast (hR p (mem_insert_self _ _)).pos
    have hdiv : a/(p : ℝ) ≤ 1 := (div_le_one hpp).mpr (hlarge p (mem_insert_self _ _))
    have hm := mul_le_mul_of_nonneg_right hdiv hdn
    have hmul : (a/(p : ℝ))*density R ≤ 1 := by linarith
    have he : density (insert p R) = (1-1/(p : ℝ))*density R := prod_insert hp
    rw [he,card_insert_of_notMem hp,Nat.cast_add,Nat.cast_one]
    have hid : a*((1-1/(p : ℝ))*density R) = a*density R-(a/(p : ℝ))*density R := by ring
    rw [hid]
    linarith

#print axioms density_card_lower
end Erdos970.MixedPattern

namespace Erdos970.FiniteSelberg
open Finset GapAverages
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma unionSourceGain_nonneg (p v : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (B : Finset ι) (j : ℕ) : 0 ≤ unionSourceGain p v B j := by
  have hR : ∀ q ∈ B.image p \ B.image v, q.Prime := by
    intro q hq
    obtain ⟨i,_,rfl⟩ := mem_image.mp (mem_sdiff.mp hq).1
    exact hp i
  exact div_nonneg (Nat.cast_nonneg _) (density_pos _ hR).le

/-- If missing actual primes are at least j+1, the retained inverse density
cannot raise the effective gain above j+1. -/
theorem unionSourceGain_le_budget (p v : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (B : Finset ι) (j : ℕ)
    (hlarge : ∀ q ∈ B.image p \ B.image v, j+1 ≤ q) :
    unionSourceGain p v B j ≤ (j : ℝ)+1 := by
  let R := B.image p \ B.image v
  let U := B.image p ∪ B.image v
  have hR : ∀ q ∈ R, q.Prime := by
    intro q hq
    obtain ⟨i,_,rfl⟩ := mem_image.mp (mem_sdiff.mp hq).1
    exact hp i
  have hd := density_pos R hR
  have hb := MixedPattern.density_card_lower R hR ((j : ℝ)+1) (by positivity)
    (fun q hq => by exact_mod_cast hlarge q hq)
  have hRU : R ⊆ U := by
    intro q hq
    exact mem_union_left _ (mem_sdiff.mp hq).1
  have hcard : R.card ≤ U.card := card_le_card hRU
  change ((j+1-U.card : ℕ) : ℝ)/density R ≤ (j : ℝ)+1
  by_cases hu : j+1 ≤ U.card
  · rw [Nat.sub_eq_zero_of_le hu,Nat.cast_zero,zero_div]
    positivity
  · have hu' : U.card ≤ j+1 := by omega
    rw [Nat.cast_sub hu',Nat.cast_add,Nat.cast_one]
    apply (div_le_iff₀ hd).mpr
    have hcr : (R.card : ℝ) ≤ U.card := by exact_mod_cast hcard
    linarith

#print axioms unionSourceGain_nonneg
#print axioms unionSourceGain_le_budget
end Erdos970.FiniteSelberg

namespace Erdos970.RecursiveSieve
open Finset FiniteSelberg
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In this range, sharpening the union charge does not overcome the same-model
source redundancy. The earlier-prefix relation and plain positive certificate
are both essential stated premises. -/
theorem unionSource_le_of_plain_certificate (q : ℕ → ℝ)
    (p v : ι → ℕ) (hp : ∀ i, (p i).Prime) (B : Finset ι) (j : ℕ)
    (hBj : B.card ≤ j) (hq : ∀ i < j, 0 ≤ q i ∧ q i ≤ 1)
    (hlarge : ∀ r ∈ B.image p \ B.image v, j+1 ≤ r)
    (g : ℝ) (hg : 0 < g) (hpos : 0 < (linearEnvelope q j g).1)
    (x : ℝ) (hx : 0 ≤ x) :
    max 0 (unionSourceGain p v B j/g*(x-1)-unionSourceGain p v B j) ≤
      (linearEnvelope q B.card x).1 :=
  affineSource_le_of_plain_positive q B.card j hBj hq g hg hpos _
    (unionSourceGain_nonneg p v hp B j) (unionSourceGain_le_budget p v hp B j hlarge) x hx

#print axioms unionSource_le_of_plain_certificate
end Erdos970.RecursiveSieve
