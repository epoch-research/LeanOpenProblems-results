import Submission.WeightedPartialFibers
import Submission.TranslatedSquareFibers

/-!
An algebraically constructed example where nonuniform fiber selection has a
strictly better bound than every constant-probability alteration bound.
The two fibers are actual squares and are additive translates. The root height
is very large relative to the ten values in each fiber; no asymptotic lower
bound for Erdős 773 is asserted.
-/
namespace Erdos773.WeightedSquareExample
open Finset MatchedResidueLifting PartialResidueFibers PartialFiberSelection
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

/-- Factoring C=3*19^18 as 19^i * (3*19^(18-i)) yields two roots whose
squares differ by C. Both factors are odd. -/
def lowRoot (i : ℕ) : ℕ := (3*19^(18-i)-19^i)/2
def highRoot (i : ℕ) : ℕ := (3*19^(18-i)+19^i)/2

def lowValues : Finset ℕ := (range 10).image (fun i => lowRoot i^2)
def highValues : Finset ℕ := (range 10).image (fun i => highRoot i^2)
def values (r : ℕ) : Finset ℕ := if r=1 then lowValues else highValues

lemma translates : ∀ i ∈ range 10, highRoot i^2=lowRoot i^2+3*19^18 := by
  decide +kernel

lemma low_sidon : IsSidon (lowValues : Set ℕ) := by
  unfold IsSidon
  simp only [mem_coe]
  decide +kernel

lemma high_sidon : IsSidon (highValues : Set ℕ) := by
  unfold IsSidon
  simp only [mem_coe]
  decide +kernel

lemma matching : PairMatching 9 {1,2} := by
  unfold PairMatching
  decide +kernel

lemma residues : ∀ r ∈ ({1,2} : Finset ℕ), ∀ a ∈ values r, a%9=r^2%9 := by
  decide +kernel

lemma fiber_card : lowValues.card=10 ∧ highValues.card=10 := by
  decide +kernel

lemma overlap_card : (positiveDiffs lowValues ∩ positiveDiffs highValues).card=45 := by
  decide +kernel

lemma union_card : (({1,2} : Finset ℕ).biUnion values).card=20 := by
  rw [card_biUnion (fun r hr s hs hne => fibers_disjoint matching residues hr hs hne)]
  simp [values, fiber_card.1, fiber_card.2]

lemma label_pairs : ((({1,2} : Finset ℕ) ×ˢ {1,2}).filter (fun rs => rs.1 < rs.2)) = {(1,2)} := by
  decide

lemma key_card : (crossKeys {1,2} values).card=45 := by
  rw [crossKeys_card, label_pairs]
  simpa [values] using overlap_card

/-- The probabilities are 1 and 1/9. -/
theorem nonuniform_bound : (95/9 : ℝ) ≤
    (maxSidonSubsetCard (({1,2} : Finset ℕ).biUnion values) : ℝ) := by
  let p : ℕ → ℝ := fun r => if r=1 then 1 else 1/9
  have hs : ∀ r ∈ ({1,2} : Finset ℕ), IsSidon (values r : Set ℕ) := by
    intro r hr
    simp only [mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact low_sidon
    · exact high_sidon
  have hp : ∀ r ∈ ({1,2} : Finset ℕ), 0 ≤ p r := by intro r _; dsimp [p]; split <;> norm_num
  have hp1 : ∀ r ∈ ({1,2} : Finset ℕ), p r ≤ 1 := by intro r _; dsimp [p]; split <;> norm_num
  have hh := WeightedPartialFibers.overlap_alteration 9 {1,2} values matching residues hs p hp hp1
  have hmass : (∑ r ∈ ({1,2} : Finset ℕ), p r*(values r).card)=(100/9 : ℝ) := by
    norm_num [p, values, fiber_card.1, fiber_card.2]
  have hcost : (∑ rs ∈ (({1,2} : Finset ℕ) ×ˢ {1,2}).filter (fun rs => rs.1 < rs.2),
      p rs.1^2*p rs.2^2*(positiveDiffs (values rs.1) ∩ positiveDiffs (values rs.2)).card) =
        (5/9 : ℝ) := by
    rw [label_pairs]
    norm_num [p, values, overlap_card]
  rw [hmass,hcost] at hh
  have he : (100/9 : ℝ)-5/9=95/9 := by norm_num
  rw [he] at hh
  exact hh

/-- Ceiling for the constant-probability expression on this same union.
This is not an upper bound on the maximum Sidon-subset cardinality. -/
theorem uniform_expression_bound (p : ℝ) (hp : 0 ≤ p) :
    p*(({1,2} : Finset ℕ).biUnion values).card-p^4*(crossKeys {1,2} values).card ≤ 8 := by
  rw [union_card, key_card]
  norm_num only [Nat.cast_ofNat]
  have ht : p^4 ≥ p/2-3/16 := by
    have hn : 0 ≤ p^2+p+3/4 := by positivity
    nlinarith only [mul_nonneg (sq_nonneg (p-1/2)) hn]
  by_cases h : p ≤ 1/4
  · nlinarith only [h, pow_nonneg hp 4]
  · nlinarith only [h, ht]

lemma value_union : ({1,2} : Finset ℕ).biUnion values=lowValues ∪ highValues := by
  simp [values]

lemma value_translate : highValues=lowValues.image (fun a => a+3*19^18) := by
  ext a
  constructor
  · intro ha
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
    exact mem_image.mpr ⟨lowRoot i^2,mem_image.mpr ⟨i,hi,rfl⟩,(translates i hi).symm⟩
  · intro ha
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hb
    exact mem_image.mpr ⟨i,hi,translates i hi⟩

lemma maximum_upper : maxSidonSubsetCard (({1,2} : Finset ℕ).biUnion values) ≤ 11 := by
  have hup := TranslatedSquareFibers.max_translate_union lowValues (3*19^18) (by positivity)
  rw [← value_translate,← value_union,fiber_card.1] at hup
  exact hup

lemma maximum_lower : 11 ≤ maxSidonSubsetCard (({1,2} : Finset ℕ).biUnion values) := by
  by_contra hn
  have hn' : maxSidonSubsetCard (({1,2} : Finset ℕ).biUnion values) ≤ 10 := by omega
  have hnR : (maxSidonSubsetCard (({1,2} : Finset ℕ).biUnion values) : ℝ) ≤ 10 := by
    exact_mod_cast hn'
  have hh := nonuniform_bound
  linarith

/-- The nonuniform certificate, together with integrality and the translated
union bound, gives the exact finite maximum. -/
theorem exact_maximum : maxSidonSubsetCard (({1,2} : Finset ℕ).biUnion values)=11 :=
  Nat.le_antisymm maximum_upper maximum_lower

#print axioms nonuniform_bound
#print axioms uniform_expression_bound
#print axioms exact_maximum
end Erdos773.WeightedSquareExample
