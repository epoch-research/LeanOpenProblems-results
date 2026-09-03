import Submission.PrimeDensitySourceRedundancy

/-! Transitive closure of same-model arithmetic-source recycling. Zero-gain
nodes require no certificate, and the true zero-budget length one is allowed.
These are limitations of the specified affine-source recurrence only. -/
namespace Erdos970.RecursiveSieve
open Finset FiniteSelberg GapAverages

lemma unit_affine_source_le_plain_zero (q : ℕ → ℝ) (g : ℝ) (hg : 1 ≤ g)
    (x : ℝ) (hx : 0 ≤ x) :
    max 0 ((1/g)*(x-1)-1) ≤ (linearEnvelope q 0 x).1 := by
  rw [linearEnvelope_lower_eq_max q 0 (by simp) x hx]
  simp only [Finset.univ_eq_empty,Finset.sum_empty,sub_zero]
  have hg0 : 0 < g := by linarith
  have ha0 : 0 ≤ 1/g := by positivity
  have ha1 : 1/g ≤ 1 := (div_le_one hg0).mpr hg
  apply max_le (le_max_left _ _)
  by_cases hxx : 1 ≤ x
  · have hh := mul_le_mul_of_nonneg_right ha1 (sub_nonneg.mpr hxx)
    have ht := le_max_right 0 (x-1)
    linarith
  · have hh := mul_nonpos_of_nonneg_of_nonpos ha0 (show x-1 ≤ 0 by linarith)
    have ht := le_max_left 0 (x-1)
    linarith

/-- The genuine zero-budget bound g>=1 is already dominated, despite the
plain recurrence not being strictly positive at its exact endpoint g=1. -/
theorem zero_budget_union_source_le (K n : ℕ) (hn : n ≤ K) (p : Fin K → ℕ)
    (g x : ℝ) (hg : 1 ≤ g) (hx : 0 ≤ x) :
    max 0 (unionSourceGain p (fun i => Nat.nth Nat.Prime i.val) (prefixIndices K n) 0/g*(x-1)-
      unionSourceGain p (fun i => Nat.nth Nat.Prime i.val) (prefixIndices K n) 0) ≤
        (linearEnvelope firstPrimeMarginal n x).1 := by
  by_cases hn0 : n = 0
  · subst n
    have he : prefixIndices K 0 = ∅ := by simp [prefixIndices]
    simp only [he,unionSourceGain,image_empty,union_empty,card_empty,Nat.zero_add,
      Nat.sub_zero,Nat.cast_one,sdiff_self,Finset.bot_eq_empty,density,prod_empty,div_one]
    exact unit_affine_source_le_plain_zero firstPrimeMarginal g hg x hx
  · have hinj : Function.Injective (fun i : Fin K => Nat.nth Nat.Prime i.val) := by
      intro i j he
      exact Fin.ext ((Nat.nth_strictMono Nat.infinite_setOf_prime).injective he)
    have hc : n ≤ ((prefixIndices K n).image p ∪
        (prefixIndices K n).image (fun i => Nat.nth Nat.Prime i.val)).card := by
      calc
        n = ((prefixIndices K n).image (fun i : Fin K => Nat.nth Nat.Prime i.val)).card := by
          rw [card_image_of_injective _ hinj,prefixIndices_card K n hn]
        _ ≤ _ := card_le_card subset_union_right
    have he : 0+1-((prefixIndices K n).image p ∪
        (prefixIndices K n).image (fun i => Nat.nth Nat.Prime i.val)).card = 0 := by omega
    simp only [unionSourceGain,he,Nat.cast_zero,zero_div,zero_mul,sub_zero,max_self]
    exact linearEnvelope_lower_nonneg _ _ _

/-- Only positive-budget, nonzero-gain nodes require a plain positive source
certificate. The omitted terminal-budget source causes no circular premise. -/
theorem union_seeded_eq_plain_of_active_certificates
    (K : ℕ) (p : Fin K → ℕ) (hp : ∀ i, (p i).Prime) (j g : ℕ → ℕ)
    (hg : ∀ n ≤ K, 0 < g n)
    (hpos : ∀ n ≤ K, 0 < j n →
      ((prefixIndices K n).image p ∪
        (prefixIndices K n).image (fun i => Nat.nth Nat.Prime i.val)).card ≤ j n →
      0 < (linearEnvelope firstPrimeMarginal (j n) (g n : ℝ)).1)
    (x : ℝ) (hx : 0 ≤ x) :
    seededLinearEnvelope firstPrimeMarginal
      (unionBlockSource p (fun i => Nat.nth Nat.Prime i.val) j g) K x =
        linearEnvelope firstPrimeMarginal K x := by
  apply seededLinearEnvelope_eq_plain firstPrimeMarginal _ K
    (fun i _ => ⟨(firstPrimeMarginal_valid i).1,(firstPrimeMarginal_valid i).2.le⟩) _ x hx
  intro n hn y hy
  unfold unionBlockSource
  dsimp only
  by_cases hj0 : j n = 0
  · rw [hj0]
    exact zero_budget_union_source_le K n hn p (g n : ℝ) y
      (by exact_mod_cast hg n hn) hy
  · by_cases hu : ((prefixIndices K n).image p ∪
        (prefixIndices K n).image (fun i => Nat.nth Nat.Prime i.val)).card ≤ j n
    · exact firstPrime_unionSource_le_of_plain_certificate K n (j n) hn p hp
        (g n : ℝ) (by exact_mod_cast hg n hn) (hpos n hn (by omega) hu) y
    · have he : j n+1-((prefixIndices K n).image p ∪
          (prefixIndices K n).image (fun i => Nat.nth Nat.Prime i.val)).card = 0 := by omega
      simp only [unionSourceGain,he,Nat.cast_zero,zero_div,zero_mul,sub_zero,max_self]
      exact linearEnvelope_lower_nonneg _ _ _

/-- Well-founded reuse of earlier affine-source certificates cannot generate
positivity outside the plain first-prime envelope. Source lengths at budget
zero may equal1. Actual prime lists and source choices may vary at every step.
No claim is made about independent arithmetic bounds or exact floor sources. -/
theorem grounded_union_positivity_is_plain (m : ℕ → ℕ) (hm : ∀ k, 0 < m k)
    (hstep : ∀ K, 0 < K → ∃ (p : Fin K → ℕ) (j : ℕ → ℕ),
      (∀ i, (p i).Prime) ∧ (∀ n ≤ K, j n < K) ∧
        0 < (seededLinearEnvelope firstPrimeMarginal
          (unionBlockSource p (fun i => Nat.nth Nat.Prime i.val) j (fun n => m (j n)))
            K (m K : ℝ)).1) :
    ∀ K, 0 < K → 0 < (linearEnvelope firstPrimeMarginal K (m K : ℝ)).1 := by
  intro K
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro hK
    obtain ⟨p,j,hp,hj,hpositive⟩ := hstep K hK
    rw [union_seeded_eq_plain_of_active_certificates K p hp j (fun n => m (j n))
      (fun n _ => hm (j n)) (fun n hn hj0 _ => ih (j n) (hj n hn) hj0)
      (m K : ℝ) (Nat.cast_nonneg _)] at hpositive
    exact hpositive

/-- At a first failed plain budget, smaller-budget source recycling cannot
supply a positive certificate. The root source has zero gain automatically. -/
theorem first_failure_not_repaired (m : ℕ → ℕ) (hm : ∀ k, 0 < m k) (K : ℕ)
    (hprev : ∀ j < K, 0 < j → 0 < (linearEnvelope firstPrimeMarginal j (m j : ℝ)).1)
    (hfail : (linearEnvelope firstPrimeMarginal K (m K : ℝ)).1 = 0)
    (p : Fin K → ℕ) (hp : ∀ i, (p i).Prime) (j : ℕ → ℕ)
    (hj : ∀ n ≤ K, j n < K) :
    (seededLinearEnvelope firstPrimeMarginal
      (unionBlockSource p (fun i => Nat.nth Nat.Prime i.val) j (fun n => m (j n)))
        K (m K : ℝ)).1 = 0 := by
  rw [union_seeded_eq_plain_of_active_certificates K p hp j (fun n => m (j n))
    (fun n _ => hm (j n)) (fun n hn hj0 _ => hprev (j n) (hj n hn) hj0)
    (m K : ℝ) (Nat.cast_nonneg _)]
  exact hfail

#print axioms zero_budget_union_source_le
#print axioms union_seeded_eq_plain_of_active_certificates
#print axioms grounded_union_positivity_is_plain
#print axioms first_failure_not_repaired
end Erdos970.RecursiveSieve
