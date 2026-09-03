import Submission.BudgetInterceptFlatExplore
import Submission.InterceptSelectionScaleExplore

/-! Explicit relative-error conditions for the cubic selector, and its
remaining obstruction at full-prefix density. These are not a disproof. -/
namespace Erdos66BudgetInterceptScale
open Erdos66BudgetInterceptFlat Erdos66InterceptPrefix Erdos66OriginRepair
  Erdos66Counting Erdos66InterceptSelectionScale Erdos66FullFaithfulLiftObstruction
open Filter AdditiveCombinatorics
open scoped Topology
set_option maxHeartbeats 1800000

lemma cubic_relative_bound (p h ε D : ℝ) (hp : 0 < p)
    (hε : 0 ≤ ε) (hD : 0 ≤ D) (hbudget : p*D^3 ≤ 6912*h^9)
    (hscale : 6912*h^3 ≤ p*ε^3) : D ≤ ε*h^2 := by
  apply (pow_le_pow_iff_left₀ hD (by positivity) (by norm_num : (3:ℕ)≠0)).mp
  have hh6 : 0 ≤ h^6 := by positivity
  have hpow : p*D^3 ≤ p*(ε*h^2)^3 := calc
    _ ≤ 6912*h^9 := hbudget
    _ = (6912*h^3)*h^6 := by ring
    _ ≤ (p*ε^3)*h^6 := mul_le_mul_of_nonneg_right hscale hh6
    _ = _ := by ring
  nlinarith only [hpow,hp]

/-- A convenient sufficient relative-error regime. In particular the
incidence term is small when h³/p is small, not merely when h⁷/p is small. -/
theorem exists_relative_anchored_graph {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F≠2) (U S : Finset F) (hS : ∀u∈U,∀v∈U,u+v∈S)
    (hU : 0 < U.card) (hsize : 2*U.card^2 < Fintype.card F)
    (ε : ℝ) (hε : 0 ≤ ε) (hlinear : 24 ≤ ε*U.card)
    (hsupport : 16*(S.card : ℝ) ≤ ε^2*(U.card : ℝ)^2)
    (hscale : 6912*(U.card : ℝ)^3 ≤ (Fintype.card F : ℝ)*ε^3) :
    ∃ a : F, (∀x : F,(x,0)∈anchored U a ↔ x∈U) ∧
      ∀z : F × F,
        |(pairCount (anchored U a) (anchored U a) z : ℝ)-(U.card : ℝ)^2| ≤
          3*ε*(U.card : ℝ)^2 := by
  obtain ⟨a,D,hrow,hbound⟩ := exists_budget_anchored_graph hF U S hS hU hsize
  refine ⟨a,hrow,fun z ↦ ?_⟩
  obtain ⟨he,hD⟩ := hbound z
  have hDc : (Fintype.card F : ℝ)*(D z : ℝ)^3 ≤ 6912*(U.card : ℝ)^9 := by exact_mod_cast hD
  have hd := cubic_relative_bound (Fintype.card F) U.card ε (D z)
    (by exact_mod_cast Fintype.card_pos) hε (Nat.cast_nonneg _) hDc hscale
  have hl : 24*(U.card : ℝ) ≤ ε*(U.card : ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_right hlinear (Nat.cast_nonneg U.card)
    nlinarith only [hh]
  have hr : Real.sqrt (16*(S.card : ℝ)*(U.card : ℝ)^2) ≤ ε*(U.card : ℝ)^2 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hsupport (sq_nonneg (U.card : ℝ))
    nlinarith only [hh]
  linarith

/-- Even the weakened opposite-pair exclusion certificate eventually fails
for full old prefixes of a hypothetical witness. This does not rule out a
better selector or an unrelated construction. -/
theorem full_prefix_fails_budget_condition {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠ N : ℕ in atTop, ¬2*(count A N)^2 < N := by
  filter_upwards [count_square_eventually_gt_cutoff hc ht] with N hN
  omega

theorem prime_prefix_fails_budget_condition {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      ¬2*(prefixParameters A p).card^2 < Fintype.card (ZMod p) := by
  filter_upwards [full_prefix_fails_budget_condition hc ht] with p hp
  intro hpprime
  letI : Fact p.Prime := ⟨hpprime⟩
  simpa only [prefixParameters_card,ZMod.card] using hp

end Erdos66BudgetInterceptScale
