import Submission.SquarefreeMovingBandDensity
import Submission.StrictCubeCollision
import Submission.L2OrientedScoreObstruction

/-! A finite-square-energy score with a uniform adaptive spread on the largest
three roots of every sufficiently large squarefree collision would settle the
conjecture. This file proves the implication, not the score's existence. -/
namespace Erdos1206.UpperTripleScoreCriterion
open Finset FullPrimeScoreVariance PowerWindowMeanOscillation QuadraticPrimeMoments
  PositiveDensityTransfer
open scoped Classical

noncomputable def spread (w : ℕ → ℝ) (b c d : ℕ) : ℝ :=
  max |primeScore w b-primeScore w c|
    (max |primeScore w b-primeScore w d| |primeScore w c-primeScore w d|)

lemma pair_score_bound (w : ℕ → ℝ) {μ ε : ℝ} (hε : 0 < ε) {m n : ℕ}
    (hm : |deviation w m-μ| < ε/4) (hn : |deviation w n-μ| < ε/4)
    (hc : |center w m-center w n| < ε/4) : |primeScore w m-primeScore w n| < ε := by
  have he : primeScore w m-primeScore w n=
      ((deviation w m-μ)-(deviation w n-μ))+(center w m-center w n) := by
    simp only [deviation]
    ring
  rw [he]
  have h₁ := abs_add_le ((deviation w m-μ)-(deviation w n-μ)) (center w m-center w n)
  have h₂ := abs_sub (deviation w m-μ) (deviation w n-μ)
  linarith

/-- A genuinely adaptive condition: which pair has the required gap may vary
from collision to collision. The mean shift and all finite initial roots are
handled by the density and oscillation theorems. -/
theorem score_suffices (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    {ε : ℝ} (hε : 0 < ε) (H₀ : ℕ)
    (hgap : ∀ a b c d : ℕ,
      Squarefree a → Squarefree b → Squarefree c → Squarefree d →
      H₀ ≤ b → 0 < a → a < b → b < c → c < d → a^3+d^3=b^3+c^3 →
        ε ≤ spread w b c d) :
    ∃ A : Set ℕ,A.Infinite ∧ 0 < A.lowerDensity ∧ IsSidon ((fun n : ℕ => n^3) '' A) := by
  obtain ⟨μ,hB⟩ := SquarefreeMovingBandDensity.exists_squarefree_band w hs (div_pos hε (by norm_num : (0:ℝ) < 4))
  obtain ⟨H,hH⟩ := collision_center_oscillation w hs (div_pos hε (by norm_num : (0:ℝ) < 4))
  let B : Set ℕ := {n | Squarefree n ∧ |deviation w n-μ| < ε/4}
  let A := B ∩ Set.Ici (max H₀ H)
  have hA : 0 < A.lowerDensity := trim hB (max H₀ H)
  refine ⟨A,?_,hA,?_⟩
  · by_contra hfin
    have hz : A.lowerDensity=0 := (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hfin)).liminf_eq
    rw [hz] at hA
    exact (lt_irrefl 0) hA
  · apply (cubeSidon_iff_no_strict_positive A).mpr
    intro a ha b hb c hc d hd ha0 hab hbc hcd he
    have hbH : H ≤ b := (le_max_right _ _).trans hb.2
    have hbcC := hH a b c d hbH hcd he b c le_rfl (hbc.trans hcd).le hbc.le hcd.le
    have hbdC := hH a b c d hbH hcd he b d le_rfl (hbc.trans hcd).le (hbc.trans hcd).le le_rfl
    have hcdC := hH a b c d hbH hcd he c d hbc.le hcd.le (hbc.trans hcd).le le_rfl
    have h₁ := pair_score_bound w hε hb.1.2 hc.1.2 hbcC
    have h₂ := pair_score_bound w hε hb.1.2 hd.1.2 hbdC
    have h₃ := pair_score_bound w hε hc.1.2 hd.1.2 hcdC
    have hlt : spread w b c d < ε := max_lt h₁ (max_lt h₂ h₃)
    exact (not_lt_of_ge (hgap a b c d ha.1.1 hb.1.1 hc.1.1 hd.1.1
      ((le_max_left _ _).trans hb.2) ha0 hab hbc hcd he)) hlt

/-- The same criterion stated for a completely additive score on positive
integers, rather than its strongly additive prime-support extension. -/
theorem additive_score_suffices (f : ℕ → ℝ)
    (hmul : ∀ a b : ℕ,0 < a → 0 < b → f (a*b)=f a+f b)
    (hs : Summable (fun p : ℕ => if p.Prime then f p^2/p else 0))
    {ε : ℝ} (hε : 0 < ε) (H₀ : ℕ)
    (hgap : ∀ a b c d : ℕ,
      Squarefree a → Squarefree b → Squarefree c → Squarefree d →
      H₀ ≤ b → 0 < a → a < b → b < c → c < d → a^3+d^3=b^3+c^3 →
        ε ≤ max |f b-f c| (max |f b-f d| |f c-f d|)) :
    ∃ A : Set ℕ,A.Infinite ∧ 0 < A.lowerDensity ∧ IsSidon ((fun n : ℕ => n^3) '' A) := by
  apply score_suffices f hs hε H₀
  intro a b c d ha hb hc hd hbH ha0 hab hbc hcd he
  simpa only [spread,L2OrientedScoreObstruction.primeScore_eq f hmul hb,
    L2OrientedScoreObstruction.primeScore_eq f hmul hc,
    L2OrientedScoreObstruction.primeScore_eq f hmul hd] using
    hgap a b c d ha hb hc hd hbH ha0 hab hbc hcd he

#print axioms score_suffices
#print axioms additive_score_suffices
end Erdos1206.UpperTripleScoreCriterion
