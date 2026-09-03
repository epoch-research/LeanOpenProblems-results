import Submission.SquarefreeMovingBandDensity
import Submission.StrictCubeCollision
import Submission.FinitePrimeEnergyCompactness

/-! A weaker score criterion: all four CENTERED deviations may supply the
adaptive gap. Uniform finite energy suffices; no such budget is constructed. -/
namespace Erdos1206.CenteredScoreCriterion
open Finset Filter FullPrimeScoreVariance PowerWindowMeanOscillation QuadraticPrimeMoments
  PositiveDensityTransfer FinitePrimeEnergyCompactness PrimeBlockMeanOscillation
open scoped Classical Topology

noncomputable def spread (w : ℕ → ℝ) (a b c d : ℕ) : ℝ :=
  max (max |deviation w a-deviation w b| |deviation w a-deviation w c|)
    (max (max |deviation w a-deviation w d| |deviation w b-deviation w c|)
      (max |deviation w b-deviation w d| |deviation w c-deviation w d|))

lemma pair_lt {x y μ ε : ℝ} (hε : 0 < ε) (hx : |x-μ| < ε/3) (hy : |y-μ| < ε/3) :
    |x-y| < ε := by
  have hh := abs_sub (x-μ) (y-μ)
  have he : (x-μ)-(y-μ)=x-y := by ring
  rw [he] at hh
  linarith

/-- The lower threshold is on the smallest root, so finitely many roots can
be discarded. No comparability of the smallest root to the others is needed. -/
theorem score_suffices (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    {ε : ℝ} (hε : 0 < ε) (H₀ : ℕ)
    (hgap : ∀ a b c d : ℕ,
      Squarefree a → Squarefree b → Squarefree c → Squarefree d →
      H₀ ≤ a → 0 < a → a < b → b < c → c < d → a^3+d^3=b^3+c^3 →
        ε ≤ spread w a b c d) :
    ∃ A : Set ℕ,A.Infinite ∧ 0 < A.lowerDensity ∧ IsSidon ((fun n : ℕ => n^3) '' A) := by
  obtain ⟨μ,hB⟩ := SquarefreeMovingBandDensity.exists_squarefree_band w hs (div_pos hε (by norm_num : (0:ℝ) < 3))
  let B : Set ℕ := {n | Squarefree n ∧ |deviation w n-μ| < ε/3}
  let A := B ∩ Set.Ici H₀
  have hA : 0 < A.lowerDensity := trim hB H₀
  refine ⟨A,?_,hA,?_⟩
  · by_contra hfin
    have hz : A.lowerDensity=0 := (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hfin)).liminf_eq
    rw [hz] at hA
    exact (lt_irrefl 0) hA
  · apply (cubeSidon_iff_no_strict_positive A).mpr
    intro a ha b hb c hc d hd ha0 hab hbc hcd he
    have hlt : spread w a b c d < ε := by
      exact max_lt (max_lt (pair_lt hε ha.1.2 hb.1.2) (pair_lt hε ha.1.2 hc.1.2))
        (max_lt (max_lt (pair_lt hε ha.1.2 hd.1.2) (pair_lt hε hb.1.2 hc.1.2))
          (max_lt (pair_lt hε hb.1.2 hd.1.2) (pair_lt hε hc.1.2 hd.1.2)))
    exact (not_lt_of_ge (hgap a b c d ha.1.1 hb.1.1 hc.1.1 hd.1.1 ha.2
      ha0 hab hbc hcd he)) hlt

def FiniteMargin (H₀ N : ℕ) (ε : ℝ) (w : ℕ → ℝ) : Prop :=
  ∀ a b c d : ℕ,
    Squarefree a → Squarefree b → Squarefree c → Squarefree d →
    H₀ ≤ a → d ≤ N → 0 < a → a < b → b < c → c < d → a^3+d^3=b^3+c^3 →
      ε ≤ spread w a b c d

lemma deviation_cutoff (N : ℕ) (w : ℕ → ℝ) {n : ℕ} (hn : n ≤ N) (hcut : cutoff n ≤ N) :
    deviation (cutoffWeight N w) n=deviation w n := by
  have hscore : primeScore (cutoffWeight N w) n=primeScore w n := by
    apply sum_congr rfl
    intro p hp
    exact if_pos ⟨Nat.prime_of_mem_primeFactors hp,(Nat.le_of_mem_primeFactors hp).trans hn⟩
  have hcenter : center (cutoffWeight N w) n=center w n := by
    unfold center prefixMean
    apply sum_congr rfl
    intro p hp
    have hpr := (Nat.mem_primesBelow.mp hp).2
    have hpN : p ≤ N := (Nat.le_of_lt_succ (Nat.mem_primesBelow.mp hp).1).trans hcut
    rw [cutoffWeight,if_pos ⟨hpr,hpN⟩]
  simp only [deviation,hscore,hcenter]

lemma deviation_tendsto {w : ℕ → ℝ} {v : ℕ → ℕ → ℝ}
    (hv : ∀ p,Tendsto (fun j => v j p) atTop (nhds (w p))) (n : ℕ) :
    Tendsto (fun j => deviation (v j) n) atTop (nhds (deviation w n)) := by
  apply Tendsto.sub
  · exact tendsto_finset_sum n.primeFactors (fun p _ => hv p)
  · exact tendsto_finset_sum (Nat.primesBelow (cutoff n+1)) (fun p _ => (hv p).div_const _)

lemma spread_tendsto {w : ℕ → ℝ} {v : ℕ → ℕ → ℝ}
    (hv : ∀ p,Tendsto (fun j => v j p) atTop (nhds (w p))) (a b c d : ℕ) :
    Tendsto (fun j => spread (v j) a b c d) atTop (nhds (spread w a b c d)) := by
  have ht (m n : ℕ) := ((deviation_tendsto hv m).sub (deviation_tendsto hv n)).abs
  exact ((ht a b).max (ht a c)).max (((ht a d).max (ht b c)).max ((ht b d).max (ht c d)))

/-- The finite-prefix score coefficients are truncated before compactness.
For each fixed collision its roots AND its four centering cutoffs are eventually
below the testing cutoff, so all centered constraints pass to the limit. -/
theorem uniform_budget_suffices {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (H₀ : ℕ)
    (h : ∀ N : ℕ,∃ w : ℕ → ℝ,prefixEnergy N w ≤ C ∧ FiniteMargin H₀ N ε w) :
    ∃ A : Set ℕ,A.Infinite ∧ 0 < A.lowerDensity ∧ IsSidon ((fun n : ℕ => n^3) '' A) := by
  choose w henergy hmargin using h
  obtain ⟨v,φ,hφ,hv,_,hs⟩ := subsequence hC w henergy
  apply score_suffices v hs hε H₀
  intro a b c d ha hb hc hd haH ha0 hab hbc hcd he
  let M := d+cutoff a+cutoff b+cutoff c+cutoff d
  have hgap : ∀ᶠ j : ℕ in atTop,ε ≤ spread (cutoffWeight (φ j) (w (φ j))) a b c d := by
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop M)] with j hj
    have hdN : d ≤ φ j := by dsimp [M] at hj; omega
    have hca : cutoff a ≤ φ j := by dsimp [M] at hj; omega
    have hcb : cutoff b ≤ φ j := by dsimp [M] at hj; omega
    have hcc : cutoff c ≤ φ j := by dsimp [M] at hj; omega
    have hcd' : cutoff d ≤ φ j := by dsimp [M] at hj; omega
    simp only [spread,deviation_cutoff (φ j) (w (φ j)) ((hab.trans (hbc.trans hcd)).le.trans hdN) hca,
      deviation_cutoff (φ j) (w (φ j)) ((hbc.trans hcd).le.trans hdN) hcb,
      deviation_cutoff (φ j) (w (φ j)) (hcd.le.trans hdN) hcc,
      deviation_cutoff (φ j) (w (φ j)) hdN hcd']
    exact hmargin (φ j) a b c d ha hb hc hd haH hdN ha0 hab hbc hcd he
  exact ge_of_tendsto (spread_tendsto hv a b c d) hgap

#print axioms score_suffices
#print axioms uniform_budget_suffices
end Erdos1206.CenteredScoreCriterion
