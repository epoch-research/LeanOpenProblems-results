import Submission.UpperTripleScoreCriterion
import Submission.FinitePrimeEnergyCompactness

/-! Uniform finite reciprocal-prime energy budgets for adaptive upper-triple
spread would suffice. No such uniform bound is asserted. -/
namespace Erdos1206.FiniteUpperTripleScoreCriterion
open Finset Filter FinitePrimeEnergyCompactness UpperTripleScoreCriterion QuadraticPrimeMoments
open scoped Classical Topology

/-- The lower threshold is fixed while the upper cutoff grows. -/
def FiniteMargin (H₀ N : ℕ) (ε : ℝ) (w : ℕ → ℝ) : Prop :=
  ∀ a b c d : ℕ,
    Squarefree a → Squarefree b → Squarefree c → Squarefree d →
    H₀ ≤ b → d ≤ N → 0 < a → a < b → b < c → c < d → a^3+d^3=b^3+c^3 →
      ε ≤ spread w b c d

lemma primeScore_cutoff (N : ℕ) (w : ℕ → ℝ) {n : ℕ} (hn : n ≤ N) :
    primeScore (cutoffWeight N w) n=primeScore w n := by
  apply sum_congr rfl
  intro p hp
  exact if_pos ⟨Nat.prime_of_mem_primeFactors hp,(Nat.le_of_mem_primeFactors hp).trans hn⟩

lemma spread_cutoff (N : ℕ) (w : ℕ → ℝ) {b c d : ℕ}
    (hb : b ≤ N) (hc : c ≤ N) (hd : d ≤ N) :
    spread (cutoffWeight N w) b c d=spread w b c d := by
  simp only [spread,primeScore_cutoff N w hb,primeScore_cutoff N w hc,primeScore_cutoff N w hd]

lemma primeScore_tendsto {w : ℕ → ℝ} {v : ℕ → ℕ → ℝ}
    (hv : ∀ p,Tendsto (fun j => v j p) atTop (nhds (w p))) (n : ℕ) :
    Tendsto (fun j => primeScore (v j) n) atTop (nhds (primeScore w n)) :=
  tendsto_finset_sum n.primeFactors (fun p _ => hv p)

lemma spread_tendsto {w : ℕ → ℝ} {v : ℕ → ℕ → ℝ}
    (hv : ∀ p,Tendsto (fun j => v j p) atTop (nhds (w p))) (b c d : ℕ) :
    Tendsto (fun j => spread (v j) b c d) atTop (nhds (spread w b c d)) := by
  exact ((primeScore_tendsto hv b).sub (primeScore_tendsto hv c)).abs.max
    (((primeScore_tendsto hv b).sub (primeScore_tendsto hv d)).abs.max
      ((primeScore_tendsto hv c).sub (primeScore_tendsto hv d)).abs)

/-- All finite cutoffs must satisfy the SAME energy budget and the SAME
positive spread. A finite optimizer or finitely many cutoffs do not suffice. -/
theorem uniform_budget_suffices {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (H₀ : ℕ)
    (h : ∀ N : ℕ,∃ w : ℕ → ℝ,prefixEnergy N w ≤ C ∧ FiniteMargin H₀ N ε w) :
    ∃ A : Set ℕ,A.Infinite ∧ 0 < A.lowerDensity ∧ IsSidon ((fun n : ℕ => n^3) '' A) := by
  choose w henergy hmargin using h
  obtain ⟨v,φ,hφ,hv,_,hs⟩ := subsequence hC w henergy
  apply score_suffices v hs hε H₀
  intro a b c d ha hb hc hd hbH ha0 hab hbc hcd he
  have hgap : ∀ᶠ j : ℕ in atTop,ε ≤ spread (cutoffWeight (φ j) (w (φ j))) b c d := by
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop d)] with j hj
    rw [spread_cutoff (φ j) (w (φ j)) ((hbc.trans hcd).le.trans hj) (hcd.le.trans hj) hj]
    exact hmargin (φ j) a b c d ha hb hc hd hbH hj ha0 hab hbc hcd he
  exact ge_of_tendsto (spread_tendsto hv b c d) hgap

#print axioms uniform_budget_suffices
end Erdos1206.FiniteUpperTripleScoreCriterion
