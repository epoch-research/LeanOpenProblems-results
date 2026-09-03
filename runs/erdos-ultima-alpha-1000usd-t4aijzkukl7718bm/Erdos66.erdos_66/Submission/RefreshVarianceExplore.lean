import Submission.RefreshAlgebraExplore
import Submission.RepVarianceExplore

/-! A finite noise bound for independently refreshing Boolean membership.
The concentration budget is a hypothesis, not an unconditional repair. -/
namespace Erdos66RefreshVariance
open Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli Erdos66BernoulliConcentration
  Erdos66RefreshAlgebra Erdos66RepVariance AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1600000

lemma pair_survival (L : ℕ) (θ : ℝ) (a : Fin (L+1) → Bool) (p : Fin (L+1) → ℝ)
    (hθ : 0 ≤ θ ∧ θ ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (b : Fin (L+1) × Fin (L+1)) :
    (1-θ)^2*monomial (pairCoords b) a ≤ ∏ i∈pairCoords b, blend θ a p i := by
  have hb (i : Fin (L+1)) : (1-θ)*bit (a i) ≤ blend θ a p i := by
    dsimp [blend]
    exact le_add_of_nonneg_right (mul_nonneg hθ.1 (hp i).1)
  have hbit (i : Fin (L+1)) : 0 ≤ bit (a i) := by cases a i <;> norm_num [bit]
  have hs : 0 ≤ 1-θ := sub_nonneg.mpr hθ.2
  have hq := blend_bounds θ a p hθ hp
  by_cases he : b.1=b.2
  · simp only [pairCoords,he,Finset.insert_eq_of_mem (Finset.mem_singleton_self _),
      Finset.prod_singleton,monomial]
    have ht : (1-θ)^2 ≤ 1-θ := by nlinarith [hθ.1,hθ.2]
    exact (mul_le_mul_of_nonneg_right ht (hbit b.2)).trans (hb b.2)
  · have hm := mul_le_mul (hb b.1) (hb b.2) (mul_nonneg hs (hbit b.2)) (hq b.1).1
    rw [pair_monomial]
    simp only [pairCoords]
    rw [Finset.prod_insert (show b.1∉({b.2}:Finset (Fin (L+1))) by simpa using he),
      Finset.prod_singleton]
    nlinarith only [hm]

lemma variance_binary_comparison (u β b : ℝ)
    (hb : b=0 ∨ b=1) (hkeep : β*b ≤ u) :
    u*(1-u) ≤ u+(1-2*β)*b := by
  rcases hb with rfl | rfl
  · nlinarith [sq_nonneg u]
  · nlinarith [sq_nonneg (1-u)]

/-- A useful sharper proxy before expanding the refreshed mean. -/
lemma refresh_variance_mean_bound (L n : ℕ) (θ : ℝ) (a : Fin (L+1) → Bool)
    (p : Fin (L+1) → ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    repVarianceProxy L n (blend θ a p) ≤ repMean L n (blend θ a p)+
      (1-2*(1-θ)^2)*(sumRep (selected L a) n:ℝ) := by
  have hh := Finset.sum_le_sum (s := halfPairs L n) (fun b hb ↦
    mul_le_mul_of_nonneg_left
      (variance_binary_comparison (∏ i∈pairCoords b, blend θ a p i) ((1-θ)^2)
        (monomial (pairCoords b) a)
        (monomial_binary _ _) (pair_survival L θ a p hθ hp b)) (pairWeight_bounds b).1)
  rw [selected_rep]
  simpa only [repVarianceProxy,repMean,mul_add,Finset.sum_add_distrib,
    Finset.mul_sum,mul_assoc,mul_left_comm] using hh

/-- In particular the noise proxy is proportional to theta, with old/old,
old/profile, profile/profile and diagonal terms all displayed. -/
lemma refresh_variance_bound (L n : ℕ) (θ : ℝ) (a : Fin (L+1) → Bool)
    (p : Fin (L+1) → ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    repVarianceProxy L n (blend θ a p) ≤ θ*((2-θ)*(sumRep (selected L a) n:ℝ)+
      2*(1-θ)*pairConv L n (fun i ↦ bit (a i)) p+θ*pairConv L n p p+1) := by
  have hh := refresh_variance_mean_bound L n θ a p hθ hp
  rw [refresh_mean] at hh
  have hd := (refresh_diag_bounds L n θ a p hθ hp).2
  nlinarith only [hh,hd]

/-- One finite partial refresh with an explicit noise criterion. No assumption
of independent representation counts at different targets is used. -/
theorem exists_refresh (L : ℕ) (θ : ℝ) (a : Fin (L+1) → Bool)
    (p : Fin (L+1) → ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ℕ) (V : ℕ → ℝ) (ε : ℝ) (hε : 0<ε) (hε1 : ε ≤ 1)
    (hV : ∀ n∈S, θ*((2-θ)*(sumRep (selected L a) n:ℝ)+
      2*(1-θ)*pairConv L n (fun i ↦ bit (a i)) p+θ*pairConv L n p p+1) ≤ V n)
    (hsmall : (∑ n∈S, 2*Real.exp (-ε^2*V n/8))<1) :
    ∃ ω, 0<weight (blend θ a p) ω ∧ ∀ n∈S,
      |(sumRep (selected L ω) n:ℝ)-repMean L n (blend θ a p)|<ε*V n := by
  exact exists_rep_variance_bound L _ (blend_bounds θ a p hθ hp) S V ε hε hε1
    (fun n hn ↦ (refresh_variance_bound L n θ a p hθ hp).trans (hV n hn)) hsmall

end Erdos66RefreshVariance
