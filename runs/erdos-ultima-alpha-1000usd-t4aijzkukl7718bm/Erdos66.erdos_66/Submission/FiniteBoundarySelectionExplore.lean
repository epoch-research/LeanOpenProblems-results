import Submission.BoundaryPairPotentialExplore
import Submission.FiniteTripleIntersectionSelectionExplore

/-! Joint finite ordered rounding with arbitrarily small boundary envelopes
and any budgeted finite family of two-sided representation costs. -/
namespace Erdos66FiniteBoundarySelection
open AdditiveCombinatorics Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli
  Erdos66MatchingPolynomialSelection Erdos66BernoulliMatchingPolynomial
  Erdos66BoundaryPairMean Erdos66BoundaryPairCounts Erdos66BoundaryPairPotential
  Erdos66TripleIntersectionMean Erdos66OrderedPipagePrefix Erdos66Fractional
  Erdos66SummableTailBudget Erdos66FiniteTripleIntersectionSelection
open scoped Classical
set_option maxHeartbeats 2000000

 theorem exists_uniform_boundary_selection : ∃ N₀ : ℕ → ℕ,
    ∀ (L H : ℕ) (κ : Type*) (T : Finset κ) (n : κ → ℕ) (t w : κ → ℝ),
      (∀ k∈T, 0 ≤ w k) →
      (∑ k∈T, w k*(Real.exp (2*|t k|)*expect (fun i : Fin (L+1) ↦ profile i.val)
        (fun σ ↦ Real.exp (t k*(sumRep (selected L σ) (n k) : ℝ))))) ≤ 1/2 →
      ∃ ω : Fin (L+1) → Bool,
        Brackets (fun i ↦ profile i.val) (fun i ↦ bit (ω i)) ∧
        (∑ k∈T, w k*Real.exp (t k*(sumRep (selected L ω) (n k) : ℝ))) ≤ 1 ∧
        (∀ j ≤ H, ∀ n ≤ H, N₀ j ≤ n →
          ((j:ℝ)+1)*((boundary (selected L ω) (cutoff j) n).card:ℝ) ≤ 3*ell n) := by
  have hcut (j : ℕ) : ∃ M : ℕ, ∀ S : Finset ℕ, (∀ n∈S, M ≤ n) →
      (∑ n∈S, boundaryTail n) < (1/2:ℝ)^j/8 :=
    exists_tail_budget _ boundaryTail_summable _ (by positivity)
  choose M hM using hcut
  let N₀ : ℕ → ℕ := fun j ↦ max ((cutoff j)^2) (M j)
  refine ⟨N₀,?_⟩
  intro L H κ T n t w hw hbudget
  let U : Finset (Σ _j : ℕ, ℕ) := (Finset.range (H+1)).sigma (fun j ↦ Finset.Icc (N₀ j) H)
  let p : Fin (L+1) → ℝ := fun i ↦ profile i.val
  let P : (Fin (L+1) → ℝ) → ℝ := fun x ↦
    ∑ q∈U, boundaryWeight q.2*matchingPoly (boundaryPairs L (cutoff q.1) q.2) pairCoords ((q.1:ℝ)+1) x
  let R : (Fin (L+1) → Bool) → ℝ := fun ω ↦
    ∑ k∈T, w k*Real.exp (t k*(sumRep (selected L ω) (n k) : ℝ))
  have hP (x : Fin (L+1) → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ P x :=
    Finset.sum_nonneg (fun q _ ↦ mul_nonneg (boundaryWeight_pos _).le
      (matchingPoly_nonneg _ _ _ (by positivity) x hx))
  have hR (ω : Fin (L+1) → Bool) : 0 ≤ R ω :=
    Finset.sum_nonneg (fun k hk ↦ mul_nonneg (hw k hk) (Real.exp_pos _).le)
  have hmean : P p ≤ 1/4 := by
    dsimp only [P,U]
    simp only [Finset.sum_sigma]
    apply (Finset.sum_le_sum (fun j hj ↦ ?_)).trans (horizon_budget H)
    calc
      _ ≤ ∑ n∈Finset.Icc (N₀ j) H, boundaryTail n := by
        apply Finset.sum_le_sum
        intro n hn
        exact weighted_boundary_mean L j n ((le_max_left _ _).trans (Finset.mem_Icc.mp hn).1)
      _ ≤ (1/2:ℝ)^j/8 := (hM j _ (fun n hn ↦ (le_max_right _ _).trans (Finset.mem_Icc.mp hn).1)).le
  obtain ⟨ω,hbr,hcost⟩ := exists_matching_poly_selection L U
    (fun q ↦ boundaryPairs L (cutoff q.1) q.2) (fun _ ↦ pairCoords)
    (fun q ↦ (q.1:ℝ)+1) (fun q ↦ boundaryWeight q.2)
    (fun q _ ↦ by positivity) (fun q _ ↦ (boundaryWeight_pos _).le)
    T n t w hw p (fun i ↦ ⟨profile_nonneg i.val,profile_le_one i.val⟩)
  have htotal : P (fun i ↦ bit (ω i))+R ω < 1 := by
    exact hcost.trans_lt (by linarith only [hmean,hbudget])
  have hbit (i : Fin (L+1)) : 0 ≤ bit (ω i) := by cases ω i <;> norm_num [bit]
  refine ⟨ω,hbr,by have := hP _ hbit; dsimp only [R] at *; linarith only [htotal,this],?_⟩
  intro j hj n hn hN₀
  let q : Σ _j : ℕ, ℕ := ⟨j,n⟩
  have hq : q∈U := by
    simp only [U,q,Finset.mem_sigma,Finset.mem_range,Finset.mem_Icc]
    exact ⟨by omega,hN₀,hn⟩
  have hsingle := Finset.single_le_sum (s := U) (a := q)
    (f := fun q ↦ boundaryWeight q.2*matchingPoly (boundaryPairs L (cutoff q.1) q.2) pairCoords
      ((q.1:ℝ)+1) (fun i ↦ bit (ω i)))
    (fun q _ ↦ mul_nonneg (boundaryWeight_pos _).le
      (matchingPoly_nonneg _ _ _ (by positivity) _ hbit)) hq
  have hpone : P (fun i ↦ bit (ω i)) < 1 := by have := hR ω; linarith only [htotal,this]
  exact weighted_boundary_bounds_count L j n ω (hsingle.trans_lt hpone)

end Erdos66FiniteBoundarySelection
