import Submission.MatchingPolynomialSelectionExplore
import Submission.TripleIntersectionPotentialExplore
import Submission.SummableTailBudgetExplore

/-! Joint finite selection of polynomial-horizon triple-intersection bounds,
ordered prefix brackets, and compensated two-sided representation costs. -/
namespace Erdos66FiniteTripleIntersectionSelection
open Filter AdditiveCombinatorics Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli
  Erdos66MatchingPolynomialSelection Erdos66BernoulliMatchingPolynomial
  Erdos66TripleIntersectionGeometry Erdos66TripleIntersectionMean
  Erdos66TripleIntersectionPotential Erdos66OrderedPipagePrefix
  Erdos66Fractional Erdos66SummableTailBudget
open scoped Classical Topology
set_option maxHeartbeats 2400000

lemma horizon_budget (H : ℕ) : (∑ h∈Finset.range (H+1), (1/2:ℝ)^h/8) ≤ 1/4 := by
  have hs := (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)).div_const 8
  have hh := hs.sum_le_tsum (Finset.range (H+1)) (fun h _ ↦ by positivity)
  rw [tsum_div_const,tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)] at hh
  norm_num at hh ⊢
  exact hh

abbrev Test := Σ _h : ℕ, Σ _N : ℕ, ℕ × ℕ

 theorem exists_uniform_triple_selection : ∃ N₀ : ℕ → ℕ, (∀ h, 1 ≤ N₀ h) ∧
    ∀ (L H : ℕ) (κ : Type*) (T : Finset κ) (n : κ → ℕ) (t w : κ → ℝ),
      (∀ k∈T, 0 ≤ w k) →
      (∑ k∈T, w k*(Real.exp (2*|t k|)*expect (fun i : Fin (L+1) ↦ profile i.val)
        (fun σ ↦ Real.exp (t k*(sumRep (selected L σ) (n k) : ℝ))))) ≤ 1/2 →
      ∃ ω : Fin (L+1) → Bool,
        Brackets (fun i ↦ profile i.val) (fun i ↦ bit (ω i)) ∧
        (∑ k∈T, w k*Real.exp (t k*(sumRep (selected L ω) (n k) : ℝ))) ≤ 1 ∧
        (∀ h ≤ H, ∀ N ≤ H, ∀ n z, N₀ h ≤ N → n ≤ 4*N → z ≤ N^h →
          (realized (triples L N n z) coords ω).card ≤ 36*(h+4)) := by
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp eventually_weighted_triple_mean
  have hcut (h : ℕ) : ∃ M : ℕ, ∀ S : Finset ℕ, (∀ N∈S, M ≤ N) →
      (∑ N∈S, rowTail N) < (1/2:ℝ)^h/8 :=
    exists_tail_budget _ rowTail_summable _ (by positivity)
  choose M hM using hcut
  let N₀ : ℕ → ℕ := fun h ↦ max 1 (max N₁ (M h))
  have hN₀ (h : ℕ) : 1 ≤ N₀ h := le_max_left _ _
  refine ⟨N₀,hN₀,?_⟩
  intro L H κ T n t w hw hbudget
  let U : Finset Test := (Finset.range (H+1)).sigma (fun h ↦
    (Finset.Icc (N₀ h) H).sigma (fun N ↦ (Finset.range (4*N+1)) ×ˢ (Finset.range (N^h+1))))
  let p : Fin (L+1) → ℝ := fun i ↦ profile i.val
  let P : (Fin (L+1) → ℝ) → ℝ := fun x ↦
    ∑ q∈U, tripleWeight q.1 q.2.1*matchingPoly
      (triples L q.2.1 q.2.2.1 q.2.2.2) coords (tilt q.2.1) x
  let R : (Fin (L+1) → Bool) → ℝ := fun ω ↦
    ∑ k∈T, w k*Real.exp (t k*(sumRep (selected L ω) (n k) : ℝ))
  have hP (x : Fin (L+1) → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ P x :=
    Finset.sum_nonneg (fun q _ ↦ mul_nonneg (tripleWeight_pos _ _).le
      (matchingPoly_nonneg _ _ _ (tilt_nonneg _) x hx))
  have hR (ω : Fin (L+1) → Bool) : 0 ≤ R ω :=
    Finset.sum_nonneg (fun k hk ↦ mul_nonneg (hw k hk) (Real.exp_pos _).le)
  have hmean : P p ≤ 1/4 := by
    dsimp only [P,U]
    simp only [Finset.sum_sigma,Finset.sum_product]
    apply (Finset.sum_le_sum (fun h hh ↦ ?_)).trans (horizon_budget H)
    calc
      _ ≤ ∑ N∈Finset.Icc (N₀ h) H, rowTail N := by
        apply Finset.sum_le_sum
        intro N hN
        have hN₁' : N₁ ≤ N :=
          (le_max_left N₁ (M h)).trans ((le_max_right 1 _).trans (Finset.mem_Icc.mp hN).1)
        calc
          _ ≤ ∑ n∈Finset.range (4*N+1), ∑ z∈Finset.range (N^h+1),
              Real.exp 1/((N:ℝ)+1)^(h+4) := by
            apply Finset.sum_le_sum
            intro n hn
            apply Finset.sum_le_sum
            intro z hz
            exact hN₁ N hN₁' L h n z (by have := Finset.mem_range.mp hn; omega)
          _ = ((4*N+1:ℕ):ℝ)*(N^h+1:ℕ)*(Real.exp 1/((N:ℝ)+1)^(h+4)) := by
            simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_assoc]
          _ ≤ rowTail N := target_count_weight h N
      _ ≤ (1/2:ℝ)^h/8 := (hM h _ (fun N hN ↦
        (le_max_right N₁ (M h)).trans ((le_max_right 1 _).trans (Finset.mem_Icc.mp hN).1))).le
  obtain ⟨ω,hbr,hcost⟩ := exists_matching_poly_selection L U
    (fun q ↦ triples L q.2.1 q.2.2.1 q.2.2.2) (fun _ ↦ coords)
    (fun q ↦ tilt q.2.1) (fun q ↦ tripleWeight q.1 q.2.1)
    (fun q _ ↦ tilt_nonneg _) (fun q _ ↦ (tripleWeight_pos _ _).le)
    T n t w hw p (fun i ↦ ⟨profile_nonneg i.val,profile_le_one i.val⟩)
  have htotal : P (fun i ↦ bit (ω i))+R ω < 1 := by
    exact hcost.trans_lt (by linarith only [hmean,hbudget])
  have hbit (i : Fin (L+1)) : 0 ≤ bit (ω i) := by cases ω i <;> norm_num [bit]
  refine ⟨ω,hbr,by have := hP _ hbit; dsimp only [R] at *; linarith only [htotal,this],?_⟩
  intro h hh N hN n z hN₀' hn hz
  let q : Test := ⟨h,N,n,z⟩
  have hq : q∈U := by
    simp only [U,q,Finset.mem_sigma,Finset.mem_range,Finset.mem_Icc,Finset.mem_product]
    exact ⟨by omega,⟨hN₀',hN⟩,by omega,by omega⟩
  have hsingle := Finset.single_le_sum (s := U) (a := q)
    (f := fun q ↦ tripleWeight q.1 q.2.1*matchingPoly
      (triples L q.2.1 q.2.2.1 q.2.2.2) coords (tilt q.2.1) (fun i ↦ bit (ω i)))
    (fun q _ ↦ mul_nonneg (tripleWeight_pos _ _).le
      (matchingPoly_nonneg _ _ _ (tilt_nonneg _) _ hbit)) hq
  have hpone : P (fun i ↦ bit (ω i)) < 1 := by have := hR ω; linarith only [htotal,this]
  exact weighted_cost_bounds_count L h N n z (by have := (hN₀ h).trans hN₀'; omega) ω
    (hsingle.trans_lt hpone)

end Erdos66FiniteTripleIntersectionSelection
