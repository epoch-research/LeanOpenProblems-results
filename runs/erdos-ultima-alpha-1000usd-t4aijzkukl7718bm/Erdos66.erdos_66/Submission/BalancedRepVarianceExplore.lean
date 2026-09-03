import Submission.RepVarianceExplore
import Submission.PrefixBalancedTwoSidedSelectionExplore

/-! Variance-sensitive two-sided finite selection retaining every prefix
floor/ceiling bracket. Dependent rounding costs an additive two in each test. -/
namespace Erdos66BalancedRepVariance
open Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli Erdos66RepVariance
  Erdos66PrefixBalancedTwoSidedSelection Erdos66OrderedPipagePrefix
  AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 2200000

/-- Relative to independent Bernoulli concentration, preserving every prefix
bracket costs only an additive two, not a full mean-scale variance charge. -/
theorem exists_prefix_balanced_variance_bound (L : ℕ) (p : Fin (L+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset ℕ) (V : ℕ → ℝ) (ε : ℝ)
    (hε : 0<ε) (hε1 : ε ≤ 1) (hV : ∀ n∈S, repVarianceProxy L n p ≤ V n)
    (hsmall : (∑ n∈S, 2*Real.exp (-ε^2*V n/8))<1) :
    ∃ ω, Brackets p (fun i ↦ bit (ω i)) ∧
      ∀ n∈S, |(sumRep (selected L ω) n:ℝ)-repMean L n p|<ε*V n+2 := by
  let t : ℝ := ε/4
  have ht : 0<t := by dsimp [t]; positivity
  have htbound : |t| ≤ 1/2 := by rw [abs_of_pos ht]; dsimp [t]; linarith
  let T : Finset (ℕ × Bool) := S ×ˢ Finset.univ
  let τ : ℕ × Bool → ℝ := fun z ↦ if z.2 then t else -t
  let W : ℕ × Bool → ℝ := fun z ↦ Real.exp (-τ z*repMean L z.1 p-t*(ε*V z.1+2))
  have htabs (z : ℕ × Bool) : |τ z|=t := by
    dsimp [τ]
    cases z.2 <;> simp only [Bool.false_eq_true,if_false,if_true,abs_neg,abs_of_pos ht]
  have hmgf (z : ℕ × Bool) (hz : z∈T) :
      expect p (fun ω ↦ Real.exp (τ z*((sumRep (selected L ω) z.1:ℝ)-repMean L z.1 p))) ≤
        Real.exp (2*(τ z)^2*V z.1) := by
    exact (rep_variance_mgf L z.1 p hp (τ z) (by rw [htabs]; rw [abs_of_pos ht] at htbound; exact htbound)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hV z.1 (Finset.mem_product.mp hz).1) (by positivity)))
  have hterm (z : ℕ × Bool) (hz : z∈T) :
      W z*(Real.exp (2*|τ z|)*expect p
        (fun ω ↦ Real.exp (τ z*(sumRep (selected L ω) z.1:ℝ)))) ≤
      Real.exp (-ε^2*V z.1/8) := by
    have he (ω : Fin (L+1) → Bool) :
        Real.exp (τ z*(sumRep (selected L ω) z.1:ℝ))=
        Real.exp (τ z*repMean L z.1 p)*
          Real.exp (τ z*((sumRep (selected L ω) z.1:ℝ)-repMean L z.1 p)) := by
      rw [←Real.exp_add]; congr 1; ring
    simp_rw [he]
    rw [expect_const_mul,htabs]
    have hw : W z*Real.exp (2*t)*Real.exp (τ z*repMean L z.1 p)=Real.exp (-t*ε*V z.1) := by
      dsimp [W]
      rw [←Real.exp_add,←Real.exp_add]
      congr 1
      ring
    rw [←mul_assoc,←mul_assoc,hw]
    have hh := mul_le_mul_of_nonneg_left (hmgf z hz) (Real.exp_pos (-t*ε*V z.1)).le
    apply hh.trans_eq
    rw [←Real.exp_add]
    congr 1
    have hs : (τ z)^2=t^2 := by
      dsimp [τ]
      cases z.2 <;> simp
    rw [hs]
    dsimp [t]
    ring
  obtain ⟨ω,hbr,hcost⟩ := exists_prefix_balanced_selection L p hp T Prod.fst τ W
    (fun z _ ↦ (Real.exp_pos _).le)
  have htotal : (∑ z∈T, W z*Real.exp (τ z*(sumRep (selected L ω) z.1:ℝ)))<1 := by
    apply hcost.trans_lt
    apply (Finset.sum_le_sum hterm).trans_lt
    simpa only [T,Finset.sum_product,Finset.sum_const,Finset.card_univ,Fintype.card_bool,
      nsmul_eq_mul,Nat.cast_ofNat] using hsmall
  have hsingle (n : ℕ) (hn : n∈S) (b : Bool) :
      τ (n,b)*((sumRep (selected L ω) n:ℝ)-repMean L n p)-t*(ε*V n+2)<0 := by
    have hh := (Finset.single_le_sum (s := T) (a := (n,b))
      (f := fun z ↦ W z*Real.exp (τ z*(sumRep (selected L ω) z.1:ℝ)))
      (fun z _ ↦ mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (Finset.mem_product.mpr ⟨hn,Finset.mem_univ _⟩)).trans_lt htotal
    dsimp only [W] at hh
    rw [←Real.exp_add,Real.exp_lt_one_iff] at hh
    nlinarith only [hh]
  refine ⟨ω,hbr,fun n hn ↦ ?_⟩
  have h₀ := hsingle n hn false
  have h₁ := hsingle n hn true
  simp only [τ,Bool.false_eq_true,if_false,if_true] at h₀ h₁
  rw [abs_lt]
  constructor <;> nlinarith only [h₀,h₁,ht]

end Erdos66BalancedRepVariance
