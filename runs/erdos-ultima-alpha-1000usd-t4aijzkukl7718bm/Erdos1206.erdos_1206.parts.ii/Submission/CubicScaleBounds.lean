import Submission.CubicSamplingStage

/-! Geometric scales and quantitative hub/moment bounds under a linear
collision-count hypothesis. The hypothesis is not proved for any source. -/
namespace Erdos1206.CubicScaleBounds
open Finset CubicHypergraph HypergraphHubTrimming CubicSamplingStage
open scoped BigOperators Classical

def cutoff (j : ℕ) : ℕ := (2^j)^12
def threshold (j : ℕ) : ℕ := (2^j)^11

lemma cutoff_pos (j : ℕ) : 0 < cutoff j := by unfold cutoff; positivity
lemma cutoff_mono : Monotone cutoff := by
  intro i j hij
  exact Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) hij) _
lemma cutoff_succ (j : ℕ) : cutoff (j+1)=4096*cutoff j := by
  simp only [cutoff,pow_succ (2:ℕ) j,mul_pow]
  norm_num
  ring

lemma cutoff_eq (j : ℕ) : cutoff j=4096^j := by
  dsimp only [cutoff]
  rw [←pow_mul,Nat.mul_comm j 12,pow_mul]
  norm_num

lemma le_cutoff (j : ℕ) : j ≤ cutoff j := by
  exact (Nat.lt_two_pow_self (n := j)).le.trans
    (Nat.le_self_pow (by omega : 12≠0) (2^j))

lemma cutoff_le_iff {i j : ℕ} : cutoff i ≤ cutoff j ↔ i ≤ j := by
  rw [cutoff_eq,cutoff_eq]
  exact Nat.pow_le_pow_iff_right (by norm_num)

/-- Lower bounds on the geometric grid give bounds in every intervening
prefix, with one fixed additive allowance for the initial scales. -/
lemma interpolate (B : Finset ℕ) {j₀ J : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hgrid : ∀ j∈Ico j₀ (J+1), 4*ε*cutoff j ≤ ((B.filter (fun v => v < cutoff j)).card:ℝ)) :
    ∀ n ≤ cutoff J, (ε/1024)*n ≤ ((B.filter (fun v => v < n)).card:ℝ)+(ε/1024)*cutoff j₀ := by
  intro n hn
  by_cases hsmall : n < cutoff j₀
  · have hh : (ε/1024)*(n:ℝ) ≤ (ε/1024)*cutoff j₀ :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hsmall.le) (by positivity)
    linarith [show (0:ℝ) ≤ (B.filter (fun v => v < n)).card by positivity]
  · have hn1 : 1 ≤ n := (cutoff_pos j₀).trans_le (by omega)
    obtain ⟨j,hjn,hnj⟩ := exists_nat_pow_near hn1 (by norm_num : 1 < (4096:ℕ))
    rw [←cutoff_eq] at hjn hnj
    have hj₀ : j₀ ≤ j := by
      by_contra hh
      have hji : j+1 ≤ j₀ := by omega
      have hm := cutoff_mono hji
      omega
    have hjJ : j ≤ J := cutoff_le_iff.mp (hjn.trans hn)
    have hjT : j∈Ico j₀ (J+1) := mem_Ico.mpr ⟨hj₀,by omega⟩
    have hc : (B.filter (fun v => v < cutoff j)).card ≤ (B.filter (fun v => v < n)).card := by
      apply card_le_card
      intro v hv
      exact mem_filter.mpr ⟨(mem_filter.mp hv).1,(mem_filter.mp hv).2.trans_le hjn⟩
    have hnr : (n:ℝ) ≤ 4096*cutoff j := by
      rw [cutoff_succ] at hnj
      exact_mod_cast hnj.le
    have hmul := mul_le_mul_of_nonneg_left hnr (by positivity : 0 ≤ ε/1024)
    have hcr : ((B.filter (fun v => v < cutoff j)).card:ℝ) ≤ (B.filter (fun v => v < n)).card := by exact_mod_cast hc
    have hinit : 0 ≤ (ε/1024)*cutoff j₀ := by positivity
    nlinarith [hgrid j hjT]

lemma hubs_bound (S : Set ℕ) {C j : ℕ}
    (hC : (edges (cutoff j) S).card ≤ C*cutoff j) :
    (hubs (edges (cutoff j) S) (threshold j)).card ≤ 4*C*2^j := by
  have hh := (hubs_card_mul_le (edges (cutoff j) S) (threshold j) 4
    (fun e he => (mem_edges.mp he).2.2.card.le)).trans (Nat.mul_le_mul_left 4 hC)
  have heq : 4*(C*cutoff j)=(4*C*2^j)*threshold j := by
    dsimp only [cutoff,threshold]
    rw [pow_succ (2^j) 11]
    ring
  rw [heq] at hh
  exact Nat.le_of_mul_le_mul_right hh (by dsimp [threshold]; positivity)

lemma bad_bound (S : Set ℕ) {C j : ℕ}
    (hC : (edges (cutoff j) S).card ≤ C*cutoff j) :
    (bad (edges (cutoff j) S) (hubs (edges (cutoff j) S) (threshold j))).card ≤
      (16*C^2*CubicPairCodegree.codegreeConstant)*(2^j)^5 := by
  have hh := bad_card_le (edges (cutoff j) S)
    (hubs (edges (cutoff j) S) (threshold j))
    (CubicPairCodegree.codegreeConstant*(2^j)^3)
    (fun _ _ hxy => pair_codegree_bound S hxy)
  apply hh.trans
  calc
    _ ≤ (4*C*2^j)^2*(CubicPairCodegree.codegreeConstant*(2^j)^3) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (hubs_bound S hC) _)
    _ = _ := by ring

lemma budget_bound (S : Set ℕ) {C j : ℕ} {ε : ℝ}
    (hC : (edges (cutoff j) S).card ≤ C*cutoff j) :
    ((cutoff j:ℝ)+4*(edges (cutoff j) S).card*threshold j)/(ε*cutoff j)^2 ≤
      ((4*C+1:ℝ)/ε^2)*(1/2:ℝ)^j := by
  have hCR : ((edges (cutoff j) S).card:ℝ) ≤ (C:ℝ)*cutoff j := by exact_mod_cast hC
  have ht : (0:ℝ) < (2:ℝ)^j := by positivity
  have ht1 : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have hn : (cutoff j:ℝ)=((2:ℝ)^j)^12 := by simp [cutoff]
  have hd : (threshold j:ℝ)=((2:ℝ)^j)^11 := by simp [threshold]
  rw [hn] at hCR
  rw [hn,hd]
  have hp : ((2:ℝ)^j)^12 ≤ ((2:ℝ)^j)^23 := pow_le_pow_right₀ ht1 (by omega)
  calc
    _ ≤ (((2:ℝ)^j)^12+4*((C:ℝ)*((2:ℝ)^j)^12)*((2:ℝ)^j)^11)/(ε*((2:ℝ)^j)^12)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_right hCR (show 0 ≤ 4*((2:ℝ)^j)^11 by positivity)]
    _ ≤ ((4*C+1:ℝ)*((2:ℝ)^j)^23)/(ε*((2:ℝ)^j)^12)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith only [hp]
    _ = _ := by
      rw [div_pow,mul_pow,div_mul_eq_div_div]
      by_cases hε : ε=0
      · simp [hε]
      · field_simp
        ring

#print axioms bad_bound
#print axioms budget_bound
end Erdos1206.CubicScaleBounds
