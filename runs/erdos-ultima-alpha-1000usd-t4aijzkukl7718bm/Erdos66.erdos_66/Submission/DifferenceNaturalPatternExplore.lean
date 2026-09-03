import Submission.ExactBracketPatternHostExplore
import Submission.LocalDifferencePotentialExplore

/-! Local difference matching tests in the natural positive-pattern
interface, with a polynomial code and logarithmic Boolean count bound. -/
namespace Erdos66DifferenceNaturalPattern
open Filter AdditiveCombinatorics Erdos66NaturalPositivePattern Erdos66MatchingNaturalPattern
  Erdos66BernoulliMatchingPolynomial Erdos66DisjointMatchingPolynomial
  Erdos66DifferenceMatching Erdos66LocalDifferencePotential Erdos66FiniteRepBernoulli
  Erdos66FiniteBernoulli Erdos66Fractional Erdos66NaturalPatternRestriction
  Erdos66RarePatternCodeGrowth
open scoped Classical Topology
set_option maxHeartbeats 2400000

noncomputable def differencePattern (N d b : ℕ) : Pattern :=
  matchingPattern (2*N) (edgeClass (2*N) N d b) pairCoords (1/2) (by norm_num)

def differenceCode (N d b : ℕ) : ℕ := Nat.pair 2 (Nat.pair N (Nat.pair d b))

lemma differencePattern_mean (N d b : ℕ) (hd : 0<d) :
    (differencePattern N d b).eval profile ≤ 3*((N : ℝ)+1) := by
  rw [differencePattern,matchingPattern_eval,←matchingPoly_expect]
  simp_rw [matchingPoly_binary_disjoint _ _ (edgeClass_disjoint (2*N) N d b hd),
    ←monomial_sum_eq_count]
  change expect (fun i : Fin (2*N+1) ↦ profile i.val)
    (fun ω ↦ Real.exp ((1/2 : ℝ)*matchingCount (2*N) N d b ω)) ≤ _
  apply (matching_upper_mean (2*N) N d b hd (fun i ↦ profile i.val)
    (fun i ↦ ⟨profile_nonneg _,profile_le_one _⟩)).trans
  have hh := harmonic_matching_mean (2*N) N d b hd
  have hb := harmonic_le_one_add_log (N+1)
  have he : Real.exp (1+Real.log ((N+1 : ℕ) : ℝ))=Real.exp 1*((N : ℝ)+1) := by
    rw [Real.exp_add,Real.exp_log (by positivity)]
    push_cast
    rfl
  have h := (Real.exp_le_exp.mpr (hh.trans hb)).trans_eq he
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith [Real.exp_one_lt_d9]) (by positivity))

lemma differencePattern_value (A : Set ℕ) (N d b : ℕ) (hd : 0<d) :
    (differencePattern N d b).value (fun i ↦ decide (i∈A))=
      Real.exp ((1/2 : ℝ)*matchingCount (2*N) N d b (restrict A (2*N))) := by
  rw [Pattern.value,differencePattern,matchingPattern_eval]
  change matchingPoly _ _ _ (fun i ↦ bit (restrict A (2*N) i))=_
  rw [matchingPoly_binary_disjoint _ _ (edgeClass_disjoint (2*N) N d b hd),←monomial_sum_eq_count]
  rfl

lemma localDiff_restrict (A : Set ℕ) (L N d : ℕ) (hL : 2*N ≤ L+1) :
    localDiff (selected L (restrict A L)) N d=localDiff A N d := by
  rw [selected_restrict,localDiff,localDiff]
  congr 1
  ext a
  simp only [Finset.mem_filter,Finset.mem_range,Set.mem_inter_iff,Set.mem_Iic]
  constructor
  · rintro ⟨ha,hN,hd,⟨h1,_⟩,⟨h2,_⟩⟩
    exact ⟨ha,hN,hd,h1,h2⟩
  · rintro ⟨ha,hN,hd,h1,h2⟩
    exact ⟨ha,hN,hd,⟨h1,by omega⟩,⟨h2,by omega⟩⟩

lemma differenceCode_bound (N d b : ℕ) (hN : 2 ≤ N) (hd : d<N) (hb : b<2) :
    differenceCode N d b+1 ≤ (N+1)^8 := by
  have h1 := pair_succ_le_sq d b (N+1) (by omega) (by omega)
  have h2 := pair_succ_le_pow N (Nat.pair d b) (N+1) 2 (by omega) (by omega) le_rfl h1
  exact pair_succ_le_pow 2 (Nat.pair N (Nat.pair d b)) (N+1) 4
    (by omega) (by omega) (by omega) h2

lemma localDiff_of_pattern_budget (A : Set ℕ) (M N d : ℕ) (hN : 2 ≤ N) (hM : M ≤ N)
    (hd : 0<d) (hbudget : ∀ b<2, d<N →
      (differencePattern N d b).value (fun i ↦ decide (i∈A)) ≤
        ((differenceCode N d b : ℝ)+M+2)^4) :
    (localDiff A N d : ℝ) ≤ 144*Real.log ((N : ℝ)+1) := by
  by_cases hdn : d<N
  · have hbound (b : ℕ) (hb : b<2) :
        matchingCount (2*N) N d b (restrict A (2*N)) ≤ 72*Real.log ((N : ℝ)+1) := by
      have hc := code_shift_bound (differenceCode N d b) M N 8 (by omega) hM (by omega)
        (differenceCode_bound N d b hN hdn hb)
      have hc' : (differenceCode N d b : ℝ)+M+2 ≤ ((N : ℝ)+1)^9 := by exact_mod_cast hc
      have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (differenceCode N d b : ℝ)+M+2) hc' 4
      have hh := hbudget b hb hdn
      rw [differencePattern_value A N d b hd] at hh
      have hl := Real.log_le_log (Real.exp_pos _) (hh.trans hp)
      rw [Real.log_exp,Real.log_pow,Real.log_pow] at hl
      norm_num only [Nat.cast_ofNat] at hl
      linarith
    have he := selected_localDiff (2*N) N d (by omega) (restrict A (2*N))
    rw [localDiff_restrict A (2*N) N d (by omega)] at he
    linarith [hbound 0 (by norm_num),hbound 1 (by norm_num)]
  · rw [localDiff_zero_large A N d (by omega),Nat.cast_zero]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith))

end Erdos66DifferenceNaturalPattern
