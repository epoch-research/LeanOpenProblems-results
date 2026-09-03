import Submission.BuchstabSplitCost

/-! A fully quantitative logarithmic prefix choice. The complete error is
linear in the level at exponent21/10, with an absolute constant. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg
set_option maxHeartbeats 0

noncomputable def splitIndex (L : ℝ) : ℕ := ⌊L/100⌋₊+3

lemma splitIndex_bounds (L : ℝ) (hL : 0 ≤ L) :
    L/100 ≤ (splitIndex L : ℝ) ∧ (splitIndex L : ℝ) ≤ L/100+3 ∧ 3 ≤ splitIndex L := by
  have hlo := Nat.lt_floor_add_one (L/100)
  have hhi := Nat.floor_le (show 0 ≤ L/100 by positivity)
  dsimp only [splitIndex]
  push_cast
  constructor
  · linarith
  constructor
  · linarith
  · trivial

lemma splitIndex_logs (L : ℝ) (hL : 10000 ≤ L) :
    2 ≤ (splitIndex L : ℝ) ∧ 1 ≤ log (splitIndex L : ℝ) ∧
      1 ≤ log L ∧ log L/2 ≤ log (splitIndex L : ℝ) := by
  obtain ⟨hlo,hhi,hthree⟩ := splitIndex_bounds L (by linarith)
  have hthreeR : (3 : ℝ) ≤ splitIndex L := by exact_mod_cast hthree
  have hJpos : (0 : ℝ) < splitIndex L := by linarith
  have hLpos : 0 < L := by linarith
  have hlogJ : 1 ≤ log (splitIndex L : ℝ) := (le_log_iff_exp_le hJpos).mpr (by linarith [exp_one_lt_three])
  have hlogL : 1 ≤ log L := (le_log_iff_exp_le hLpos).mpr (by linarith [exp_one_lt_three])
  have hsq : L ≤ (splitIndex L : ℝ)^2 := by nlinarith only [hL,hlo]
  have hh := log_le_log hLpos hsq
  rw [log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  exact ⟨by linarith,hlogJ,hlogL,by linarith⟩

lemma splitIndex_power (L : ℝ) (hL : 0 ≤ L) :
    (4 : ℝ)^(splitIndex L) ≤ 64*exp (L/50) := by
  have hfloor := Nat.floor_le (show 0 ≤ L/100 by positivity)
  have hlog4 : log (4 : ℝ) ≤ 2 := by
    have hh : log (4 : ℝ) = 2*log 2 := by rw [show (4 : ℝ)=2^2 by norm_num,log_pow]; norm_num
    rw [hh]
    linarith [log_two_lt_d9]
  have he : (4 : ℝ)^⌊L/100⌋₊ ≤ exp (L/50) := by
    rw [← exp_log (by norm_num : (0 : ℝ) < 4),← exp_nat_mul]
    apply exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hlog4 (Nat.cast_nonneg ⌊L/100⌋₊)
    nlinarith only [hfloor,hm]
  unfold splitIndex
  rw [pow_add]
  norm_num only [show (4 : ℝ)^3=64 by norm_num]
  nlinarith only [he]

lemma splitEarlyCost_bound (L : ℝ) (hL : 1 ≤ L) :
    splitEarlyCost (splitIndex L) ≤ 321*L*exp (L/50) := by
  obtain ⟨hlo,hhi,hthree⟩ := splitIndex_bounds L (by linarith)
  have hp := splitIndex_power L (by linarith)
  have he : 1 ≤ exp (L/50) := one_le_exp (by linarith)
  have hc : (splitIndex L : ℝ)+1 ≤ 5*L := by linarith
  have hm := mul_le_mul hc hp (by positivity) (by positivity : 0 ≤ 5*L)
  have hLe : 1 ≤ L*exp (L/50) := one_le_mul_of_one_le_of_one_le hL he
  unfold splitEarlyCost
  nlinarith only [hm,hLe]

lemma split_early_absorption (L : ℝ) (hL : 1000000 ≤ L) (K : ℕ) (hK : (K : ℝ) ≤ exp L) :
    splitEarlyCost (splitIndex L)*(1+(K : ℝ)^2)+(K : ℝ) ≤ exp ((21/10 : ℝ)*L) := by
  have hLp : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hE := splitEarlyCost_bound L hL1
  have he2 : 1 ≤ exp (2*L) := one_le_exp (by positivity)
  have hK2 : (K : ℝ)^2 ≤ exp (2*L) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg K) hK 2
    simpa only [← exp_nat_mul, Nat.cast_ofNat] using hh
  have hKm : 1+(K : ℝ)^2 ≤ 2*exp (2*L) := by linarith
  have hmul := mul_le_mul hE hKm (by positivity) (by positivity : 0 ≤ 321*L*exp (L/50))
  have heprod : exp (L/50)*exp (2*L) = exp ((101/50 : ℝ)*L) := by rw [← exp_add]; congr 1; ring
  have hfirst : splitEarlyCost (splitIndex L)*(1+(K : ℝ)^2) ≤
      642*L*exp ((101/50 : ℝ)*L) := by
    calc
      _ ≤ _ := hmul
      _ = 642*L*(exp (L/50)*exp (2*L)) := by ring
      _ = _ := by rw [heprod]
  have hKe : (K : ℝ) ≤ L*exp ((101/50 : ℝ)*L) := by
    have hh : exp L ≤ exp ((101/50 : ℝ)*L) := exp_le_exp.mpr (by linarith)
    have hm := mul_le_mul_of_nonneg_right hL1 (exp_pos ((101/50 : ℝ)*L)).le
    nlinarith only [hK,hh,hm]
  have hsmall : 643*L ≤ exp ((2/25 : ℝ)*L) := by
    have hh := quadratic_le_exp_of_nonneg (show 0 ≤ (2/25 : ℝ)*L by positivity)
    nlinarith only [hh,hL]
  have hm := mul_le_mul_of_nonneg_right hsmall (exp_pos ((101/50 : ℝ)*L)).le
  have he : exp ((2/25 : ℝ)*L)*exp ((101/50 : ℝ)*L) = exp ((21/10 : ℝ)*L) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he] at hm
  linarith only [hfirst,hKe,hm]

noncomputable def splitLevelConstant : ℝ := 1+256*exp 4*inverseLogSquareConstant*
  (1+(WeightedMertens.reciprocalConstant+2)^2)

lemma splitLevelConstant_pos : 0 < splitLevelConstant := by
  have := inverseLogSquareConstant_pos
  unfold splitLevelConstant
  positivity

lemma split_tail_absorption (L : ℝ) (hL : 1000000 ≤ L) (K : ℕ) (hK : (K : ℝ) ≤ exp L) :
    splitTailCost (splitIndex L)*(1+(prefixReciprocal nthPrime K)^2) ≤ splitLevelConstant-1 := by
  obtain ⟨hJ,hlogJ,hlogL,hloghalf⟩ := splitIndex_logs L (by linarith)
  have hLp : 0 < L := by linarith
  have hlogLp : 0 < log L := by linarith
  have hlogJp : 0 < log (splitIndex L : ℝ) := by linarith
  have hC : 0 ≤ WeightedMertens.reciprocalConstant := by
    have hb := WeightedMertens.boundConstant_pos
    have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have hll2 : log (log (2 : ℝ)) ≤ 0 := log_nonpos hl2.le (by linarith [log_two_lt_d9])
    unfold WeightedMertens.reciprocalConstant
    have he : 0 ≤ 2*(WeightedMertens.boundConstant+1)/log 2 := by positivity
    linarith
  have hlogK : log ((K : ℝ)+2) ≤ 2*L := by
    have he : 2 ≤ exp L := by linarith [add_one_le_exp L]
    have hh := log_le_log (by positivity : 0 < (K : ℝ)+2)
      (show (K : ℝ)+2 ≤ 2*exp L by linarith)
    rw [log_mul (by norm_num) (exp_pos L).ne',log_exp] at hh
    linarith [log_two_lt_d9]
  have hloglogK : log (log ((K : ℝ)+2)) ≤ 1+log L := by
    have hh := log_le_log (log_pos (by have := Nat.cast_nonneg (α := ℝ) K; linarith)) hlogK
    rw [log_mul (by norm_num) hLp.ne'] at hh
    linarith [log_two_lt_d9]
  have hZ := prefixReciprocal_nonneg nthPrime K
  have hZupper : prefixReciprocal nthPrime K ≤ (WeightedMertens.reciprocalConstant+2)*log L := by
    have hh := prefixReciprocal_loglog nthPrime nthPrime_prime nthPrime_strictMono.injective K
    have hm := mul_nonneg (show 0 ≤ WeightedMertens.reciprocalConstant+1 by linarith)
      (show 0 ≤ log L-1 by linarith)
    nlinarith only [hh,hloglogK,hm]
  have hZsq := pow_le_pow_left₀ hZ hZupper 2
  have hlogsq : log L^2 ≤ 4*log (splitIndex L : ℝ)^2 := by nlinarith only [hloghalf,hlogL,hlogJ]
  have hlogone : 1 ≤ log L^2 := one_le_pow₀ hlogL
  have hnum : 1+(prefixReciprocal nthPrime K)^2 ≤
      (1+(WeightedMertens.reciprocalConstant+2)^2)*(4*log (splitIndex L : ℝ)^2) := by
    have hm := mul_le_mul_of_nonneg_left hlogsq
      (show 0 ≤ 1+(WeightedMertens.reciprocalConstant+2)^2 by positivity)
    nlinarith only [hZsq,hlogone,hm]
  have hratio : (1+(prefixReciprocal nthPrime K)^2)/log (splitIndex L : ℝ)^2 ≤
      4*(1+(WeightedMertens.reciprocalConstant+2)^2) := by
    apply (div_le_iff₀ (sq_pos_of_pos hlogJp)).mpr
    nlinarith only [hnum]
  have hI := inverseLogSquareConstant_pos
  have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 64*exp 4*inverseLogSquareConstant by positivity)
  dsimp only [splitTailCost,splitLevelConstant]
  convert hm using 1 <;> ring

/-- An absolute linear error constant at the actual divisor exponent21/10.
The prefix `k ≤ K` is arbitrary. -/
theorem split_complete_error (L : ℝ) (hL : 1000000 ≤ L) (k K : ℕ)
    (hk : k ≤ K) (hK : (K : ℝ) ≤ exp L) :
    lowerErrorStep primeMarginal (primeKeep nthPrime)
      (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 1)
      k (exp ((21/10 : ℝ)*L)) ≤ splitLevelConstant*exp ((21/10 : ℝ)*L) := by
  obtain ⟨hJ,hlogJ,hlogL,hloghalf⟩ := splitIndex_logs L (by linarith)
  have hh := split_lower_one (splitIndex L) k K hk hJ hlogJ (exp ((21/10 : ℝ)*L)) (exp_pos _).le
  have he := split_early_absorption L hL K hK
  have ht := mul_le_mul_of_nonneg_right (split_tail_absorption L hL K hK) (exp_pos ((21/10 : ℝ)*L)).le
  nlinarith only [hh,he,ht]

#print axioms split_complete_error
end Erdos970.RecursiveSieve.Buchstab
