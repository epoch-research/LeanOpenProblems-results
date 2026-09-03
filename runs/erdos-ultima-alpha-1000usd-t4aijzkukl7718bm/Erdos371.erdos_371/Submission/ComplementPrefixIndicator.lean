import Submission.ComplementPrefixArithmetic
import Submission.ShortComplementIndicator

/-! Uniform restoration of the moving size indicator over every prefix
X≤B^k, for each fixed degree k and any growing subpower rough cutoff. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma complementPrefixAt_power (B D k n : ℕ) :
    complementPrefixAt B D (B^k) n=shortRoughComplementAt B D k n := rfl

lemma complementPrefixAt_error_le (B D k X n : ℕ) (hB : 1 < B) (hn : 0 < n) (hX : X ≤ B^k) :
    |complementPrefixAt B D X n-untruncatedComplementPrefix B X n| ≤
      subsetPolynomial k (activePrimeAtoms (largePrimeSet B (B^k)) n).card := by
  have he : complementPrefixAt B D X n-untruncatedComplementPrefix B X n =
      (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
        ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
          if e ≤ B^k then (ArithmeticFunction.moebius e : ℝ)*
            (if e ≤ X then (if D*e < roughRadical B (n*(n+1)) then 0 else
              -divisorSideColour n (roughRadical B (n*(n+1))/e)) else 0) else 0 := by
    unfold complementPrefixAt untruncatedComplementPrefix
    rw [← mul_sub,← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro e _
    by_cases hc : e ≤ B^k
    · by_cases he : e ≤ X <;> by_cases hd : D*e < roughRadical B (n*(n+1)) <;> simp [hc,he,hd]
    · have he : ¬e ≤ X := fun he => hc (he.trans hX)
      simp [hc,he]
  rw [he,abs_mul,roughRadical_moebius_abs,one_mul]
  refine (short_moebius_sum_abs_le B k n hB hn _ ?_).trans
    (subsetPolynomial_mono k (activeBlockPrimes_card_le _ _))
  intro e
  split_ifs <;> simp only [abs_zero,abs_neg,divisorSideColour_abs] <;> norm_num

lemma complementPrefixAt_eq_of_large (B D X n : ℕ)
    (hR : D*X < roughRadical B (n*(n+1))) :
    complementPrefixAt B D X n=untruncatedComplementPrefix B X n := by
  unfold complementPrefixAt untruncatedComplementPrefix
  congr 1
  apply sum_congr rfl
  intro e _
  by_cases he : e ≤ X
  · have hd : D*e < roughRadical B (n*(n+1)) := (Nat.mul_le_mul_left D he).trans_lt hR
    rw [if_pos ⟨he,hd⟩,if_pos he]
  · rw [if_neg (not_and_of_not_left _ he),if_neg he]

lemma complementPrefixAt_error_clip_bound (B D k X R n : ℕ) (hB : 1 < B) (hn : 0 < n) (hX : X ≤ B^k) :
    |complementPrefixAt B D X n-untruncatedComplementPrefix B X n| ≤
      (1+subsetPolynomial k R)*(1-‖roughComplementUnit B (D*B^k) n‖)+
        (if R ≤ (activePrimeAtoms (largePrimeSet B (B^k)) n).card then
          subsetPolynomial k (activePrimeAtoms (largePrimeSet B (B^k)) n).card else 0) := by
  rw [roughComplementUnit_norm]
  by_cases hR : D*B^k < roughRadical B (n*(n+1))
  · rw [if_pos hR,sub_self,mul_zero,zero_add,complementPrefixAt_eq_of_large B D X n ((Nat.mul_le_mul_left D hX).trans_lt hR),
      sub_self,abs_zero]
    split_ifs
    · exact subsetPolynomial_nonneg _ _
    · rfl
  · rw [if_neg hR,sub_zero,mul_one]
    have hb := complementPrefixAt_error_le B D k X n hB hn hX
    split_ifs with hm
    · linarith [subsetPolynomial_nonneg k R]
    · have hh := subsetPolynomial_mono k (show (activePrimeAtoms (largePrimeSet B (B^k)) n).card ≤ R by omega)
      linarith

/-- Along any subpower cutoff tending to infinity, restoring the size
condition has vanishing mean absolute error for every fixed short degree. -/
theorem complementPrefixAt_mean_error_uniform (B H : ℕ → ℕ) (k : ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hHB : ∀ᶠ N in atTop, H N ≤ B N+1) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ X ≤ (B N)^k,
      (∑ n ∈ range N, |complementPrefixAt (B N) (H N*N) X (n+1)-
        untruncatedComplementPrefix (B N) X (n+1)|)/N < ε := by
  intro ε hε
  let M : ℝ := 16*(k+1)
  obtain ⟨R,hR,htail⟩ := prime_pattern_polynomial_tail_shifted k M (ε/2) (by positivity)
  let Q := 1+subsetPolynomial k R
  have hQ : 0 < Q := by dsimp [Q]; linarith [subsetPolynomial_nonneg k R]
  have hunit := short_complement_size_indicator_average_one B H k hBatTop hB hHB
  have hprob : Tendsto (fun N : ℕ => Q*(1-
      (∑ n ∈ range N, ‖roughComplementUnit (B N) ((H N*N)*(B N)^k) (n+1)‖)/N))
      atTop (𝓝 0) := by
    have ht : Tendsto (fun N : ℕ => 1-
      (∑ n ∈ range N, ‖roughComplementUnit (B N) ((H N*N)*(B N)^k) (n+1)‖)/N)
      atTop (𝓝 (1-1 : ℝ)) := tendsto_const_nhds.sub hunit
    simpa only [sub_self,mul_zero] using ht.const_mul Q
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hBatTop)).atTop_div_const
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  filter_upwards [htail,hBatTop.eventually_gt_atTop 1,hlog.eventually_ge_atTop 2,
    subpower_pow_eventually_le B hB k (1/(4*(k+3 : ℝ))) (by positivity),
    hprob.eventually_lt_const (show (0 : ℝ) < ε/2 by positivity),eventually_gt_atTop (0 : ℕ)]
      with N htail hBN hlogN hpN hsmall hN
  intro X hX
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let P := largePrimeSet (B N) ((B N)^k)
  have hmass : 2*∑ p ∈ P, (1 : ℝ)/p ≤ M := short_power_band_mass_upper (B N) k hBN hlogN
  have ht := htail P (by
    intro p hp
    obtain ⟨hpp,_,hpu⟩ := (mem_largePrimeSet_iff p _ _).mp hp
    refine ⟨hpp,?_⟩
    exact ((show (p : ℝ) ≤ ((B N)^k : ℕ) by exact_mod_cast hpu).trans
      (by exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ (B N)) k)).trans hpN) hmass
  have hb := sum_le_sum (s := range N) (fun n _ =>
    complementPrefixAt_error_clip_bound (B N) (H N*N) k X R (n+1) hBN (by omega) hX)
  rw [sum_add_distrib,← mul_sum,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,mul_one] at hb
  have he : (Q*((N : ℝ)-
      ∑ n ∈ range N, ‖roughComplementUnit (B N) ((H N*N)*(B N)^k) (n+1)‖)+
      ∑ n ∈ range N, if R ≤ (activePrimeAtoms P (n+1)).card then
        subsetPolynomial k (activePrimeAtoms P (n+1)).card else 0)/(N : ℝ) =
      Q*(1-(∑ n ∈ range N, ‖roughComplementUnit (B N) ((H N*N)*(B N)^k) (n+1)‖)/N)+
      (∑ n ∈ range N, if R ≤ (activePrimeAtoms P (n+1)).card then
        subsetPolynomial k (activePrimeAtoms P (n+1)).card else 0)/(N : ℝ) := by
    field_simp
  have hbd := div_le_div_of_nonneg_right hb hNr.le
  change (∑ n ∈ range N, |complementPrefixAt (B N) (H N*N) X (n+1)-
      untruncatedComplementPrefix (B N) X (n+1)|)/N ≤ _ at hbd
  change _ ≤ (Q*((N : ℝ)-
      ∑ n ∈ range N, ‖roughComplementUnit (B N) ((H N*N)*(B N)^k) (n+1)‖)+
      ∑ n ∈ range N, if R ≤ (activePrimeAtoms P (n+1)).card then
        subsetPolynomial k (activePrimeAtoms P (n+1)).card else 0)/(N : ℝ) at hbd
  rw [he] at hbd
  linarith

#print axioms complementPrefixAt_mean_error_uniform
end Erdos371
