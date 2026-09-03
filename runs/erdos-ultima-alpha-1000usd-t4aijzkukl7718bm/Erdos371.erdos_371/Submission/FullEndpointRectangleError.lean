import Submission.AlmostLinearRadicalThreshold
import Submission.RoughHighEndpointEvent

/-! Restoration of the factored mixed rectangle through the full high
endpoint N. The low factor is still restricted to each fixed B-power. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma mixed_high_cutoff_invariant (B D W F A X n : ℕ) (hAX : A ≤ X)
    (hno : ¬∃ g ∈ Icc A X, g ∣ roughRadical W (n*(n+1))) :
    mixedComplementRectangleAt B D W F X n=mixedComplementRectangleAt B D W F A n ∧
      highDivisorWeight W X n=highDivisorWeight W A n := by
  have he (g : ℕ) (hg : g ∈ (roughRadical W (n*(n+1))).divisors) : g ≤ X ↔ g ≤ A := by
    constructor
    · intro hgX
      by_contra h
      exact hno ⟨g,mem_Icc.mpr ⟨by omega,hgX⟩,(Nat.mem_divisors.mp hg).1⟩
    · exact fun hgA => hgA.trans hAX
  constructor
  · unfold mixedComplementRectangleAt
    congr 1
    apply sum_congr rfl
    intro f hf
    apply sum_congr rfl
    intro g hg
    simp only [he g hg]
  · unfold highDivisorWeight
    apply sum_congr rfl
    intro g hg
    simp only [he g hg]

lemma mixed_full_endpoint_point_error (B D W F A k L N n : ℕ)
    (hB : 1 < B) (hW : 1 < W) (hWN : N+1 ≤ W^L)
    (hn : 0 < n) (hnN : n ≤ N) (hF : F ≤ B^k) (hAN : A ≤ N) :
    |mixedComplementRectangleAt B D W F N n-highDivisorWeight W N n*untruncatedComplementPrefix B F n| ≤
      |mixedComplementRectangleAt B D W F A n-highDivisorWeight W A n*untruncatedComplementPrefix B F n|+
      2*(2 : ℝ)^(2*L)*(if ∃ g ∈ Icc A N, g ∣ roughRadical W (n*(n+1)) then
        (2 : ℝ)^(activeBlockPrimes (largePrimeSet B (B^k)) (activePrimeAtoms (largePrimeSet B (B^k)) n)).card else 0) := by
  by_cases he : ∃ g ∈ Icc A N, g ∣ roughRadical W (n*(n+1))
  · rw [if_pos he]
    have ha := mixedComplementRectangleAt_abs_le B D W F N k L N n hB hW hWN hn hnN hF
    have hw := (high_weight_and_complement_bound W L N n B D N hW hWN hn hnN).1
    have hp := (untruncatedComplementPrefix_abs_le B (B^k) k F n hB hn hF le_rfl).trans
      (subsetPolynomial_le_two_pow k _)
    have hprod := mul_le_mul hw hp (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 2^(2*L))
    rw [← abs_mul] at hprod
    have hh := (abs_sub _ _).trans (add_le_add ha hprod)
    linarith [abs_nonneg (mixedComplementRectangleAt B D W F A n-
      highDivisorWeight W A n*untruncatedComplementPrefix B F n)]
  · obtain ⟨hm,hw⟩ := mixed_high_cutoff_invariant B D W F A N n hAN he
    simp only [if_neg he,hm,hw,mul_zero,add_zero,le_refl]

/-- Uniform in all low-factor endpoints F≤B^k, with the high endpoint equal
exactly to N. No moving power q is inserted into a fixed-q estimate. -/
theorem mixed_full_endpoint_mean_error (B H W : ℕ → ℕ) (k L : ℕ) (hL : 0 < L)
    (hBt : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hH : ∀ᶠ N : ℕ in atTop, H N ≤ B N+1)
    (hW : ∀ᶠ N : ℕ in atTop, 1 < W N ∧ N+1 ≤ (W N)^L) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ (B N)^k,
      (∑ n ∈ range N, |mixedComplementRectangleAt (B N) (H N*N) (W N) F N (n+1)-
        highDivisorWeight (W N) N (n+1)*untruncatedComplementPrefix (B N) F (n+1)|)/N < ε := by
  obtain ⟨A,hA,hlogA,hRad⟩ := exists_almost_linear_radical_threshold B H k hBt hB hH
  have herrA := mixedRectangle_mean_error_of_radical B (fun N => H N*N) W A k L hL hBt hB hW hRad
  have hEnd := highEndpoint_indicator_mean_zero A W L hL (hW.mono fun N h => ⟨h.1,(Nat.le_succ N).trans h.2⟩) hA hlogA
  have hExp := short_band_exp_exception_zero B k
    (fun N n => ∃ g ∈ Icc (A N) N, g ∣ roughRadical (W N) ((n+1)*(n+2))) hBt hEnd
  have hBound := hExp.const_mul (2*(2 : ℝ)^(2*L))
  simp only [mul_zero] at hBound
  intro ε hε
  filter_upwards [herrA (ε/2) (by positivity),hBound.eventually_lt_const (show (0 : ℝ) < ε/2 by positivity),
    hBt.eventually_gt_atTop 1,hW,hA] with N ha he hb hw hA
  intro F hF
  have hs := sum_le_sum (s := range N) (fun n hn =>
    mixed_full_endpoint_point_error (B N) (H N*N) (W N) F (A N) k L N (n+1)
      hb hw.1 hw.2 (by omega) (by have := mem_range.mp hn; omega) hF hA.2)
  simp only [sum_add_distrib,← mul_sum,Nat.add_assoc,Nat.reduceAdd] at hs
  have hmean := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div,mul_div_assoc] at hmean
  exact hmean.trans_lt (by linarith [ha F hF])

#print axioms mixed_full_endpoint_mean_error
end Erdos371
