import Submission.QuadraticSubpowerPrimeEdge
import Submission.ShortComplementPattern

/-! Uniform integrability of the actual large-product prime-pair count.
The small-prime cofactor bound controls its unbounded multiplicity. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology
set_option autoImplicit false

lemma primeFactors_above_card_bound (Y K N n : ℕ) (hY : 1 < Y) (hN : N ≤ Y^K) (hn : n ≤ N) :
    (n.primeFactors.filter (fun p => Y<p)).card ≤ K := by
  by_cases hn0 : n=0
  · simp [hn0]
  apply short_prime_product_card_le _ Y K hY
  · intro p hp
    exact (mem_filter.mp hp).2
  · have hd : (∏ p ∈ n.primeFactors.filter (fun p => Y<p), p) ∣ n :=
      (prod_dvd_prod_of_subset _ _ id (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd n)
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd).trans (hn.trans hN)

lemma highMinCrossPrimePairs_card_bound (Y K N n : ℕ) (hY : 1 < Y)
    (hN : N ≤ Y^K) (hn : n < N) : (highMinCrossPrimePairs N Y n).card ≤ K^2 := by
  have hsub : highMinCrossPrimePairs N Y n ⊆
      n.primeFactors.filter (fun p => Y<p) ×ˢ (n+1).primeFactors.filter (fun p => Y<p) := by
    intro pq hpq
    obtain ⟨hpq,hY⟩ := mem_filter.mp hpq
    obtain ⟨hpq,_⟩ := mem_filter.mp hpq
    obtain ⟨hp,hq⟩ := mem_product.mp hpq
    obtain ⟨hYp,hYq⟩ := lt_min_iff.mp hY
    exact mem_product.mpr ⟨mem_filter.mpr ⟨hp,hYp⟩,mem_filter.mpr ⟨hq,hYq⟩⟩
  apply (card_le_card hsub).trans
  rw [card_product,pow_two]
  exact Nat.mul_le_mul (primeFactors_above_card_bound Y K N n hY hN hn.le)
    (primeFactors_above_card_bound Y K N (n+1) hY hN (by omega))

/-- Tail mass of the count itself tends uniformly to zero as the truncation
level grows. This is stronger than a mere bounded first moment. -/
theorem largeCrossPrimePairs_uniform_integrability (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, if M < (largeCrossPrimePairs N n).card
        then ((largeCrossPrimePairs N n).card : ℝ) else 0)/N < ε := by
  have hdecay : Tendsto (fun k : ℕ => (147456*Real.exp 2)/(k+1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (147456*Real.exp 2)).comp (tendsto_add_atTop_nat 1)
  obtain ⟨k,hk,hk80⟩ :=
    ((hdecay.eventually_lt_const (show (0 : ℝ)<ε/2 by positivity)).and
      (eventually_ge_atTop (80 : ℕ))).exists
  let X := rootRoughCutoff k
  have hX : ∀ᶠ N : ℕ in atTop, 1 ≤ X N := (rootRoughCutoff_atTop k).eventually_ge_atTop 1
  have hsmall : ∀ᶠ N : ℕ in atTop, Real.log (X N+1 : ℝ)/Real.log N ≤ 1/40 := by
    filter_upwards [rootRoughCutoff_log_eventually_le k] with N hN
    apply hN.trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<k+1)).mpr
    have hkr : (80 : ℝ) ≤ k := by exact_mod_cast hk80
    linarith
  have hroot : Tendsto (fun N : ℕ => (8 : ℝ)/Real.sqrt N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨2*(k+1)^2,?_⟩
  filter_upwards [smallCrossPrimePairs_eventually_normalized_bound X hX hsmall,
    rootRoughCutoff_log_eventually_le k,(rootRoughCutoff_atTop k).eventually_gt_atTop 1,
    hroot.eventually_lt_const (show (0 : ℝ)<ε/2 by positivity)] with N hbound hlog hX1 hrootN
  have hpoint (n : ℕ) (hn : n ∈ range N) :
      (if 2*(k+1)^2 < (largeCrossPrimePairs N n).card
        then ((largeCrossPrimePairs N n).card : ℝ) else 0) ≤
      2*((smallCrossPrimePairs N (X N) n).card : ℝ) := by
    by_cases hc : 2*(k+1)^2 < (largeCrossPrimePairs N n).card
    · rw [if_pos hc]
      have hcap := highMinCrossPrimePairs_card_bound (X N) (k+1) N n hX1
        (rootRoughCutoff_power k N) (mem_range.mp hn)
      have he := largeCrossPrimePairs_card_partition N (X N) n
      exact_mod_cast (show (largeCrossPrimePairs N n).card ≤ 2*(smallCrossPrimePairs N (X N) n).card by omega)
    · rw [if_neg hc]
      positivity
  have hsum := div_le_div_of_nonneg_right (sum_le_sum hpoint) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  rw [← mul_sum,mul_div_assoc] at hsum
  have hmain := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 73728*Real.exp 2)
  have hfinal : 2*((∑ n ∈ range N, ((smallCrossPrimePairs N (X N) n).card : ℝ))/N) ≤
      147456*Real.exp 2/(k+1 : ℝ)+8/Real.sqrt N := by
    have hb := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2)
    have he : 2*(36864*Real.exp 2*(Real.log (X N+1 : ℝ)/Real.log N)+4/Real.sqrt N) =
      73728*Real.exp 2*(Real.log (X N+1 : ℝ)/Real.log N)+8/Real.sqrt N := by ring
    rw [he] at hb
    exact hb.trans (add_le_add (by convert hmain using 1; ring) le_rfl)
  exact (hsum.trans hfinal).trans_lt (by linarith)

/-- Multiplying this pair count by any uniformly bounded test of vanishing
mean absolute value still gives vanishing mean absolute value. -/
theorem largeCrossPrimePairs_uniform_absolute_continuity (w : ℕ → ℕ → ℝ)
    (hw : ∀ N n, |w N n| ≤ 1)
    (hmean : Tendsto (fun N : ℕ => (∑ n ∈ range N, |w N n|)/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, (largeCrossPrimePairs N n).card*|w N n|)/N) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall (fun N => hε.trans_le (by positivity))
  · intro ε hε
    obtain ⟨M,hM⟩ := largeCrossPrimePairs_uniform_integrability (ε/2) (by positivity)
    have ht := hmean.const_mul (M : ℝ)
    simp only [mul_zero] at ht
    filter_upwards [hM,ht.eventually_lt_const (show (0 : ℝ)<ε/2 by positivity)] with N htail htest
    have hpoint (n : ℕ) (hn : n ∈ range N) :
        (largeCrossPrimePairs N n).card*|w N n| ≤
          (if M < (largeCrossPrimePairs N n).card then ((largeCrossPrimePairs N n).card : ℝ) else 0)+
            M*|w N n| := by
      by_cases hlarge : M < (largeCrossPrimePairs N n).card
      · rw [if_pos hlarge]
        have hb := mul_le_of_le_one_right (Nat.cast_nonneg (largeCrossPrimePairs N n).card) (hw N n)
        have hz : (0 : ℝ) ≤ M*|w N n| := by positivity
        linarith
      · rw [if_neg hlarge,zero_add]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (not_lt.mp hlarge)) (abs_nonneg _)
    have hs := div_le_div_of_nonneg_right (sum_le_sum hpoint) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    rw [sum_add_distrib,← mul_sum,add_div,mul_div_assoc] at hs
    linarith

/-- In particular, every density-zero exceptional set is negligible even
with this unbounded arithmetic multiplicity attached. -/
theorem largeCrossPrimePairs_negligible_exceptional_set
    (Q : ℕ → ℕ → Prop) [∀ N n, Decidable (Q N n)]
    (hQ : Tendsto (fun N : ℕ => (((range N).filter (Q N)).card : ℝ)/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, if Q N n then ((largeCrossPrimePairs N n).card : ℝ) else 0)/N)
      atTop (𝓝 0) := by
  let w : ℕ → ℕ → ℝ := fun N n => if Q N n then 1 else 0
  have hw : ∀ N n, |w N n| ≤ 1 := by
    intro N n
    dsimp only [w]
    split_ifs <;> norm_num
  have hmean : Tendsto (fun N : ℕ => (∑ n ∈ range N, |w N n|)/N) atTop (𝓝 0) := by
    convert hQ using 1
    ext N
    have he (n : ℕ) : |w N n|=(if Q N n then (1 : ℝ) else 0) := by
      dsimp only [w]
      split_ifs <;> norm_num
    simp_rw [he]
    simp
  have ht := largeCrossPrimePairs_uniform_absolute_continuity w hw hmean
  convert ht using 1
  ext N
  congr 1
  apply sum_congr rfl
  intro n hn
  dsimp only [w]
  split_ifs <;> norm_num

#print axioms largeCrossPrimePairs_uniform_integrability
#print axioms largeCrossPrimePairs_uniform_absolute_continuity
end Erdos371
