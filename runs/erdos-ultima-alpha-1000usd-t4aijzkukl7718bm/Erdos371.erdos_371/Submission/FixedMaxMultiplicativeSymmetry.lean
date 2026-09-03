import Submission.FixedPrimeAvoidanceSkew

/-! A fixed finite-range max-multiplicative function has reversible two-point
natural means. The function is fixed before taking the endpoint to infinity;
this theorem is not uniform over moving prime cutoffs. -/
namespace Erdos371.FixedPrimeAvoidance
open Finset Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

private def MeanZero (f : ℕ → ℝ) : Prop :=
  Tendsto (fun N : ℕ => (∑ n ∈ range N, f n)/N) atTop (𝓝 0)

private lemma MeanZero.sub {f g : ℕ → ℝ} (hf : MeanZero f) (hg : MeanZero g) :
    MeanZero (fun n => f n-g n) := by
  simpa only [MeanZero,sum_sub_distrib,sub_div,sub_zero] using Filter.Tendsto.sub hf hg

private lemma MeanZero.const_mul {f : ℕ → ℝ} (hf : MeanZero f) (c : ℝ) :
    MeanZero (fun n => c*f n) := by
  simpa only [MeanZero,← mul_sum,mul_div_assoc,mul_zero] using Filter.Tendsto.const_mul c hf

private lemma MeanZero.congr_eventually {f g : ℕ → ℝ} (hf : MeanZero f) (he : f =ᶠ[atTop] g) :
    MeanZero g := by
  have hd : Tendsto (fun n => g n-f n) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    simp only [hn,sub_self]
  have hh := hf.add hd.cesaro
  simp only [add_zero] at hh
  change Tendsto _ atTop (𝓝 0)
  convert hh using 1
  ext N
  simp only [sum_sub_distrib,← div_eq_inv_mul]
  ring

private def ReversalPair (f g : ℕ → ℝ) : Prop := MeanZero (pairSkew f g)

private lemma ReversalPair.sub_left {f g h : ℕ → ℝ}
    (hf : ReversalPair f h) (hg : ReversalPair g h) :
    ReversalPair (fun n => f n-g n) h := by
  have he : pairSkew (fun n => f n-g n) h = fun n => pairSkew f h n-pairSkew g h n := by
    funext n
    simp only [pairSkew]
    ring
  unfold ReversalPair
  rw [he]
  exact hf.sub hg

private lemma ReversalPair.sub_right {f g h : ℕ → ℝ}
    (hg : ReversalPair f g) (hh : ReversalPair f h) :
    ReversalPair f (fun n => g n-h n) := by
  have he : pairSkew f (fun n => g n-h n) = fun n => pairSkew f g n-pairSkew f h n := by
    funext n
    simp only [pairSkew]
    ring
  unfold ReversalPair
  rw [he]
  exact hg.sub hh

private lemma ReversalPair.congr_pos {f g f' g' : ℕ → ℝ}
    (h : ReversalPair f g) (hf : ∀ n, 0 < n → f n=f' n) (hg : ∀ n, 0 < n → g n=g' n) :
    ReversalPair f' g' := by
  apply MeanZero.congr_eventually h
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [pairSkew,hf n hn,hg n hn,hf (n+1) (by omega),hg (n+1) (by omega)]

lemma max_label_le_iff_prime_factors (L : ℕ → ℕ) (hL1 : L 1=0)
    (hL : ∀ a b, 0 < a → 0 < b → L (a*b)=max (L a) (L b)) (t : ℕ) :
    ∀ n, 0 < n → (L n ≤ t ↔ ∀ p, p.Prime → p ∣ n → L p ≤ t) := by
  apply induction_on_primes
  · intro hn
    omega
  · intro _
    simp only [hL1,Nat.zero_le,true_iff]
    intro p hp hd
    exact (hp.not_dvd_one hd).elim
  · intro p a hp ih hpa
    have ha : 0 < a := by
      cases a with
      | zero => simp at hpa
      | succ a => omega
    rw [hL p a hp.pos ha,max_le_iff,ih ha]
    constructor
    · rintro ⟨hpL,haL⟩ q hq hd
      rcases hq.dvd_mul.mp hd with hqp | hqa
      · have he := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
        simpa only [he] using hpL
      · exact haL q hq hqa
    · intro h
      refine ⟨h p hp (dvd_mul_right p a),?_⟩
      intro q hq hqa
      exact h q hq (dvd_mul_of_dvd_right hqa p)

noncomputable def thresholdIndicator (L : ℕ → ℕ) (t n : ℕ) : ℝ := if L n ≤ t then 1 else 0
noncomputable def levelIndicator (L : ℕ → ℕ) (t n : ℕ) : ℝ := if L n=t then 1 else 0

lemma threshold_eq_avoid (L : ℕ → ℕ) (hL1 : L 1=0)
    (hL : ∀ a b, 0 < a → 0 < b → L (a*b)=max (L a) (L b))
    (t n : ℕ) (hn : 0 < n) :
    thresholdIndicator L t n = avoid {p | t < L p} n := by
  unfold thresholdIndicator avoid
  have he : L n ≤ t ↔ ∀ p, p.Prime → p ∈ {p | t < L p} → ¬p ∣ n := by
    rw [max_label_le_iff_prime_factors L hL1 hL t n hn]
    constructor
    · intro h p hp hpt hd
      exact (h p hp hd).not_gt hpt
    · intro h p hp hd
      by_contra ht
      exact h p hp (by simpa using ht) hd
  simp only [he]

private lemma max_threshold_reversal (L : ℕ → ℕ) (hL1 : L 1=0)
    (hL : ∀ a b, 0 < a → 0 < b → L (a*b)=max (L a) (L b)) (s t : ℕ) :
    ReversalPair (thresholdIndicator L s) (thresholdIndicator L t) :=
  ReversalPair.congr_pos (fixed_avoidance_skew_tendsto {p | s < L p} {p | t < L p})
    (fun n hn => (threshold_eq_avoid L hL1 hL s n hn).symm)
    (fun n hn => (threshold_eq_avoid L hL1 hL t n hn).symm)

lemma level_zero (L : ℕ → ℕ) : levelIndicator L 0 = thresholdIndicator L 0 := by
  funext n
  simp [levelIndicator,thresholdIndicator]

lemma level_succ (L : ℕ → ℕ) (a : ℕ) :
    levelIndicator L (a+1) = fun n => thresholdIndicator L (a+1) n-thresholdIndicator L a n := by
  funext n
  simp only [levelIndicator,thresholdIndicator]
  split_ifs <;> (first | omega | norm_num)

private lemma max_level_reversal (L : ℕ → ℕ) (hL1 : L 1=0)
    (hL : ∀ a b, 0 < a → 0 < b → L (a*b)=max (L a) (L b)) (a b : ℕ) :
    ReversalPair (levelIndicator L a) (levelIndicator L b) := by
  cases a with
  | zero =>
    rw [level_zero]
    cases b with
    | zero => rw [level_zero]; exact max_threshold_reversal L hL1 hL 0 0
    | succ b =>
      rw [level_succ]
      exact (max_threshold_reversal L hL1 hL 0 (b+1)).sub_right (max_threshold_reversal L hL1 hL 0 b)
  | succ a =>
    rw [level_succ]
    cases b with
    | zero =>
      rw [level_zero]
      exact (max_threshold_reversal L hL1 hL (a+1) 0).sub_left (max_threshold_reversal L hL1 hL a 0)
    | succ b =>
      rw [level_succ]
      exact ((max_threshold_reversal L hL1 hL (a+1) (b+1)).sub_right
        (max_threshold_reversal L hL1 hL (a+1) b)).sub_left
        ((max_threshold_reversal L hL1 hL a (b+1)).sub_right (max_threshold_reversal L hL1 hL a b))

lemma finite_label_skew_expansion (L : ℕ → ℕ) (Q : ℕ) (hQ : ∀ n, L n ≤ Q)
    (C : ℕ → ℕ → ℝ) (hC : ∀ a b, C b a = -C a b) (n : ℕ) :
    2*C (L n) (L (n+1)) = ∑ a ∈ range (Q+1), ∑ b ∈ range (Q+1),
      C a b*pairSkew (levelIndicator L a) (levelIndicator L b) n := by
  simp only [pairSkew,levelIndicator,mul_sub,sum_sub_distrib,mul_ite,mul_one,mul_zero,
    sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_range,Nat.lt_succ_iff,hQ,if_true]
  rw [hC]
  ring

/-- Every bounded antisymmetric observable of a FIXED finite-range
max-multiplicative label has zero natural mean. No uniformity in L is asserted. -/
theorem fixed_max_multiplicative_skew_tendsto (L : ℕ → ℕ) (Q : ℕ) (hQ : ∀ n, L n ≤ Q)
    (hL1 : L 1=0) (hL : ∀ a b, 0 < a → 0 < b → L (a*b)=max (L a) (L b))
    (C : ℕ → ℕ → ℝ) (hC : ∀ a b, C b a = -C a b) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, C (L n) (L (n+1)))/N) atTop (𝓝 0) := by
  have ht := tendsto_finset_sum (range (Q+1)) (fun a _ =>
    tendsto_finset_sum (range (Q+1)) (fun b _ =>
      (max_level_reversal L hL1 hL a b).const_mul (C a b)))
  simp only [sum_const_zero] at ht
  have hs : MeanZero (fun n => 2*C (L n) (L (n+1))) := by
    change Tendsto _ atTop (𝓝 0)
    convert ht using 1
    ext N
    simp only [← sum_div]
    congr 1
    simp_rw [finite_label_skew_expansion L Q hQ C hC]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    rw [sum_comm]
  have hh := hs.const_mul (1/2)
  simpa only [MeanZero,one_div,← mul_assoc,inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),one_mul] using hh

#print axioms fixed_max_multiplicative_skew_tendsto
end Erdos371.FixedPrimeAvoidance
