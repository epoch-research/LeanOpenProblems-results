import Submission.ResidueProfileProjectionExplore
import Submission.SharpCapRoundingObstructionExplore
import Submission.ScaledFractionalTailExplore

/-! The fractional continuation of a prescribed prefix. Bounded prefix
discrepancy controls its mixed error uniformly, and gives an absolutely
vanishing far-future bias. The transition quadratic error remains explicit. -/
namespace Erdos66HybridPrefixPrediction
open Filter AdditiveCombinatorics Erdos66Fractional Erdos66Generating
  Erdos66Rounding Erdos66ResidueProfileProjection Erdos66SharpCapRoundingObstruction
open scoped Topology Classical
set_option maxHeartbeats 1700000

/-- Summation by parts for a nonnegative increasing weight, requiring only
prefix bounds up to the finite endpoint in question. -/
lemma monotone_weighted_prefix_bound (w p : ℕ → ℝ) (D : ℝ) (hD : 0≤D)
    (hp : ∀ n, 0≤p n) (hm : Monotone p) (N : ℕ)
    (hw : ∀ k≤N, |∑ j∈Finset.range k, w j|≤D) :
    |∑ j∈Finset.range N, w j*p j|≤2*D*p N := by
  rw [weighted_prefix_identity]
  have hsteps : (∑ j∈Finset.range N, (p (j+1)-p j))=p N-p 0 := by
    have hh := sum_steps p N
    have hn := congrArg Neg.neg hh
    simpa only [←Finset.sum_neg_distrib,neg_sub] using hn
  calc
    _ ≤ |(∑ j∈Finset.range N, w j)*p N|+
        |∑ j∈Finset.range N, (∑ k∈Finset.range (j+1), w k)*(p j-p (j+1))| :=
      abs_add_le _ _
    _ ≤ D*p N+∑ j∈Finset.range N, D*(p (j+1)-p j) := by
      apply add_le_add
      · rw [abs_mul,abs_of_nonneg (hp N)]
        exact mul_le_mul_of_nonneg_right (hw N le_rfl) (hp N)
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul,abs_of_nonpos (sub_nonpos.mpr (hm (Nat.le_succ j)))]
        have hh := mul_le_mul_of_nonneg_right (hw (j+1) (by
          have := Finset.mem_range.mp hj; omega)) (sub_nonneg.mpr (hm (Nat.le_succ j)))
        convert hh using 1 <;> ring
    _ = D*(2*p N-p 0) := by rw [←Finset.mul_sum,hsteps]; ring
    _ ≤ _ := by nlinarith [mul_nonneg hD (hp 0)]

noncomputable def prefixError (A : Set ℕ) (N i : ℕ) : ℝ :=
  if i<N then roundingError A i else 0

noncomputable def hybrid (A : Set ℕ) (N i : ℕ) : ℝ :=
  if i<N then indicator A i else profile i

lemma hybrid_bounds (A : Set ℕ) (N i : ℕ) : 0≤hybrid A N i ∧ hybrid A N i≤1 := by
  unfold hybrid
  split_ifs
  · exact ⟨indicator_nonneg A i,indicator_le_one A i⟩
  · exact ⟨profile_nonneg i,profile_le_one i⟩

lemma hybrid_eq_profile_add_error (A : Set ℕ) (N : ℕ) :
    hybrid A N=fun i ↦ profile i+prefixError A N i := by
  funext i
  simp only [hybrid,prefixError,roundingError]
  split_ifs <;> ring

/-- Exact predictive decomposition, with no discarded quadratic term. -/
theorem hybrid_decomposition (A : Set ℕ) (N n : ℕ) :
    sumConv (hybrid A N) (hybrid A N) n=(harmonic (n+1):ℝ)+
      2*sumConv (prefixError A N) profile n+
        sumConv (prefixError A N) (prefixError A N) n := by
  rw [hybrid_eq_profile_add_error,sumConv_add_self,profile_convolution,
    sumConv_comm_real profile]

lemma prefix_error_mixed_eq (A : Set ℕ) (N n : ℕ) (hN : N≤n+1) :
    sumConv (prefixError A N) profile n=
      ∑ i∈Finset.range N, roundingError A i*profile (n-i) := by
  unfold sumConv
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    _ = ∑ i∈Finset.range (n+1), if i<N then roundingError A i*profile (n-i) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [prefixError,ite_mul,zero_mul]
    _ = _ := by
      rw [←Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter,Finset.mem_range]
      omega

/-- The prescribed old discrepancy is the only hypothesis on A. The
bound is independent of the number of selected old points. -/
theorem prefix_error_mixed_bound (A : Set ℕ) (N n : ℕ) (hN : N≤n)
    (D : ℝ) (hD : 0≤D)
    (hbal : ∀ k≤N, |∑ i∈Finset.range k, roundingError A i|≤D) :
    |sumConv (prefixError A N) profile n|≤2*D*profile (n-N) := by
  rw [prefix_error_mixed_eq A N n (by omega)]
  exact monotone_weighted_prefix_bound (roundingError A) (fun i ↦ profile (n-i)) D hD
    (fun i ↦ profile_nonneg _) (fun i j hij ↦ profile_antitone (by omega)) N hbal

lemma prefix_error_self_zero (A : Set ℕ) (N n : ℕ) (hn : 2*N≤n+1) :
    sumConv (prefixError A N) (prefixError A N) n=0 := by
  apply Finset.sum_eq_zero
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  change (if ij.1<N then roundingError A ij.1 else 0)*
    (if ij.2<N then roundingError A ij.2 else 0)=0
  split_ifs <;> first | omega | ring

/-- At a transition target the unresolved predictive error is exactly the
truncated quadratic error, up to a controlled, small mixed term. -/
theorem transition_bias_control (A : Set ℕ) (N n : ℕ) (hN : N≤n)
    (D : ℝ) (hD : 0≤D)
    (hbal : ∀ k≤N, |∑ i∈Finset.range k, roundingError A i|≤D) :
    |(sumConv (hybrid A N) (hybrid A N) n-(harmonic (n+1):ℝ))-
      sumConv (prefixError A N) (prefixError A N) n|≤4*D*profile (n-N) := by
  rw [hybrid_decomposition]
  have hh := mul_le_mul_of_nonneg_left (prefix_error_mixed_bound A N n hN D hD hbal)
    (by norm_num : (0:ℝ)≤2)
  have he : ((harmonic (n+1):ℝ)+2*sumConv (prefixError A N) profile n+
      sumConv (prefixError A N) (prefixError A N) n-(harmonic (n+1):ℝ))-
      sumConv (prefixError A N) (prefixError A N) n=2*sumConv (prefixError A N) profile n := by ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith

/-- Beyond twice the cutoff, the old quadratic error vanishes exactly. -/
theorem far_future_bias_bound (A : Set ℕ) (N n : ℕ) (hn : 2*N≤n)
    (D : ℝ) (hD : 0≤D)
    (hbal : ∀ k≤N, |∑ i∈Finset.range k, roundingError A i|≤D) :
    |sumConv (hybrid A N) (hybrid A N) n-(harmonic (n+1):ℝ)|≤4*D*profile (n/2) := by
  have hb := transition_bias_control A N n (by omega) D hD hbal
  rw [prefix_error_self_zero A N n (by omega),sub_zero] at hb
  have hm : profile (n-N)≤profile (n/2) := profile_antitone (by omega)
  exact hb.trans (mul_le_mul_of_nonneg_left hm (by positivity))

/-- The far-future bound tends to zero absolutely, uniformly over all
balanced prescribed prefixes whose cutoff is at most half the target. -/
theorem uniform_far_future_prediction (D : ℝ) (hD : 0≤D) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (A : Set ℕ) (N : ℕ), 2*N≤n →
      (∀ k≤N, |∑ i∈Finset.range k, roundingError A i|≤D) →
      |sumConv (hybrid A N) (hybrid A N) n-(harmonic (n+1):ℝ)|<ε := by
  have hdiv : Tendsto (fun n : ℕ ↦ n/2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (2*b)] with n hn
    omega
  have hl := (profile_tendsto_zero.comp hdiv).const_mul (4*D)
  simp only [mul_zero,Function.comp_def] at hl
  filter_upwards [hl.eventually_lt_const hε] with n hn A N hN hbal
  exact (far_future_bias_bound A N n hN D hD hbal).trans_lt hn


section FiniteMeans
open Erdos66FiniteRepBernoulli

lemma finite_mean_eq_conv_diag (p : ℕ → ℝ) (L n : ℕ) (hn : n≤L) :
    repMean L n (fun i ↦ p i.val)=sumConv p p n+diagCorrection L n (fun i ↦ p i.val) := by
  rw [mean_decomposition,pairs_sum_range L n (fun i j ↦ p i*p j),sumConv,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_pos (by have := Finset.mem_range.mp hi; omega)]

lemma hybrid_diag_bound (A : Set ℕ) (N L n : ℕ) (hN : N≤n/2) :
    0≤diagCorrection L n (fun i ↦ hybrid A N i.val) ∧
      diagCorrection L n (fun i ↦ hybrid A N i.val)≤profile (n/2) := by
  have hlo := (diagCorrection_bounds L n (fun i ↦ hybrid A N i.val)
    (fun i ↦ hybrid_bounds A N i.val)).1
  refine ⟨hlo,?_⟩
  let S := (halfPairs L n).filter (fun a ↦ a.1=a.2)
  have hval (a : Fin (L+1)×Fin (L+1)) (ha : a∈S) : a.1.val=n/2 := by
    obtain ⟨ha,he⟩ := Finset.mem_filter.mp ha
    have hs := (mem_halfPairs.mp ha).1
    have he' := congrArg Fin.val he
    omega
  have hcard : S.card≤1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha1 := hval a ha
    have hb1 := hval b hb
    have ha2 := congrArg Fin.val (Finset.mem_filter.mp ha).2
    have hb2 := congrArg Fin.val (Finset.mem_filter.mp hb).2
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  have hterm (a : Fin (L+1)×Fin (L+1)) (ha : a∈S) :
      hybrid A N a.1.val-(hybrid A N a.1.val)^2≤profile (n/2) := by
    rw [hval a ha,hybrid,if_neg (by omega)]
    nlinarith [sq_nonneg (profile (n/2))]
  have hh := Finset.sum_le_sum hterm
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  have hc : (S.card:ℝ)≤1 := by exact_mod_cast hcard
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hc (profile_nonneg (n/2))])

/-- Actual finite Bernoulli representation means, including their diagonal
correction, have uniformly vanishing absolute far-future predictive bias. -/
theorem far_future_bernoulli_mean_bound (A : Set ℕ) (N L n : ℕ)
    (hn : n≤L) (hN : 2*N≤n) (D : ℝ) (hD : 0≤D)
    (hbal : ∀ k≤N, |∑ i∈Finset.range k, roundingError A i|≤D) :
    |repMean L n (fun i ↦ hybrid A N i.val)-(harmonic (n+1):ℝ)|≤
      (4*D+1)*profile (n/2) := by
  rw [finite_mean_eq_conv_diag _ L n hn]
  have hb := far_future_bias_bound A N n hN D hD hbal
  have hd := hybrid_diag_bound A N L n (by omega)
  rw [abs_le] at hb ⊢
  constructor <;> nlinarith [profile_nonneg (n/2)]

theorem uniform_far_future_bernoulli_mean (D : ℝ) (hD : 0≤D) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (A : Set ℕ) (N L : ℕ), n≤L → 2*N≤n →
      (∀ k≤N, |∑ i∈Finset.range k, roundingError A i|≤D) →
      |repMean L n (fun i ↦ hybrid A N i.val)-(harmonic (n+1):ℝ)|<ε := by
  have hdiv : Tendsto (fun n : ℕ ↦ n/2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (2*b)] with n hn
    omega
  have hl := (profile_tendsto_zero.comp hdiv).const_mul (4*D+1)
  simp only [mul_zero,Function.comp_def] at hl
  filter_upwards [hl.eventually_lt_const hε] with n hn A N L hL hN hbal
  exact (far_future_bernoulli_mean_bound A N L n hL hN D hD hbal).trans_lt hn


/-- There is no Bernoulli diagonal correction in the first window: the
only possible diagonal coordinate belongs to the already fixed old prefix. -/
lemma transition_diag_zero (A : Set ℕ) (N L n : ℕ) (hn : n<2*N) :
    diagCorrection L n (fun i ↦ hybrid A N i.val)=0 := by
  apply Finset.sum_eq_zero
  intro a ha
  obtain ⟨ha,he⟩ := Finset.mem_filter.mp ha
  have hs := (mem_halfPairs.mp ha).1
  have he' := congrArg Fin.val he
  have hlow : a.1.val<N := by omega
  dsimp only
  rw [hybrid,if_pos hlow]
  simp only [indicator]
  split_ifs <;> norm_num

/-- For actual finite Bernoulli means in the first transition window, the
lookahead quadratic error is the whole remaining bias up to the small
linear discrepancy bound. -/
theorem transition_bernoulli_bias_control (A : Set ℕ) (N L n : ℕ)
    (hn : n≤L) (hN : N≤n) (hhigh : n<2*N) (D : ℝ) (hD : 0≤D)
    (hbal : ∀ k≤N, |∑ i∈Finset.range k, roundingError A i|≤D) :
    |(repMean L n (fun i ↦ hybrid A N i.val)-(harmonic (n+1):ℝ))-
      sumConv (prefixError A N) (prefixError A N) n|≤4*D*profile (n-N) := by
  rw [finite_mean_eq_conv_diag _ L n hn,transition_diag_zero A N L n hhigh,add_zero]
  exact transition_bias_control A N n hN D hD hbal

end FiniteMeans
end Erdos66HybridPrefixPrediction
