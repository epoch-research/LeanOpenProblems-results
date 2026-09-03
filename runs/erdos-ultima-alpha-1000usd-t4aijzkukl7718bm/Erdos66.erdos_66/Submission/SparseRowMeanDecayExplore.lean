import Submission.SparseRowConvolutionBoundsExplore
import Submission.NaturalScaleRankWindowExplore
import Submission.InsertionMatchingPatternExplore

/-! Vanishing natural-scale row counts imply a simultaneous sublogarithmic
insertion, provided the actual profile has the stated central row covers. -/
namespace Erdos66SparseRowMeanDecay
open Filter AdditiveCombinatorics Erdos66FractionalFourthPower Erdos66Fractional Erdos66Generating Erdos66Rounding
  Erdos66ClampedPrefixContinuation Erdos66SparseRowConvolutionBounds
  Erdos66BoundaryPairMean Erdos66TripleIntersectionMean Erdos66CumulativeRoundingError
  Erdos66InsertionMatchingPattern
open scoped Classical Topology
set_option maxHeartbeats 3600000

lemma log_size_atTop : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ)+2)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_atTop_mono
    (fun n ↦ le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2)) tendsto_natCast_atTop_atTop)

lemma quotient_profile_bound (n d : ℕ) (hd : 1 ≤ d) (hl : 1 ≤ Real.log ((n : ℝ)+2)) :
    profile (n/d^2)*Real.sqrt (((n : ℝ)+1)*Real.log ((n : ℝ)+2)) ≤
      2*(d : ℝ)*Real.log ((n : ℝ)+2) := by
  let m := n/d^2
  let L := Real.log ((n : ℝ)+2)
  have hL : 0 ≤ L := by dsimp only [L]; linarith
  have hdp : 0<d^2 := by positivity
  have hn : n+1 ≤ d^2*(m+1) := by
    have hmod := Nat.mod_lt n hdp
    have he := Nat.mod_add_div n (d^2)
    dsimp only [m]
    nlinarith
  have hn' : (n : ℝ)+1 ≤ (d : ℝ)^2*((m : ℝ)+1) := by exact_mod_cast hn
  have hm : m ≤ n := Nat.div_le_self _ _
  have hH := harmonic_le_one_add_log (m+1)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ)<((m+1 : ℕ) : ℝ))
    (show ((m+1 : ℕ) : ℝ) ≤ (n : ℝ)+2 by exact_mod_cast (show m+1 ≤ n+2 by omega))
  have hp := profile_square_bound m
  push_cast at hp
  have hp' : ((m : ℝ)+1)*(profile m)^2 ≤ 2*L := by
    dsimp only [L]
    linarith
  have hb : ((n : ℝ)+1)*(profile m)^2 ≤ 2*(d : ℝ)^2*L := by
    have hh := mul_le_mul_of_nonneg_right hn' (sq_nonneg (profile m))
    have hh' := mul_le_mul_of_nonneg_left hp' (sq_nonneg (d : ℝ))
    nlinarith only [hh,hh']
  have hsq : (profile m*Real.sqrt (((n : ℝ)+1)*L))^2 ≤ (2*(d : ℝ)*L)^2 := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    have hh := mul_le_mul_of_nonneg_right hb hL
    nlinarith only [hh,show 0 ≤ (d : ℝ)^2*L^2 by positivity]
  exact le_of_sq_le_sq hsq (by positivity)

lemma sparse_quotient_profile_decay (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n)
    (hdec : Tendsto (fun n : ℕ ↦ R n/Real.sqrt (((n : ℝ)+1)*Real.log ((n : ℝ)+2))) atTop (𝓝 0))
    (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n : ℕ ↦ profile (n/d^2)*R n/Real.log ((n : ℝ)+2)) atTop (𝓝 0) := by
  have hh := hdec.const_mul (2*(d : ℝ))
  simp only [mul_zero] at hh
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n ↦
    div_nonneg (mul_nonneg (profile_nonneg _) (hR n))
      (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)))) ?_ hh
  filter_upwards [log_size_atTop.eventually_ge_atTop 1] with n hn
  have hL : 0<Real.log ((n : ℝ)+2) := by linarith
  have hs : 0<Real.sqrt (((n : ℝ)+1)*Real.log ((n : ℝ)+2)) := by positivity
  have hp := (div_le_iff₀ hL).mpr (quotient_profile_bound n d hd hn)
  have hb := mul_le_mul_of_nonneg_right hp (div_nonneg (hR n) hs.le)
  convert hb using 1; field_simp

/-- A finite cover of the middle by constant-height rows. Rows may be
truncated at the two middle endpoints. Their total mass and total height
are both charged explicitly. -/
def HasCentralRows (q : ℕ → ℝ) (n m : ℕ) (C R : ℝ) : Prop :=
  ∃ (J : Finset ℕ) (a b : ℕ → ℕ) (c : ℕ → ℝ),
    (∀ j∈J, 0 ≤ c j) ∧
    (∀ j∈J, m ≤ a j ∧ a j ≤ b j ∧ b j ≤ n+1-m) ∧
    (∀ i∈Finset.Ico m (n+1-m), q i ≤ ∑ j∈J, if i∈Finset.Ico (a j) (b j) then c j else 0) ∧
    (∑ j∈J, c j*(b j-a j : ℕ)) ≤ 2*R ∧ (∑ j∈J, c j) ≤ C*profile m*R

lemma row_insertion_mean_bound (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i) (C R : ℝ) (hC : 0 ≤ C)
    (hqp : ∀ i, q i ≤ C*profile i) (n d : ℕ) (hd : 2 ≤ d)
    (hmass : mass q (n+1) ≤ 2*R) (hrow : HasCentralRows q n (n/d^2) C R) :
    2*sumConv q (indicator A) n+sumConv q q n+1 ≤
      (4*C+2*C^2)*boundaryMean d n+16*C+1+(4+6*C)*profile (n/d^2)*R := by
  obtain ⟨J,a,b,c,hc,hj,hcover,hM,hH⟩ := hrow
  have hm := quotient_half d n hd
  have hmid := central_rows_bound A hbr q n (n/d^2) J a b c hc hj (by omega) hcover
  have hmid' : (∑ i∈Finset.Ico (n/d^2) (n+1-n/d^2), q i*indicator A (n-i)) ≤
      (2+2*C)*profile (n/d^2)*R := by
    have hh := mul_le_mul_of_nonneg_left hM (profile_nonneg (n/d^2))
    nlinarith only [hmid,hh,hH]
  have hmix := mixed_three_parts_bound A hbr q C hC hqp n d hd
  have hself := self_three_parts_bound q hq C hC hqp n d hd
  have hh := mul_le_mul_of_nonneg_left hmass (mul_nonneg hC (profile_nonneg (n/d^2)))
  nlinarith only [hmix,hself,hmid',hh]

lemma row_insertion_mean_decay (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i) (C : ℝ) (hC : 0 ≤ C)
    (hqp : ∀ i, q i ≤ C*profile i) (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n)
    (hdec : Tendsto (fun n : ℕ ↦ R n/Real.sqrt (((n : ℝ)+1)*Real.log ((n : ℝ)+2))) atTop (𝓝 0))
    (hmass : ∀ᶠ n : ℕ in atTop, mass q (n+1) ≤ 2*R n)
    (hrow : ∀ d ≥ 2, ∀ᶠ n : ℕ in atTop, HasCentralRows q n (n/d^2) C (R n)) :
    Tendsto (fun n : ℕ ↦
      (2*sumConv q (indicator A) n+sumConv q q n+1)/Real.log ((n : ℝ)+2)) atTop (𝓝 0) := by
  let K := 32*C+16*C^2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hn0 (n : ℕ) : 0 ≤ 2*sumConv q (indicator A) n+sumConv q q n+1 := by
    have hmix : 0 ≤ sumConv q (indicator A) n :=
      Finset.sum_nonneg (fun ij _ ↦ mul_nonneg (hq _) (indicator_nonneg A _))
    have hself : 0 ≤ sumConv q q n := Finset.sum_nonneg (fun ij _ ↦ mul_nonneg (hq _) (hq _))
    linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hdlim : Tendsto (fun d : ℕ ↦ K/(d : ℝ)) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop K
  obtain ⟨d,hd,hdε⟩ := ((eventually_ge_atTop 2).and (hdlim.eventually_lt_const (half_pos hε))).exists
  have hdp : (0 : ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hrest := ((log_size_atTop.const_div_atTop (16*C+1)).add
    ((sparse_quotient_profile_decay R hR hdec d (by omega)).const_mul (4+6*C))).const_add (K/d)
  simp only [mul_zero,add_zero] at hrest
  have hrest' : ∀ᶠ n : ℕ in atTop,
      K/d+(16*C+1)/Real.log ((n : ℝ)+2)+
        (4+6*C)*(profile (n/d^2)*R n/Real.log ((n : ℝ)+2)) < ε := by
    have hh := hrest.eventually_lt_const (show K/(d : ℝ)<ε by linarith)
    simpa only [add_assoc] using hh
  filter_upwards [hrest',hmass,hrow d hd,eventually_ge_atTop (d^2),
    log_size_atTop.eventually_ge_atTop 1] with n hsmall hm hr hn hlog
  have hL : 0<Real.log ((n : ℝ)+2) := by linarith
  have hb := boundaryMean_bound d n hd hn
  have hlog' : Real.log ((n : ℝ)+1) ≤ Real.log ((n : ℝ)+2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hell : ell n ≤ 2*Real.log ((n : ℝ)+2) := by dsimp only [ell]; linarith
  have hbb : boundaryMean d n ≤ 8/(d : ℝ)*Real.log ((n : ℝ)+2) := by
    have hh := mul_le_mul_of_nonneg_left hell (show 0 ≤ 4/(d : ℝ) by positivity)
    convert hb.trans hh using 1; ring
  have hmain := row_insertion_mean_bound A hbr q hq C (R n) hC hqp n d hd hm hr
  have hmain' : 2*sumConv q (indicator A) n+sumConv q q n+1 ≤
      K/(d : ℝ)*Real.log ((n : ℝ)+2)+(16*C+1)+(4+6*C)*profile (n/d^2)*R n := by
    have hh := mul_le_mul_of_nonneg_left hbb (show 0 ≤ 4*C+2*C^2 by positivity)
    have he : (4*C+2*C^2)*(8/(d : ℝ)*Real.log ((n : ℝ)+2))=
        K/(d : ℝ)*Real.log ((n : ℝ)+2) := by dsimp only [K]; ring
    rw [he] at hh
    linarith only [hmain,hh]
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (hn0 n) hL.le)]
  have hfinal := div_le_div_of_nonneg_right hmain' hL.le
  have he : (K/(d : ℝ)*Real.log ((n : ℝ)+2)+(16*C+1)+(4+6*C)*profile (n/d^2)*R n)/
      Real.log ((n : ℝ)+2)=K/d+(16*C+1)/Real.log ((n : ℝ)+2)+
        (4+6*C)*(profile (n/d^2)*R n/Real.log ((n : ℝ)+2)) := by field_simp
  rw [he] at hfinal
  exact hfinal.trans_lt hsmall

 theorem exists_sparse_row_insertion (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hqA : ∀ i∈A, q i=0)
    (C : ℝ) (hC : 0 ≤ C) (hqp : ∀ i, q i ≤ C*profile i)
    (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n)
    (hdec : Tendsto (fun n : ℕ ↦ R n/Real.sqrt (((n : ℝ)+1)*Real.log ((n : ℝ)+2))) atTop (𝓝 0))
    (hmass : ∀ᶠ n : ℕ in atTop, mass q (n+1) ≤ 2*R n)
    (hrow : ∀ d ≥ 2, ∀ᶠ n : ℕ in atTop, HasCentralRows q n (n/d^2) C (R n)) :
    ∃ F : Set ℕ, Disjoint F A ∧ (∀ L, PrefixBrackets q F L) ∧ (∀ i∈F, q i≠0) ∧
      Tendsto (fun n : ℕ ↦ ((sumRep (A∪F) n : ℝ)-(sumRep A n : ℝ))/
        Real.log ((n : ℝ)+2)) atTop (𝓝 0) :=
  exists_sublog_insertion A q hq hqA
    (row_insertion_mean_decay A hbr q (fun i ↦ (hq i).1) C hC hqp R hR hdec hmass hrow)

end Erdos66SparseRowMeanDecay
