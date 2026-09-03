import Submission.ClampedPrefixContinuationExplore

/-! Finite selection with an arbitrary prescribed bracketed prefix and no
accumulation of the bracket allowance. Tail budgets remain explicit. -/
namespace Erdos66BracketPreservingExtension
open AdditiveCombinatorics Erdos66Generating Erdos66Rounding
  Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli Erdos66OrderedPipagePrefix
  Erdos66PrefixBalancedUpperLimit Erdos66HybridPrefixPrediction
  Erdos66ClampedPrefixContinuation Erdos66BalancedRepVariance Erdos66RepVariance
open scoped Classical
set_option maxHeartbeats 2200000

lemma unit_mul_sub_bound (a b c d : ℝ) (ha : 0≤ a ∧ a≤ 1) (hd : 0≤ d ∧ d≤ 1) :
    |a*b-c*d|≤ |a-c|+|b-d| := by
  have he : a*b-c*d=a*(b-d)+(a-c)*d := by ring
  rw [he]
  calc
    _ ≤ |a*(b-d)|+|(a-c)*d| := abs_add_le _ _
    _ = a*|b-d|+|a-c| *d := by rw [abs_mul,abs_mul,abs_of_nonneg ha.1,abs_of_nonneg hd.1]
    _ ≤ _ := by nlinarith [abs_nonneg (a-c),abs_nonneg (b-d)]

lemma unit_prod_sub_bound {ι : Type*} (S : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i, 0≤ p i ∧ p i≤ 1) (hq : ∀ i, 0≤ q i ∧ q i≤ 1) :
    |(∏ i∈S, p i)-(∏ i∈S, q i)|≤ ∑ i∈S, |p i-q i| := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.sum_insert hi]
    have hprod : 0≤ (∏ i∈S, q i) ∧ (∏ i∈S, q i)≤ 1 :=
      ⟨Finset.prod_nonneg (fun i _ ↦ (hq i).1),
        Finset.prod_le_one (fun i _ ↦ (hq i).1) (fun i _ ↦ (hq i).2)⟩
    exact (unit_mul_sub_bound _ _ _ _ (hp i) hprod).trans (by linarith)

/-- Every target is a matching, so changing total probability mass by d
changes its representation mean by at most 2d. -/
theorem repMean_l1_bound (L n : ℕ) (p q : Fin (L+1) → ℝ)
    (hp : ∀ i, 0≤ p i ∧ p i≤ 1) (hq : ∀ i, 0≤ q i ∧ q i≤ 1) :
    |repMean L n p-repMean L n q|≤ 2*∑ i, |p i-q i| := by
  rw [repMean,repMean,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a∈halfPairs L n,
        |pairWeight a*(∏ i∈pairCoords a, p i)-pairWeight a*(∏ i∈pairCoords a, q i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a∈halfPairs L n, 2*∑ i∈pairCoords a, |p i-q i| := by
      apply Finset.sum_le_sum
      intro a ha
      rw [←mul_sub,abs_mul,abs_of_nonneg (pairWeight_bounds a).1]
      exact mul_le_mul (pairWeight_bounds a).2 (unit_prod_sub_bound _ p q hp hq)
        (abs_nonneg _) (by norm_num)
    _ = 2*∑ i∈(halfPairs L n).biUnion pairCoords, |p i-q i| := by
      rw [Finset.sum_biUnion (pairCoords_disjoint L n),Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_univ_sum_of_nonneg (fun i ↦ abs_nonneg (p i-q i))) (by norm_num)

lemma sum_fin_eq_mass (L : ℕ) (f : ℕ → ℝ) : (∑ i : Fin (L+1), f i.val)=mass f (L+1) := by
  have ht : (Finset.univ.filter (fun i : Fin (L+1) ↦ i.val<L+1))=Finset.univ := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
    exact i.isLt
  have hh := pref_fin_sum L (L+1) le_rfl f
  unfold pref at hh
  rw [ht] at hh
  exact hh

lemma selected_pref (L : ℕ) (ω : Fin (L+1) → Bool) (k : ℕ) (hk : k≤ L+1) :
    pref (fun i ↦ bit (ω i)) k=mass (indicator (selected L ω)) k := by
  have he : (fun i : Fin (L+1) ↦ bit (ω i))=
      (fun i : Fin (L+1) ↦ indicator (selected L ω) i.val) := by
    funext i
    simp only [indicator,mem_selected,bit]
  rw [he,pref_fin_sum L k hk]
  rfl

lemma rounded_old_mass (p : ℕ → ℝ) (A : Set ℕ) (N L : ℕ)
    (ω : Fin (L+1) → Bool)
    (hbr : Brackets (fun i ↦ continuation p A N i.val) (fun i ↦ bit (ω i)))
    (k : ℕ) (hkN : k≤ N) (hkL : k≤ L+1) :
    mass (indicator (selected L ω)) k=mass (indicator A) k := by
  have hb := hbr k
  rw [selected_pref L ω k hkL,pref_fin_sum L k hkL] at hb
  change (⌊mass (continuation p A N) k⌋:ℝ)≤ _ ∧ _≤ (⌈mass (continuation p A N) k⌉:ℝ) at hb
  rw [mass_continuation,clampMass_of_le p A N k hkN] at hb
  obtain ⟨m,hm⟩ := old_mass_integer A k
  rw [hm,Int.floor_natCast,Int.ceil_natCast] at hb
  rw [hm]
  exact le_antisymm hb.2 hb.1

/-- Prefix brackets preserve every old Boolean bit, not just old mass. -/
theorem rounded_old_membership (p : ℕ → ℝ) (A : Set ℕ) (N L : ℕ) (hNL : N≤ L+1)
    (ω : Fin (L+1) → Bool)
    (hbr : Brackets (fun i ↦ continuation p A N i.val) (fun i ↦ bit (ω i)))
    (i : ℕ) (hi : i<N) : (i∈selected L ω ↔ i∈A) := by
  have h₀ := rounded_old_mass p A N L ω hbr i (by omega) (by omega)
  have h₁ := rounded_old_mass p A N L ω hbr (i+1) (by omega) (by omega)
  rw [mass_succ,mass_succ,h₀] at h₁
  have he : indicator (selected L ω) i=indicator A i := by linarith
  by_cases hA : i∈A <;> by_cases hB : i∈selected L ω <;>
    simp_all [indicator]

lemma rounded_prefix_brackets (p : ℕ → ℝ) (hp : ∀ i, 0≤ p i ∧ p i≤ 1)
    (A : Set ℕ) (N L : ℕ) (hA : PrefixBrackets p A N)
    (ω : Fin (L+1) → Bool)
    (hbr : Brackets (fun i ↦ continuation p A N i.val) (fun i ↦ bit (ω i))) :
    PrefixBrackets p (selected L ω) (L+1) := by
  have hb := (continuation_finite_brackets p hp A N L hA).trans hbr
  intro k hk
  have hh := hb k
  rw [selected_pref L ω k hk,pref_fin_sum L k hk] at hh
  exact hh

/-- The bracket correction changes any finite Bernoulli mean by at most two. -/
theorem continuation_mean_correction (p : ℕ → ℝ) (hp : ∀ i, 0≤ p i ∧ p i≤ 1)
    (A : Set ℕ) (N : ℕ) (hbr : PrefixBrackets p A N) (L n : ℕ) :
    |repMean L n (fun i ↦ continuation p A N i.val)-
      repMean L n (fun i ↦ rawHybrid p A N i.val)|≤ 2 := by
  have hraw (i : ℕ) : 0≤ rawHybrid p A N i ∧ rawHybrid p A N i≤ 1 := by
    unfold rawHybrid
    split_ifs
    · exact ⟨indicator_nonneg A i,indicator_le_one A i⟩
    · exact hp i
  have hh := repMean_l1_bound L n (fun i ↦ continuation p A N i.val)
    (fun i ↦ rawHybrid p A N i.val)
    (fun i ↦ continuation_bounds p hp A N i.val) (fun i ↦ hraw i.val)
  dsimp only at hh
  rw [sum_fin_eq_mass L (fun i ↦ |continuation p A N i-rawHybrid p A N i|)] at hh
  have hb := continuation_l1_le_one p hp A N hbr (L+1)
  change mass (fun i ↦ |continuation p A N i-rawHybrid p A N i|) (L+1)≤ 1 at hb
  linarith


/-- General conditional extension: the old prefix is prescribed first,
and the SAME original prefix brackets are retained after rounding. -/
theorem exists_bracket_preserving_extension (p : ℕ → ℝ)
    (hp : ∀ i, 0≤ p i ∧ p i≤ 1) (A : Set ℕ) (N L : ℕ) (hNL : N≤ L+1)
    (hA : PrefixBrackets p A N) (S : Finset ℕ) (V : ℕ → ℝ) (ε : ℝ)
    (hε : 0<ε) (hε1 : ε≤ 1)
    (hV : ∀ n∈S, repVarianceProxy L n (fun i ↦ continuation p A N i.val)≤ V n)
    (hsmall : (∑ n∈S, 2*Real.exp (-ε^2*V n/8))<1) :
    ∃ C : Set ℕ, C.Finite ∧ (∀ i∈C, i≤ L) ∧
      (∀ i<N, i∈C ↔ i∈A) ∧ (∀ n<N, sumRep C n=sumRep A n) ∧
      PrefixBrackets p C (L+1) ∧
      ∀ n∈S, |(sumRep C n:ℝ)-repMean L n (fun i ↦ continuation p A N i.val)|<ε*V n+2 := by
  obtain ⟨ω,hbr,hrep⟩ := exists_prefix_balanced_variance_bound L
    (fun i ↦ continuation p A N i.val)
    (fun i ↦ continuation_bounds p hp A N i.val) S V ε hε hε1 hV hsmall
  have hold := rounded_old_membership p A N L hNL ω hbr
  refine ⟨selected L ω,selected_finite L ω,?_,hold,?_,
    rounded_prefix_brackets p hp A N L hA ω hbr,hrep⟩
  · rintro i ⟨j,rfl,hj⟩
    exact Nat.le_of_lt_succ j.isLt
  · intro n hn
    exact Erdos66Compactness.sumRep_congr_below (fun i hi ↦ hold i (by omega))

section Harmonic
open Erdos66Fractional

lemma harmonic_prefix_balance (A : Set ℕ) (N : ℕ) (hbr : PrefixBrackets profile A N) :
    ∀ k≤ N, |∑ i∈Finset.range k, roundingError A i|≤ 1 := by
  intro k hk
  simpa only [roundingError,Finset.sum_sub_distrib,mass] using
    prefix_discrepancy_bound profile A N hbr k hk

/-- Mean control and bracket regeneration are simultaneous. This estimate
is additive, not a selected Boolean representation bound. -/
theorem continuation_far_future_mean (A : Set ℕ) (N : ℕ)
    (hbr : PrefixBrackets profile A N) (L n : ℕ) (hnL : n≤ L) (hnN : 2*N≤ n) :
    |repMean L n (fun i ↦ continuation profile A N i.val)-(harmonic (n+1):ℝ)|≤
      2+5*profile (n/2) := by
  have hc := continuation_mean_correction profile
    (fun i ↦ ⟨profile_nonneg i,profile_le_one i⟩) A N hbr L n
  have hm := far_future_bernoulli_mean_bound A N L n hnL hnN 1 (by norm_num)
    (harmonic_prefix_balance A N hbr)
  change |repMean L n (fun i ↦ continuation profile A N i.val)-
    repMean L n (fun i ↦ hybrid A N i.val)|≤ 2 at hc
  have hh := abs_sub_le (repMean L n (fun i ↦ continuation profile A N i.val))
    (repMean L n (fun i ↦ hybrid A N i.val)) (harmonic (n+1):ℝ)
  nlinarith

/-- In the first window the original truncated quadratic defect is still
explicit. The clamp corrects the bracket invariant, not this defect. -/
theorem continuation_transition_mean (A : Set ℕ) (N : ℕ)
    (hbr : PrefixBrackets profile A N) (L n : ℕ) (hnL : n≤ L)
    (hnN : N≤ n) (hnN' : n<2*N) :
    |(repMean L n (fun i ↦ continuation profile A N i.val)-(harmonic (n+1):ℝ))-
      sumConv (prefixError A N) (prefixError A N) n|≤ 2+4*profile (n-N) := by
  have hc := continuation_mean_correction profile
    (fun i ↦ ⟨profile_nonneg i,profile_le_one i⟩) A N hbr L n
  have hm := transition_bernoulli_bias_control A N L n hnL hnN hnN' 1 (by norm_num)
    (harmonic_prefix_balance A N hbr)
  change |repMean L n (fun i ↦ continuation profile A N i.val)-
    repMean L n (fun i ↦ hybrid A N i.val)|≤ 2 at hc
  have hh := abs_add_le
    (repMean L n (fun i ↦ continuation profile A N i.val)-repMean L n (fun i ↦ hybrid A N i.val))
    ((repMean L n (fun i ↦ hybrid A N i.val)-(harmonic (n+1):ℝ))-
      sumConv (prefixError A N) (prefixError A N) n)
  have he : (repMean L n (fun i ↦ continuation profile A N i.val)-repMean L n (fun i ↦ hybrid A N i.val))+
    ((repMean L n (fun i ↦ hybrid A N i.val)-(harmonic (n+1):ℝ))-
      sumConv (prefixError A N) (prefixError A N) n)=
    (repMean L n (fun i ↦ continuation profile A N i.val)-(harmonic (n+1):ℝ))-
      sumConv (prefixError A N) (prefixError A N) n := by ring
  rw [he] at hh
  nlinarith


/-- Far-future requests can be selected simultaneously while exactly keeping
old bits, old representation counts, and the original discrepancy brackets.
The explicit summed-tail budget is not removed. -/
theorem exists_harmonic_far_extension (A : Set ℕ) (N L : ℕ) (hNL : N≤ L+1)
    (hA : PrefixBrackets profile A N) (S : Finset ℕ)
    (hS : ∀ n∈S, 2*N≤ n ∧ n≤ L) (ε : ℝ) (hε : 0<ε) (hε1 : ε≤ 1)
    (hsmall : (∑ n∈S, 2*Real.exp
      (-ε^2*((harmonic (n+1):ℝ)+2+5*profile (n/2))/8))<1) :
    ∃ C : Set ℕ, C.Finite ∧ (∀ i∈C, i≤ L) ∧
      (∀ i<N, i∈C ↔ i∈A) ∧ (∀ n<N, sumRep C n=sumRep A n) ∧
      PrefixBrackets profile C (L+1) ∧
      ∀ n∈S, |(sumRep C n:ℝ)-(harmonic (n+1):ℝ)|<
        ε*((harmonic (n+1):ℝ)+2+5*profile (n/2))+4+5*profile (n/2) := by
  let V : ℕ → ℝ := fun n ↦ (harmonic (n+1):ℝ)+2+5*profile (n/2)
  have hV (n : ℕ) (hn : n∈S) :
      repVarianceProxy L n (fun i ↦ continuation profile A N i.val)≤ V n := by
    have hm := continuation_far_future_mean A N hA L n (hS n hn).2 (hS n hn).1
    have hv := repVarianceProxy_le_mean L n (fun i ↦ continuation profile A N i.val)
      (fun i ↦ continuation_bounds profile
        (fun i ↦ ⟨profile_nonneg i,profile_le_one i⟩) A N i.val)
    have hh := (abs_le.mp hm).2
    dsimp [V]
    linarith
  obtain ⟨C,hC,hCL,hold,hrepold,hbr,hrep⟩ := exists_bracket_preserving_extension profile
    (fun i ↦ ⟨profile_nonneg i,profile_le_one i⟩) A N L hNL hA S V ε hε hε1 hV hsmall
  refine ⟨C,hC,hCL,hold,hrepold,hbr,fun n hn ↦ ?_⟩
  have hh := abs_sub_le (sumRep C n:ℝ)
    (repMean L n (fun i ↦ continuation profile A N i.val)) (harmonic (n+1):ℝ)
  have hm := continuation_far_future_mean A N hA L n (hS n hn).2 (hS n hn).1
  have hr := hrep n hn
  dsimp [V] at hr
  linarith

end Harmonic
end Erdos66BracketPreservingExtension
