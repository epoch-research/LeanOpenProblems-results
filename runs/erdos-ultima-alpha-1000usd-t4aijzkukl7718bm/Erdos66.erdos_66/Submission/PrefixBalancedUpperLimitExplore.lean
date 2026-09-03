import Submission.PrefixBalancedUpperSelectionExplore
import Submission.ScaledFractionalTailExplore
import Submission.SummableTailBudgetExplore
import Submission.CompactnessExplore
import Submission.RoundingExplore
import Submission.ClippedRepairExplore

/-! An infinite set with uniformly bounded prefix discrepancy from the
fractional profile and a logarithmic upper representation envelope.
No pointwise lower asymptotic bound is asserted. -/
namespace Erdos66PrefixBalancedUpperLimit
open Filter AdditiveCombinatorics Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli
  Erdos66PrefixBalancedUpperSelection Erdos66OrderedPipagePrefix
  Erdos66ScaledFractionalTail Erdos66SummableTailBudget Erdos66Compactness
  Erdos66Rounding Erdos66ClippedRepair Erdos66Generating
open scoped Classical Topology
set_option maxHeartbeats 2400000

noncomputable def encodedMass (f : ℕ → Bool) (k : ℕ) : ℝ :=
  ∑ i∈Finset.range k, bit (f i)

lemma continuous_encodedMass (k : ℕ) : Continuous (fun f : ℕ → Bool ↦ encodedMass f k) := by
  apply continuous_finset_sum
  intro i hi
  exact (continuous_of_discreteTopology (f := bit)).comp (continuous_apply i)

lemma encodedMass_decide (A : Set ℕ) (k : ℕ) :
    encodedMass (fun n ↦ decide (n∈A)) k=∑ i∈Finset.range k, indicator A i := by
  simp [encodedMass,bit,indicator]

lemma pref_fin_sum (L k : ℕ) (hk : k≤L+1) (p : ℕ → ℝ) :
    pref (fun i : Fin (L+1) ↦ p i.val) k=∑ i∈Finset.range k, p i := by
  apply Finset.sum_bij (fun i hi ↦ i.val)
  · intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  · intro i hi j hj he
    exact Fin.ext he
  · intro i hi
    refine ⟨⟨i,by have := Finset.mem_range.mp hi; omega⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_range.mp hi⟩
  · intro i hi
    rfl

lemma finite_prefix_bound (L : ℕ) (p : ℕ → ℝ) (ω : Fin (L+1) → Bool)
    (hbr : Brackets (fun i : Fin (L+1) ↦ p i.val) (fun i ↦ bit (ω i)))
    (k : ℕ) (hk : k≤L+1) :
    |(∑ i∈Finset.range k, indicator (selected L ω) i)-(∑ i∈Finset.range k, p i)|≤1 := by
  have he : pref (fun i ↦ bit (ω i)) k=∑ i∈Finset.range k, indicator (selected L ω) i := by
    have hh : (fun i : Fin (L+1) ↦ bit (ω i))=(fun i : Fin (L+1) ↦ indicator (selected L ω) i.val) := by
      funext i
      simp only [indicator,mem_selected,bit]
    rw [hh,pref_fin_sum L k hk]
  have hb := hbr k
  rw [he,pref_fin_sum L k hk p] at hb
  have hlo := Int.lt_floor_add_one (∑ i∈Finset.range k, p i)
  have hhi := Int.ceil_lt_add_one (∑ i∈Finset.range k, p i)
  rw [abs_le]
  constructor <;> linarith

lemma upper_exponential_mean (L n : ℕ) (p : Fin (L+1) → ℝ)
    (hp : ∀ i, 0≤p i ∧ p i≤1) :
    expect p (fun ω ↦ Real.exp ((1/2:ℝ)*(sumRep (selected L ω) n : ℝ)))≤
      Real.exp (repMean L n p) := by
  have hm := rep_mgf L n p hp (1/2) (by norm_num)
  have he (ω : Fin (L+1) → Bool) :
      Real.exp ((1/2:ℝ)*(sumRep (selected L ω) n : ℝ))=
      Real.exp ((1/2:ℝ)*repMean L n p)*
        Real.exp ((1/2:ℝ)*((sumRep (selected L ω) n : ℝ)-repMean L n p)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [expect_const_mul]
  have hh := mul_le_mul_of_nonneg_left hm (Real.exp_pos ((1/2:ℝ)*repMean L n p)).le
  have he' : Real.exp ((1/2:ℝ)*repMean L n p)*Real.exp (2*(1/2:ℝ)^2*repMean L n p)=
      Real.exp (repMean L n p) := by rw [←Real.exp_add]; congr 1; ring
  exact hh.trans_eq he'

lemma exists_finite_balanced_upper (p : ℕ → ℝ) (hp : ∀ n, 0≤p n ∧ p n≤1)
    (c : ℝ) (hc : 0≤c)
    (hconv : Tendsto (fun n ↦ sumConv p p n/Real.log n) atTop (𝓝 c)) :
    ∃ N : ℕ, ∀ L : ℕ, ∃ A : Set ℕ,
      (∀ k≤L, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)|≤1) ∧
      (∀ n, N≤n → n≤L → (sumRep A n : ℝ)≤(2*c+4)*logScale n) := by
  have hser : Summable (fun n : ℕ ↦ 1/((n:ℝ)+2)^(3/2:ℝ)) := by
    have hs := (Real.summable_one_div_nat_add_rpow 2 (3/2)).mpr (by norm_num)
    have he (n : ℕ) : |(n:ℝ)+2|=(n:ℝ)+2 := abs_of_pos (by positivity)
    simpa only [he] using hs
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (uniform_mean_approximation p hp c hconv (1/2) (by norm_num))
  obtain ⟨N₂,hN₂⟩ := exists_tail_budget _ hser 1 (by norm_num)
  let N := max 2 (max N₁ N₂)
  refine ⟨N,fun L ↦ ?_⟩
  let T := Finset.Icc N L
  let w : ℕ → ℝ := fun n ↦ Real.exp (-(c+2)*logScale n)
  have hm (n : ℕ) (hn : n∈T) : repMean L n (fun i ↦ p i.val)≤(c+1/2)*logScale n := by
    have hnN := (Finset.mem_Icc.mp hn).1
    have hnL := (Finset.mem_Icc.mp hn).2
    have hn2 : 2≤n := (le_max_left _ _).trans hnN
    have hln : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    have hh := (abs_lt.mp (hN₁ n (by dsimp [N] at hnN; omega) L hnL)).2
    have hdiv : repMean L n (fun i ↦ p i.val)/Real.log n≤c+1/2 := by linarith
    have hlog : Real.log (n:ℝ)≤logScale n := Real.log_le_log
      (by exact_mod_cast (show 0<n by omega)) (by linarith)
    exact ((div_le_iff₀ hln).mp hdiv).trans
      (mul_le_mul_of_nonneg_left hlog (by linarith))
  have hterm (n : ℕ) (hn : n∈T) :
      w n*expect (fun i : Fin (L+1) ↦ p i.val)
        (fun ω ↦ Real.exp ((1/2:ℝ)*(sumRep (selected L ω) n : ℝ)))≤1/((n:ℝ)+2)^(3/2:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left
      (upper_exponential_mean L n (fun i ↦ p i.val) (fun i ↦ hp i.val))
      (Real.exp_pos (-(c+2)*logScale n)).le
    apply hh.trans
    rw [←Real.exp_add]
    have hb : -(c+2)*logScale n+repMean L n (fun i ↦ p i.val)≤-(3/2:ℝ)*logScale n := by linarith [hm n hn]
    calc
      _ ≤ Real.exp (-(3/2:ℝ)*logScale n) := Real.exp_le_exp.mpr hb
      _ = 1/((n:ℝ)+2)^(3/2:ℝ) := by
        rw [Real.rpow_def_of_pos (by positivity),one_div,←Real.exp_neg,logScale]
        congr 1
        ring
  obtain ⟨ω,hbr,hcost⟩ := exists_prefix_balanced_upper_selection L (fun i ↦ p i.val)
    (fun i ↦ hp i.val) T id (fun _ ↦ (1/2:ℝ)) w
    (fun _ _ ↦ by norm_num) (fun n _ ↦ (Real.exp_pos _).le)
  have hsmall : (∑ n∈T, w n*Real.exp ((1/2:ℝ)*(sumRep (selected L ω) n : ℝ)))<1 := by
    apply hcost.trans_lt
    rw [expect_sum]
    simp only [expect_const_mul]
    apply (Finset.sum_le_sum hterm).trans_lt
    exact hN₂ T (fun n hn ↦ by have hnN := (Finset.mem_Icc.mp hn).1; dsimp [N] at hnN; omega)
  refine ⟨selected L ω,fun k hk ↦ finite_prefix_bound L p ω hbr k (by omega),?_⟩
  intro n hn hnL
  have hsingle := Finset.single_le_sum (s := T) (a := n)
    (f := fun n ↦ w n*Real.exp ((1/2:ℝ)*(sumRep (selected L ω) n : ℝ)))
    (fun n _ ↦ mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Finset.mem_Icc.mpr ⟨hn,hnL⟩)
  have hh := hsingle.trans_lt hsmall
  dsimp [w] at hh
  rw [←Real.exp_add,Real.exp_lt_one_iff] at hh
  linarith

/-- The same infinite set has bounded prefix discrepancy and a global-tail
O(log n) upper bound. This does not assert a pointwise asymptotic lower bound. -/
theorem exists_balanced_upper (p : ℕ → ℝ) (hp : ∀ n, 0≤p n ∧ p n≤1)
    (c : ℝ) (hc : 0≤c)
    (hconv : Tendsto (fun n ↦ sumConv p p n/Real.log n) atTop (𝓝 c)) :
    ∃ A : Set ℕ,
      (∀ k, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)|≤1) ∧
      (∀ᶠ n : ℕ in atTop, (sumRep A n : ℝ)≤(2*c+4)*logScale n) := by
  obtain ⟨N,hN⟩ := exists_finite_balanced_upper p hp c hc hconv
  let C : ℕ → Set (ℕ → Bool) := fun L ↦ {f |
    (∀ k≤L, |encodedMass f k-(∑ i∈Finset.range k, p i)|≤1) ∧
    (∀ n, N≤n → n≤L → encodedRep f n≤(2*c+4)*logScale n)}
  have hclosed (L : ℕ) : IsClosed (C L) := by
    dsimp only [C]
    rw [Set.setOf_and]
    apply IsClosed.inter
    · simp only [Set.setOf_forall]
      exact isClosed_iInter (fun k ↦ isClosed_iInter (fun _ ↦
        isClosed_le ((continuous_encodedMass k).sub continuous_const).abs continuous_const))
    · simp only [Set.setOf_forall]
      exact isClosed_iInter (fun n ↦ isClosed_iInter (fun _ ↦ isClosed_iInter (fun _ ↦
        isClosed_le (continuous_encodedRep n) continuous_const)))
  have hne (L : ℕ) : (C L).Nonempty := by
    obtain ⟨A,hA,hu⟩ := hN L
    refine ⟨fun i ↦ decide (i∈A),?_,?_⟩
    · intro k hk
      simpa only [encodedMass_decide] using hA k hk
    · intro n hn hnL
      simpa only [encodedRep_decide] using hu n hn hnL
  have hmono (L : ℕ) : C (L+1)⊆C L := by
    intro f hf
    exact ⟨fun k hk ↦ hf.1 k (by omega),fun n hn hnL ↦ hf.2 n hn (by omega)⟩
  obtain ⟨f,hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    hmono hne (hclosed 0).isCompact hclosed
  let A : Set ℕ := {i | f i=true}
  refine ⟨A,?_,eventually_atTop.mpr ⟨N,fun n hn ↦ ?_⟩⟩
  · intro k
    have hh := (Set.mem_iInter.mp hf k).1 k le_rfl
    have he : encodedMass f k=∑ i∈Finset.range k, indicator A i := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [bit,indicator,A]
      cases f i <;> simp
    rwa [he] at hh
  · have hh := (Set.mem_iInter.mp hf n).2 n hn le_rfl
    simpa only [encodedRep_eq_sumRep] using hh

/-- A bounded-discrepancy rounding of the exact harmonic fractional profile
can be chosen to have no superlogarithmic representation peaks. -/
theorem exists_harmonic_rounding_with_upper_bound :
    ∃ A : Set ℕ,
      (∀ n, |prefixSum (roundingError A) n|≤1) ∧
      (∀ᶠ n : ℕ in atTop, (sumRep A n : ℝ)≤6*logScale n) := by
  obtain ⟨A,hA,hu⟩ := exists_balanced_upper Erdos66Fractional.profile
    (fun n ↦ ⟨Erdos66Fractional.profile_nonneg n,Erdos66Fractional.profile_le_one n⟩)
    1 (by norm_num) Erdos66Fractional.profile_log_limit
  refine ⟨A,?_,?_⟩
  · intro n
    simpa only [prefixSum,roundingError,Finset.sum_sub_distrib] using hA (n+1)
  · simpa only [show (2:ℝ)*1+4=6 by norm_num] using hu

end Erdos66PrefixBalancedUpperLimit
