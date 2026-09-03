import Submission.DifferenceMatchingExplore
import Submission.ScaledFractionalTailExplore

/-! Actual local difference counts and summable upper-potential bounds for
the exact harmonic probability profile. No repair algorithm is asserted. -/
namespace Erdos66LocalDifferencePotential
open Filter AdditiveCombinatorics Erdos66DifferenceMatching Erdos66FiniteBernoulli
  Erdos66FiniteRepBernoulli Erdos66Fractional Erdos66FractionalFourthPower
open scoped Classical Topology
set_option maxHeartbeats 2400000

noncomputable def localDiff (A : Set ℕ) (N d : ℕ) : ℕ :=
  ((Finset.range (2*N)).filter (fun i ↦ N ≤ i ∧ i+d<2*N ∧ i∈A ∧ i+d∈A)).card

lemma class_split (L N d : ℕ) (ω : Fin (L+1) → Bool) :
    (∑ a∈edges L N d, monomial (pairCoords a) ω)=
      matchingCount L N d 0 ω+matchingCount L N d 1 ω := by
  have he : (edges L N d).filter (fun a ↦ ¬(a.1.val/d)%2=0)=edgeClass L N d 1 := by
    ext a
    simp only [Finset.mem_filter,edgeClass]
    have hh : (a.1.val/d)%2<2 := Nat.mod_lt _ (by norm_num)
    constructor <;> rintro ⟨ha,hb⟩ <;> exact ⟨ha,by omega⟩
  have hh := Finset.sum_filter_add_sum_filter_not (edges L N d) (fun a ↦ (a.1.val/d)%2=0)
    (fun a ↦ monomial (pairCoords a) ω)
  rw [he] at hh
  exact hh.symm

lemma selected_localDiff (L N d : ℕ) (hL : 2*N ≤ L+1) (ω : Fin (L+1) → Bool) :
    (localDiff (selected L ω) N d : ℝ)=matchingCount L N d 0 ω+matchingCount L N d 1 ω := by
  have hcard : localDiff (selected L ω) N d=
      ((edges L N d).filter (fun a ↦ ω a.1=true ∧ ω a.2=true)).card := by
    unfold localDiff
    apply Finset.card_bij (fun i hi ↦
      (⟨i,by have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega⟩,
       ⟨i+d,by have := (Finset.mem_filter.mp hi).2.2.1; omega⟩))
    · intro i hi
      obtain ⟨hi2,hiN,hd2,hiA,hdA⟩ := Finset.mem_filter.mp hi
      simp only [Finset.mem_filter,mem_edges]
      refine ⟨⟨hiN,hd2,True.intro⟩,?_,?_⟩
      · exact (mem_selected L ω _).mp hiA
      · exact (mem_selected L ω _).mp hdA
    · intro i hi j hj he
      exact congrArg (fun a : Fin (L+1) × Fin (L+1) ↦ a.1.val) he
    · intro a ha
      obtain ⟨haE,ha1,ha2⟩ := Finset.mem_filter.mp ha
      obtain ⟨hN,h2,he⟩ := mem_edges.mp haE
      refine ⟨a.1.val,?_,?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr (by omega),hN,by omega,(mem_selected L ω a.1).mpr ha1,?_⟩
        rw [he]
        exact (mem_selected L ω a.2).mpr ha2
      · apply Prod.ext
        · rfl
        · exact Fin.ext he
  rw [hcard,←class_split]
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro a ha
  rw [pair_monomial]
  cases h1 : ω a.1 <;> cases h2 : ω a.2 <;> norm_num [bit,h1,h2]

lemma localDiff_zero_large (A : Set ℕ) (N d : ℕ) (hd : N ≤ d) : localDiff A N d=0 := by
  unfold localDiff
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨_,hiN,hi2,_⟩ := Finset.mem_filter.mp hi
  omega

lemma harmonic_matching_mean (L N d b : ℕ) (hd : 0<d) :
    matchingMean L N d b (fun i ↦ profile i.val) ≤ (harmonic (N+1):ℝ) := by
  have hh := matchingMean_le L N d b hd (fun i ↦ profile i.val) (fun i ↦ profile_nonneg i.val)
    (profile N) (fun i hi _ ↦ profile_antitone hi)
  have hs := profile_square_bound N
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hp := sq_nonneg (profile N)
  push_cast at hs
  exact hh.trans (by nlinarith)

noncomputable def weight (N : ℕ) : ℝ := Real.exp (-6*Real.log ((N:ℝ)+2))

lemma harmonic_weighted_mean (L N d b : ℕ) (hd : 0<d) :
    weight N*expect (fun i : Fin (L+1) ↦ profile i.val)
      (fun ω ↦ Real.exp ((1/2:ℝ)*matchingCount L N d b ω)) ≤ Real.exp 1/((N:ℝ)+2)^5 := by
  have hmean := matching_upper_mean L N d b hd (fun i ↦ profile i.val)
    (fun i ↦ ⟨profile_nonneg i.val,profile_le_one i.val⟩)
  have hH := harmonic_le_one_add_log (N+1)
  have hlog : Real.log ((N+1:ℕ):ℝ) ≤ Real.log ((N:ℝ)+2) :=
    Real.log_le_log (by positivity) (by push_cast; linarith)
  have hm : matchingMean L N d b (fun i ↦ profile i.val) ≤ 1+Real.log ((N:ℝ)+2) :=
    (harmonic_matching_mean L N d b hd).trans (by linarith)
  apply (mul_le_mul_of_nonneg_left hmean (Real.exp_pos _).le).trans
  change Real.exp (-6*Real.log ((N:ℝ)+2))*Real.exp _ ≤ _
  rw [←Real.exp_add]
  calc
    _  ≤  Real.exp (1-5*Real.log ((N:ℝ)+2)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp 1/((N:ℝ)+2)^5 := by
      rw [Real.exp_sub]
      congr 1
      simpa only [Nat.cast_ofNat,Real.exp_log (by positivity : 0<(N:ℝ)+2)] using (Real.exp_nat_mul (Real.log ((N:ℝ)+2)) 5)

lemma matching_tail_summable : Summable (fun N : ℕ ↦ 2*(N:ℝ)*(Real.exp 1/((N:ℝ)+2)^5)) := by
  have hs := (Real.summable_one_div_nat_add_rpow 2 (4:ℕ)).mpr (by norm_num)
  have hs' : Summable (fun N : ℕ ↦ 2*Real.exp 1/((N:ℝ)+2)^4) := by
    have hh := hs.mul_left (2*Real.exp 1)
    simpa only [Real.rpow_natCast,abs_of_nonneg (by positivity : (0:ℝ) ≤ (↑(_:ℕ):ℝ)+2),mul_one_div] using hh
  apply Summable.of_nonneg_of_le (fun N ↦ by positivity) _ hs'
  intro N
  have hx : 0<(N:ℝ)+2 := by positivity
  have he : 2*Real.exp 1/((N:ℝ)+2)^4=2*Real.exp 1*((N:ℝ)+2)/((N:ℝ)+2)^5 := by field_simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (show (N:ℝ) ≤ (N:ℝ)+2 by linarith) (show 0 ≤ 2*Real.exp 1 by positivity)
  have hh' := div_le_div_of_nonneg_right hh (show 0 ≤ ((N:ℝ)+2)^5 by positivity)
  convert hh' using 1 <;> ring

end Erdos66LocalDifferencePotential
