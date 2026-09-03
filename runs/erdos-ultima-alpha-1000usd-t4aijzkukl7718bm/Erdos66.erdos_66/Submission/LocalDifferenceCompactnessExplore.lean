import Submission.FiniteLocalDifferenceSelectionExplore
import Submission.PrefixBalancedCostCompactnessExplore

/-! Closed local-difference bounds retained alongside prefix discrepancy and
summable representation costs. -/
namespace Erdos66LocalDifferenceCompactness
open AdditiveCombinatorics Erdos66LocalDifferencePotential Erdos66FiniteBernoulli
  Erdos66Compactness Erdos66PrefixBalancedUpperLimit Erdos66Generating
open scoped Classical Topology
set_option maxHeartbeats 2200000

noncomputable def encodedDiff (f : ℕ → Bool) (N d : ℕ) : ℝ :=
  ∑ i∈Finset.range (2*N), if N ≤ i ∧ i+d<2*N then bit (f i)*bit (f (i+d)) else 0

lemma continuous_encodedDiff (N d : ℕ) : Continuous (fun f : ℕ → Bool ↦ encodedDiff f N d) := by
  apply continuous_finset_sum
  intro i hi
  by_cases h : N ≤ i ∧ i+d<2*N
  · simp only [if_pos h]
    exact ((continuous_of_discreteTopology (f := bit)).comp (continuous_apply i)).mul
      ((continuous_of_discreteTopology (f := bit)).comp (continuous_apply (i+d)))
  · simp only [if_neg h]
    exact continuous_const

lemma encodedDiff_decide (A : Set ℕ) (N d : ℕ) :
    encodedDiff (fun i ↦ decide (i∈A)) N d=(localDiff A N d : ℝ) := by
  rw [localDiff,Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : N ≤ i ∧ i+d<2*N
  · obtain ⟨hN,hd⟩ := h
    by_cases ha : i∈A <;> by_cases hb : i+d∈A <;> simp [bit,hN,hd,ha,hb]
  · have hh : ¬(N ≤ i ∧ i+d<2*N ∧ i∈A ∧ i+d∈A) := fun hh ↦ h ⟨hh.1,hh.2.1⟩
    simp only [if_neg h,if_neg hh]

lemma encodedDiff_eq_localDiff (f : ℕ → Bool) (N d : ℕ) :
    encodedDiff f N d=(localDiff {i | f i=true} N d : ℝ) := by
  simpa using (encodedDiff_decide {i | f i=true} N d)

 theorem exists_summable_costs_with_local_diff (p : ℕ → ℝ) (N₀ : ℕ)
    (cost : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ j n, Continuous (cost j n))
    (hpos : ∀ j n x, 0 ≤ cost j n x)
    (hfinite : ∀ L : ℕ, ∃ A : Set ℕ,
      (∀ k ≤ L, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)| ≤ 1) ∧
      (∀ N ≤ L, ∀ d, N₀ ≤ N → 0<d → (localDiff A N d : ℝ) ≤ 24*Real.log ((N:ℝ)+2)) ∧
      (∀ j ≤ L, ∀ K ≤ L, (∑ n∈Finset.range K, cost j n (sumRep A n)) ≤ 1)) :
    ∃ A : Set ℕ,
      (∀ k, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)| ≤ 1) ∧
      (∀ N d, N₀ ≤ N → 0<d → (localDiff A N d : ℝ) ≤ 24*Real.log ((N:ℝ)+2)) ∧
      (∀ j, Summable (fun n ↦ cost j n (sumRep A n))) := by
  let C : ℕ → Set (ℕ → Bool) := fun L ↦ {f |
    (∀ k ≤ L, |encodedMass f k-(∑ i∈Finset.range k, p i)| ≤ 1) ∧
    (∀ N ≤ L, ∀ d, N₀ ≤ N → 0<d → encodedDiff f N d ≤ 24*Real.log ((N:ℝ)+2)) ∧
    (∀ j ≤ L, ∀ K ≤ L, (∑ n∈Finset.range K, cost j n (encodedRep f n)) ≤ 1)}
  have hclosed (L : ℕ) : IsClosed (C L) := by
    dsimp only [C]
    simp only [Set.setOf_and]
    apply IsClosed.inter
    · simp only [Set.setOf_forall]
      exact isClosed_iInter (fun k ↦ isClosed_iInter (fun _ ↦
        isClosed_le ((continuous_encodedMass k).sub continuous_const).abs continuous_const))
    · apply IsClosed.inter
      · simp only [Set.setOf_forall]
        exact isClosed_iInter (fun N ↦ isClosed_iInter (fun _ ↦ isClosed_iInter (fun d ↦
          isClosed_iInter (fun _ ↦ isClosed_iInter (fun _ ↦
            isClosed_le (continuous_encodedDiff N d) continuous_const)))))
      · simp only [Set.setOf_forall]
        refine isClosed_iInter (fun j ↦ isClosed_iInter (fun _ ↦
          isClosed_iInter (fun K ↦ isClosed_iInter (fun _ ↦ ?_))))
        exact isClosed_le (continuous_finset_sum _ (fun n _ ↦
          (hcont j n).comp (continuous_encodedRep n))) continuous_const
  have hne (L : ℕ) : (C L).Nonempty := by
    obtain ⟨A,hA,hd,hcost⟩ := hfinite L
    refine ⟨fun i ↦ decide (i∈A),?_,?_,?_⟩
    · intro k hk
      simpa only [encodedMass_decide] using hA k hk
    · intro N hN d hN₀ hd'
      simpa only [encodedDiff_decide] using hd N hN d hN₀ hd'
    · intro j hj K hK
      simpa only [encodedRep_decide] using hcost j hj K hK
  have hmono (L : ℕ) : C (L+1)⊆C L := by
    intro f hf
    exact ⟨fun k hk ↦ hf.1 k (by omega),fun N hN d hN₀ hd ↦ hf.2.1 N (by omega) d hN₀ hd,
      fun j hj K hK ↦ hf.2.2 j (by omega) K (by omega)⟩
  obtain ⟨f,hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    hmono hne (hclosed 0).isCompact hclosed
  let A : Set ℕ := {i | f i=true}
  refine ⟨A,?_,?_,?_⟩
  · intro k
    have hh := (Set.mem_iInter.mp hf k).1 k le_rfl
    have he : encodedMass f k=∑ i∈Finset.range k, indicator A i := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [bit,indicator,A]
      cases f i <;> simp
    rwa [he] at hh
  · intro N d hN₀ hd
    have hh := (Set.mem_iInter.mp hf N).2.1 N le_rfl d hN₀ hd
    simpa only [encodedDiff_eq_localDiff] using hh
  · intro j
    apply summable_of_sum_range_le (c := 1) (fun n ↦ hpos j n _)
    intro K
    have hh := (Set.mem_iInter.mp hf (max j K)).2.2 j (le_max_left _ _) K (le_max_right _ _)
    simpa only [encodedRep_eq_sumRep] using hh

end Erdos66LocalDifferenceCompactness
