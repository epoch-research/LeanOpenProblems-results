import Submission.SparseRowCountingScaleExplore

/-! One simultaneous transversal of all sparse ordered candidate rows,
with sublogarithmic representation increment at every target. -/
namespace Erdos66SimultaneousIntervalRowSelection
open Filter AdditiveCombinatorics Erdos66Counting Erdos66Fractional
  Erdos66Generating Erdos66ClampedPrefixContinuation Erdos66InfiniteRowProbability
  Erdos66InfiniteIntervalRows Erdos66SparseRowMeanDecay Erdos66SparseRowCountingScale
  Erdos66BoundaryPairMean Erdos66ReflectionRoundingPatch
open scoped Classical Topology
set_option maxHeartbeats 3600000

 theorem exists_sparse_interval_transversal
    (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (E : Set ℕ) (S : ℕ → Finset ℕ) (L U : ℕ → ℕ)
    (hne : ∀ d∈E, (S d).Nonempty)
    (hsub : ∀ d∈E, S d ⊆ Finset.Ico (L d) (U d))
    (hfresh : ∀ d∈E, ∀ i∈S d, i∉A)
    (hord : ∀ d∈E, ∀ e∈E, d<e → U d ≤ L e)
    (hloc : ∀ d∈E, ∀ i∈Finset.Ico (L d) (U d), d ≤ 2*i)
    (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ d∈E, ∀ i∈Finset.Ico (L d) (U d), ((S d).card : ℝ)⁻¹ ≤ C*profile i)
    (hfill : ∀ d∈E, ((S d).card : ℝ)⁻¹*(U d-L d : ℕ) ≤ 2)
    (hdec : Tendsto (fun n : ℕ ↦ (count E n : ℝ)/Real.sqrt ((n : ℝ)*Real.log n)) atTop (𝓝 0)) :
    ∃ F : Set ℕ, Disjoint F A ∧
      (∀ i∈F, ∃ d∈E, i∈S d) ∧
      (∀ d∈E, (intervalPart F (L d) (U d)).card=1) ∧
      Tendsto (fun n : ℕ ↦ ((sumRep (A∪F) n : ℝ)-(sumRep A n : ℝ))/
        Real.log ((n : ℝ)+2)) atTop (𝓝 0) := by
  have hdj : E.PairwiseDisjoint (fun d ↦ Finset.Ico (L d) (U d)) := by
    intro d hd e he hde
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' := Finset.mem_Ico.mp hi
    have hj' := Finset.mem_Ico.mp hj
    rcases lt_or_gt_of_ne hde with h | h
    · have hh := hord d hd e he h
      omega
    · have hh := hord e he d hd h
      omega
  have hsdj := candidates_pairwise_disjoint E S L U hsub hdj
  let q := rowProb E S
  have hq (i : ℕ) : 0 ≤ q i ∧ q i ≤ 1 :=
    ⟨rowProb_nonneg E S i,rowProb_le_one E S hsdj i⟩
  have hqA (i : ℕ) (hi : i∈A) : q i=0 := rowProb_eq_zero E S i
    (fun d hd hdi ↦ hfresh d hd i hdi hi)
  have hqp := interval_rowProb_profile E S L U hsub hdj C hC hw
  let R (n : ℕ) : ℝ := count E (2*(n+1)+1)
  have hR (n : ℕ) : 0 ≤ R n := Nat.cast_nonneg _
  have hRdec := sparse_row_count_decay E E (Set.Subset.refl _) hdec
  have hmass : ∀ᶠ n : ℕ in atTop, mass q (n+1) ≤ 2*R n := Filter.Eventually.of_forall (fun n ↦ by
    have hh := interval_rowProb_prefix E S L U hsub hloc n
    change mass q (n+1) ≤ R n at hh
    linarith [hR n])
  have hrow : ∀ d ≥ 2, ∀ᶠ n : ℕ in atTop, HasCentralRows q n (n/d^2) C (R n) := by
    intro d hd
    apply Filter.Eventually.of_forall
    intro n
    exact interval_rowProb_central_rows E S L U hsub hloc C hC hw hfill n (n/d^2)
      (by have := quotient_half d n hd; omega)
  obtain ⟨F,hFA,hFbr,hs,hlim⟩ := exists_sparse_row_insertion A hbr q hq hqA C hC hqp R hR hRdec hmass hrow
  refine ⟨F,hFA,?_,?_,hlim⟩
  · intro i hi
    exact (rowProb_support E S hsdj i).mp (hs i hi)
  · intro d hd
    exact interval_rowProb_exactly_one E S L U hne hsub hord F hFbr d hd

end Erdos66SimultaneousIntervalRowSelection
