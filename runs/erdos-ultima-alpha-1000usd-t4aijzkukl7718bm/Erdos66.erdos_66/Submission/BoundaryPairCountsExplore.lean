import Submission.BoundaryPairMeanExplore
import Submission.CentralTripleCountsExplore

/-! Natural boundary-pair counts and their finite Boolean realizations. -/
namespace Erdos66BoundaryPairCounts
open Erdos66BoundaryPairMean Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli
  Erdos66CentralTripleCounts Erdos66BernoulliMatchingPolynomial
open scoped Classical Topology
set_option maxHeartbeats 1600000

noncomputable def boundary (A : Set ℕ) (d n : ℕ) : Finset ℕ :=
  (Finset.range (n/d^2)).filter (fun a ↦ a∈A ∧ n-a∈A)

lemma selected_boundary_card (L d n : ℕ) (hd : 2 ≤ d) (ω : Fin (L+1) → Bool) :
    (realized (boundaryPairs L d n) pairCoords ω).card=(boundary (selected L ω) d n).card := by
  apply Finset.card_bij (fun a _ ↦ a.1.val)
  · intro a ha
    obtain ⟨ha,hω⟩ := (mem_realized _ _ _ _).mp ha
    obtain ⟨hn,hd,hlt⟩ := mem_boundaryPairs.mp ha
    have h1 := (mem_selected L ω a.1).mpr (hω _ (by simp [pairCoords]))
    have h2 := (mem_selected L ω a.2).mpr (hω _ (by simp [pairCoords]))
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hd,h1,by rwa [show n-a.1.val=a.2.val by omega]⟩
  · intro a ha b hb he
    obtain ⟨ha,_⟩ := (mem_realized _ _ _ _).mp ha
    obtain ⟨hb,_⟩ := (mem_realized _ _ _ _).mp hb
    have ha' := (mem_boundaryPairs.mp ha).1
    have hb' := (mem_boundaryPairs.mp hb).1
    exact Prod.ext (Fin.ext he) (Fin.ext (by omega))
  · intro a ha
    obtain ⟨ha,h1,h2⟩ := Finset.mem_filter.mp ha
    have ha' := Finset.mem_range.mp ha
    have hhalf := quotient_half d n hd
    let x : Fin (L+1) := ⟨a,selected_bound h1⟩
    let y : Fin (L+1) := ⟨n-a,selected_bound h2⟩
    refine ⟨(x,y),(mem_realized _ _ _ _).mpr ⟨mem_boundaryPairs.mpr
      ⟨by dsimp [x,y]; omega,ha',by change a<n-a; omega⟩,?_⟩,rfl⟩
    intro i hi
    simp only [pairCoords,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact (mem_selected L ω x).mp h1
    · exact (mem_selected L ω y).mp h2

noncomputable def encodedBoundary (f : ℕ → Bool) (d n : ℕ) : ℝ :=
  ∑ a∈Finset.range (n/d^2), bit (f a)*bit (f (n-a))

lemma continuous_encodedBoundary (d n : ℕ) :
    Continuous (fun f : ℕ → Bool ↦ encodedBoundary f d n) := by
  exact continuous_finset_sum _ (fun a _ ↦
    ((continuous_of_discreteTopology (f := bit)).comp (continuous_apply a)).mul
      ((continuous_of_discreteTopology (f := bit)).comp (continuous_apply (n-a))))

lemma encodedBoundary_decide (A : Set ℕ) (d n : ℕ) :
    encodedBoundary (fun i ↦ decide (i∈A)) d n=((boundary A d n).card:ℝ) := by
  rw [boundary,Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h1 : a∈A <;> by_cases h2 : n-a∈A <;> simp [bit,h1,h2]

lemma encodedBoundary_eq (f : ℕ → Bool) (d n : ℕ) :
    encodedBoundary f d n=((boundary {i | f i=true} d n).card:ℝ) := by
  simpa using encodedBoundary_decide {i | f i=true} d n

lemma boundary_mono {A B : Set ℕ} (hAB : A ⊆ B) (d n : ℕ) : boundary A d n ⊆ boundary B d n := by
  intro a ha
  obtain ⟨ha,h1,h2⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨ha,hAB h1,hAB h2⟩

end Erdos66BoundaryPairCounts
