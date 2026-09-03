import Submission.InsertionIncrementComparisonExplore
import Submission.BoundaryPairCountsExplore

/-! New boundary pairs and central triples are charged to new sum
representations. These bounds do not require probabilistic independence. -/
namespace Erdos66PatternInsertionDomination
open AdditiveCombinatorics Erdos66CentralTripleCounts Erdos66BoundaryPairCounts
  Erdos66Explore
open scoped Classical
set_option maxHeartbeats 2200000

noncomputable def repEndpoints (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range (n+1)).filter (fun a ↦ a∈A ∧ n-a∈A)

lemma mem_repEndpoints {A : Set ℕ} {n a : ℕ} : a∈repEndpoints A n ↔ a ≤ n ∧ a∈A ∧ n-a∈A := by
  simp only [repEndpoints,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]

lemma repEndpoints_card (A : Set ℕ) (n : ℕ) : (repEndpoints A n).card=sumRep A n := by
  rw [sumRep_def]
  apply Finset.card_bij (fun a _ ↦ (a,n-a))
  · intro a ha
    obtain ⟨han,ha,hb⟩ := mem_repEndpoints.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr (by omega),ha,hb⟩
  · intro a _ b _ he
    exact congrArg Prod.fst he
  · intro p hp
    obtain ⟨hp,h1,h2⟩ := Finset.mem_filter.mp hp
    have he := Finset.mem_antidiagonal.mp hp
    refine ⟨p.1,mem_repEndpoints.mpr ⟨by omega,h1,by simpa only [show n-p.1=p.2 by omega] using h2⟩,?_⟩
    exact Prod.ext rfl (by omega)

lemma repEndpoints_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) : repEndpoints A n ⊆ repEndpoints B n := by
  intro a ha
  obtain ⟨han,ha,hb⟩ := mem_repEndpoints.mp ha
  exact mem_repEndpoints.mpr ⟨han,hAB ha,hAB hb⟩

noncomputable def newEndpoints (A B : Set ℕ) (n : ℕ) : Finset ℕ := repEndpoints B n\repEndpoints A n

lemma newEndpoints_card (A B : Set ℕ) (hAB : A ⊆ B) (n : ℕ) :
    ((newEndpoints A B n).card : ℝ)=(sumRep B n : ℝ)-sumRep A n := by
  rw [newEndpoints,Finset.card_sdiff_of_subset (repEndpoints_mono hAB n),repEndpoints_card,repEndpoints_card,
    Nat.cast_sub (sumRep_mono hAB n)]

lemma fiber_mono {A B : Set ℕ} (hAB : A ⊆ B) (N n z : ℕ) : fiber A N n z ⊆ fiber B N n z := by
  intro a ha
  obtain ⟨han,hNa,hNb,haz,ha,hb,hc⟩ := mem_fiber.mp ha
  exact mem_fiber.mpr ⟨han,hNa,hNb,haz,hAB ha,hAB hb,hAB hc⟩

lemma fiber_union_cover (A B : Set ℕ) (N n z : ℕ) :
    fiber B N n z ⊆ (fiber A N n z ∪ newEndpoints A B n) ∪ newEndpoints A B z := by
  intro a ha
  obtain ⟨han,hNa,hNb,haz,haB,hbB,hcB⟩ := mem_fiber.mp ha
  by_cases hpair : a∈A ∧ n-a∈A
  · by_cases hc : z-a∈A
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (mem_fiber.mpr ⟨han,hNa,hNb,haz,hpair.1,hpair.2,hc⟩))
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨mem_repEndpoints.mpr ⟨haz,haB,hcB⟩,
        fun h ↦ hc (mem_repEndpoints.mp h).2.2⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_sdiff.mpr ⟨mem_repEndpoints.mpr ⟨han,haB,hbB⟩,
      fun h ↦ hpair (mem_repEndpoints.mp h).2⟩

lemma fiber_increment_bound (A B : Set ℕ) (hAB : A ⊆ B) (N n z : ℕ) :
    ((fiber B N n z).card : ℝ) ≤ (fiber A N n z).card+
      ((sumRep B n : ℝ)-sumRep A n)+((sumRep B z : ℝ)-sumRep A z) := by
  have hh := (Finset.card_le_card (fiber_union_cover A B N n z)).trans (Finset.card_union_le _ _)
  have hh' := Finset.card_union_le (fiber A N n z) (newEndpoints A B n)
  have hc : ((fiber B N n z).card : ℝ) ≤ (fiber A N n z).card+
      (newEndpoints A B n).card+(newEndpoints A B z).card := by exact_mod_cast (show
      (fiber B N n z).card ≤ (fiber A N n z).card+(newEndpoints A B n).card+(newEndpoints A B z).card by omega)
  rwa [newEndpoints_card A B hAB n,newEndpoints_card A B hAB z] at hc

lemma boundary_union_cover (A B : Set ℕ) (d n : ℕ) :
    boundary B d n ⊆ boundary A d n ∪ newEndpoints A B n := by
  intro a ha
  obtain ⟨har,haB,hbB⟩ := Finset.mem_filter.mp ha
  have han : a ≤ n := by have := Finset.mem_range.mp har; have := Nat.div_le_self n (d^2); omega
  by_cases hA : a∈A ∧ n-a∈A
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨har,hA⟩)
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨mem_repEndpoints.mpr ⟨han,haB,hbB⟩,
      fun h ↦ hA (mem_repEndpoints.mp h).2⟩)

lemma boundary_increment_bound (A B : Set ℕ) (hAB : A ⊆ B) (d n : ℕ) :
    ((boundary B d n).card : ℝ) ≤ (boundary A d n).card+((sumRep B n : ℝ)-sumRep A n) := by
  have hh := (Finset.card_le_card (boundary_union_cover A B d n)).trans (Finset.card_union_le _ _)
  have hh' : ((boundary B d n).card : ℝ) ≤ (boundary A d n).card+(newEndpoints A B n).card := by
    exact_mod_cast hh
  rwa [newEndpoints_card A B hAB n] at hh'

lemma fiber_eq_empty_of_small (A : Set ℕ) (N n z : ℕ) (h : n<N ∨ z<N) : fiber A N n z=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨han,hNa,_,haz,_⟩ := mem_fiber.mp ha
  omega

end Erdos66PatternInsertionDomination
