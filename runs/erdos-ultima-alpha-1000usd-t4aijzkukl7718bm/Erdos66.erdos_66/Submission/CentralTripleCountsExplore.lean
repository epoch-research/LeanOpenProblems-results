import Submission.FiniteTripleIntersectionSelectionExplore
import Submission.PrefixBalancedCostCompactnessExplore

/-! Actual central triple-intersection counts, their Boolean encoding, and
the at-most-two repeated-coordinate exceptions at distinct targets. -/
namespace Erdos66CentralTripleCounts
open Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli Erdos66TripleIntersectionGeometry
  Erdos66BernoulliMatchingPolynomial Erdos66Compactness
open scoped Classical Topology
set_option maxHeartbeats 2200000

noncomputable def fiber (A : Set ℕ) (N n z : ℕ) : Finset ℕ :=
  (Finset.range (n+1)).filter (fun a ↦ N ≤ a ∧ N ≤ n-a ∧ a ≤ z ∧
    a∈A ∧ n-a∈A ∧ z-a∈A)

lemma mem_fiber {A : Set ℕ} {N n z a : ℕ} : a∈fiber A N n z ↔
    a ≤ n ∧ N ≤ a ∧ N ≤ n-a ∧ a ≤ z ∧ a∈A ∧ n-a∈A ∧ z-a∈A := by
  simp only [fiber,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]

noncomputable def regular (A : Set ℕ) (N n z : ℕ) : Finset ℕ :=
  (fiber A N n z).filter (fun a ↦ a≠n-a ∧ a≠z-a ∧ n-a≠z-a)

lemma selected_bound {L a : ℕ} {ω : Fin (L+1) → Bool} (ha : a∈selected L ω) : a<L+1 := by
  obtain ⟨i,rfl,_⟩ := ha
  exact i.isLt

lemma selected_regular_image (L N n z : ℕ) (ω : Fin (L+1) → Bool) :
    regular (selected L ω) N n z = (realized (triples L N n z) coords ω).image (fun e ↦ e.1.val) := by
  ext a
  constructor
  · intro ha
    obtain ⟨ha,hab,hac,hbc⟩ := Finset.mem_filter.mp ha
    obtain ⟨han,hNa,hNb,haz,haA,hbA,hcA⟩ := mem_fiber.mp ha
    let x : Fin (L+1) := ⟨a,selected_bound haA⟩
    let y : Fin (L+1) := ⟨n-a,selected_bound hbA⟩
    let v : Fin (L+1) := ⟨z-a,selected_bound hcA⟩
    have hxy : x≠y := fun he ↦ hab (congrArg Fin.val he)
    have hxv : x≠v := fun he ↦ hac (congrArg Fin.val he)
    have hyv : y≠v := fun he ↦ hbc (congrArg Fin.val he)
    apply Finset.mem_image.mpr
    refine ⟨(x,y,v),(mem_realized _ _ _ _).mpr ⟨mem_triples.mpr
      ⟨hNa,hNb,by dsimp [x,y]; omega,by dsimp [x,v]; omega,hxy,hxv,hyv⟩,?_⟩,rfl⟩
    intro i hi
    simp only [coords,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact (mem_selected L ω x).mp haA
    · exact (mem_selected L ω y).mp hbA
    · exact (mem_selected L ω v).mp hcA
  · intro ha
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨he,hω⟩ := (mem_realized _ _ _ _).mp he
    obtain ⟨hNa,hNb,hn,hz,hab,hac,hbc⟩ := mem_triples.mp he
    have hb : n-e.1.val=e.2.1.val := by omega
    have hc : z-e.1.val=e.2.2.val := by omega
    apply Finset.mem_filter.mpr
    refine ⟨mem_fiber.mpr ⟨by omega,hNa,by omega,by omega,?_,?_,?_⟩,?_,?_,?_⟩
    · exact (mem_selected L ω e.1).mpr (hω _ (by simp [coords]))
    · rw [hb]; exact (mem_selected L ω e.2.1).mpr (hω _ (by simp [coords]))
    · rw [hc]; exact (mem_selected L ω e.2.2).mpr (hω _ (by simp [coords]))
    · rw [hb]; exact fun he ↦ hab (Fin.ext he)
    · rw [hc]; exact fun he ↦ hac (Fin.ext he)
    · rw [hb,hc]; exact fun he ↦ hbc (Fin.ext he)

lemma selected_regular_card (L N n z : ℕ) (ω : Fin (L+1) → Bool) :
    (regular (selected L ω) N n z).card = (realized (triples L N n z) coords ω).card := by
  rw [selected_regular_image]
  exact Finset.card_image_iff.mpr (first_injective.mono (realized_subset _ _ _))

lemma fiber_card_le_regular_add_two (A : Set ℕ) (N n z : ℕ) (hnz : n≠z) :
    (fiber A N n z).card ≤ (regular A N n z).card+2 := by
  let F := fiber A N n z
  let P : ℕ → Prop := fun a ↦ a≠n-a ∧ a≠z-a ∧ n-a≠z-a
  have hb : F.filter (fun a ↦ ¬P a) ⊆ {n/2,z/2} := by
    intro a ha
    obtain ⟨ha,hbad⟩ := Finset.mem_filter.mp ha
    obtain ⟨han,_,_,haz,_⟩ := mem_fiber.mp ha
    change ¬(a≠n-a ∧ a≠z-a ∧ n-a≠z-a) at hbad
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have hh := (Finset.card_le_card hb).trans (Finset.card_le_two : ({n/2,z/2} : Finset ℕ).card ≤ 2)
  have hs := Finset.card_filter_add_card_filter_not (s := F) (p := P)
  change (F.filter P).card+(F.filter (fun a ↦ ¬P a)).card=F.card at hs
  change F.card ≤ (F.filter P).card+2
  omega

lemma selected_fiber_bound (L N n z K : ℕ) (ω : Fin (L+1) → Bool) (hnz : n≠z)
    (hK : (realized (triples L N n z) coords ω).card ≤ K) :
    (fiber (selected L ω) N n z).card ≤ K+2 := by
  have hh := fiber_card_le_regular_add_two (selected L ω) N n z hnz
  rw [selected_regular_card] at hh
  omega

noncomputable def encoded (f : ℕ → Bool) (N n z : ℕ) : ℝ :=
  ∑ a∈Finset.range (n+1), if N ≤ a ∧ N ≤ n-a ∧ a ≤ z then
    bit (f a)*bit (f (n-a))*bit (f (z-a)) else 0

lemma continuous_encoded (N n z : ℕ) : Continuous (fun f : ℕ → Bool ↦ encoded f N n z) := by
  apply continuous_finset_sum
  intro a ha
  by_cases h : N ≤ a ∧ N ≤ n-a ∧ a ≤ z
  · simp only [if_pos h]
    exact (((continuous_of_discreteTopology (f := bit)).comp (continuous_apply a)).mul
      ((continuous_of_discreteTopology (f := bit)).comp (continuous_apply (n-a)))).mul
      ((continuous_of_discreteTopology (f := bit)).comp (continuous_apply (z-a)))
  · simp only [if_neg h]; exact continuous_const

lemma encoded_decide (A : Set ℕ) (N n z : ℕ) :
    encoded (fun i ↦ decide (i∈A)) N n z = ((fiber A N n z).card : ℝ) := by
  rw [fiber,Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : N ≤ a ∧ N ≤ n-a ∧ a ≤ z
  · obtain ⟨hNa,hNb,haz⟩ := h
    by_cases h1 : a∈A <;> by_cases h2 : n-a∈A <;> by_cases h3 : z-a∈A <;>
      simp [bit,hNa,hNb,haz,h1,h2,h3]
  · have hh : ¬(N ≤ a ∧ N ≤ n-a ∧ a ≤ z ∧ a∈A ∧ n-a∈A ∧ z-a∈A) :=
      fun hh ↦ h ⟨hh.1,hh.2.1,hh.2.2.1⟩
    simp only [if_neg h,if_neg hh]

lemma encoded_eq_fiber (f : ℕ → Bool) (N n z : ℕ) :
    encoded f N n z = ((fiber {i | f i=true} N n z).card : ℝ) := by
  simpa using encoded_decide {i | f i=true} N n z

end Erdos66CentralTripleCounts
