import Submission.AdaptiveSingletonAlgebraExplore
import Submission.AdaptiveHitSelectionExplore

/-! One replacement per disjoint candidate row, with a common insertion-load
potential. The prescribed deletion set is not included in this load. -/
namespace Erdos66AdaptiveSingletonSelection
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66FiniteSwapAlgebra
  Erdos66AdaptiveSingletonAlgebra Erdos66AdaptiveHitSelection
open scoped Classical
set_option maxHeartbeats 3200000

 theorem exists_adaptive_singletons {α : Type*} [Fintype α]
    (A : Finset ℕ) (n m : ℕ) (f : ℕ → α → ℕ)
    (hinj : ∀ k < m, Function.Injective (f k))
    (hrows : ∀ i < m, ∀ j < m, i≠j → ∀ a b, f i a≠f j b)
    (hhalf : ∀ k < m, ∀ a, n<2*f k a)
    (B₀ B₁ : ℝ)
    (hB₀ : ∀ k < m, ((Finset.univ.filter (fun a ↦ f k a∈A)).card : ℝ) ≤ B₀)
    (hB₁ : ∀ k < m, ((partnerChoices A (f k) n).card : ℝ) ≤ B₁)
    (T : Finset ℕ) (q t : ℝ) (K R : ℕ → ℝ) (hq : 0<q) (ht : 0<t)
    (hK : ∀ k < m, ∀ z∈T, ((partnerChoices A (f k) z).card : ℝ) ≤ K z)
    (hbudget : q+B₀+B₁ ≤ Fintype.card α)
    (hsmall : (∑ z∈T, Real.exp ((m : ℝ)*(Real.exp t*(K z+m+1)/q)-t*R z))<1) :
    ∃ F : Finset ℕ, F.card=m ∧ Disjoint A F ∧
      (∀ u∈F, ∃ k < m, ∃ a, u=f k a) ∧
      (∀ k < m, ∃ a, f k a∈F) ∧
      pairs F A n=0 ∧ sumRep (F : Set ℕ) n=0 ∧
      ∀ z∈T, insertionEnergy A F z<5*R z := by
  let Inv (k : ℕ) (F : Finset ℕ) : Prop := F.card=k ∧ Disjoint A F ∧
    (∀ u∈F, ∃ j < k, ∃ a, u=f j a) ∧
    (∀ j < k, ∃ a, f j a∈F) ∧ pairs F A n=0
  let choices (k : ℕ) (_F : Finset ℕ) := insertionChoices A (f k) n
  let next (k : ℕ) (F : Finset ℕ) (a : α) := insert (f k a) F
  let load (F : Finset ℕ) (z : ℕ) := insertionEnergy A F z/5
  let hit (k : ℕ) (F : Finset ℕ) (z : ℕ) := insertionHits A F (f k) z
  let b (z : ℕ) := Real.exp t*(K z+m+1)/q
  have h₀ : Inv 0 ∅ := by simp [Inv,pairs]
  have hl₀ : ∀ z∈T, load ∅ z=0 := by simp [load,insertionEnergy,pairs,sumRep_def]
  have hav : ∀ k < m, ∀ F, Inv k F → q ≤ (choices k F).card := by
    intro k hk F hF
    exact insertionChoices_card A (f k) n B₀ B₁ q (hB₀ k hk) (hB₁ k hk) hbudget
  have hfresh (k : ℕ) (hk : k < m) (F : Finset ℕ) (hF : Inv k F) (a : α) : f k a∉F := by
    intro ha
    obtain ⟨j,hj,b,he⟩ := hF.2.2.1 (f k a) ha
    exact hrows k hk j (by omega) (by omega) a b he
  have hnext : ∀ k < m, ∀ F, Inv k F → ∀ a∈choices k F, Inv (k+1) (next k F a) := by
    intro k hk F hF a ha
    obtain ⟨hcard,hAF,hpoints,hcover,hcenter⟩ := hF
    have hfresh' : f k a∉F := hfresh k hk F ⟨hcard,hAF,hpoints,hcover,hcenter⟩ a
    obtain ⟨hnew,hzero⟩ := insertionChoices_properties A (f k) n a ha
    refine ⟨?_,?_,?_,?_,?_⟩
    · dsimp only [next]
      rw [Finset.card_insert_of_notMem hfresh',hcard]
    · exact Finset.disjoint_insert_right.mpr ⟨hnew,hAF⟩
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact ⟨k,by omega,a,rfl⟩
      · obtain ⟨j,hj,b,he⟩ := hpoints u hu
        exact ⟨j,by omega,b,he⟩
    · intro j hj
      by_cases he : j=k
      · subst j
        exact ⟨a,Finset.mem_insert_self _ _⟩
      · obtain ⟨b,hb⟩ := hcover j (by omega)
        exact ⟨b,Finset.mem_insert_of_mem hb⟩
    · have hd : Disjoint ({f k a} : Finset ℕ) F := by simpa using hfresh'
      have he : ({f k a} : Finset ℕ)∪F=insert (f k a) F := by simp
      dsimp only [next]
      rw [←he,pairs_union_left _ _ _ _ hd,hzero,hcenter]
  have hhit : ∀ k < m, ∀ F, Inv k F → ∀ z∈T, ((hit k F z).card : ℝ) ≤ K z+m+1 := by
    intro k hk F hF z hz
    have hh := insertionHits_card A F (f k) (hinj k hk) z (K z) (hK k hk z hz)
    have hc : (F.card : ℝ)=k := by exact_mod_cast hF.1
    have hkm : (k : ℝ) ≤ m := by exact_mod_cast hk.le
    change ((insertionHits A F (f k) z).card : ℝ) ≤ _
    linarith
  have hload : ∀ k < m, ∀ F, Inv k F → ∀ a∈choices k F, ∀ z∈T,
      load (next k F a) z ≤ load F z+(if a∈hit k F z then 1 else 0) := by
    intro k hk F hF a ha z hz
    have hh := insertionEnergy_step A F (f k) a (hfresh k hk F hF a) z
    dsimp only [load,next,hit]
    linarith
  obtain ⟨F,hF,hload⟩ := exists_adaptive_small_hits m ∅ Inv choices next load hit T q t
    (fun z ↦ K z+m+1) b R hq ht h₀ hl₀ hav hnext hhit hload (fun _ _ ↦ le_rfl) hsmall
  refine ⟨F,hF.1,hF.2.1,hF.2.2.1,hF.2.2.2.1,hF.2.2.2.2,?_,?_⟩
  · rw [←pairs_self]
    have hu (u : ℕ) (hu : u∈F) : n<2*u := by
      obtain ⟨k,hk,a,rfl⟩ := hF.2.2.1 u hu
      exact hhalf k hk a
    exact pairs_above_half F F n hu hu
  · intro z hz
    have hh := hload z hz
    dsimp only [load] at hh
    linarith

end Erdos66AdaptiveSingletonSelection
