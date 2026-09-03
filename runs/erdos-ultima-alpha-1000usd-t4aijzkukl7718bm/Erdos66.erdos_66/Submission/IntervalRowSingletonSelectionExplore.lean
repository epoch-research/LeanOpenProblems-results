import Submission.RowAdaptiveHitSelectionExplore
import Submission.EqualWidthRowPackingExplore

/-! Adaptive insertion into disjoint equal-width rows. The old degree may vary
with the row; the previously selected new points contribute at most two. -/
namespace Erdos66IntervalRowSingletonSelection
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66FiniteSwapAlgebra
  Erdos66AdaptiveSingletonAlgebra Erdos66AdaptivePacketChoice
  Erdos66RowAdaptiveHitSelection Erdos66EqualWidthRowPacking
open scoped Classical
set_option maxHeartbeats 3200000

 theorem exists_interval_singletons
    (A : Finset ℕ) (L : ℕ → ℕ) (w m : ℕ)
    (hsep : ∀ i < m, ∀ j < m, i≠j → L i+w ≤ L j ∨ L j+w ≤ L i)
    (B q t : ℝ) (T : Finset ℕ) (K : ℕ → ℕ → ℝ) (R : ℕ → ℝ)
    (hq : 0<q) (ht : 0<t)
    (hB : ∀ k < m, ((Finset.univ.filter (fun i : Fin w ↦ L k+i.val∈A)).card : ℝ) ≤ B)
    (hbudget : q+B ≤ w)
    (hK : ∀ k < m, ∀ z∈T,
      ((partnerChoices A (fun i : Fin w ↦ L k+i.val) z).card : ℝ) ≤ K k z)
    (hsmall : (∑ z∈T, Real.exp
      ((∑ k∈Finset.range m, Real.exp t*(K k z+3)/q)-t*R z))<1) :
    ∃ F : Finset ℕ, F.card=m ∧ Disjoint A F ∧
      (∀ u∈F, ∃ k < m, ∃ i : Fin w, u=L k+i.val) ∧
      (∀ k < m, ∃ i : Fin w, L k+i.val∈F) ∧
      ∀ z∈T, insertionEnergy A F z<5*R z := by
  classical
  letI : DecidableEq (Fin w) := fun a b ↦ Classical.propDecidable (a=b)
  let f (k : ℕ) (i : Fin w) := L k+i.val
  have hf (k : ℕ) : Function.Injective (f k) := by
    intro i j he
    apply Fin.ext
    dsimp only [f] at he
    omega
  have hrow (k : ℕ) (i : Fin w) : L k ≤ f k i ∧ f k i < L k+w := by
    dsimp only [f]
    have := i.isLt
    omega
  let Inv (k : ℕ) (F : Finset ℕ) : Prop := F.card=k ∧ Disjoint A F ∧
    (∀ u∈F, ∃ j < k, ∃ i, u=f j i) ∧
    (∀ j < k, ∃ i, f j i∈F) ∧
    (∀ j < m, ∀ u∈F, ∀ v∈F,
      (L j ≤ u ∧ u < L j+w) → (L j ≤ v ∧ v < L j+w) → u=v)
  let choices (k : ℕ) (_F : Finset ℕ) := Finset.univ.filter (fun i : Fin w ↦ f k i∉A)
  let next (k : ℕ) (F : Finset ℕ) (i : Fin w) := insert (f k i) F
  let load (F : Finset ℕ) (z : ℕ) := insertionEnergy A F z/5
  let hit (k : ℕ) (F : Finset ℕ) (z : ℕ) := insertionHits A F (f k) z
  let b (k z : ℕ) := Real.exp t*(K k z+3)/q
  have h₀ : Inv 0 ∅ := by simp [Inv]
  have hl₀ : ∀ z∈T, load ∅ z=0 := by simp [load,insertionEnergy,pairs,sumRep_def]
  have hav : ∀ k < m, ∀ F, Inv k F → q ≤ (choices k F).card := by
    intro k hk F _
    have he := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin w)))
      (p := fun i ↦ f k i∈A)
    have he' : ((Finset.univ.filter (fun i : Fin w ↦ f k i∈A)).card : ℝ)+
        (choices k F).card=w := by
      simp only [Finset.card_univ, Fintype.card_fin] at he
      exact_mod_cast he
    have hh := hB k hk
    change ((Finset.univ.filter (fun i : Fin w ↦ f k i∈A)).card : ℝ) ≤ B at hh
    linarith
  have hfresh (k : ℕ) (hk : k < m) (F : Finset ℕ) (hF : Inv k F) (i : Fin w) : f k i∉F := by
    intro hi
    obtain ⟨j,hj,a,he⟩ := hF.2.2.1 (f k i) hi
    have hsame := row_unique L w m hsep k j (f k i) hk (by omega) (hrow k i)
      (by rw [he]; exact hrow j a)
    omega
  have hnext : ∀ k < m, ∀ F, Inv k F → ∀ a∈choices k F, Inv (k+1) (next k F a) := by
    intro k hk F hF a ha
    have hnew : f k a∉A := (Finset.mem_filter.mp ha).2
    have hfresh' := hfresh k hk F hF a
    obtain ⟨hcard,hAF,hpoints,hcover,huniq⟩ := hF
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
    · intro j hj u hu v hv huj hvj
      rcases Finset.mem_insert.mp hu with rfl | hu <;>
        rcases Finset.mem_insert.mp hv with rfl | hv
      · rfl
      · have hkj := row_unique L w m hsep k j (f k a) hk hj (hrow k a) huj
        obtain ⟨i,hi,c,rfl⟩ := hpoints v hv
        have hij := row_unique L w m hsep i j (f i c) (by omega) hj (hrow i c) hvj
        omega
      · have hkj := row_unique L w m hsep k j (f k a) hk hj (hrow k a) hvj
        obtain ⟨i,hi,c,rfl⟩ := hpoints u hu
        have hij := row_unique L w m hsep i j (f i c) (by omega) hj (hrow i c) huj
        omega
      · exact huniq j hj u hu v hv huj hvj
  have hhit : ∀ k < m, ∀ F, Inv k F → ∀ z∈T, ((hit k F z).card : ℝ) ≤ K k z+3 := by
    intro k hk F hF z hz
    have hp : ∀ u∈F, ∃ j < m, L j ≤ u ∧ u < L j+w := by
      intro u hu
      obtain ⟨j,hj,a,rfl⟩ := hF.2.2.1 u hu
      exact ⟨j,by omega,hrow j a⟩
    have hFbound : ((partnerChoices F (f k) z).card : ℝ) ≤ 2 := by
      exact_mod_cast partnerChoices_card_le_two L w m hsep F hp hF.2.2.2.2 (L k) z
    have hd : ((Finset.univ.filter (fun a : Fin w ↦ 2*f k a=z)).card : ℝ) ≤ 1 := by
      exact_mod_cast injective_double_card (f k) (hf k) z
    have hu : ((hit k F z).card : ℝ) ≤
        (partnerChoices A (f k) z).card+(partnerChoices F (f k) z).card+
          (Finset.univ.filter (fun a : Fin w ↦ 2*f k a=z)).card := by
      have h1 := Finset.card_union_le (partnerChoices A (f k) z ∪ partnerChoices F (f k) z)
        (Finset.univ.filter (fun a : Fin w ↦ 2*f k a=z))
      have h2 := Finset.card_union_le (partnerChoices A (f k) z) (partnerChoices F (f k) z)
      dsimp only [hit,insertionHits]
      exact_mod_cast h1.trans (Nat.add_le_add_right h2 _)
    have hA := hK k hk z hz
    change ((partnerChoices A (f k) z).card : ℝ) ≤ K k z at hA
    linarith
  have hload : ∀ k < m, ∀ F, Inv k F → ∀ a∈choices k F, ∀ z∈T,
      load (next k F a) z ≤ load F z+(if a∈hit k F z then 1 else 0) := by
    intro k hk F hF a _ z _
    have hh := insertionEnergy_step A F (f k) a (hfresh k hk F hF a) z
    dsimp only [load,next,hit]
    split_ifs at hh ⊢ <;> linarith
  obtain ⟨F,hF,hload⟩ := exists_row_adaptive_small_hits m ∅ Inv choices next load hit T q t
    (fun k z ↦ K k z+3) b R hq ht h₀ hl₀ hav hnext hhit hload
    (fun _ _ _ _ ↦ le_rfl) hsmall
  refine ⟨F,hF.1,hF.2.1,hF.2.2.1,hF.2.2.2.1,?_⟩
  intro z hz
  have hh := hload z hz
  dsimp only [load] at hh
  linarith

end Erdos66IntervalRowSingletonSelection
