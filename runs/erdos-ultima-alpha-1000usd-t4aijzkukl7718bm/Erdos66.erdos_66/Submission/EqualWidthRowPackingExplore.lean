import Submission.AdaptiveSingletonAlgebraExplore

/-! Local packing for one selected point per disjoint equal-width interval. -/
namespace Erdos66EqualWidthRowPacking
open scoped Classical
set_option maxHeartbeats 1200000

/-- Disjoint equal-width rows have unique row membership. -/
lemma row_unique (L : ℕ → ℕ) (w m : ℕ)
    (hsep : ∀ i < m, ∀ j < m, i≠j → L i+w ≤ L j ∨ L j+w ≤ L i)
    (i j u : ℕ) (hi : i < m) (hj : j < m)
    (hui : L i ≤ u ∧ u < L i+w) (huj : L j ≤ u ∧ u < L j+w) : i=j := by
  by_contra hij
  rcases hsep i hi j hj hij with h | h <;> omega

/-- A window of width `w` contains at most two points of a partial transversal
of disjoint rows of width `w`. -/
lemma local_card_le_two (L : ℕ → ℕ) (w m : ℕ)
    (hsep : ∀ i < m, ∀ j < m, i≠j → L i+w ≤ L j ∨ L j+w ≤ L i)
    (F : Finset ℕ)
    (hpoints : ∀ u∈F, ∃ j < m, L j ≤ u ∧ u < L j+w)
    (huniq : ∀ j < m, ∀ u∈F, ∀ v∈F,
      (L j ≤ u ∧ u < L j+w) → (L j ≤ v ∧ v < L j+w) → u=v)
    (a : ℕ) : (F.filter (fun u ↦ a ≤ u ∧ u < a+w)).card ≤ 2 := by
  by_contra hc
  obtain ⟨u,v,x,hu,hv,hx,huv,hux,hvx⟩ := Finset.two_lt_card_iff.mp (by omega :
    2 < (F.filter (fun u ↦ a ≤ u ∧ u < a+w)).card)
  obtain ⟨huF,huI⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvF,hvI⟩ := Finset.mem_filter.mp hv
  obtain ⟨hxF,hxI⟩ := Finset.mem_filter.mp hx
  obtain ⟨i,hi,hui⟩ := hpoints u huF
  obtain ⟨j,hj,hvj⟩ := hpoints v hvF
  obtain ⟨k,hk,hxk⟩ := hpoints x hxF
  have hij : i≠j := by
    rintro rfl
    exact huv (huniq i hi u huF v hvF hui hvj)
  have hik : i≠k := by
    rintro rfl
    exact hux (huniq i hi u huF x hxF hui hxk)
  have hjk : j≠k := by
    rintro rfl
    exact hvx (huniq j hj v hvF x hxF hvj hxk)
  rcases hsep i hi j hj hij with h | h <;>
    rcases hsep i hi k hk hik with h' | h' <;>
    rcases hsep j hj k hk hjk with h'' | h'' <;> omega

/-- The reflected partners of one interval have the same local packing bound. -/
lemma partnerChoices_card_le_two (L : ℕ → ℕ) (w m : ℕ)
    (hsep : ∀ i < m, ∀ j < m, i≠j → L i+w ≤ L j ∨ L j+w ≤ L i)
    (F : Finset ℕ)
    (hpoints : ∀ u∈F, ∃ j < m, L j ≤ u ∧ u < L j+w)
    (huniq : ∀ j < m, ∀ u∈F, ∀ v∈F,
      (L j ≤ u ∧ u < L j+w) → (L j ≤ v ∧ v < L j+w) → u=v)
    (b z : ℕ) :
    (Erdos66AdaptiveSingletonAlgebra.partnerChoices F (fun i : Fin w ↦ b+i.val) z).card ≤ 2 := by
  apply le_trans (b := (F.filter (fun u ↦ z+1-(b+w) ≤ u ∧ u < z+1-(b+w)+w)).card)
  · apply Finset.card_le_card_of_injOn (fun i : Fin w ↦ z-(b+i.val))
    · intro i hi
      simp only [Erdos66AdaptiveSingletonAlgebra.partnerChoices, Finset.mem_coe,
        Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨hi,hF⟩ := hi
      apply Finset.mem_filter.mpr
      exact ⟨hF,by dsimp only; have := i.isLt; omega⟩
    · intro i hi j hj he
      simp only [Erdos66AdaptiveSingletonAlgebra.partnerChoices, Finset.mem_coe,
        Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      change z-(b+i.val)=z-(b+j.val) at he
      apply Fin.ext
      omega
  · exact local_card_le_two L w m hsep F hpoints huniq _

end Erdos66EqualWidthRowPacking
