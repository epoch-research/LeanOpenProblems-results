import Submission.ChainRingDefinitions

/-! Normalizing the selected degree-three vertices within the three twin classes. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ChainRing
set_option maxHeartbeats 600000

lemma exists_perm_mem_iff {U : Type*} [Fintype U] [DecidableEq U]
    (A B : Finset U) (hc : A.card = B.card) :
    ∃ σ : Equiv.Perm U, ∀ j, j ∈ A ↔ σ j ∈ B := by
  let eA : (A : Set U) ≃ (B : Set U) := Finset.equivOfCardEq hc
  have hcc : Fintype.card ((A : Set U)ᶜ : Set U) = Fintype.card ((B : Set U)ᶜ : Set U) := by
    rw [Fintype.card_compl_set,Fintype.card_compl_set,Fintype.card_congr eA]
  let eC := Fintype.equivOfCardEq hcc
  obtain ⟨σ,hσ⟩ := (Equiv.Set.compl eA).symm eC
  refine ⟨σ,fun j => ⟨?_,?_⟩⟩
  · intro hj
    have he := hσ ⟨j,hj⟩
    have hm := (eA ⟨j,hj⟩).property
    simpa only [← he] using hm
  · intro hj
    let a := eA.symm ⟨σ j,hj⟩
    have he : σ a.val = σ j := (hσ a).trans (congrArg Subtype.val (eA.apply_symm_apply ⟨σ j,hj⟩))
    have haj := σ.injective he
    exact haj ▸ a.property

def vertexPerm (σ : Fin 3 → Equiv.Perm (Fin 6)) : Equiv.Perm Vertex where
  toFun
    | .inl h => .inl h
    | .inr (i,j) => .inr (i,σ i j)
  invFun
    | .inl h => .inl h
    | .inr (i,j) => .inr (i,(σ i).symm j)
  left_inv := by intro x; cases x with
    | inl h => rfl
    | inr p => rcases p with ⟨i,j⟩; simp
  right_inv := by intro x; cases x with
    | inl h => rfl
    | inr p => rcases p with ⟨i,j⟩; simp

noncomputable def activeIso (ring : Bool) (A B : Fin 3 → Finset (Fin 6))
    (σ : Fin 3 → Equiv.Perm (Fin 6)) (hσ : ∀ i j, j ∈ A i ↔ σ i j ∈ B i) :
    active ring A ≃g active ring B where
  toEquiv := vertexPerm σ
  map_rel_iff' := by
    intro x y
    cases x with
    | inl h =>
      cases y with
      | inl k => rfl
      | inr p =>
        rcases p with ⟨i,j⟩
        exact and_congr (hσ i j).symm Iff.rfl
    | inr p =>
      rcases p with ⟨i,j⟩
      cases y with
      | inl h => exact and_congr (hσ i j).symm Iff.rfl
      | inr q => rfl

lemma exists_canonical_iso (ring : Bool) (A : Fin 3 → Finset (Fin 6)) :
    ∃ a : Fin 3 → Fin 7, Nonempty (active ring A ≃g canonical ring a) := by
  let a : Fin 3 → Fin 7 := fun i => ⟨(A i).card,by
    have h := Finset.card_le_univ (A i)
    simp only [Fintype.card_fin] at h
    omega⟩
  have he : ∀ i, ∃ σ : Equiv.Perm (Fin 6), ∀ j, j ∈ A i ↔ σ j ∈ initial (a i) := by
    intro i
    apply exists_perm_mem_iff
    exact (initial_card (a i)).symm
  choose σ hσ using he
  exact ⟨a,⟨activeIso ring A (fun i => initial (a i)) σ hσ⟩⟩

lemma active_forestBound (ring : Bool)
    (hc : ∀ a : Fin 3 → Fin 7, ForestBound (canonical ring a))
    (A : Fin 3 → Finset (Fin 6)) : ForestBound (active ring A) := by
  obtain ⟨a,⟨e⟩⟩ := exists_canonical_iso ring A
  exact (hc a).of_iso e.symm

end Erdos184Work.ChainRing
#print axioms Erdos184Work.ChainRing.active_forestBound
