import Submission.RobustOddWheel

/-!
A minimal persistent odd-wheel normal form. This is conditional on a
non-coverable graph and does not settle Erdos 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595MinimalRobustOddWheel
open Erdos595Work Erdos595RobustOddWheel

variable {V : Type*}

def Persistent (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ D : SimpleGraph V, IsCountableUnionOfTriangleFree D → WheelWalk (G \ D) n

lemma cover_sup (G H : SimpleGraph V)
    (hG : IsCountableUnionOfTriangleFree G)
    (hH : IsCountableUnionOfTriangleFree H) :
    IsCountableUnionOfTriangleFree (G ⊔ H) := by
  let K : ℕ → SimpleGraph V := fun n => if n = 0 then G else H
  have hK : ∀ n, IsCountableUnionOfTriangleFree (K n) := by
    intro n
    dsimp [K]
    split_ifs <;> assumption
  have he : (⨆ n, K n) = G ⊔ H := by
    ext a b
    simp only [SimpleGraph.iSup_adj,SimpleGraph.sup_adj]
    constructor
    · rintro ⟨n,hn⟩
      by_cases he : n = 0
      · exact Or.inl (by simpa [K,he] using hn)
      · exact Or.inr (by simpa [K,he] using hn)
    · rintro (h | h)
      · exact ⟨0,by simpa [K] using h⟩
      · exact ⟨1,by simpa [K] using h⟩
  rw [← he]
  exact Erdos595LocalTuple.cover_iSup K hK

lemma persistent_diff (G E : SimpleGraph V)
    (hE : IsCountableUnionOfTriangleFree E) {n : ℕ}
    (hn : Persistent G n) : Persistent (G \ E) n := by
  intro D hD
  have hw := hn (E ⊔ D) (cover_sup E D hE hD)
  have he : G \ (E ⊔ D) = (G \ E) \ D := by
    ext a b
    simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj,not_or,and_assoc]
  exact he ▸ hw

/-- After deleting a covered edge graph, the least persistent odd rim-walk
length is also the least odd rim-walk length that occurs at all. The rim is
still formulated as a walk; no induced-cycle claim is made here. -/
theorem minimal_residual (G : SimpleGraph V) (hK : G.CliqueFree 4)
    (hG : ¬IsCountableUnionOfTriangleFree G) :
    ∃ (E : SimpleGraph V) (n : ℕ),
      IsCountableUnionOfTriangleFree E ∧
      (G \ E).CliqueFree 4 ∧ ¬IsCountableUnionOfTriangleFree (G \ E) ∧
      5 ≤ n ∧ Odd n ∧ Persistent (G \ E) n ∧
      ∀ m < n, Odd m → ¬WheelWalk (G \ E) m := by
  classical
  have hp : ∃ n, Odd n ∧ Persistent G n := fixed_odd_length G hG
  let n := Nat.find hp
  have hn : Odd n ∧ Persistent G n := Nat.find_spec hp
  have hless : ∀ m < n, Odd m → ¬Persistent G m := by
    intro m hm ho hper
    exact (Nat.find_min hp hm) ⟨ho,hper⟩
  have hD : ∀ m : ℕ, ∃ D : SimpleGraph V,
      IsCountableUnionOfTriangleFree D ∧
        (m < n → Odd m → ¬WheelWalk (G \ D) m) := by
    intro m
    by_cases hm : m < n ∧ Odd m
    · have hh := hless m hm.1 hm.2
      simp only [Persistent,not_forall] at hh
      obtain ⟨D,hD,hw⟩ := hh
      exact ⟨D,hD,fun _ _ => hw⟩
    · refine ⟨⊥,⟨fun _ => ⊥,fun _ => SimpleGraph.cliqueFree_bot (by decide),by simp⟩,?_⟩
      exact fun hlt ho => (hm ⟨hlt,ho⟩).elim
  choose D hD hw using hD
  let E : SimpleGraph V := ⨆ m, D m
  have hE : IsCountableUnionOfTriangleFree E := Erdos595LocalTuple.cover_iSup D hD
  have hnot : ¬IsCountableUnionOfTriangleFree (G \ E) :=
    fun h => hG (cover_diff G E hE h)
  have h5 : 5 ≤ n := by
    have hb : IsCountableUnionOfTriangleFree (⊥ : SimpleGraph V) :=
      ⟨fun _ => ⊥,fun _ => SimpleGraph.cliqueFree_bot (by decide),by simp⟩
    have hwG : WheelWalk G n := by simpa using hn.2 ⊥ hb
    have h1 : n ≠ 1 := fun he => not_wheelWalk_one G (he ▸ hwG)
    have h3 : n ≠ 3 := fun he => not_wheelWalk_three G hK (he ▸ hwG)
    obtain ⟨k,hk⟩ := hn.1
    omega
  refine ⟨E,n,hE,hK.anti (fun _ _ h => h.1),hnot,h5,hn.1,
    persistent_diff G E hE hn.2,?_⟩
  intro m hm ho hwalk
  apply hw m hm ho
  apply wheelWalk_mono (G := G \ E) (H := G \ D m) ?_ hwalk
  intro a b hab
  exact ⟨hab.1,fun h => hab.2 (SimpleGraph.iSup_adj.mpr ⟨m,h⟩)⟩

#print axioms minimal_residual
#print axioms persistent_diff
end Erdos595MinimalRobustOddWheel
