import Submission.LocalChromaticProduct
import Submission.LocalTupleCover
import Submission.CountableBadEdgeFilter

/-!
A fixed-length odd wheel walk persists after every coverable edge deletion
in any graph without a countable triangle-free edge cover. This necessary
condition does not supply a K4-free example or settle Erdos 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595RobustOddWheel
open Erdos595Work

variable {V : Type*}

/-- A closed rim walk of the specified length in one vertex neighborhood. -/
def WheelWalk (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ v : V, ∃ a : G.neighborSet v,
    ∃ w : (G.induce (G.neighborSet v)).Walk a a, w.length = n

lemma wheelWalk_mono {G H : SimpleGraph V} (hGH : G ≤ H) {n : ℕ}
    (hw : WheelWalk G n) : WheelWalk H n := by
  obtain ⟨v,a,w,hw⟩ := hw
  let f : G.induce (G.neighborSet v) →g H.induce (H.neighborSet v) :=
    ⟨fun x => ⟨x.val,hGH x.property⟩,fun h => hGH h⟩
  exact ⟨v,f a,w.map f,by simpa only [SimpleGraph.Walk.length_map] using hw⟩

lemma cover_of_no_odd_wheel (G : SimpleGraph V)
    (hG : ∀ n, Odd n → ¬WheelWalk G n) :
    IsCountableUnionOfTriangleFree G := by
  apply Erdos595LocalChromaticProduct.cover_of_neighborhood_colorings
  intro v
  have hb : (G.induce (G.neighborSet v)).Colorable 2 := by
    apply SimpleGraph.two_colorable_iff_forall_loop_even.mpr
    intro a w
    apply Nat.not_odd_iff_even.mp
    intro ho
    exact hG w.length ho ⟨v,a,w,rfl⟩
  obtain ⟨c⟩ := hb
  exact ⟨SimpleGraph.Coloring.mk (fun a => (c a).val)
    (fun h he => c.valid h (Fin.ext he))⟩

lemma cover_diff (G D : SimpleGraph V)
    (hD : IsCountableUnionOfTriangleFree D)
    (hR : IsCountableUnionOfTriangleFree (G \ D)) :
    IsCountableUnionOfTriangleFree G := by
  obtain ⟨H,hH,hcov⟩ := hD
  obtain ⟨K,hK,hcovK⟩ := hR
  apply Erdos595CountableBadEdge.cover_of_countable_family G
    (fun i : ℕ × Bool => if i.2 then H i.1 else K i.1)
  · intro i
    split_ifs <;> simp_all
  · intro a b hab
    by_cases hd : D.Adj a b
    · rw [hcov,SimpleGraph.iSup_adj] at hd
      obtain ⟨n,hn⟩ := hd
      exact ⟨(n,true),hn⟩
    · have hr : (G \ D).Adj a b := ⟨hab,hd⟩
      rw [hcovK,SimpleGraph.iSup_adj] at hr
      obtain ⟨n,hn⟩ := hr
      exact ⟨(n,false),hn⟩

/-- Countable completeness fixes one odd length before any covered deletion
is chosen. No assertion about an infinite inverse-limit thread is used. -/
theorem fixed_odd_length (G : SimpleGraph V)
    (hG : ¬IsCountableUnionOfTriangleFree G) :
    ∃ n : ℕ, Odd n ∧ ∀ D : SimpleGraph V,
      IsCountableUnionOfTriangleFree D → WheelWalk (G \ D) n := by
  classical
  by_contra hn
  push_neg at hn
  have hd : ∀ n : ℕ, ∃ D : SimpleGraph V,
      IsCountableUnionOfTriangleFree D ∧ (Odd n → ¬WheelWalk (G \ D) n) := by
    intro n
    by_cases ho : Odd n
    · obtain ⟨D,hD,hw⟩ := hn n ho
      exact ⟨D,hD,fun _ => hw⟩
    · exact ⟨⊥,⟨fun _ => ⊥,fun _ => SimpleGraph.cliqueFree_bot (by decide),by simp⟩,
        fun h => (ho h).elim⟩
  choose D hD hw using hd
  let E : SimpleGraph V := ⨆ n, D n
  have hE : IsCountableUnionOfTriangleFree E := Erdos595LocalTuple.cover_iSup D hD
  apply hG (cover_diff G E hE ?_)
  apply cover_of_no_odd_wheel
  intro n ho hwalk
  apply hw n ho
  apply wheelWalk_mono (G := G \ E) (H := G \ D n) ?_ hwalk
  intro a b hab
  exact ⟨hab.1,fun h => hab.2 (SimpleGraph.iSup_adj.mpr ⟨n,h⟩)⟩

/-- A loopless graph has no one-step wheel rim. -/
lemma not_wheelWalk_one (G : SimpleGraph V) : ¬WheelWalk G 1 := by
  rintro ⟨v,a,w,hw⟩
  exact (SimpleGraph.Walk.adj_of_length_eq_one hw).ne rfl

/-- A three-step wheel rim would give a four-clique. -/
lemma not_wheelWalk_three (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    ¬WheelWalk G 3 := by
  classical
  rintro ⟨v,a,w,hw⟩
  cases w with
  | nil => simp at hw
  | cons hab w =>
    cases w with
    | nil => simp at hw
    | cons hbc w =>
      have hca := SimpleGraph.Walk.adj_of_length_eq_one
        (show w.length = 1 by simpa using hw)
      exact no_adj_common_neighbors hG a.property
        (show G.Adj v _ from Subtype.property _) hab
        (show G.Adj v _ from Subtype.property _) hca.symm hbc

/-- For a K4-free counterexample the robust odd length is at least five. -/
theorem fixed_odd_length_ge_five (G : SimpleGraph V) (hK : G.CliqueFree 4)
    (hG : ¬IsCountableUnionOfTriangleFree G) :
    ∃ n : ℕ, 5 ≤ n ∧ Odd n ∧ ∀ D : SimpleGraph V,
      IsCountableUnionOfTriangleFree D → WheelWalk (G \ D) n := by
  obtain ⟨n,ho,hn⟩ := fixed_odd_length G hG
  have hb : IsCountableUnionOfTriangleFree (⊥ : SimpleGraph V) :=
    ⟨fun _ => ⊥,fun _ => SimpleGraph.cliqueFree_bot (by decide),by simp⟩
  have hw : WheelWalk G n := by simpa using hn ⊥ hb
  have h1 : n ≠ 1 := fun he => not_wheelWalk_one G (he ▸ hw)
  have h3 : n ≠ 3 := fun he => not_wheelWalk_three G hK (he ▸ hw)
  refine ⟨n,?_,ho,hn⟩
  obtain ⟨k,hk⟩ := ho
  omega

#print axioms fixed_odd_length_ge_five
#print axioms fixed_odd_length
#print axioms cover_of_no_odd_wheel
end Erdos595RobustOddWheel
