import FormalConjecturesUtil
import Submission.UpToConeFan

/-! Bipartite suspensions and their local embedding test. -/
open Filter SimpleGraph Asymptotics Finset
namespace Erdos713Suspension
set_option maxHeartbeats 2000000

/-- Add adjacent universal anchors, one of each color. -/
def graph {W : Type*} (H : SimpleGraph W) (c : H.Coloring Bool) : SimpleGraph (Bool ⊕ W) where
  Adj a b := match a,b with
    | Sum.inl x, Sum.inl y => x ≠ y
    | Sum.inl x, Sum.inr y => x ≠ c y
    | Sum.inr x, Sum.inl y => c x ≠ y
    | Sum.inr x, Sum.inr y => H.Adj x y
  symm := by rintro (a|a) (b|b) h <;> exact h.symm
  loopless := by rintro (a|a) h; exact h rfl; exact H.loopless a h

instance {W : Type*} (H : SimpleGraph W) [DecidableRel H.Adj] (c : H.Coloring Bool) :
    DecidableRel (graph H c).Adj := by
  intro a b
  cases a <;> cases b <;> dsimp [graph] <;> infer_instance

private def flip : Equiv.Perm Bool where
  toFun b := !b
  invFun b := !b
  left_inv b := Bool.not_not b
  right_inv b := Bool.not_not b

lemma color_agreement_walk {W : Type*} {H : SimpleGraph W} (c d : H.Coloring Bool)
    {u v : W} (p : H.Walk u v) (h : c u = d u) : c v = d v := by
  induction p with
  | nil => exact h
  | @cons u v w huv p ih =>
    apply ih
    have hc := c.valid huv
    have hd := d.valid huv
    cases e1 : c u <;> cases e2 : c v <;> cases e3 : d u <;> cases e4 : d v <;>
      simp_all

lemma colorings_equiv {W : Type*} {H : SimpleGraph W} (hH : H.Connected)
    (c d : H.Coloring Bool) : ∃ e : Equiv.Perm Bool, ∀ w, d w = e (c w) := by
  classical
  let w₀ : W := hH.nonempty.some
  by_cases he : c w₀ = d w₀
  · refine ⟨Equiv.refl _,fun w => ?_⟩
    obtain ⟨p⟩ := hH w₀ w
    exact (color_agreement_walk c d p he).symm
  · let c' : H.Coloring Bool := Coloring.mk (fun w => !(c w))
      (by intro u v huv h; exact c.valid huv (by cases e1 : c u <;> cases e2 : c v <;> simp_all))
    have he' : c' w₀ = d w₀ := by
      change Bool.not (c w₀) = d w₀
      cases e1 : c w₀ <;> cases e2 : d w₀ <;> simp_all
    refine ⟨flip,fun w => ?_⟩
    obtain ⟨p⟩ := hH w₀ w
    exact (color_agreement_walk c' d p he').symm

def localSet {V : Type*} (G : SimpleGraph V) (u v : V) : Set V :=
  {z | z ≠ u ∧ z ≠ v ∧ (G.Adj u z ∨ G.Adj v z)}

lemma local_card_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : Nat.card (localSet G u v) ≤ G.degree u + G.degree v := by
  classical
  have hsub : (localSet G u v).toFinset ⊆ G.neighborFinset u ∪ G.neighborFinset v := by
    intro z hz
    rcases (show z ∈ localSet G u v from Set.mem_toFinset.mp hz).2.2 with h | h
    · exact mem_union_left _ (by simpa using h)
    · exact mem_union_right _ (by simpa using h)
  simpa only [Set.toFinset_card, Fintype.card_eq_nat_card, card_neighborFinset_eq_degree] using
    (card_le_card hsub).trans (card_union_le _ _)

lemma contained_of_local {W V : Type*} (H : SimpleGraph W) (c : H.Coloring Bool)
    (hH : H.Connected) (G : SimpleGraph V) (hBip : G.IsBipartite)
    {u v : V} (huv : G.Adj u v) (hlocal : H ⊑ G.induce (localSet G u v)) :
    graph H c ⊑ G := by
  classical
  obtain ⟨χ₀⟩ := hBip
  let χ : G.Coloring Bool := Coloring.mk (fun w => finTwoEquiv (χ₀ w))
    (by intro x y h he; exact χ₀.valid h (finTwoEquiv.injective he))
  have hχ : χ u ≠ χ v := χ.valid huv
  let anchor : Bool → V := fun b => if b = χ u then u else v
  have anchor_color (b : Bool) : χ (anchor b) = b := by
    dsimp only [anchor]
    split_ifs with hb
    · exact hb.symm
    · cases e1 : χ u <;> cases e2 : χ v <;> cases b <;> simp_all
  have anchor_inj : Function.Injective anchor := fun a b h => by
    simpa only [anchor_color] using congrArg χ h
  have anchor_adj (a b : Bool) (hab : a ≠ b) : G.Adj (anchor a) (anchor b) := by
    dsimp only [anchor]
    split_ifs with ha hb
    · exact (hab (ha.trans hb.symm)).elim
    · exact huv
    · exact huv.symm
    · have he : a = b := by
        cases e : χ u <;> cases a <;> cases b <;> simp_all
      exact (hab he).elim
  have anchor_local (a : Bool) (z : localSet G u v) (haz : a ≠ χ z) :
      G.Adj (anchor a) z := by
    rcases z.prop.2.2 with hz | hz
    · have hc : a = χ u := by
        have hh := χ.valid hz
        cases e1 : χ u <;> cases e2 : χ z <;> cases a <;> simp_all
      simpa only [anchor, if_pos hc] using hz
    · have hc : a ≠ χ u := by
        have hh := χ.valid hz
        cases e1 : χ u <;> cases e2 : χ v <;> cases e3 : χ z <;> cases a <;> simp_all
      simpa only [anchor, if_neg hc] using hz
  obtain ⟨f⟩ := hlocal
  let d : H.Coloring Bool := χ.comp ((Copy.induce G (localSet G u v)).comp f).toHom
  obtain ⟨e,he⟩ := colorings_equiv hH c d
  let m : Bool ⊕ W → V := Sum.elim (fun b => anchor (e b)) (fun w => (f w).val)
  have hcross (a : Bool) (w : W) : anchor (e a) ≠ (f w).val := by
    dsimp only [anchor]
    split_ifs
    · exact (f w).prop.1.symm
    · exact (f w).prop.2.1.symm
  refine ⟨⟨⟨m,?_⟩,?_⟩⟩
  · rintro (a|a) (b|b) hab
    · exact anchor_adj _ _ (e.injective.ne hab)
    · apply anchor_local
      change e a ≠ d b
      rw [he]
      exact e.injective.ne hab
    · apply Adj.symm
      apply anchor_local
      change e b ≠ d a
      rw [he]
      exact e.injective.ne hab.symm
    · exact f.toHom.map_adj hab
  · rintro (a|a) (b|b) hab
    · exact congrArg Sum.inl (e.injective (anchor_inj hab))
    · exact (hcross a b hab).elim
    · exact (hcross b a hab.symm).elim
    · exact congrArg Sum.inr (f.injective (Subtype.ext hab))

lemma local_free {W V : Type*} (H : SimpleGraph W) (c : H.Coloring Bool)
    (hH : H.Connected) (G : SimpleGraph V) (hBip : G.IsBipartite)
    (hfree : (graph H c).Free G) {u v : V} (huv : G.Adj u v) :
    H.Free (G.induce (localSet G u v)) := fun h => hfree (contained_of_local H c hH G hBip huv h)

end Erdos713Suspension
